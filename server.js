// ARIA cam relay — the ESP32-CAM pushes JPEG frames here (it sits behind a
// home router, so nothing on the internet can reach it directly); viewers
// on any phone/browser watch the latest frames as an MJPEG stream.
//
//   GET  /ws         camera → relay WebSocket (header X-Cam-Key: $CAM_KEY).
//                    Binary messages are JPEG frames; the relay sends the
//                    live viewer count as a text message every second so the
//                    camera can slow down when nobody is watching
//   POST /push       older one-request-per-frame uplink (same key, body: JPEG,
//                    replies with the viewer count). Much slower over long
//                    distances: every frame waits a full round trip
//   GET  /?key=      viewer page      (key: $VIEW_KEY)
//   GET  /stream     MJPEG stream     (?key=)
//   GET  /snapshot   latest JPEG      (?key=)
//   GET  /status     JSON             (?key=)
//   GET  /healthz    Render health check
//
// Zero dependencies — Node's http module only.
'use strict';

const http = require('http');
const crypto = require('crypto');

const PORT = process.env.PORT || 10000;
const CAM_KEY = process.env.CAM_KEY || '';
const VIEW_KEY = process.env.VIEW_KEY || '';
const MAX_FRAME_BYTES = 512 * 1024;
const OFFLINE_AFTER_MS = 10000;   // no frame for this long → camera offline
const POLL_VIEWER_MS = 5000;      // snapshot-polling viewers count for this long

if (!CAM_KEY || !VIEW_KEY) {
  console.error('CAM_KEY and VIEW_KEY environment variables are required');
  process.exit(1);
}

let latestFrame = null;
let latestAt = 0;
let lastPollAt = 0;
const streamViewers = new Set();

function keyMatches(given, expected) {
  const a = Buffer.from(String(given || ''));
  const b = Buffer.from(expected);
  return a.length === b.length && crypto.timingSafeEqual(a, b);
}

function viewerCount() {
  return streamViewers.size + (Date.now() - lastPollAt < POLL_VIEWER_MS ? 1 : 0);
}

function send(res, code, type, body, extra = {}) {
  res.writeHead(code, { 'Content-Type': type, 'Cache-Control': 'no-store', ...extra });
  res.end(body);
}

function writeFrame(res, frame) {
  res.write(`--frame\r\nContent-Type: image/jpeg\r\nContent-Length: ${frame.length}\r\n\r\n`);
  res.write(frame);
  res.write('\r\n');
}

function handlePush(req, res) {
  if (!keyMatches(req.headers['x-cam-key'], CAM_KEY)) return send(res, 401, 'text/plain', 'bad key');
  const chunks = [];
  let size = 0;
  req.on('data', (c) => {
    size += c.length;
    if (size > MAX_FRAME_BYTES) { send(res, 413, 'text/plain', 'frame too large'); req.destroy(); return; }
    chunks.push(c);
  });
  req.on('end', () => {
    if (res.writableEnded) return;
    if (!acceptFrame(Buffer.concat(chunks))) return send(res, 400, 'text/plain', 'not a JPEG');
    send(res, 200, 'text/plain', String(viewerCount()));
  });
}

function acceptFrame(frame) {
  if (frame.length < 4 || frame[0] !== 0xff || frame[1] !== 0xd8) return false;
  latestFrame = frame;
  latestAt = Date.now();
  for (const v of streamViewers) {
    if (v.writableLength > 2 * frame.length) continue;   // slow viewer: drop this frame for them
    writeFrame(v, frame);
  }
  return true;
}

function handleStream(req, res) {
  res.writeHead(200, {
    'Content-Type': 'multipart/x-mixed-replace; boundary=frame',
    'Cache-Control': 'no-store',
    'X-Accel-Buffering': 'no',
    Connection: 'close',
  });
  if (latestFrame) writeFrame(res, latestFrame);
  streamViewers.add(res);
  notifyCamera();   // speed the camera up now, not at the next tick
  // res (not req): req 'close' fires once the request body is consumed, not on disconnect
  const drop = () => streamViewers.delete(res);
  res.on('close', drop);
  res.on('error', drop);
}

function status() {
  const age = latestAt ? Date.now() - latestAt : null;
  return { online: age !== null && age < OFFLINE_AFTER_MS, lastFrameAgeMs: age, viewers: viewerCount() };
}

const server = http.createServer((req, res) => {
  const url = new URL(req.url, 'http://x');
  const key = url.searchParams.get('key');
  const authed = keyMatches(key, VIEW_KEY);

  if (req.method === 'POST' && url.pathname === '/push') return handlePush(req, res);
  if (req.method !== 'GET' && req.method !== 'HEAD') return send(res, 405, 'text/plain', 'method not allowed');

  switch (url.pathname) {
    case '/healthz':
      return send(res, 200, 'text/plain', 'ok');
    case '/':
      return send(res, authed ? 200 : 401, 'text/html; charset=utf-8', authed ? viewerPage() : keyPage(key !== null),
        { 'Referrer-Policy': 'no-referrer' });
    case '/stream':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return handleStream(req, res);
    case '/snapshot':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      lastPollAt = Date.now();
      if (!latestFrame) return send(res, 503, 'text/plain', 'no frame yet');
      return send(res, 200, 'image/jpeg', latestFrame);
    case '/status':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return send(res, 200, 'application/json', JSON.stringify(status()));
    default:
      return send(res, 404, 'text/plain', 'not found');
  }
});

// ── Camera WebSocket uplink ─────────────────────────────────────────────
// Minimal RFC 6455 server for the single camera connection, so the relay
// stays dependency-free.
const WS_GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
let camSocket = null;

function wsFrame(opcode, payload) {
  const n = payload.length;
  const head = n < 126 ? Buffer.from([0x80 | opcode, n])
    : n < 65536 ? Buffer.from([0x80 | opcode, 126, n >> 8, n & 0xff])
    : (() => { const h = Buffer.alloc(10); h[0] = 0x80 | opcode; h[1] = 127; h.writeBigUInt64BE(BigInt(n), 2); return h; })();
  return Buffer.concat([head, payload]);
}

function notifyCamera() {
  if (camSocket && !camSocket.destroyed) camSocket.write(wsFrame(0x1, Buffer.from(String(viewerCount()))));
}
setInterval(notifyCamera, 1000);

server.on('upgrade', (req, socket) => {
  const url = new URL(req.url, 'http://x');
  if (url.pathname !== '/ws' || String(req.headers.upgrade).toLowerCase() !== 'websocket' ||
      !req.headers['sec-websocket-key'] || !keyMatches(req.headers['x-cam-key'], CAM_KEY)) {
    socket.end('HTTP/1.1 401 Unauthorized\r\nConnection: close\r\n\r\n');
    return;
  }
  const accept = crypto.createHash('sha1').update(req.headers['sec-websocket-key'] + WS_GUID).digest('base64');
  socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n' +
               `Sec-WebSocket-Accept: ${accept}\r\n\r\n`);
  socket.setNoDelay(true);
  if (camSocket) camSocket.destroy();   // newest camera connection wins
  camSocket = socket;
  console.log('camera connected');
  notifyCamera();

  let buf = Buffer.alloc(0);
  let parts = [];
  let partsLen = 0;
  socket.on('data', (chunk) => {
    buf = buf.length ? Buffer.concat([buf, chunk]) : chunk;
    for (;;) {
      if (buf.length < 2) return;
      const fin = buf[0] & 0x80, opcode = buf[0] & 0x0f, masked = buf[1] & 0x80;
      let len = buf[1] & 0x7f, off = 2;
      if (len === 126) { if (buf.length < 4) return; len = buf.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (buf.length < 10) return; len = Number(buf.readBigUInt64BE(2)); off = 10; }
      if (partsLen + len > MAX_FRAME_BYTES) { socket.destroy(); return; }
      const maskAt = off;
      if (masked) off += 4;
      if (buf.length < off + len) return;   // wait for the rest of this message
      const payload = Buffer.from(buf.subarray(off, off + len));
      if (masked) for (let i = 0; i < len; i++) payload[i] ^= buf[maskAt + (i & 3)];
      buf = buf.subarray(off + len);

      if (opcode === 0x8) { socket.end(wsFrame(0x8, Buffer.alloc(0))); return; }   // close
      if (opcode === 0x9) { socket.write(wsFrame(0xA, payload)); continue; }        // ping → pong
      if (opcode === 0x2 || opcode === 0x0) {                                        // binary / continuation
        parts.push(payload);
        partsLen += len;
        if (fin) { acceptFrame(Buffer.concat(parts)); parts = []; partsLen = 0; }
      }
    }
  });
  socket.on('error', () => socket.destroy());
  socket.on('close', () => {
    if (camSocket === socket) camSocket = null;
    console.log('camera disconnected');
  });
});

server.listen(PORT, () => console.log(`cam relay listening on :${PORT}`));

// ── Pages ───────────────────────────────────────────────────────────────
const STYLE = `
  :root { color-scheme: dark; }
  * { box-sizing: border-box; }
  body { margin: 0; min-height: 100vh; background: #0b0d10; color: #e8eaed;
         font: 15px/1.4 system-ui, -apple-system, sans-serif; display: flex; flex-direction: column; }
  header { display: flex; align-items: center; justify-content: space-between; padding: 12px 16px; gap: 12px; }
  h1 { font-size: 16px; margin: 0; font-weight: 600; }
  .pill { font-size: 13px; padding: 4px 10px; border-radius: 999px; background: #1f2329; white-space: nowrap; }
  .pill.live { background: #12391f; color: #6ee7a0; }
  .pill.off { background: #3a1616; color: #fca5a5; }
  main { flex: 1; display: flex; align-items: center; justify-content: center; padding: 0 16px; }
  img { width: 100%; max-width: 960px; aspect-ratio: 4 / 3; object-fit: contain; background: #000; border-radius: 10px; }
  footer { display: flex; gap: 10px; justify-content: center; padding: 16px; flex-wrap: wrap; }
  button, a.btn { background: #1f2329; color: #e8eaed; border: 1px solid #2d333b; border-radius: 8px;
                  padding: 10px 16px; font: inherit; text-decoration: none; cursor: pointer; }
  form { margin: auto; padding: 24px 16px; display: flex; flex-direction: column; gap: 12px; width: 100%; max-width: 360px; }
  input { background: #15181c; color: inherit; border: 1px solid #2d333b; border-radius: 8px; padding: 10px 12px; font: inherit; }
  .err { color: #fca5a5; margin: 0; }
`;

function keyPage(wrongKey) {
  return `<!doctype html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1"><title>ARIA Cam</title>
<style>${STYLE}</style></head><body>
<form method="get" action="/">
  <h1>ARIA Cam</h1>
  <p>Enter the view key to watch the live feed.</p>
  ${wrongKey ? '<p class="err">That key is not valid.</p>' : ''}
  <input name="key" type="password" placeholder="View key" autocomplete="off" required autofocus>
  <button type="submit">Watch</button>
</form></body></html>`;
}

function viewerPage() {
  return `<!doctype html><html><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1"><title>ARIA Cam</title>
<style>${STYLE}</style></head><body>
<header><h1>ARIA Cam</h1><span id="pill" class="pill">Connecting…</span></header>
<main><img id="feed" alt="Live camera feed"></main>
<footer>
  <button id="fs" type="button">Fullscreen</button>
  <a id="snap" class="btn" download="aria-cam.jpg">Save snapshot</a>
</footer>
<script>
  const key = new URLSearchParams(location.search).get('key');
  const q = '?key=' + encodeURIComponent(key);
  const img = document.getElementById('feed');
  const pill = document.getElementById('pill');
  document.getElementById('snap').href = '/snapshot' + q;
  document.getElementById('fs').onclick = () => (img.requestFullscreen || img.webkitRequestFullscreen || (() => {})).call(img);

  // MJPEG stream; if the browser can't render it, fall back to polling snapshots.
  let polling = false;
  img.onerror = () => {
    if (polling) return;
    polling = true;
    const tick = () => { img.src = '/snapshot' + q + '&t=' + Date.now(); };
    img.onload = () => setTimeout(tick, 250);
    img.onerror = () => setTimeout(tick, 2000);
    tick();
  };
  img.src = '/stream' + q;

  async function refresh() {
    try {
      const s = await (await fetch('/status' + q, { cache: 'no-store' })).json();
      if (s.online) {
        pill.className = 'pill live';
        pill.textContent = 'Live · ' + s.viewers + ' watching';
      } else {
        pill.className = 'pill off';
        pill.textContent = s.lastFrameAgeMs === null ? 'Camera offline'
          : 'Camera offline · last frame ' + Math.round(s.lastFrameAgeMs / 1000) + 's ago';
      }
    } catch { pill.className = 'pill off'; pill.textContent = 'Relay unreachable'; }
  }
  refresh();
  setInterval(refresh, 3000);
</script></body></html>`;
}
