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
//   POST /meta       tracker → relay  (header X-Cam-Key, JSON body): face boxes,
//                    names, emotions and the robot's mood, drawn over the video
//   GET  /events     Server-Sent Events stream of /meta updates (?key=)
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

const MAX_META_BYTES = 8 * 1024;

let latestFrame = null;
let latestAt = 0;
let lastPollAt = 0;
const streamViewers = new Set();
let latestMeta = null;            // JSON string of the last /meta
const metaSubscribers = new Set();

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

function handleMeta(req, res) {
  if (!keyMatches(req.headers['x-cam-key'], CAM_KEY)) return send(res, 401, 'text/plain', 'bad key');
  const chunks = [];
  let size = 0;
  req.on('data', (c) => {
    size += c.length;
    if (size > MAX_META_BYTES) { send(res, 413, 'text/plain', 'too large'); req.destroy(); return; }
    chunks.push(c);
  });
  req.on('end', () => {
    if (res.writableEnded) return;
    let meta;
    try { meta = JSON.parse(Buffer.concat(chunks).toString('utf8')); } catch { return send(res, 400, 'text/plain', 'bad json'); }
    latestMeta = JSON.stringify(meta);            // re-serialised: only valid JSON reaches viewers
    for (const s of metaSubscribers) s.write(`data: ${latestMeta}\n\n`);
    send(res, 204, 'text/plain', '');
  });
}

function handleEvents(req, res) {
  res.writeHead(200, {
    'Content-Type': 'text/event-stream',
    'Cache-Control': 'no-store',
    'X-Accel-Buffering': 'no',
    Connection: 'keep-alive',
  });
  res.write(': connected\n\n');          // flush headers now — Node holds them until the first write
  if (latestMeta) res.write(`data: ${latestMeta}\n\n`);
  metaSubscribers.add(res);
  const ping = setInterval(() => res.write(': ping\n\n'), 15000);   // keep proxies from idling it out
  res.on('close', () => { clearInterval(ping); metaSubscribers.delete(res); });
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
  if (req.method === 'POST' && url.pathname === '/meta') return handleMeta(req, res);
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
    case '/events':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return handleEvents(req, res);
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
  main { flex: 1; display: flex; flex-direction: column; align-items: center; justify-content: center;
         gap: 12px; padding: 0 16px; }
  .stage { position: relative; width: 100%; max-width: 960px; }
  img { display: block; width: 100%; aspect-ratio: 4 / 3; object-fit: contain; background: #000; border-radius: 10px; }
  #overlay { position: absolute; inset: 0; width: 100%; height: 100%; pointer-events: none; }
  .info { display: flex; gap: 10px; width: 100%; max-width: 960px; flex-wrap: wrap; }
  .card { flex: 1 1 200px; background: #15181c; border: 1px solid #2d333b; border-radius: 10px; padding: 10px 14px; }
  .card .label { font-size: 12px; color: #9aa0a6; text-transform: uppercase; letter-spacing: .04em; }
  .card .value { font-size: 17px; margin-top: 2px; }
  .card .sub { font-size: 13px; color: #9aa0a6; }
  .meter { height: 4px; background: #2d333b; border-radius: 2px; margin-top: 6px; overflow: hidden; }
  .meter > span { display: block; height: 100%; background: #6ee7a0; width: 0; transition: width .6s; }
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
<main>
  <div class="stage"><img id="feed" alt="Live camera feed"><canvas id="overlay"></canvas></div>
  <div class="info">
    <div class="card"><div class="label">In view</div><div class="value" id="who">—</div><div class="sub" id="who-sub">face tracker offline</div></div>
    <div class="card"><div class="label">ARIA's mood</div><div class="value" id="mood">—</div>
      <div class="sub">energy</div><div class="meter"><span id="energy"></span></div></div>
  </div>
</main>
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
  const stage = document.querySelector('.stage');   // fullscreen the video + overlay together
  document.getElementById('fs').onclick = () =>
    (stage.requestFullscreen || stage.webkitRequestFullscreen || (() => {})).call(stage);

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

  // ── Face tracker overlay (from the laptop tracker via /meta → /events) ──
  const EMOJI = { happy: '😊', surprise: '😮', sad: '😢', angry: '😠', neutral: '🙂' };
  const EXPR_MOOD = { purr: '😌 purring', heart: '😍 in love', yawn: '🥱 yawning', sideeye: '😒 sulking',
                      wink: '😉 winking', surprise: '😲 surprised', think: '🤔 thinking',
                      curious: '🧐 curious', squint: '🤨 suspicious', wake: '😪 waking up' };
  const canvas = document.getElementById('overlay'), ctx = canvas.getContext('2d');
  let meta = null, metaAt = 0;
  const shown = [];                        // smoothed boxes being drawn

  const es = new EventSource('/events' + q);
  es.onmessage = (e) => { try { meta = JSON.parse(e.data); metaAt = Date.now(); updateCards(); } catch {} };

  function updateCards() {
    const fresh = meta && Date.now() - metaAt < 3000;
    const faces = fresh ? (meta.faces || []) : [];
    const who = document.getElementById('who'), sub = document.getElementById('who-sub');
    if (!fresh) { who.textContent = '—'; sub.textContent = 'face tracker offline'; }
    else if (!faces.length) { who.textContent = 'Nobody'; sub.textContent = 'watching the room'; }
    else {
      const f = faces[0];
      const name = f.id === 'known' ? f.name : f.id === 'unknown' ? 'Stranger' : 'Someone';
      who.textContent = name + ' ' + (EMOJI[f.emo] || '');
      sub.textContent = (faces.length > 1 ? faces.length + ' people · ' : '') + (f.emo || 'neutral')
        + (f.look ? ' · looking at the camera' : '');
    }
    const r = fresh && meta.robot;
    const mood = document.getElementById('mood');
    if (!r) { mood.textContent = '—'; }
    else {
      mood.textContent = r.sleeping ? '😴 asleep' : EXPR_MOOD[r.expr]
        || (r.energy < 0.3 ? '😩 tired' : r.boredom > 0.5 ? '😐 bored' : r.affection > 0.7 ? '🥰 affectionate' : '🙂 calm');
      document.getElementById('energy').style.width = Math.round((r.energy || 0) * 100) + '%';
    }
  }
  setInterval(updateCards, 1000);

  function draw() {
    const W = img.clientWidth, H = img.clientHeight, dpr = window.devicePixelRatio || 1;
    if (canvas.width !== Math.round(W * dpr)) { canvas.width = Math.round(W * dpr); canvas.height = Math.round(H * dpr); }
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, W, H);
    // where the picture actually sits inside the letterboxed <img>
    const nw = img.naturalWidth || 4, nh = img.naturalHeight || 3, s = Math.min(W / nw, H / nh);
    const dw = nw * s, dh = nh * s, ox = (W - dw) / 2, oy = (H - dh) / 2;
    const faces = meta && Date.now() - metaAt < 2500 ? (meta.faces || []) : [];
    faces.forEach((f, i) => {                // ease each box toward its latest position
      const t = shown[i] || (shown[i] = { ...f });
      for (const k of ['x', 'y', 'w', 'h']) t[k] += (f[k] - t[k]) * 0.35;
    });
    shown.length = faces.length;
    faces.forEach((f, i) => {
      const b = shown[i], x = ox + b.x * dw, y = oy + b.y * dh, w = b.w * dw, h = b.h * dh;
      const color = f.id === 'known' ? '#6ee7a0' : f.id === 'unknown' ? '#fbbf24' : '#e8eaed';
      ctx.strokeStyle = color; ctx.lineWidth = 2;
      const c = Math.min(w, h) * 0.22;         // corner brackets
      ctx.beginPath();
      [[x, y, 1, 1], [x + w, y, -1, 1], [x, y + h, 1, -1], [x + w, y + h, -1, -1]].forEach(([px, py, sx, sy]) => {
        ctx.moveTo(px + sx * c, py); ctx.lineTo(px, py); ctx.lineTo(px, py + sy * c);
      });
      ctx.stroke();
      const label = (f.id === 'known' ? f.name : f.id === 'unknown' ? 'Stranger' : '…') + ' ' + (EMOJI[f.emo] || '');
      ctx.font = '600 13px system-ui, sans-serif';
      const tw = ctx.measureText(label).width + 12, ly = Math.max(0, y - 22);
      ctx.fillStyle = 'rgba(11,13,16,0.75)'; ctx.fillRect(x, ly, tw, 20);
      ctx.fillStyle = color; ctx.fillText(label, x + 6, ly + 14);
    });
    requestAnimationFrame(draw);
  }
  requestAnimationFrame(draw);
</script></body></html>`;
}
