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
//   GET  /events     Server-Sent Events: /meta updates as messages, plus named
//                    "log" events for the activity timeline (?key=)
//   GET  /?key=      viewer page      (key: $VIEW_KEY)
//   POST /cmd        page → camera command (header X-Admin-Key: $ADMIN_KEY,
//                    else $CAM_KEY; JSON {cmd, args}) — LED, night mode,
//                    privacy, resolution, restart
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
const ADMIN_KEY = process.env.ADMIN_KEY || CAM_KEY;   // controls; defaults to the camera's key
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
const frameTimes = [];            // arrival times of recent frames, for the fps readout
let frameSize = null;             // {w, h} from the latest JPEG's header

// Activity timeline, derived from /meta. Presence is debounced — a face that
// drops out for a frame or two doesn't log "left" and "arrived" again.
const LOG_MAX = 30;
const activity = [];              // newest first: {t, kind, text}
const presence = { here: false, lastFace: 0, who: null, sleeping: null };

// Camera state reported over its WebSocket every ~2 s (settings + health).
let camState = null;

function broadcast(event, obj) {
  const line = `event: ${event}\ndata: ${JSON.stringify(obj)}\n\n`;
  for (const s of metaSubscribers) s.write(line);
}

function handleCamText(text) {
  let m;
  try { m = JSON.parse(text); } catch { return; }
  if (m.t === 'state') {
    delete m.t;
    const wasPrivate = camState && camState.privacy;
    camState = m;
    broadcast('cam', camState);
    if (camState.privacy && !wasPrivate) logEvent('privacy', 'Privacy mode on');
    if (!camState.privacy && wasPrivate) logEvent('privacy', 'Privacy mode off');
  } else if (m.t === 'motion') {
    logEvent('motion', 'Motion detected');
  }
}

const COMMANDS = {                // name → argument validator
  led: (a) => /^\d{1,3}$/.test(a[0]) && +a[0] <= 100,
  ledauto: (a) => /^[01]$/.test(a[0]),
  night: (a) => ['auto', 'on', 'off'].includes(a[0]),
  privacy: (a) => /^[01]$/.test(a[0]),
  privhours: (a) => a.length === 2 && a.every((h) => /^\d{1,2}$/.test(h) && +h < 24),
  profile: (a) => ['auto', '0', '1'].includes(a[0]),
  sensitivity: (a) => ['low', 'medium', 'high'].includes(a[0]),
  restart: (a) => a.length === 0,
};

function handleCmd(req, res) {
  if (!keyMatches(req.headers['x-admin-key'], ADMIN_KEY)) return send(res, 401, 'text/plain', 'bad admin key');
  const chunks = [];
  req.on('data', (c) => { chunks.push(c); if (chunks.length > 8) req.destroy(); });
  req.on('end', () => {
    let body;
    try { body = JSON.parse(Buffer.concat(chunks).toString('utf8')); } catch { return send(res, 400, 'text/plain', 'bad json'); }
    const cmd = String(body.cmd || ''), args = (body.args || []).map(String);
    if (!COMMANDS[cmd] || !COMMANDS[cmd](args)) return send(res, 400, 'text/plain', 'unknown command or bad arguments');
    if (!camSocket || camSocket.destroyed) return send(res, 503, 'text/plain', 'camera not connected');
    camSocket.write(wsFrame(0x1, Buffer.from([cmd, ...args].join(' '))));
    send(res, 202, 'text/plain', 'sent');
  });
}

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

// Width/height from a baseline or progressive JPEG's SOF marker.
function jpegSize(buf) {
  let i = 2;
  while (i + 9 < buf.length) {
    if (buf[i] !== 0xff) { i++; continue; }
    const marker = buf[i + 1];
    if (marker === 0xc0 || marker === 0xc2) return { h: buf.readUInt16BE(i + 5), w: buf.readUInt16BE(i + 7) };
    if (marker === 0xd8 || marker === 0x01 || (marker >= 0xd0 && marker <= 0xd7)) { i += 2; continue; }
    i += 2 + buf.readUInt16BE(i + 2);
  }
  return null;
}

function fps() {
  const now = Date.now();
  while (frameTimes.length && now - frameTimes[0] > 5000) frameTimes.shift();
  return frameTimes.length / 5;
}

function logEvent(kind, text) {
  const e = { t: Date.now(), kind, text };
  activity.unshift(e);
  if (activity.length > LOG_MAX) activity.pop();
  for (const s of metaSubscribers) s.write(`event: log\ndata: ${JSON.stringify(e)}\n\n`);
}

function trackActivity(meta) {
  const now = Date.now();
  const f = (meta.faces || [])[0];
  if (f) {
    presence.lastFace = now;
    if (!presence.here) { presence.here = true; logEvent('arrive', 'Someone appeared'); }
    const who = f.id === 'known' ? f.name : f.id === 'unknown' ? 'stranger' : null;
    if (who && who !== presence.who) {
      presence.who = who;
      if (f.id === 'known') logEvent('known', `${who} is here`);
      else logEvent('stranger', 'Unknown person in view');
    }
  }
  const r = meta.robot;
  if (r && typeof r.sleeping === 'boolean' && r.sleeping !== presence.sleeping) {
    if (presence.sleeping !== null) logEvent(r.sleeping ? 'sleep' : 'wake', r.sleeping ? 'ARIA fell asleep' : 'ARIA woke up');
    presence.sleeping = r.sleeping;
  }
}

setInterval(() => {                               // "left" once nobody's been seen for 6s
  if (presence.here && Date.now() - presence.lastFace > 6000) {
    const who = presence.who && presence.who !== 'stranger' ? presence.who : 'Everyone';
    presence.here = false;
    presence.who = null;
    logEvent('leave', `${who} left`);
  }
}, 1000);

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
    trackActivity(meta);
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
  for (const e of [...activity].reverse()) res.write(`event: log\ndata: ${JSON.stringify(e)}\n\n`);
  if (camState) res.write(`event: cam\ndata: ${JSON.stringify(camState)}\n\n`);
  metaSubscribers.add(res);
  const ping = setInterval(() => res.write(': ping\n\n'), 15000);   // keep proxies from idling it out
  res.on('close', () => { clearInterval(ping); metaSubscribers.delete(res); });
}

function acceptFrame(frame) {
  if (frame.length < 4 || frame[0] !== 0xff || frame[1] !== 0xd8) return false;
  latestFrame = frame;
  latestAt = Date.now();
  frameTimes.push(latestAt);
  frameSize = jpegSize(frame) || frameSize;
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
  return { online: age !== null && age < OFFLINE_AFTER_MS, lastFrameAgeMs: age, viewers: viewerCount(),
           fps: Math.round(fps() * 10) / 10, width: frameSize && frameSize.w, height: frameSize && frameSize.h };
}

const server = http.createServer((req, res) => {
  const url = new URL(req.url, 'http://x');
  const key = url.searchParams.get('key');
  const authed = keyMatches(key, VIEW_KEY);

  if (req.method === 'POST' && url.pathname === '/push') return handlePush(req, res);
  if (req.method === 'POST' && url.pathname === '/meta') return handleMeta(req, res);
  if (req.method === 'POST' && url.pathname === '/cmd') return handleCmd(req, res);
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
      if (opcode === 0x1 && fin) { handleCamText(payload.toString('utf8')); continue; }   // state / motion
      if (opcode === 0x2 || opcode === 0x0) {                                        // binary / continuation
        parts.push(payload);
        partsLen += len;
        if (fin) { acceptFrame(Buffer.concat(parts)); parts = []; partsLen = 0; }
      }
    }
  });
  socket.on('error', () => socket.destroy());
  socket.on('close', () => {
    if (camSocket === socket) { camSocket = null; camState = null; broadcast('cam', null); }
    console.log('camera disconnected');
  });
});

server.listen(PORT, () => console.log(`cam relay listening on :${PORT}`));

// ── Pages ───────────────────────────────────────────────────────────────
// Dark "smart camera" dashboard. No external assets: system fonts, inline SVG.
const STYLE = `
  :root {
    color-scheme: dark;
    --bg: #07090c; --surface: #0e1217; --surface-2: #141920; --line: #202833;
    --text: #e6edf3; --muted: #8b97a6; --accent: #5eead4; --accent-dim: rgba(94,234,212,.14);
    --good: #4ade80; --warn: #fbbf24; --bad: #f87171; --violet: #a78bfa;
    --radius: 16px;
  }
  * { box-sizing: border-box; }
  [hidden] { display: none !important; }   /* component display rules must not beat hidden */
  html, body { margin: 0; background: var(--bg); color: var(--text); }
  body { min-height: 100vh; font: 15px/1.45 ui-sans-serif, system-ui, -apple-system, "Segoe UI", Roboto, sans-serif;
         -webkit-font-smoothing: antialiased; }
  button, a { font: inherit; color: inherit; }

  .top { display: flex; align-items: center; justify-content: space-between; gap: 12px;
         max-width: 1280px; margin: 0 auto; padding: 16px; }
  .brand { display: flex; align-items: center; gap: 12px; }
  .logo { width: 40px; height: 40px; border-radius: 12px; background: var(--surface-2); border: 1px solid var(--line);
          display: grid; place-items: center; }
  .logo svg { width: 26px; height: 26px; }
  .name { font-weight: 700; letter-spacing: .08em; }
  .tag { font-size: 12px; color: var(--muted); }
  .top-right { display: flex; align-items: center; gap: 10px; }
  .clock { font-variant-numeric: tabular-nums; color: var(--muted); font-size: 14px; }
  .live { display: inline-flex; align-items: center; gap: 8px; padding: 6px 12px; border-radius: 999px;
          background: var(--surface-2); border: 1px solid var(--line); font-size: 13px; white-space: nowrap; }
  .live i { width: 8px; height: 8px; border-radius: 50%; background: var(--muted); }
  .live.on i { background: var(--good); box-shadow: 0 0 0 0 rgba(74,222,128,.6); animation: pulse 1.8s infinite; }
  .live.off i { background: var(--bad); }
  @keyframes pulse { 0% { box-shadow: 0 0 0 0 rgba(74,222,128,.55); } 70% { box-shadow: 0 0 0 8px rgba(74,222,128,0); }
                     100% { box-shadow: 0 0 0 0 rgba(74,222,128,0); } }

  .grid { display: grid; grid-template-columns: minmax(0, 1fr) 340px; gap: 16px;
          max-width: 1280px; margin: 0 auto; padding: 0 16px 16px; }
  @media (max-width: 900px) { .grid { grid-template-columns: minmax(0, 1fr); } }

  .stage { position: relative; aspect-ratio: 4 / 3; background: #000; border-radius: var(--radius);
           overflow: hidden; border: 1px solid var(--line); }
  .stage img { position: absolute; inset: 0; width: 100%; height: 100%; object-fit: contain; }
  #overlay { position: absolute; inset: 0; width: 100%; height: 100%; pointer-events: none; }
  .hud { position: absolute; display: flex; gap: 6px; align-items: center; pointer-events: none; }
  .hud.tl { top: 12px; left: 12px; } .hud.tr { top: 12px; right: 12px; }
  @media (max-width: 420px) { #hud-res { display: none; } }   /* keep the two chip rows apart on small phones */
  .chip, .rec { padding: 4px 10px; border-radius: 999px; font-size: 12px; font-weight: 600;
                background: rgba(7,9,12,.6); backdrop-filter: blur(6px); -webkit-backdrop-filter: blur(6px);
                border: 1px solid rgba(255,255,255,.08); font-variant-numeric: tabular-nums; }
  .rec { display: inline-flex; align-items: center; gap: 6px; color: #fff; }
  .rec i { width: 7px; height: 7px; border-radius: 50%; background: var(--bad); animation: blink 1.2s steps(2) infinite; }
  @keyframes blink { 50% { opacity: .25; } }
  .controls { position: absolute; right: 12px; bottom: 12px; display: flex; gap: 8px; opacity: 0; transition: opacity .2s; }
  .stage:hover .controls, .stage:focus-within .controls { opacity: 1; }
  @media (hover: none) { .controls { opacity: 1; } }
  .icon { width: 40px; height: 40px; display: grid; place-items: center; border-radius: 12px; cursor: pointer;
          background: rgba(7,9,12,.65); backdrop-filter: blur(6px); -webkit-backdrop-filter: blur(6px);
          border: 1px solid rgba(255,255,255,.1); text-decoration: none; }
  .icon svg { width: 20px; height: 20px; }
  .icon[aria-pressed="true"] { color: var(--accent); border-color: rgba(94,234,212,.4); }
  .offline { position: absolute; inset: 0; display: grid; place-content: center; justify-items: center; gap: 10px;
             background: radial-gradient(circle at center, rgba(20,25,32,.85), rgba(7,9,12,.95)); color: var(--muted);
             text-align: center; padding: 16px; }
  .offline[hidden] { display: none; }
  .offline svg { width: 40px; height: 40px; opacity: .7; }
  .offline b { color: var(--text); font-size: 17px; }
  .stage:fullscreen { border-radius: 0; border: 0; }

  .side { display: flex; flex-direction: column; gap: 16px; min-width: 0; }
  .card { background: var(--surface); border: 1px solid var(--line); border-radius: var(--radius); padding: 16px; }
  .card-head { display: flex; align-items: center; justify-content: space-between; gap: 8px; margin-bottom: 12px; }
  .card h2 { margin: 0; font-size: 12px; font-weight: 600; color: var(--muted); text-transform: uppercase; letter-spacing: .1em; }
  .mood { font-size: 14px; }
  .badge { min-width: 24px; padding: 2px 8px; border-radius: 999px; background: var(--surface-2);
           border: 1px solid var(--line); font-size: 12px; text-align: center; font-variant-numeric: tabular-nums; }

  .robot-wrap { position: relative; background: #020304; border-radius: 12px; border: 1px solid var(--line); overflow: hidden; }
  #robot { display: block; width: 100%; aspect-ratio: 2 / 1; image-rendering: pixelated;
           filter: drop-shadow(0 0 4px rgba(94,234,212,.55)); }
  .robot-off { position: absolute; inset: 0; display: grid; place-items: center; color: var(--muted); font-size: 13px; }
  .robot-off[hidden] { display: none; }
  .meters { display: grid; gap: 8px; margin-top: 14px; }
  .meter { display: grid; grid-template-columns: 76px 1fr 34px; align-items: center; gap: 10px; font-size: 13px; color: var(--muted); }
  .meter .bar { height: 6px; border-radius: 999px; background: var(--surface-2); overflow: hidden; }
  .meter .bar span { display: block; height: 100%; width: 0; border-radius: 999px; transition: width .8s ease; }
  .meter .val { text-align: right; font-variant-numeric: tabular-nums; }
  #m-energy { background: linear-gradient(90deg, #22d3ee, var(--accent)); }
  #m-affection { background: linear-gradient(90deg, #f472b6, #fb7185); }
  #m-boredom { background: linear-gradient(90deg, #64748b, #94a3b8); }

  .person { display: flex; align-items: center; gap: 12px; }
  .avatar { width: 48px; height: 48px; flex: none; border-radius: 50%; display: grid; place-items: center;
            font-weight: 700; font-size: 18px; background: var(--surface-2); border: 2px solid var(--line); color: var(--muted); }
  .avatar.known { border-color: var(--good); color: var(--good); background: rgba(74,222,128,.1); }
  .avatar.stranger { border-color: var(--warn); color: var(--warn); background: rgba(251,191,36,.1); }
  .avatar.seeing { border-color: var(--accent); color: var(--accent); background: var(--accent-dim); }
  .p-name { font-weight: 600; font-size: 16px; }
  .p-sub { font-size: 13px; color: var(--muted); }
  .emo { margin-left: auto; font-size: 28px; line-height: 1; }

  .log { list-style: none; margin: 0; padding: 0; display: grid; gap: 2px; max-height: 260px; overflow-y: auto; }
  .log li { display: grid; grid-template-columns: 10px 1fr auto; align-items: center; gap: 10px;
            padding: 8px 4px; border-bottom: 1px solid var(--line); font-size: 14px; }
  .log li:last-child { border-bottom: 0; }
  .log li i { width: 8px; height: 8px; border-radius: 50%; background: var(--muted); }
  .log li.known i { background: var(--good); } .log li.stranger i { background: var(--warn); }
  .log li.arrive i { background: var(--accent); } .log li.sleep i, .log li.wake i { background: var(--violet); }
  .log li time { font-size: 12px; color: var(--muted); font-variant-numeric: tabular-nums; }
  .log li.empty { display: block; color: var(--muted); border: 0; }
  .log li.new { animation: slidein .4s ease; }
  @keyframes slidein { from { opacity: 0; transform: translateY(-4px); } }


  .seg { display: inline-flex; background: var(--surface-2); border: 1px solid var(--line); border-radius: 10px; padding: 3px; gap: 2px; }
  .seg button { border: 0; background: transparent; color: var(--muted); padding: 6px 10px; border-radius: 7px; cursor: pointer; font-size: 13px; }
  .seg button[aria-pressed="true"] { background: var(--accent-dim); color: var(--accent); font-weight: 600; }
  .seg button:disabled { cursor: not-allowed; opacity: .5; }
  .ctl { display: grid; grid-template-columns: 1fr auto; align-items: center; gap: 10px; padding: 9px 0;
         border-bottom: 1px solid var(--line); font-size: 14px; }
  .ctl:last-of-type { border-bottom: 0; }
  .ctl small { display: block; color: var(--muted); font-size: 12px; }
  .switch { position: relative; width: 44px; height: 26px; border-radius: 999px; border: 1px solid var(--line);
            background: var(--surface-2); cursor: pointer; padding: 0; }
  .switch::after { content: ""; position: absolute; top: 3px; left: 3px; width: 18px; height: 18px; border-radius: 50%;
                   background: var(--muted); transition: transform .2s, background .2s; }
  .switch[aria-checked="true"] { background: var(--accent-dim); border-color: rgba(94,234,212,.4); }
  .switch[aria-checked="true"]::after { transform: translateX(18px); background: var(--accent); }
  .hours { display: flex; align-items: center; gap: 6px; font-size: 13px; color: var(--muted); }
  .hours select { background: var(--surface-2); color: var(--text); border: 1px solid var(--line); border-radius: 8px; padding: 5px; font: inherit; }
  .btn { background: var(--surface-2); border: 1px solid var(--line); border-radius: 10px; padding: 8px 12px; cursor: pointer; font-size: 13px; }
  .btn.primary { background: var(--accent); color: #04110f; border: 0; font-weight: 700; }
  .btn.danger { color: var(--bad); }
  .health { display: grid; grid-template-columns: repeat(2, 1fr); gap: 6px 12px; margin-top: 12px; font-size: 12px; color: var(--muted); }
  .health b { color: var(--text); font-weight: 600; font-variant-numeric: tabular-nums; }
  .locked { color: var(--muted); font-size: 13px; display: flex; align-items: center; justify-content: space-between; gap: 10px; }
  .log li.motion i { background: #fb923c; } .log li.privacy i { background: var(--violet); }
  .privacy-screen { position: absolute; inset: 0; display: grid; place-content: center; justify-items: center; gap: 8px;
                    background: repeating-linear-gradient(135deg, #0b0e13 0 14px, #0e1218 14px 28px); color: var(--muted); text-align: center; }
  .privacy-screen[hidden] { display: none; }
  .privacy-screen svg { width: 44px; height: 44px; color: var(--violet); }
  .privacy-screen b { color: var(--text); font-size: 17px; }
  .chip.night { color: #c4b5fd; }

  .foot { max-width: 1280px; margin: 0 auto; padding: 4px 16px 24px; color: var(--muted); font-size: 12px; }

  .login { min-height: 100vh; display: grid; place-items: center; padding: 16px; }
  .login form { width: 100%; max-width: 360px; background: var(--surface); border: 1px solid var(--line);
                border-radius: var(--radius); padding: 24px; display: grid; gap: 14px; }
  .login h1 { margin: 0; font-size: 20px; }
  .login p { margin: 0; color: var(--muted); }
  .login input { background: var(--surface-2); color: var(--text); border: 1px solid var(--line); border-radius: 10px;
                 padding: 12px; font: inherit; }
  .login input:focus { outline: 2px solid var(--accent); outline-offset: 1px; }
  .login button { background: var(--accent); color: #04110f; border: 0; border-radius: 10px; padding: 12px; font-weight: 700; cursor: pointer; }
  .err { color: var(--bad); }
`;

const LOGO = `<svg viewBox="0 0 26 26" fill="#5eead4" aria-hidden="true">
  <rect x="3" y="7" width="8" height="10" rx="3"/><rect x="15" y="7" width="8" height="10" rx="3"/>
  <rect x="5" y="9" width="2.5" height="2" rx="1" fill="#07090c"/><rect x="17" y="9" width="2.5" height="2" rx="1" fill="#07090c"/></svg>`;

function keyPage(wrongKey) {
  return `<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1"><meta name="theme-color" content="#07090c">
<title>ARIA Cam</title><style>${STYLE}</style></head><body>
<div class="login"><form method="get" action="/">
  <div class="brand"><div class="logo">${LOGO}</div><div><div class="name">ARIA</div><div class="tag">Home camera</div></div></div>
  <h1>Enter view key</h1>
  <p>This camera is private. Ask its owner for the key.</p>
  ${wrongKey ? '<p class="err">That key is not valid.</p>' : ''}
  <input name="key" type="password" placeholder="View key" autocomplete="off" required autofocus aria-label="View key">
  <button type="submit">Watch</button>
</form></div></body></html>`;
}

function viewerPage() {
  return `<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="theme-color" content="#07090c"><title>ARIA Cam</title>
<style>${STYLE}</style></head><body>
<header class="top">
  <div class="brand"><div class="logo">${LOGO}</div><div><div class="name">ARIA</div><div class="tag">Home camera</div></div></div>
  <div class="top-right"><span class="clock" id="clock"></span><span class="live" id="live"><i></i><span id="live-text">Connecting</span></span></div>
</header>

<main class="grid">
  <section aria-label="Live video">
    <div class="stage" id="stage">
      <img id="feed" alt="Live camera feed">
      <canvas id="overlay" aria-hidden="true"></canvas>
      <div class="hud tl"><span class="rec"><i></i>LIVE</span><span class="chip" id="hud-time"></span></div>
      <div class="hud tr"><span class="chip night" id="hud-night" hidden>☾ Night</span><span class="chip" id="hud-res">—</span><span class="chip" id="hud-fps">— fps</span></div>
      <div class="privacy-screen" id="privacy-screen" hidden>
        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" aria-hidden="true"><rect x="5" y="10" width="14" height="10" rx="2"/><path d="M8 10V7a4 4 0 0 1 8 0v3"/></svg>
        <b>Privacy mode on</b><span id="privacy-text">The camera isn&rsquo;t streaming or detecting.</span>
      </div>
      <div class="offline" id="offline" hidden>
        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.6" aria-hidden="true">
          <path d="M3 3l18 18M10.6 6H15a2 2 0 0 1 2 2v2l4-3v10M17 17H5a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2"/></svg>
        <b>Camera offline</b><span id="offline-text">Waiting for the camera…</span>
      </div>
      <div class="controls">
        <button class="icon" id="btn-overlay" aria-pressed="true" title="Face boxes" aria-label="Toggle face boxes">
          <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" aria-hidden="true">
            <path d="M4 8V5a1 1 0 0 1 1-1h3M16 4h3a1 1 0 0 1 1 1v3M20 16v3a1 1 0 0 1-1 1h-3M8 20H5a1 1 0 0 1-1-1v-3"/>
            <circle cx="12" cy="11" r="3"/><path d="M7.5 17.5a5 5 0 0 1 9 0"/></svg></button>
        <a class="icon" id="btn-snap" title="Save snapshot" aria-label="Save snapshot" download="aria-cam.jpg">
          <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" aria-hidden="true">
            <path d="M4 8a2 2 0 0 1 2-2h2l1.5-2h5L16 6h2a2 2 0 0 1 2 2v9a2 2 0 0 1-2 2H6a2 2 0 0 1-2-2z"/><circle cx="12" cy="12.5" r="3.5"/></svg></a>
        <button class="icon" id="btn-fs" title="Fullscreen" aria-label="Fullscreen">
          <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" aria-hidden="true">
            <path d="M4 9V4h5M20 9V4h-5M4 15v5h5M20 15v5h-5"/></svg></button>
      </div>
    </div>
  </section>

  <aside class="side">
    <section class="card" aria-label="ARIA">
      <div class="card-head"><h2>ARIA</h2><span class="mood" id="mood">—</span></div>
      <div class="robot-wrap"><canvas id="robot" width="128" height="64" aria-label="ARIA's face, live"></canvas>
        <div class="robot-off" id="robot-off">ARIA's face appears when the tracker is running</div></div>
      <div class="meters">
        <div class="meter"><span>Energy</span><div class="bar"><span id="m-energy"></span></div><span class="val" id="v-energy">–</span></div>
        <div class="meter"><span>Affection</span><div class="bar"><span id="m-affection"></span></div><span class="val" id="v-affection">–</span></div>
        <div class="meter"><span>Boredom</span><div class="bar"><span id="m-boredom"></span></div><span class="val" id="v-boredom">–</span></div>
      </div>
    </section>

    <section class="card" aria-label="In view">
      <div class="card-head"><h2>In view</h2><span class="badge" id="count">0</span></div>
      <div class="person"><div class="avatar" id="avatar">–</div>
        <div><div class="p-name" id="who">—</div><div class="p-sub" id="who-sub">Face tracker offline</div></div>
        <div class="emo" id="emo" aria-hidden="true"></div></div>
    </section>

    <section class="card" aria-label="Activity">
      <div class="card-head"><h2>Activity</h2></div>
      <ol class="log" id="log"><li class="empty">Nothing yet</li></ol>
    </section>

    <section class="card" aria-label="Camera controls">
      <div class="card-head"><h2>Camera</h2><span class="mood" id="cam-conn">—</span></div>
      <div class="locked" id="locked"><span>Controls are locked.</span><button class="btn primary" id="unlock">Unlock</button></div>
      <div id="controls" hidden>
        <div class="ctl"><div>Privacy<small id="priv-sub">Stops streaming and detection</small></div>
          <button class="switch" id="priv" role="switch" aria-checked="false" aria-label="Privacy mode"></button></div>
        <div class="ctl"><div>Private hours<small>Daily</small></div>
          <div class="hours"><select id="ph-s" aria-label="From"></select>–<select id="ph-e" aria-label="To"></select>
            <button class="btn" id="ph-save">Set</button></div></div>
        <div class="ctl"><div>Night mode<small id="night-sub">Black &amp; white in the dark</small></div>
          <div class="seg" data-cmd="night"><button data-v="auto">Auto</button><button data-v="on">On</button><button data-v="off">Off</button></div></div>
        <div class="ctl"><div>Light<small>Flash LED</small></div>
          <div class="seg" data-cmd="light"><button data-v="off">Off</button><button data-v="auto">Auto</button><button data-v="30">Low</button><button data-v="100">High</button></div></div>
        <div class="ctl"><div>Motion alerts<small>Low ignores curtains &amp; plants moving</small></div>
          <div class="seg" data-cmd="sensitivity"><button data-v="low">Low</button><button data-v="medium">Med</button><button data-v="high">High</button></div></div>
        <div class="ctl"><div>Resolution</div>
          <div class="seg" data-cmd="profile"><button data-v="auto">Auto</button><button data-v="0">400p</button><button data-v="1">640p</button></div></div>
        <div class="ctl"><div>Restart camera<small>Takes about 15 seconds</small></div><button class="btn danger" id="restart">Restart</button></div>
      </div>
      <div class="health" id="health"></div>
    </section>
  </aside>
</main>
<footer class="foot">ESP32-CAM · streamed via Render · <span id="viewers">0</span> watching</footer>

<script>
  var key = new URLSearchParams(location.search).get('key');
  var q = '?key=' + encodeURIComponent(key);
  var $ = function (id) { return document.getElementById(id); };
  var img = $('feed'), stage = $('stage');

  // ── Video (MJPEG; falls back to polling snapshots) ──
  var polling = false;
  img.onerror = function () {
    if (polling) return;
    polling = true;
    var tick = function () { img.src = '/snapshot' + q + '&t=' + Date.now(); };
    img.onload = function () { setTimeout(tick, 250); };
    img.onerror = function () { setTimeout(tick, 2000); };
    tick();
  };
  img.src = '/stream' + q;
  $('btn-snap').href = '/snapshot' + q;
  $('btn-fs').onclick = function () {
    if (document.fullscreenElement) return document.exitFullscreen();
    (stage.requestFullscreen || stage.webkitRequestFullscreen || function () {}).call(stage);
  };
  var showBoxes = true;
  try { showBoxes = localStorage.getItem('aria-boxes') !== '0'; } catch (e) {}
  var boxBtn = $('btn-overlay');
  boxBtn.setAttribute('aria-pressed', String(showBoxes));
  boxBtn.onclick = function () {
    showBoxes = !showBoxes;
    boxBtn.setAttribute('aria-pressed', String(showBoxes));
    try { localStorage.setItem('aria-boxes', showBoxes ? '1' : '0'); } catch (e) {}
  };

  // ── Clock + camera status ──
  function pad(n) { return (n < 10 ? '0' : '') + n; }
  setInterval(function () {
    var d = new Date();
    $('clock').textContent = d.toLocaleTimeString([], { hour: 'numeric', minute: '2-digit' });
    $('hud-time').textContent = d.toLocaleDateString([], { day: 'numeric', month: 'short' }) + ' ' +
      pad(d.getHours()) + ':' + pad(d.getMinutes()) + ':' + pad(d.getSeconds());
  }, 1000);

  async function refresh() {
    var live = $('live'), off = $('offline');
    try {
      var s = await (await fetch('/status' + q, { cache: 'no-store' })).json();
      $('viewers').textContent = s.viewers;
      if (s.online) {
        live.className = 'live on'; $('live-text').textContent = 'Live';
        off.hidden = true;
        $('hud-fps').textContent = (s.fps || 0).toFixed(1) + ' fps';
        if (s.width) $('hud-res').textContent = s.width + '×' + s.height;
      } else {
        live.className = 'live off'; $('live-text').textContent = 'Offline';
        off.hidden = false;
        $('offline-text').textContent = s.lastFrameAgeMs === null ? 'Waiting for the camera…'
          : 'Last frame ' + ago(s.lastFrameAgeMs) + ' ago';
      }
    } catch (e) { live.className = 'live off'; $('live-text').textContent = 'Unreachable'; }
  }
  function ago(ms) {
    var s = Math.round(ms / 1000);
    return s < 60 ? s + 's' : s < 3600 ? Math.round(s / 60) + ' min' : Math.round(s / 3600) + ' h';
  }
  refresh(); setInterval(refresh, 3000);

  // ── Tracker data (faces, ARIA's mood + face) over Server-Sent Events ──
  var EMOJI = { happy: '😊', surprise: '😮', sad: '😢', angry: '😠', neutral: '🙂' };
  var EXPR_MOOD = { purr: '😌 Purring', heart: '😍 In love', yawn: '🥱 Yawning', sideeye: '😒 Sulking',
                    wink: '😉 Winking', surprise: '😲 Surprised', think: '🤔 Thinking', curious: '🧐 Curious',
                    squint: '🤨 Suspicious', wake: '😪 Waking up' };
  var meta = null, metaAt = 0, shown = [];
  var es = new EventSource('/events' + q);
  es.onmessage = function (e) { try { meta = JSON.parse(e.data); metaAt = Date.now(); render(); } catch (x) {} };
  es.addEventListener('log', function (e) { try { addLog(JSON.parse(e.data)); } catch (x) {} });

  function fresh() { return meta && Date.now() - metaAt < 3000; }

  function render() {
    var faces = fresh() ? (meta.faces || []) : [];
    $('count').textContent = fresh() ? (meta.n || faces.length) : 0;
    var av = $('avatar'), f = faces[0];
    if (!fresh()) {
      $('who').textContent = '—'; $('who-sub').textContent = 'Face tracker offline';
      av.className = 'avatar'; av.textContent = '–'; $('emo').textContent = '';
    } else if (!f) {
      $('who').textContent = 'Nobody'; $('who-sub').textContent = 'Watching the room';
      av.className = 'avatar'; av.textContent = '·'; $('emo').textContent = '';
    } else {
      var known = f.id === 'known', stranger = f.id === 'unknown';
      $('who').textContent = known ? f.name : stranger ? 'Stranger' : 'Someone';
      $('who-sub').textContent = (f.emo || 'neutral') + (f.look ? ' · looking at the camera' : '') +
        (faces.length > 1 ? ' · +' + (faces.length - 1) : '');
      av.className = 'avatar ' + (known ? 'known' : stranger ? 'stranger' : 'seeing');
      av.textContent = known ? f.name.charAt(0).toUpperCase() : stranger ? '?' : '…';
      $('emo').textContent = EMOJI[f.emo] || '';
    }
    var r = fresh() && meta.robot;
    if (r) {
      $('mood').textContent = r.sleeping ? '😴 Asleep' : EXPR_MOOD[r.expr] ||
        (r.energy < 0.3 ? '😩 Tired' : r.boredom > 0.5 ? '😐 Bored' : r.affection > 0.7 ? '🥰 Affectionate' : '🙂 Calm');
      [['energy', r.energy], ['affection', r.affection], ['boredom', r.boredom]].forEach(function (m) {
        var v = Math.round((m[1] || 0) * 100);
        $('m-' + m[0]).style.width = v + '%'; $('v-' + m[0]).textContent = v + '%';
      });
    } else {                                   // tracker offline: don't show stale numbers
      $('mood').textContent = '—';
      ['energy', 'affection', 'boredom'].forEach(function (k) {
        $('m-' + k).style.width = '0'; $('v-' + k).textContent = '–';
      });
    }
  }
  setInterval(render, 1000);

  // ── Activity timeline ──
  var LOG_MAX = 20;
  function addLog(e) {
    var list = $('log'), empty = list.querySelector('.empty');
    if (empty) empty.remove();
    var li = document.createElement('li');
    li.className = e.kind + ' new';
    var dot = document.createElement('i');
    var text = document.createElement('span'); text.textContent = e.text;
    var t = document.createElement('time');
    t.textContent = new Date(e.t).toLocaleTimeString([], { hour: 'numeric', minute: '2-digit' });
    li.append(dot, text, t);
    list.prepend(li);
    while (list.children.length > LOG_MAX) list.lastChild.remove();
  }


  // ── Camera: state, controls, privacy screen ──
  var cam = null;
  es.addEventListener('cam', function (e) { try { cam = JSON.parse(e.data); renderCam(); } catch (x) {} });
  var adminKey = null;
  try { adminKey = localStorage.getItem('aria-admin'); } catch (e) {}
  function fmtUp(s) { var h = Math.floor(s / 3600), m = Math.floor(s / 60) % 60; return h ? h + 'h ' + m + 'm' : m + 'm'; }
  function renderCam() {
    $('cam-conn').textContent = cam ? 'Connected' : 'Not connected';
    $('locked').hidden = !!adminKey; $('controls').hidden = !adminKey;
    var ps = $('privacy-screen');
    ps.hidden = !(cam && cam.privacy);
    $('hud-night').hidden = !(cam && cam.night && !cam.privacy);
    if (!cam) { $('health').textContent = ''; return; }
    if (cam.privacy) $('privacy-text').textContent = cam.privacy_manual ? 'Switched on from this page.'
      : 'Private hours ' + cam.priv_hours[0] + ':00–' + cam.priv_hours[1] + ':00.';
    $('priv').setAttribute('aria-checked', String(!!cam.privacy_manual));
    $('priv-sub').textContent = cam.privacy ? 'On — nothing is leaving the camera' : 'Stops streaming and detection';
    $('night-sub').textContent = cam.night ? 'Active now' : 'Black & white in the dark';
    setSeg('night', cam.night_mode);
    setSeg('light', cam.ledauto ? 'auto' : cam.led === 0 ? 'off' : cam.led <= 40 ? '30' : '100');
    setSeg('profile', cam.adaptive ? 'auto' : cam.profile === 'VGA' ? '1' : '0');
    if (cam.sensitivity) setSeg('sensitivity', cam.sensitivity);
    if (document.activeElement !== $('ph-s') && document.activeElement !== $('ph-e')) {
      $('ph-s').value = cam.priv_hours[0]; $('ph-e').value = cam.priv_hours[1];
    }
    var h = $('health'); h.textContent = '';
    [['Signal', cam.rssi + ' dBm'], ['Uptime', fmtUp(cam.up)], ['Memory free', cam.heap_kb + ' KB'],
     ['Last restart', cam.reset], ['Brightness', cam.brightness < 0 ? '–' : Math.round(cam.brightness / 2.55) + '%'],
     ['Last motion', cam.motion_ago ? ago(cam.motion_ago * 1000) + ' ago' : '–'],
     ['Motion level', cam.motion_level === undefined ? '–' : (cam.motion_level / 10).toFixed(1) + '%']].forEach(function (kv) {
      var d = document.createElement('div'); d.textContent = kv[0] + ' ';
      var b = document.createElement('b'); b.textContent = kv[1]; d.append(b); h.append(d);
    });
  }
  function setSeg(cmd, v) {
    document.querySelectorAll('.seg[data-cmd="' + cmd + '"] button').forEach(function (b) {
      b.setAttribute('aria-pressed', String(b.dataset.v === v));
    });
  }
  for (var hr = 0; hr < 24; hr++) {
    ['ph-s', 'ph-e'].forEach(function (id) {
      var o = document.createElement('option'); o.value = hr; o.textContent = pad(hr) + ':00'; $(id).append(o);
    });
  }
  async function send(cmd, args) {
    try {
      var r = await fetch('/cmd', { method: 'POST', headers: { 'Content-Type': 'application/json', 'X-Admin-Key': adminKey },
                                    body: JSON.stringify({ cmd: cmd, args: args || [] }) });
      if (r.status === 401) { lock(); alert('That admin key was not accepted.'); }
      else if (r.status === 503) alert('The camera is not connected right now.');
    } catch (e) { alert('Could not reach the relay.'); }
  }
  function lock() { adminKey = null; try { localStorage.removeItem('aria-admin'); } catch (e) {} renderCam(); }
  $('unlock').onclick = function () {
    var k = prompt('Admin key (the camera key, unless you set ADMIN_KEY on Render):');
    if (!k) return;
    adminKey = k.trim();
    try { localStorage.setItem('aria-admin', adminKey); } catch (e) {}
    renderCam();
  };
  $('priv').onclick = function () {
    var on = $('priv').getAttribute('aria-checked') !== 'true';
    $('priv').setAttribute('aria-checked', String(on));      // optimistic; the next state report confirms
    send('privacy', [on ? '1' : '0']);
  };
  $('ph-save').onclick = function () { send('privhours', [$('ph-s').value, $('ph-e').value]); };
  document.querySelectorAll('.seg').forEach(function (seg) {
    seg.addEventListener('click', function (e) {
      var b = e.target.closest('button'); if (!b) return;
      var v = b.dataset.v, cmd = seg.dataset.cmd;
      setSeg(cmd, v);
      if (cmd === 'light') { if (v === 'auto') send('ledauto', ['1']); else send('led', [v === 'off' ? '0' : v]); }
      else send(cmd, [v]);
    });
  });
  $('restart').onclick = function () { if (confirm('Restart the camera? The stream drops for ~15 seconds.')) send('restart'); };
  renderCam();

  // ── ARIA's live face (the OLED's 128×64 frame, 1 bit per pixel) ──
  var rc = $('robot'), rctx = rc.getContext('2d'), rimg = rctx.createImageData(128, 64), lastFrame = null;
  function drawRobot() {
    var b64 = fresh() && meta.face_frame;
    $('robot-off').hidden = !!b64;
    if (!b64) { rctx.clearRect(0, 0, 128, 64); lastFrame = null; return; }
    if (b64 === lastFrame) return;
    lastFrame = b64;
    var bin = atob(b64), px = rimg.data;
    for (var y = 0; y < 64; y++) for (var xb = 0; xb < 16; xb++) {
      var byte = bin.charCodeAt(y * 16 + xb);
      for (var bit = 0; bit < 8; bit++) {
        var i = (y * 128 + xb * 8 + bit) * 4, lit = byte & (0x80 >> bit);
        px[i] = lit ? 94 : 0; px[i + 1] = lit ? 234 : 0; px[i + 2] = lit ? 212 : 0; px[i + 3] = 255;
      }
    }
    rctx.putImageData(rimg, 0, 0);
  }

  // ── Face boxes over the video ──
  var canvas = $('overlay'), ctx = canvas.getContext('2d');
  function draw() {
    drawRobot();
    var W = canvas.clientWidth, H = canvas.clientHeight, dpr = window.devicePixelRatio || 1;
    if (canvas.width !== Math.round(W * dpr) || canvas.height !== Math.round(H * dpr)) {
      canvas.width = Math.round(W * dpr); canvas.height = Math.round(H * dpr);
    }
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, W, H);
    var nw = img.naturalWidth || 4, nh = img.naturalHeight || 3, s = Math.min(W / nw, H / nh);
    var dw = nw * s, dh = nh * s, ox = (W - dw) / 2, oy = (H - dh) / 2;
    var faces = showBoxes && meta && Date.now() - metaAt < 2500 ? (meta.faces || []) : [];
    faces.forEach(function (f, i) {
      var t = shown[i] || (shown[i] = { x: f.x, y: f.y, w: f.w, h: f.h });
      ['x', 'y', 'w', 'h'].forEach(function (k) { t[k] += (f[k] - t[k]) * 0.35; });
    });
    shown.length = faces.length;
    faces.forEach(function (f, i) {
      var b = shown[i], x = ox + b.x * dw, y = oy + b.y * dh, w = b.w * dw, h = b.h * dh;
      var color = f.id === 'known' ? '#4ade80' : f.id === 'unknown' ? '#fbbf24' : '#5eead4';
      ctx.strokeStyle = color; ctx.lineWidth = 2.5; ctx.lineCap = 'round';
      ctx.shadowColor = color; ctx.shadowBlur = 8;
      var c = Math.min(w, h) * 0.24;
      ctx.beginPath();
      [[x, y, 1, 1], [x + w, y, -1, 1], [x, y + h, 1, -1], [x + w, y + h, -1, -1]].forEach(function (p) {
        ctx.moveTo(p[0] + p[2] * c, p[1]); ctx.lineTo(p[0], p[1]); ctx.lineTo(p[0], p[1] + p[3] * c);
      });
      ctx.stroke();
      ctx.shadowBlur = 0;
      var label = (f.id === 'known' ? f.name : f.id === 'unknown' ? 'Stranger' : 'Identifying…') + '  ' + (EMOJI[f.emo] || '');
      ctx.font = '600 13px ui-sans-serif, system-ui, sans-serif';
      var tw = ctx.measureText(label).width + 16, ly = Math.max(4, y - 28);
      ctx.fillStyle = 'rgba(7,9,12,.72)';
      ctx.beginPath(); ctx.roundRect ? ctx.roundRect(x, ly, tw, 22, 11) : ctx.rect(x, ly, tw, 22); ctx.fill();
      ctx.fillStyle = color; ctx.fillText(label, x + 8, ly + 15);
    });
    requestAnimationFrame(draw);
  }
  requestAnimationFrame(draw);
</script></body></html>`;
}
