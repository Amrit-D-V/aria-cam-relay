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
//                    distances: every frame waits a full round trip.
//                    ?src=eye2 = the display's backup camera (OV7670) while
//                    the main one is down; ignored while the main one sends
//   POST /meta       tracker → relay  (header X-Cam-Key, JSON body): face boxes,
//                    names, emotions and the robot's mood, drawn over the video
//   GET  /events     Server-Sent Events: /meta updates as messages, plus named
//                    "log" events for the activity timeline (?key=)
//   GET  /?key=      viewer page      (key: $VIEW_KEY)
//   POST /cmd        page → camera command (header X-Admin-Key: $ADMIN_KEY,
//                    else $CAM_KEY; JSON {cmd, args}) — LED, night mode,
//                    privacy, resolution, restart
//   GET  /display    the OLED display's pending state (?key=): screen on/off,
//                    latest admin message, latest emotion request — it polls
//                    this every 2 s (admin sets them via /cmd: screen, message,
//                    emotion)
//   GET  /stream     MJPEG stream     (?key=)
//   GET  /snapshot   latest JPEG      (?key=)
//   GET  /status     JSON             (?key=)
//   GET  /health     camera health history (?key=): fps / WiFi / memory samples
//                    every 30 s for 24 h, and restarts with their reasons. Kept
//                    in memory, so it starts over when Render restarts the relay
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
// Which camera the frames come from: 'main' (the ESP32-CAM over /ws) or
// 'eye2' (the display's OV7670, POSTed to /push?src=eye2 while the main
// camera is down). The main camera wins whenever it's sending.
let frameSource = 'main';
let mainFrameAt = 0;

// Activity timeline, derived from /meta. Presence is debounced — a face that
// drops out for a frame or two doesn't log "left" and "arrived" again.
const LOG_MAX = 30;
const activity = [];              // newest first: {t, kind, text}
const presence = { here: false, lastFace: 0, who: null, sleeping: null };

// Camera state reported over its WebSocket every ~2 s (settings + health).
let camState = null;

// Health history for the page's charts: a sample every 30 s for 24 h, plus
// camera restarts (seen as its uptime going backwards) with the reason it
// gave. In memory only — a relay restart starts it over.
const HEALTH_EVERY_MS = 30000;
const HEALTH_KEEP = 24 * 3600 * 1000 / HEALTH_EVERY_MS;
const healthSamples = [];         // {t, on, fps, rssi, heap}
const restarts = [];              // newest first: {t, reason}
let lastUp = null;
let lastGesture = 0;

function noteCamUptime(m) {
  if (typeof m.up !== 'number') return;
  if ((lastUp !== null && m.up < lastUp) || (lastUp === null && m.up < 60)) {
    restarts.unshift({ t: Date.now() - m.up * 1000, reason: String(m.reset || 'unknown') });
    if (restarts.length > 50) restarts.pop();
    logEvent('restart', `Camera restarted (${m.reset || 'unknown'})`);
  }
  lastUp = m.up;
}

setInterval(() => {
  const on = status().online;
  healthSamples.push({ t: Date.now(), on, fps: on ? Math.round(fps() * 10) / 10 : null,
                       rssi: on && camState ? camState.rssi : null, heap: on && camState ? camState.heap_kb : null });
  if (healthSamples.length > HEALTH_KEEP) healthSamples.shift();
}, HEALTH_EVERY_MS);

// What the admin has asked of the OLED display. Ids let the display tell a
// new message/emotion from one it has already shown.
const EMOTIONS = ['giggle', 'wink', 'heart', 'surprise', 'curious', 'think', 'shy', 'dizzy',
                  'roll', 'nod', 'yawn', 'purr', 'squint', 'sleep', 'wake'];
const MSG_MAX = 120;
const VIEWS = ['auto', 'eyes', 'clock', 'weather', 'stats', 'detect', 'cam2'];
const displayState = { screen: 1, msg: null, emotion: null, seq: 0, restart: 0, view: 'auto' };

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
    noteCamUptime(m);
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
  profile: (a) => ['auto', '0', '1', '2', '3', '4'].includes(a[0]),
  sensitivity: (a) => ['low', 'medium', 'high'].includes(a[0]),
  zones: (a) => /^[0-9a-f]{12}$/.test(a[0]) && a[0] !== '000000000000',
  restart: (a) => a.length === 0,
};

function publicDisplay() {
  const m = displayState.msg;
  return { screen: displayState.screen, msg: m && Date.now() - m.t < m.secs * 1000 ? m : null,
           emotion: displayState.emotion, restart: displayState.restart, view: displayState.view };
}

function handleCmd(req, res) {
  if (!keyMatches(req.headers['x-admin-key'], ADMIN_KEY)) return send(res, 401, 'text/plain', 'bad admin key');
  const chunks = [];
  req.on('data', (c) => { chunks.push(c); if (chunks.length > 8) req.destroy(); });
  req.on('end', () => {
    let body;
    try { body = JSON.parse(Buffer.concat(chunks).toString('utf8')); } catch { return send(res, 400, 'text/plain', 'bad json'); }
    const cmd = String(body.cmd || ''), args = (body.args || []).map(String);
    // Display commands are kept here for the display to pick up (/display).
    if (cmd === 'screen') {
      if (!['on', 'off'].includes(args[0])) return send(res, 400, 'text/plain', 'screen on|off');
      displayState.screen = args[0] === 'on' ? 1 : 0;
      broadcast('display', publicDisplay());
      return send(res, 202, 'text/plain', 'queued');
    }
    if (cmd === 'message') {
      // The OLED fonts are ASCII: anything else becomes '?'. Blank clears it.
      const text = String(body.text || '').replace(/[\r\n\t]+/g, ' ').replace(/[^\x20-\x7e]/g, '?').trim().slice(0, MSG_MAX);
      const secs = Math.min(Math.max(parseInt(body.secs, 10) || 15, 5), 600);
      displayState.msg = text ? { id: ++displayState.seq, text, secs, t: Date.now() } : null;
      if (text) logEvent('message', `Message: "${text}"`);
      broadcast('display', publicDisplay());
      return send(res, 202, 'text/plain', 'queued');
    }
    if (cmd === 'restart_all') {       // camera now; the display picks it up on its next poll (≤2 s)
      if (camSocket && !camSocket.destroyed) camSocket.write(wsFrame(0x1, Buffer.from('restart')));
      displayState.restart = Date.now();
      logEvent('privacy', 'System restart (camera + display)');
      return send(res, 202, 'text/plain', 'restarting');
    }
    if (cmd === 'view') {              // what the OLED shows: auto rotation, one screen, or camera 2 live
      if (!VIEWS.includes(args[0])) return send(res, 400, 'text/plain', 'view ' + VIEWS.join('|'));
      displayState.view = args[0];
      broadcast('display', publicDisplay());
      return send(res, 202, 'text/plain', 'queued');
    }
    if (cmd === 'emotion') {
      if (!EMOTIONS.includes(args[0])) return send(res, 400, 'text/plain', 'unknown emotion');
      displayState.emotion = { id: ++displayState.seq, name: args[0], t: Date.now() };
      broadcast('display', publicDisplay());
      return send(res, 202, 'text/plain', 'queued');
    }
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
  const g = meta.gesture;           // {name, who, t} from the tracker's hand-sign reader
  if (g && typeof g.t === 'number' && g.t > lastGesture) {
    lastGesture = g.t;
    logEvent('gesture', `${String(g.name).slice(0, 40)}${g.who ? ' from ' + String(g.who).slice(0, 30) : ''}`);
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
    const src = new URL(req.url, 'http://x').searchParams.get('src') === 'eye2' ? 'eye2' : 'main';
    if (src === 'eye2' && Date.now() - mainFrameAt < 5000) return send(res, 200, 'text/plain', String(viewerCount()));
    if (!acceptFrame(Buffer.concat(chunks), src)) return send(res, 400, 'text/plain', 'not a JPEG');
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
  res.write(`event: display\ndata: ${JSON.stringify(publicDisplay())}\n\n`);
  metaSubscribers.add(res);
  const ping = setInterval(() => res.write(': ping\n\n'), 15000);   // keep proxies from idling it out
  res.on('close', () => { clearInterval(ping); metaSubscribers.delete(res); });
}

function acceptFrame(frame, src = 'main') {
  if (frame.length < 4 || frame[0] !== 0xff || frame[1] !== 0xd8) return false;
  if (src === 'main') mainFrameAt = Date.now();
  if (src !== frameSource) {
    frameSource = src;
    logEvent('backup', src === 'eye2' ? 'Main camera down — showing the backup eye' : 'Main camera back');
  }
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
           fps: Math.round(fps() * 10) / 10, width: frameSize && frameSize.w, height: frameSize && frameSize.h,
           source: frameSource };
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
    case '/display':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return send(res, 200, 'application/json', JSON.stringify(publicDisplay()));
    case '/status':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return send(res, 200, 'application/json', JSON.stringify(status()));
    case '/health':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return send(res, 200, 'application/json', JSON.stringify({ every: HEALTH_EVERY_MS, samples: healthSamples, restarts }));
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

// Keep idle HTTP connections longer than Node's 5 s default: the display
// can't reopen its TLS session while its OV7670 runs (no memory), so a
// dropped keep-alive costs it a camera pause.
server.keepAliveTimeout = 65000;
server.headersTimeout = 66000;
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
  .avatar.admin { box-shadow: 0 0 0 3px rgba(250,204,21,.35); border-color: #facc15; color: #facc15; }
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
  .log li span { overflow-wrap: anywhere; min-width: 0; }
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
  .ctl.wide { grid-template-columns: 1fr; }   /* label above a long button row */
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
  .chip.backup { color: #fbbf24; border-color: rgba(251,191,36,.4); }
  .log li.backup i { background: var(--warn); }

  .view-seg { display: flex; flex-wrap: wrap; width: 100%; margin-top: 2px; }
  .view-seg button { flex: 1 1 auto; }
  .emo-grid { display: grid; grid-template-columns: repeat(5, 1fr); gap: 6px; margin-top: 8px; }
  .emo-grid button { background: var(--surface-2); border: 1px solid var(--line); border-radius: 10px; padding: 8px 2px;
                     cursor: pointer; font-size: 12px; color: var(--muted); display: grid; gap: 2px; justify-items: center; }
  .emo-grid button b { font-size: 20px; line-height: 1; }
  .emo-grid button:hover { border-color: rgba(94,234,212,.4); color: var(--text); }
  .emo-grid button.sent { border-color: var(--accent); color: var(--accent); }
  .msg-box { display: grid; gap: 8px; margin-top: 4px; }
  .msg-box textarea { background: var(--surface-2); color: var(--text); border: 1px solid var(--line); border-radius: 10px;
                      padding: 10px; font: inherit; resize: vertical; min-height: 64px; }
  .msg-box textarea:focus { outline: 2px solid var(--accent); outline-offset: 1px; }
  .msg-row { display: flex; gap: 8px; align-items: center; justify-content: space-between; font-size: 12px; color: var(--muted); }
  .msg-row select { background: var(--surface-2); color: var(--text); border: 1px solid var(--line); border-radius: 8px; padding: 5px; font: inherit; }
  .showing { font-size: 12px; color: var(--accent); min-height: 16px; }
  .log li.message i { background: var(--accent); }
  .sub-h { font-size: 12px; color: var(--muted); text-transform: uppercase; letter-spacing: .08em; margin: 14px 0 4px; }
  .log li.restart i { background: var(--bad); } .log li.gesture i { background: #f472b6; }

  /* A hand sign seen by the tracker: big emoji pops over the video */
  .g-pop { position: absolute; left: 50%; top: 42%; transform: translate(-50%, -50%); display: grid; justify-items: center;
           gap: 6px; pointer-events: none; z-index: 3; }
  .g-pop[hidden] { display: none; }
  .g-pop .e { font-size: min(22vw, 120px); line-height: 1; filter: drop-shadow(0 6px 18px rgba(0,0,0,.6)); }
  .g-pop .t { padding: 5px 12px; border-radius: 999px; background: rgba(7,9,12,.75); border: 1px solid rgba(244,114,182,.5);
              color: #fbcfe8; font-size: 14px; font-weight: 600; white-space: nowrap; }
  .g-pop .ring { position: absolute; top: 50%; left: 50%; width: 60px; height: 60px; margin: -30px 0 0 -30px; border-radius: 50%;
                 border: 3px solid #f472b6; opacity: 0; }
  .g-pop.go .e { animation: gpop 1.9s cubic-bezier(.2,1.4,.4,1) both; }
  .g-pop.go .t { animation: gcap 1.9s ease both; }
  .g-pop.go .ring { animation: gring .8s ease-out both; }
  .g-pop.go .ring + .ring { animation-delay: .15s; }
  @keyframes gpop { 0% { transform: scale(.2) rotate(-25deg); opacity: 0; } 18% { transform: scale(1.25) rotate(8deg); opacity: 1; }
                    30% { transform: scale(.95) rotate(-3deg); } 40%, 80% { transform: scale(1) rotate(0); opacity: 1; }
                    100% { transform: scale(.85) translateY(-30px); opacity: 0; } }
  @keyframes gcap { 0%, 15% { opacity: 0; transform: translateY(8px); } 30%, 80% { opacity: 1; transform: none; } 100% { opacity: 0; } }
  @keyframes gring { from { transform: scale(.4); opacity: .9; } to { transform: scale(4.5); opacity: 0; } }
  @media (prefers-reduced-motion: reduce) { .g-pop.go .e, .g-pop.go .t { animation: gcap 1.9s ease both; } .g-pop.go .ring { animation: none; } }

  /* Detection zones editor: an 8x6 grid over the video */
  .zones { position: absolute; display: grid; grid-template-columns: repeat(8, 1fr); grid-template-rows: repeat(6, 1fr);
           touch-action: none; user-select: none; -webkit-user-select: none; }
  .zones[hidden] { display: none; }
  .zones button { border: 1px solid rgba(94,234,212,.35); background: transparent; padding: 0; cursor: pointer; }
  .zones button.off { background: repeating-linear-gradient(135deg, rgba(248,113,113,.55) 0 6px, rgba(7,9,12,.7) 6px 12px);
                      border-color: rgba(248,113,113,.4); }
  .zone-bar { position: absolute; left: 12px; right: 12px; bottom: 12px; display: flex; flex-wrap: wrap; gap: 8px;
              align-items: center; justify-content: space-between; padding: 8px 10px; border-radius: 12px;
              background: rgba(7,9,12,.8); border: 1px solid var(--line); font-size: 13px; }
  .zone-bar[hidden] { display: none; }
  .zone-bar span { color: var(--muted); }

  /* Health charts */
  .hc { margin-top: 12px; }
  .hc-head { display: flex; justify-content: space-between; font-size: 12px; color: var(--muted); margin-bottom: 4px; }
  .hc-head b { color: var(--text); font-weight: 600; font-variant-numeric: tabular-nums; }
  .hc svg { display: block; width: 100%; height: 64px; overflow: visible; margin-bottom: 16px; }
  .hc .grid-l { stroke: var(--line); stroke-width: 1; }
  .hc .ax { fill: var(--muted); font-size: 10px; font-variant-numeric: tabular-nums; }
  .hc .ln { fill: none; stroke: var(--accent); stroke-width: 2; stroke-linejoin: round; stroke-linecap: round; }
  .hc .ar { fill: var(--accent-dim); stroke: none; }
  .hc .rs { stroke: var(--bad); stroke-width: 1; stroke-dasharray: 3 3; }
  .hc .off-band { fill: rgba(248,113,113,.10); }
  .hc .xh { stroke: var(--muted); stroke-width: 1; }
  .hc .dot { fill: var(--accent); stroke: var(--surface); stroke-width: 2; }
  .h-sum { display: grid; grid-template-columns: repeat(3, 1fr); gap: 8px; margin-top: 2px; }
  .h-sum div { background: var(--surface-2); border: 1px solid var(--line); border-radius: 10px; padding: 8px; font-size: 11px; color: var(--muted); }
  .h-sum b { display: block; font-size: 17px; color: var(--text); font-variant-numeric: tabular-nums; }
  .h-tip { position: fixed; pointer-events: none; z-index: 5; padding: 6px 9px; border-radius: 8px; font-size: 12px;
           background: var(--surface-2); border: 1px solid var(--line); box-shadow: 0 4px 16px rgba(0,0,0,.4); white-space: nowrap; }
  .h-tip[hidden] { display: none; }
  .rs-list { list-style: none; margin: 10px 0 0; padding: 0; font-size: 13px; }
  .rs-list li { display: flex; justify-content: space-between; gap: 8px; padding: 5px 0; border-bottom: 1px solid var(--line); }
  .rs-list li:last-child { border-bottom: 0; }
  .rs-list time { color: var(--muted); font-variant-numeric: tabular-nums; }
  .rs-list .why { display: inline-flex; align-items: center; gap: 6px; }
  .rs-list .why::before { content: "⚠"; color: var(--warn); }
  .rs-list .why.ok::before { content: "↻"; color: var(--muted); }
  .note { font-size: 11px; color: var(--muted); margin-top: 8px; }

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
      <div class="hud tr"><span class="chip backup" id="hud-src" hidden>BACKUP · EYE 2</span><span class="chip night" id="hud-night" hidden>☾ Night</span><span class="chip" id="hud-res">—</span><span class="chip" id="hud-fps">— fps</span></div>
      <div class="privacy-screen" id="privacy-screen" hidden>
        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" aria-hidden="true"><rect x="5" y="10" width="14" height="10" rx="2"/><path d="M8 10V7a4 4 0 0 1 8 0v3"/></svg>
        <b>Privacy mode on</b><span id="privacy-text">The camera isn&rsquo;t streaming or detecting.</span>
      </div>
      <div class="offline" id="offline" hidden>
        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.6" aria-hidden="true">
          <path d="M3 3l18 18M10.6 6H15a2 2 0 0 1 2 2v2l4-3v10M17 17H5a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2"/></svg>
        <b>Camera offline</b><span id="offline-text">Waiting for the camera…</span>
      </div>
      <div class="g-pop" id="g-pop" hidden aria-live="polite"><i class="ring"></i><i class="ring"></i>
        <span class="e" id="g-emoji"></span><span class="t" id="g-text"></span></div>
      <div class="zones" id="zones" hidden aria-label="Detection zones: tap cells to watch or ignore them"></div>
      <div class="zone-bar" id="zone-bar" hidden>
        <span id="zone-info">Tap cells to ignore them</span>
        <span><button class="btn" id="zone-all">Watch all</button> <button class="btn" id="zone-cancel">Cancel</button>
          <button class="btn primary" id="zone-save">Save</button></span>
      </div>
      <div class="controls" id="stage-controls">
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
      <div class="health" id="detect"></div>
    </section>

    <section class="card" aria-label="Activity">
      <div class="card-head"><h2>Activity</h2></div>
      <ol class="log" id="log"><li class="empty">Nothing yet</li></ol>
    </section>

    <section class="card" aria-label="ARIA controls">
      <div class="card-head"><h2>Talk to ARIA</h2><span class="mood" id="disp-state">—</span></div>
      <div class="locked" id="aria-locked"><span>Controls are locked.</span><button class="btn primary" id="unlock2">Unlock</button></div>
      <div id="aria-controls" hidden>
        <div class="ctl"><div>Display<small>Turn the OLED screen on or off</small></div>
          <button class="switch" id="screen" role="switch" aria-checked="true" aria-label="Display on"></button></div>
        <div class="sub-h">Display shows</div>
        <div class="seg view-seg" id="view-seg">
          <button data-v="auto">Auto</button><button data-v="eyes">Eyes</button><button data-v="clock">Clock</button>
          <button data-v="weather">Weather</button><button data-v="stats">Stats</button><button data-v="detect">Detection</button>
          <button data-v="cam2">Camera 2</button>
        </div>
        <div class="sub-h">Message on the display</div>
        <div class="msg-box">
          <textarea id="msg" maxlength="120" placeholder="Type a message… (e.g. Dinner is ready!)"></textarea>
          <div class="msg-row">
            <span><span id="msg-count">0</span>/120 · show for
              <select id="msg-secs" aria-label="Show for"><option value="10">10 s</option><option value="30" selected>30 s</option>
                <option value="60">1 min</option><option value="300">5 min</option><option value="600">10 min</option></select></span>
            <span><button class="btn" id="msg-clear">Clear</button> <button class="btn primary" id="msg-send">Send</button></span>
          </div>
          <div class="showing" id="msg-showing"></div>
        </div>
        <div class="sub-h">Emotion</div>
        <div class="emo-grid" id="emo-grid">
          <button data-e="giggle"><b>😆</b>Giggle</button><button data-e="wink"><b>😉</b>Wink</button>
          <button data-e="heart"><b>😍</b>Love</button><button data-e="surprise"><b>😲</b>Surprise</button>
          <button data-e="curious"><b>🧐</b>Curious</button><button data-e="think"><b>🤔</b>Think</button>
          <button data-e="shy"><b>☺️</b>Shy</button><button data-e="dizzy"><b>😵</b>Dizzy</button>
          <button data-e="roll"><b>🙄</b>Eye-roll</button><button data-e="nod"><b>🙂</b>Nod</button>
          <button data-e="squint"><b>🤨</b>Suspicious</button><button data-e="purr"><b>😌</b>Purr</button>
          <button data-e="yawn"><b>🥱</b>Yawn</button><button data-e="sleep"><b>😴</b>Sleep</button>
          <button data-e="wake"><b>☀️</b>Wake up</button>
        </div>
      </div>
    </section>

    <section class="card" aria-label="Camera controls">
      <div class="card-head"><h2>Camera</h2><span class="mood" id="cam-conn">—</span></div>
      <div class="locked" id="locked"><span>Controls are locked.</span><button class="btn primary" id="unlock">Unlock</button></div>
      <div id="controls" hidden>
        <div class="ctl"><div>Camera<small id="priv-sub">On — streaming and detecting</small></div>
          <button class="switch" id="priv" role="switch" aria-checked="true" aria-label="Camera on"></button></div>
        <div class="ctl"><div>Private hours<small>Daily</small></div>
          <div class="hours"><select id="ph-s" aria-label="From"></select>–<select id="ph-e" aria-label="To"></select>
            <button class="btn" id="ph-save">Set</button></div></div>
        <div class="ctl"><div>Night mode<small id="night-sub">Black &amp; white in the dark</small></div>
          <div class="seg" data-cmd="night"><button data-v="auto">Auto</button><button data-v="on">On</button><button data-v="off">Off</button></div></div>
        <div class="ctl"><div>Light<small>Flash LED</small></div>
          <div class="seg" data-cmd="light"><button data-v="off">Off</button><button data-v="auto">Auto</button><button data-v="30">Low</button><button data-v="100">High</button></div></div>
        <div class="ctl"><div>Motion alerts<small>Low ignores curtains &amp; plants moving</small></div>
          <div class="seg" data-cmd="sensitivity"><button data-v="low">Low</button><button data-v="medium">Med</button><button data-v="high">High</button></div></div>
        <div class="ctl"><div>Detection zones<small id="zone-sub">Watching the whole picture</small></div>
          <button class="btn" id="zone-edit">Edit</button></div>
        <div class="ctl wide"><div>Resolution<small>Higher = sharper but fewer fps</small></div>
          <div class="seg" data-cmd="profile"><button data-v="auto">Auto</button><button data-v="0">400</button><button data-v="1">640</button><button data-v="2">800</button><button data-v="3">720p</button><button data-v="4">1600</button></div></div>
        <div class="ctl"><div>Restart system<small>Camera + display, about 20 seconds</small></div><button class="btn danger" id="restart">Restart</button></div>
      </div>
      <div class="health" id="health"></div>
    </section>

    <section class="card" aria-label="Camera health">
      <div class="card-head"><h2>Health</h2>
        <div class="seg" id="h-range"><button data-h="1">1h</button><button data-h="6" aria-pressed="true">6h</button><button data-h="24">24h</button></div></div>
      <div class="h-sum">
        <div>Online<b id="h-online">–</b></div><div>Restarts<b id="h-rcount">–</b></div><div>Avg fps<b id="h-fps">–</b></div>
      </div>
      <div id="h-charts"></div>
      <ol class="rs-list" id="h-restarts"></ol>
      <div class="note" id="h-note"></div>
    </section>
  </aside>
  <div class="h-tip" id="h-tip" hidden></div>
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

  var backupLive = false;                      // the display's OV7670 is standing in for the main camera
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
        $('hud-src').hidden = s.source !== 'eye2';
        if (backupLive !== (s.source === 'eye2')) { backupLive = s.source === 'eye2'; renderCam(); }
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
                    squint: '🤨 Suspicious', wake: '😪 Waking up', nod: '🙂 Nodding', giggle: '😆 Giggling',
                    shy: '☺️ Shy', dizzy: '😵 Dizzy', roll: '🙄 Rolling its eyes' };
  var meta = null, metaAt = 0, shown = [], handShown = null;
  var es = new EventSource('/events' + q);
  es.onmessage = function (e) { try { meta = JSON.parse(e.data); metaAt = Date.now(); render(); gesturePop(); } catch (x) {} };

  // A new hand sign: pop its emoji over the video (only ones made in the last few seconds,
  // so opening the page doesn't replay an old one)
  var lastSign = Date.now() - 4000, popTimer = null;
  function gesturePop() {
    var g = meta && meta.gesture;
    if (!g || typeof g.t !== 'number' || g.t <= lastSign) return;
    lastSign = g.t;
    var parts = String(g.name).split(' '), emoji = parts.shift();
    $('g-emoji').textContent = emoji;
    $('g-text').textContent = (g.who ? g.who + ' · ' : '') + parts.join(' ');
    var el = $('g-pop');
    el.hidden = false; el.classList.remove('go'); void el.offsetWidth; el.classList.add('go');
    clearTimeout(popTimer);
    popTimer = setTimeout(function () { el.hidden = true; el.classList.remove('go'); }, 2000);
    if (navigator.vibrate) navigator.vibrate(30);
  }
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
    var dt = $('detect'); dt.textContent = '';
    if (fresh()) {
      var bodies = (meta.bodies || []).length, admin = !!(f && f.admin);
      [['Faces', String(faces.length ? (meta.n || faces.length) : 0)], ['Bodies', String(bodies)],
       ['Admin', admin ? '👑 ' + f.name + ' present' : 'away'],
       ['Motion', cam && cam.motion_level !== undefined ? (cam.motion_level / 10).toFixed(1) + '%' : '–']].forEach(function (kv) {
        var d = document.createElement('div'); d.textContent = kv[0] + ' ';
        var b = document.createElement('b'); b.textContent = kv[1]; d.append(b); dt.append(d);
      });
      if (admin) { av.className = 'avatar known admin'; }
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
    $('cam-conn').textContent = cam ? 'Connected' : backupLive ? 'Main offline · backup eye 2 live' : 'Not connected';
    $('locked').hidden = !!adminKey; $('controls').hidden = !adminKey;
    $('aria-locked').hidden = !!adminKey; $('aria-controls').hidden = !adminKey;
    var ps = $('privacy-screen');
    ps.hidden = !(cam && cam.privacy);
    $('hud-night').hidden = !(cam && cam.night && !cam.privacy);
    if (!cam) { $('health').textContent = ''; return; }
    if (cam.privacy) $('privacy-text').textContent = cam.privacy_manual ? 'Switched on from this page.'
      : 'Private hours ' + cam.priv_hours[0] + ':00–' + cam.priv_hours[1] + ':00.';
    $('priv').setAttribute('aria-checked', String(!cam.privacy_manual));      // switch = camera ON
    $('priv-sub').textContent = cam.privacy ? (cam.privacy_manual ? 'Off — private, nothing leaves the camera'
      : 'Off — private hours') : 'On — streaming and detecting';
    $('night-sub').textContent = cam.night ? 'Active now' : 'Black & white in the dark';
    setSeg('night', cam.night_mode);
    setSeg('light', cam.ledauto ? 'auto' : cam.led === 0 ? 'off' : cam.led <= 40 ? '30' : '100');
    setSeg('profile', cam.adaptive ? 'auto' : String(cam.profile_i !== undefined ? cam.profile_i : cam.profile === 'VGA' ? 1 : 0));
    if (cam.sensitivity) setSeg('sensitivity', cam.sensitivity);
    if (cam.zones) {
      var ignored = zonesFromHex(cam.zones).filter(function (w) { return !w; }).length;
      $('zone-sub').textContent = ignored ? 'Ignoring ' + ignored + ' of 48 areas' : 'Watching the whole picture';
    }
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
  async function send(cmd, args, extra) {
    try {
      var body = { cmd: cmd, args: args || [] };
      for (var k in (extra || {})) body[k] = extra[k];
      var r = await fetch('/cmd', { method: 'POST', headers: { 'Content-Type': 'application/json', 'X-Admin-Key': adminKey },
                                    body: JSON.stringify(body) });
      if (r.status === 401) { lock(); alert('That admin key was not accepted.'); }
      else if (r.status === 503) alert('The camera is not connected right now.');
      return r.status;
    } catch (e) { alert('Could not reach the relay.'); return 0; }
  }
  function lock() { adminKey = null; try { localStorage.removeItem('aria-admin'); } catch (e) {} renderCam(); }
  $('unlock2').onclick = function () { $('unlock').onclick(); };
  $('unlock').onclick = function () {
    var k = prompt('Admin key (the camera key, unless you set ADMIN_KEY on Render):');
    if (!k) return;
    adminKey = k.trim();
    try { localStorage.setItem('aria-admin', adminKey); } catch (e) {}
    renderCam();
  };
  $('priv').onclick = function () {
    var cameraOn = $('priv').getAttribute('aria-checked') !== 'true';
    $('priv').setAttribute('aria-checked', String(cameraOn));   // optimistic; the next state report confirms
    send('privacy', [cameraOn ? '0' : '1']);
  };
  $('ph-save').onclick = function () { send('privhours', [$('ph-s').value, $('ph-e').value]); };
  document.querySelectorAll('.seg[data-cmd]').forEach(function (seg) {
    seg.addEventListener('click', function (e) {
      var b = e.target.closest('button'); if (!b) return;
      var v = b.dataset.v, cmd = seg.dataset.cmd;
      setSeg(cmd, v);
      if (cmd === 'light') { if (v === 'auto') send('ledauto', ['1']); else send('led', [v === 'off' ? '0' : v]); }
      else send(cmd, [v]);
    });
  });
  $('restart').onclick = function () {
    if (confirm('Restart the camera and the display? The stream drops for about 20 seconds.')) send('restart_all');
  };

  // ── Talk to ARIA: display on/off, messages, emotions ──
  var disp = null;
  es.addEventListener('display', function (e) { try { disp = JSON.parse(e.data); renderDisp(); } catch (x) {} });
  function renderDisp() {
    if (!disp) return;
    $('screen').setAttribute('aria-checked', String(!!disp.screen));
    document.querySelectorAll('#view-seg button').forEach(function (b) {
      b.setAttribute('aria-pressed', String(b.dataset.v === (disp.view || 'auto')));
    });
    $('disp-state').textContent = disp.screen ? 'Display on' : 'Display off';
    var m = disp.msg;
    if (m) {
      var left = Math.max(0, Math.round((m.t + m.secs * 1000 - Date.now()) / 1000));
      $('msg-showing').textContent = left ? 'Showing: “' + m.text + '” · ' + left + 's left' : '';
    } else $('msg-showing').textContent = '';
  }
  setInterval(renderDisp, 1000);
  $('view-seg').addEventListener('click', function (e) {
    var b = e.target.closest('button'); if (!b) return;
    if (disp) disp.view = b.dataset.v;                 // optimistic; the next display event confirms
    renderDisp();
    send('view', [b.dataset.v]);
  });
  $('screen').onclick = function () {
    var on = $('screen').getAttribute('aria-checked') !== 'true';
    $('screen').setAttribute('aria-checked', String(on));
    send('screen', [on ? 'on' : 'off']);
  };
  $('msg').oninput = function () { $('msg-count').textContent = $('msg').value.length; };
  $('msg-send').onclick = async function () {
    var text = $('msg').value.trim();
    if (!text) return;
    if (await send('message', [], { text: text, secs: +$('msg-secs').value }) === 202) {
      $('msg').value = ''; $('msg-count').textContent = '0';
    }
  };
  $('msg').onkeydown = function (e) { if (e.key === 'Enter' && !e.shiftKey) { e.preventDefault(); $('msg-send').onclick(); } };
  $('msg-clear').onclick = function () { send('message', [], { text: '' }); };
  $('emo-grid').addEventListener('click', function (e) {
    var b = e.target.closest('button'); if (!b) return;
    send('emotion', [b.dataset.e]);
    b.classList.add('sent'); setTimeout(function () { b.classList.remove('sent'); }, 900);
  });
  renderCam();

  // ── Detection zones: 8x6 grid, bit = row*8 + col, 1 = watched ──
  var ZC = 8, ZR = 6, zoneEdit = null, zonePaint = null;
  var zonesEl = $('zones');
  function zonesFromHex(h) {
    var v = BigInt('0x' + (h || 'ffffffffffff')), m = [];
    for (var i = 0; i < ZC * ZR; i++) m.push(((v >> BigInt(i)) & BigInt(1)) === BigInt(1));
    return m;
  }
  function zonesToHex(m) {
    var v = BigInt(0);
    m.forEach(function (on, i) { if (on) v |= BigInt(1) << BigInt(i); });
    return v.toString(16).padStart(12, '0');
  }
  for (var zi = 0; zi < ZC * ZR; zi++) {
    var zb = document.createElement('button'); zb.type = 'button'; zb.dataset.i = zi;
    zb.setAttribute('aria-label', 'Row ' + (Math.floor(zi / ZC) + 1) + ', column ' + (zi % ZC + 1));
    zonesEl.append(zb);
  }
  function placeZones() {                    // over the picture itself (object-fit: contain leaves bars)
    var W = stage.clientWidth, H = stage.clientHeight;
    var nw = img.naturalWidth || 4, nh = img.naturalHeight || 3, k = Math.min(W / nw, H / nh);
    zonesEl.style.width = nw * k + 'px'; zonesEl.style.height = nh * k + 'px';
    zonesEl.style.left = (W - nw * k) / 2 + 'px'; zonesEl.style.top = (H - nh * k) / 2 + 'px';
  }
  function drawZones() {
    var off = 0;
    zonesEl.querySelectorAll('button').forEach(function (b, i) {
      b.classList.toggle('off', !zoneEdit[i]); b.setAttribute('aria-pressed', String(!zoneEdit[i]));
      if (!zoneEdit[i]) off++;
    });
    $('zone-info').textContent = off ? off + ' of 48 areas ignored' : 'Tap or drag over areas to ignore';
  }
  function setCell(el) {
    if (!el || el.parentNode !== zonesEl) return;
    var i = +el.dataset.i;
    if (zoneEdit[i] !== zonePaint) { zoneEdit[i] = zonePaint; drawZones(); }
  }
  zonesEl.addEventListener('pointerdown', function (e) {
    var b = e.target.closest('button'); if (!b) return;
    e.preventDefault();
    zonePaint = !zoneEdit[+b.dataset.i];
    setCell(b);
  });
  zonesEl.addEventListener('pointermove', function (e) {
    if (zonePaint === null) return;
    setCell(document.elementFromPoint(e.clientX, e.clientY));
  });
  window.addEventListener('pointerup', function () { zonePaint = null; });
  function zoneMode(on) {
    zonesEl.hidden = !on; $('zone-bar').hidden = !on; $('stage-controls').hidden = on;
    if (on) { placeZones(); drawZones(); stage.scrollIntoView({ behavior: 'smooth', block: 'center' }); }
    else zoneEdit = null;
  }
  $('zone-edit').onclick = function () { zoneEdit = zonesFromHex(cam && cam.zones); zoneMode(true); };
  $('zone-cancel').onclick = function () { zoneMode(false); };
  $('zone-all').onclick = function () { zoneEdit = zoneEdit.map(function () { return true; }); drawZones(); };
  $('zone-save').onclick = async function () {
    if (!zoneEdit.some(Boolean)) { alert('Leave at least one area watched.'); return; }
    if (await send('zones', [zonesToHex(zoneEdit)]) === 202) zoneMode(false);
  };
  window.addEventListener('resize', function () { if (zoneEdit) placeZones(); });

  // ── Health history: fps, WiFi, memory, restarts ──
  var hData = null, hHours = 6, hCharts = [];
  var REASONS = { brownout: ['Brownout — the power dipped', 1], 'power-on': ['Power was cut', 1],
                  software: ['Restarted itself or by command', 0], crash: ['Crashed', 1], 'task-wdt': ['Froze (watchdog)', 1],
                  'interrupt-wdt': ['Froze (watchdog)', 1], watchdog: ['Froze (watchdog)', 1], external: ['Reset button', 0] };
  var METRICS = [
    { key: 'fps', title: 'Frames per second', fmt: function (v) { return v.toFixed(1); }, zero: true },
    { key: 'rssi', title: 'WiFi signal', fmt: function (v) { return v + ' dBm'; } },
    { key: 'heap', title: 'Free memory', fmt: function (v) { return v + ' KB'; } },
  ];
  async function loadHealth() {
    try { hData = await (await fetch('/health' + q, { cache: 'no-store' })).json(); renderHealth(); } catch (e) {}
  }
  document.querySelector('#h-range').addEventListener('click', function (e) {
    var b = e.target.closest('button'); if (!b) return;
    hHours = +b.dataset.h;
    this.querySelectorAll('button').forEach(function (x) { x.setAttribute('aria-pressed', String(x === b)); });
    renderHealth();
  });
  function hm(t) { return new Date(t).toLocaleTimeString([], { hour: 'numeric', minute: '2-digit' }); }
  function svgEl(tag, attrs) {
    var el = document.createElementNS('http://www.w3.org/2000/svg', tag);
    for (var k in attrs) el.setAttribute(k, attrs[k]);
    return el;
  }
  function renderHealth() {
    if (!hData) return;
    var now = Date.now(), t0 = now - hHours * 3600e3;
    var S = hData.samples.filter(function (x) { return x.t >= t0; });
    var R = hData.restarts.filter(function (x) { return x.t >= t0; });
    var on = S.filter(function (x) { return x.on; });
    $('h-online').textContent = S.length ? Math.round(on.length / S.length * 100) + '%' : '–';
    $('h-rcount').textContent = S.length ? String(R.length) : '–';
    $('h-fps').textContent = on.length ? (on.reduce(function (a, x) { return a + x.fps; }, 0) / on.length).toFixed(1) : '–';
    var box = $('h-charts'); box.textContent = ''; hCharts = [];
    if (S.length < 2) {
      $('h-note').textContent = 'Collecting — the first points appear within a minute.';
    } else {
      $('h-note').textContent = 'Since ' + hm(hData.samples[0].t) + ' · history starts over when the server restarts.';
      t0 = Math.max(t0, S[0].t);
    }
    var W = box.clientWidth || 300, H = 64, pad = 6, top = 16;
    // Average into ~3 px buckets so 24 h of 30 s samples reads as a line, not noise.
    // A bucket with any offline sample is offline.
    var span = now - t0, nb = Math.max(2, Math.floor(W / 3)), B = [];
    S.forEach(function (x) {
      var k = Math.min(nb - 1, Math.floor((x.t - t0) / span * nb));
      var b = B[k] || (B[k] = { t: 0, n: 0, on: true, fps: 0, rssi: 0, heap: 0 });
      b.t += x.t; b.n++; if (!x.on) b.on = false;
      if (x.on) { b.fps += x.fps || 0; b.rssi += x.rssi || 0; b.heap += x.heap || 0; }
    });
    var Sb = B.filter(Boolean).map(function (b) {
      var n = b.n;
      return { t: b.t / n, on: b.on, fps: b.on ? Math.round(b.fps / n * 10) / 10 : null,
               rssi: b.on ? Math.round(b.rssi / n) : null, heap: b.on ? Math.round(b.heap / n) : null };
    });
    var enough = S.length >= 2;
    METRICS.forEach(function (m) {
      if (!enough) return;
      var S = Sb;                                  // this chart draws the buckets
      var vals = S.filter(function (x) { return x[m.key] !== null; }).map(function (x) { return x[m.key]; });
      var lo = vals.length ? Math.min.apply(null, vals) : 0, hi = vals.length ? Math.max.apply(null, vals) : 1;
      if (m.zero) lo = 0;
      if (hi - lo < 2) { hi += 1; lo -= m.zero ? 0 : 1; }
      var X = function (t) { return (t - t0) / (now - t0) * W; };
      var Y = function (v) { return top + (1 - (v - lo) / (hi - lo)) * (H - top - pad); };
      var wrap = document.createElement('div'); wrap.className = 'hc';
      var last = hData.samples[hData.samples.length - 1][m.key];
      wrap.innerHTML = '<div class="hc-head"><span>' + m.title + '</span><b>' + (last === null ? 'offline' : m.fmt(last)) + '</b></div>';
      var svg = svgEl('svg', { viewBox: '0 0 ' + W + ' ' + H, role: 'img',
        'aria-label': m.title + ', last ' + hHours + ' hours, ' + m.fmt(lo) + ' to ' + m.fmt(hi) });
      svg.append(svgEl('line', { class: 'grid-l', x1: 0, x2: W, y1: H - pad, y2: H - pad }));
      svg.append(svgEl('line', { class: 'grid-l', x1: 0, x2: W, y1: top, y2: top }));
      var tHi = svgEl('text', { class: 'ax', x: 0, y: top - 4 }); tHi.textContent = m.fmt(hi); svg.append(tHi);
      var tLo = svgEl('text', { class: 'ax', x: W, y: H + 11, 'text-anchor': 'end' }); tLo.textContent = 'min ' + m.fmt(lo); svg.append(tLo);
      var segs = [], cur = null;                  // offline stretches break the line and get a red band
      S.forEach(function (x, i) {
        if (x[m.key] === null) {
          cur = null;
          var nx = S[i + 1] ? X(S[i + 1].t) : W, px = X(x.t);
          svg.append(svgEl('rect', { class: 'off-band', x: px, y: 0, width: Math.max(1, nx - px), height: H }));
        } else { if (!cur) segs.push(cur = []); cur.push([X(x.t), Y(x[m.key])]); }
      });
      segs.forEach(function (pts) {
        var d = pts.map(function (p, i) { return (i ? 'L' : 'M') + p[0].toFixed(1) + ' ' + p[1].toFixed(1); }).join('');
        if (pts.length > 1) svg.append(svgEl('path', { class: 'ar', d: d + 'L' + pts[pts.length - 1][0].toFixed(1) + ' ' + (H - pad) + 'L' + pts[0][0].toFixed(1) + ' ' + (H - pad) + 'Z' }));
        svg.append(svgEl('path', { class: 'ln', d: pts.length > 1 ? d : d + 'l0.1 0' }));
      });
      R.forEach(function (r) { var x = X(r.t); svg.append(svgEl('line', { class: 'rs', x1: x, x2: x, y1: 0, y2: H })); });
      var xh = svgEl('line', { class: 'xh', y1: 0, y2: H, visibility: 'hidden' });
      var dot = svgEl('circle', { class: 'dot', r: 4, visibility: 'hidden' });
      svg.append(xh, dot);
      hCharts.push({ m: m, xh: xh, dot: dot, X: X, Y: Y });
      svg.addEventListener('pointermove', function (e) { hover(e, svg, Sb, X); });
      svg.addEventListener('pointerleave', unhover);
      wrap.append(svg); box.append(wrap);
    });
    var list = $('h-restarts'); list.textContent = '';
    R.slice(0, 8).forEach(function (r) {
      var why = REASONS[r.reason] || [r.reason, 1];
      var li = document.createElement('li');
      var sp = document.createElement('span'); sp.className = 'why' + (why[1] ? '' : ' ok'); sp.textContent = why[0];
      var tm = document.createElement('time'); tm.textContent = hm(r.t);
      li.append(sp, tm); list.append(li);
    });
  }
  function hover(e, svg, S, X) {                 // crosshair on every chart at the nearest sample
    var rect = svg.getBoundingClientRect(), x = (e.clientX - rect.left) / rect.width * (svg.viewBox.baseVal.width);
    var best = S[0], bd = Infinity;
    S.forEach(function (s) { var d = Math.abs(X(s.t) - x); if (d < bd) { bd = d; best = s; } });
    var lines = [hm(best.t) + (best.on ? '' : ' · offline')];
    hCharts.forEach(function (c) {
      var v = best[c.m.key], px = c.X(best.t);
      c.xh.setAttribute('x1', px); c.xh.setAttribute('x2', px); c.xh.setAttribute('visibility', 'visible');
      if (v === null) c.dot.setAttribute('visibility', 'hidden');
      else { c.dot.setAttribute('cx', px); c.dot.setAttribute('cy', c.Y(v)); c.dot.setAttribute('visibility', 'visible'); }
      if (v !== null) lines.push(c.m.title + ': ' + c.m.fmt(v));
    });
    var tip = $('h-tip'); tip.innerHTML = lines.join('<br>'); tip.hidden = false;
    tip.style.left = Math.min(e.clientX + 12, innerWidth - tip.offsetWidth - 8) + 'px';
    tip.style.top = (e.clientY - tip.offsetHeight - 12) + 'px';
  }
  function unhover() {
    $('h-tip').hidden = true;
    hCharts.forEach(function (c) { c.xh.setAttribute('visibility', 'hidden'); c.dot.setAttribute('visibility', 'hidden'); });
  }
  loadHealth(); setInterval(loadHealth, 30000);
  window.addEventListener('resize', renderHealth);

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
    var bodies = showBoxes && meta && Date.now() - metaAt < 2500 ? (meta.bodies || []) : [];
    ctx.setLineDash([6, 5]); ctx.lineWidth = 1.5; ctx.strokeStyle = '#60a5fa'; ctx.shadowBlur = 0;
    ctx.font = '600 11px ui-sans-serif, system-ui, sans-serif'; ctx.fillStyle = '#60a5fa';
    bodies.forEach(function (b) {
      var x = ox + b[0] * dw, y = oy + b[1] * dh;
      ctx.strokeRect(x, y, b[2] * dw, b[3] * dh);
      ctx.fillText('person', x + 5, y + 14);
    });
    ctx.setLineDash([]);
    var hand = showBoxes && meta && Date.now() - metaAt < 1500 ? meta.hand : null;
    if (hand) {                                  // the hand the gesture reader is watching (pink)
      var hs = handShown || (handShown = { x: hand.x, y: hand.y, w: hand.w, h: hand.h });
      ['x', 'y', 'w', 'h'].forEach(function (k) { hs[k] += (hand[k] - hs[k]) * 0.4; });
      var hx = ox + hs.x * dw - 4, hy = oy + hs.y * dh - 4, hw = hs.w * dw + 8, hh = hs.h * dh + 8;
      ctx.strokeStyle = '#f472b6'; ctx.lineWidth = 2; ctx.shadowColor = '#f472b6'; ctx.shadowBlur = 10;
      ctx.beginPath(); ctx.roundRect ? ctx.roundRect(hx, hy, hw, hh, 10) : ctx.rect(hx, hy, hw, hh); ctx.stroke();
      ctx.shadowBlur = 0;
      var hl = hand.g || '✋ hand';
      ctx.font = '600 12px ui-sans-serif, system-ui, sans-serif';
      var hlw = ctx.measureText(hl).width + 14, hly = hy + hh + 4;
      ctx.fillStyle = 'rgba(7,9,12,.72)';
      ctx.beginPath(); ctx.roundRect ? ctx.roundRect(hx, hly, hlw, 20, 10) : ctx.rect(hx, hly, hlw, 20); ctx.fill();
      ctx.fillStyle = '#f9a8d4'; ctx.fillText(hl, hx + 7, hly + 14);
    } else handShown = null;
    faces.forEach(function (f, i) {
      var t = shown[i] || (shown[i] = { x: f.x, y: f.y, w: f.w, h: f.h });
      ['x', 'y', 'w', 'h'].forEach(function (k) { t[k] += (f[k] - t[k]) * 0.35; });
    });
    shown.length = faces.length;
    faces.forEach(function (f, i) {
      var b = shown[i], x = ox + b.x * dw, y = oy + b.y * dh, w = b.w * dw, h = b.h * dh;
      var color = f.admin ? '#facc15' : f.id === 'known' ? '#4ade80' : f.id === 'unknown' ? '#fbbf24' : '#5eead4';
      ctx.strokeStyle = color; ctx.lineWidth = 2.5; ctx.lineCap = 'round';
      ctx.shadowColor = color; ctx.shadowBlur = 8;
      var c = Math.min(w, h) * 0.24;
      ctx.beginPath();
      [[x, y, 1, 1], [x + w, y, -1, 1], [x, y + h, 1, -1], [x + w, y + h, -1, -1]].forEach(function (p) {
        ctx.moveTo(p[0] + p[2] * c, p[1]); ctx.lineTo(p[0], p[1]); ctx.lineTo(p[0], p[1] + p[3] * c);
      });
      ctx.stroke();
      ctx.shadowBlur = 0;
      var label = (f.admin ? '👑 ' : '') + (f.id === 'known' ? f.name : f.id === 'unknown' ? 'Stranger' : 'Identifying…') +
        (f.admin ? ' · admin' : '') + '  ' + (EMOJI[f.emo] || '');
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
