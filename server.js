// ARIA cam relay — the ESP32-CAM pushes JPEG frames here (it sits behind a
// home router, so nothing on the internet can reach it directly); viewers
// on any phone/browser watch the latest frames as an MJPEG stream.
//
//   POST /push       the camera (the OV7670 on the display board) → relay
//                    (header X-Cam-Key: $CAM_KEY, body: JPEG); replies with
//                    the viewer count. ?src=eye2 is accepted and ignored.
//   POST /meta       tracker → relay  (header X-Cam-Key, JSON body): face boxes,
//                    names, emotions and the robot's mood, drawn over the video
//   GET  /events     Server-Sent Events: /meta updates as messages, plus named
//                    "log" events for the activity timeline (?key=)
//   GET  /           the page — behind a login: POST /login with the admin key
//                    sets a signed cookie (30 days); GET /logout clears it.
//                    The page's own requests (/stream, /events, /status…) need
//                    that cookie. Devices keep their keys (VIEW_KEY for the
//                    display's /display poll, CAM_KEY for /push and /meta).
//   POST /cmd        page → display command (header X-Admin-Key: $ADMIN_KEY,
//                    else $CAM_KEY; JSON {cmd, args}) — screen, message,
//                    emotion, view, camera zoom, restart
//   GET  /display    the OLED display's pending state (?key=): screen on/off,
//                    latest admin message, latest emotion request — it polls
//                    this every 2 s (admin sets them via /cmd: screen, message,
//                    emotion)
//   GET  /stream     MJPEG stream     (?key=)
//   GET  /snapshot   latest JPEG      (?key=)
//   GET  /status     JSON             (?key=)
//   GET  /health     camera health history (?key=): online / fps samples every
//                    30 s for 24 h. Kept in memory, so it starts over when
//                    Render restarts the relay
//   GET  /healthz    Render health check
//
// AYA's pan-tilt head:
//   POST /cmd head_*  page → relay: queued in `headq` (≤8), handed to the
//                    display in its POST /display reply until it acks them
//                    (X-Head-Ack: <last id applied>)
//   POST /display    also carries X-Head: pan,tilt,mode,state and
//                    X-Spots: name:pan:tilt;… → SSE "head", /status .head
//   POST /push?src=eye2&pano=<id>&k=<i>&n=<count>   panorama frames (kept for
//                    the last 5 panoramas) → SSE "pano"
//   GET  /panos      the panoramas kept; GET /pano/<id>/<k>.jpg one frame
//   Room map: POST /display X-Map: cols,rows,p0,p1,t0,t1 (pan p0..p1 = columns
//                    0..cols-1, tilt t0..t1 = rows 0..rows-1; smaller tilt looks
//                    up, so row 0 is the top). POST /push?src=eye2&map=1&c=&r=&p=&t=
//                    keeps the latest picture per cell → SSE "map". People and
//                    security events add to the activity of the cell the head
//                    points at (decays ×0.9 an hour); X-Event "changed ... view c,r"
//                    marks a cell. GET /map.json, GET /map/<c>_<r>.jpg.
//                    POST /cmd head_map: a full scan of the room.
//   The tracker's hand signs (/meta gesture + hand) go to the display once
//   each, as `sign: {k, t, hx}` in its poll reply.
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
const OFFLINE_AFTER_MS = 30000;   // no frame for this long → camera offline (it sends one every few seconds)
const POLL_VIEWER_MS = 5000;      // snapshot-polling viewers count for this long

if (!CAM_KEY || !VIEW_KEY) {
  console.error('CAM_KEY and VIEW_KEY environment variables are required');
  process.exit(1);
}

const MAX_META_BYTES = 8 * 1024;

let latestFrame = null;
let latestSeq = 0;                // bumps with each frame: the snapshot ETag, so a poller gets a 304, not the same JPEG again
let latestAt = 0;
let lastPollAt = 0;
const streamViewers = new Set();
let latestMeta = null;            // JSON string of the last /meta
const metaSubscribers = new Set();
const frameTimes = [];            // arrival times of recent frames, for the fps readout
let frameSize = null;             // {w, h} from the latest JPEG's header
// When each part of the system was last heard from, for the page's status strip
const seen = { eye2: 0, display: 0, tracker: 0 };
// What the OLED shows, sent with each display poll (POST /display): 128x64,
// 1 bit per pixel, row-major MSB-first (the page's format), base64
let oledFrame = null;

// Activity timeline, derived from /meta. Presence is debounced — a face that
// drops out for a frame or two doesn't log "left" and "arrived" again.
const LOG_MAX = 30;
const activity = [];              // newest first: {t, kind, text}
const presence = { here: false, lastFace: 0, who: null, sleeping: null };

// Health history for the page's charts: a sample every 30 s for 24 h. In
// memory only — a relay restart starts it over.
const HEALTH_EVERY_MS = 30000;
const HEALTH_KEEP = 24 * 3600 * 1000 / HEALTH_EVERY_MS;
const healthSamples = [];         // {t, on, fps}
let lastGesture = 0;

setInterval(() => {
  const on = status().online;
  healthSamples.push({ t: Date.now(), on, fps: on ? Math.round(fps() * 10) / 10 : null });
  if (healthSamples.length > HEALTH_KEEP) healthSamples.shift();
}, HEALTH_EVERY_MS);

// What the admin has asked of the OLED display. Ids let the display tell a
// new message/emotion from one it has already shown.
const EMOTIONS = ['giggle', 'wink', 'heart', 'surprise', 'curious', 'think', 'shy', 'dizzy',
                  'roll', 'nod', 'yawn', 'purr', 'squint', 'sleep', 'wake'];
const MSG_MAX = 120;
const VIEWS = ['auto', 'eyes', 'clock', 'weather', 'stats', 'detect', 'cam2'];
// view/zoom2 start as null: after a relay restart the display keeps what it shows until someone picks
const displayState = { screen: 1, msg: null, emotion: null, seq: 0, restart: 0, shutdown: 0, view: null, zoom2: null, ignore: null };

// SSE subscribers: a page that stops reading (sleeping phone, dead link) would
// otherwise buffer every event here. Over 1 MB queued, it's skipped; still
// over after 30 s, it's dropped (the page's EventSource reconnects by itself).
const SSE_MAX_SUBS = 50;
const SSE_MAX_QUEUED = 1024 * 1024;
const sseStuckSince = new Map();  // res → when it went over SSE_MAX_QUEUED
function sseWrite(s, line) {
  if (s.writableLength > SSE_MAX_QUEUED) {
    const since = sseStuckSince.get(s);
    if (!since) sseStuckSince.set(s, Date.now());
    else if (Date.now() - since > 30000) { sseStuckSince.delete(s); metaSubscribers.delete(s); s.destroy(); }
    return;
  }
  sseStuckSince.delete(s);
  s.write(line);
}
function broadcast(event, obj) {
  const line = `event: ${event}\ndata: ${JSON.stringify(obj)}\n\n`;
  for (const s of metaSubscribers) sseWrite(s, line);
}

// The face the laptop tracker last saw (from /meta), handed to the display on
// its poll — so the tracker never has to talk to the board directly
let boardFace = null;

function publicDisplay() {
  const m = displayState.msg;
  return { screen: displayState.screen, msg: m && Date.now() - m.t < m.secs * 1000 ? m : null,
           emotion: displayState.emotion, restart: displayState.restart, shutdown: displayState.shutdown,
           view: displayState.view, zoom2: displayState.zoom2,
           ignore: displayState.ignore, face: boardFace && Date.now() - boardFace.t < 3000 ? boardFace : null };
}

// ── Login: one key (ADMIN_KEY) opens the page ────────────────────────────
// The cookie is "<expiry>.<HMAC(expiry)>" signed with the admin key, so it
// survives relay restarts and changing ADMIN_KEY on Render logs everyone out.
const SESSION_DAYS = 30;
function sign(exp) { return crypto.createHmac('sha256', 'aya-session:' + ADMIN_KEY).update(String(exp)).digest('hex'); }
function newSession() { const exp = Date.now() + SESSION_DAYS * 86400e3; return exp + '.' + sign(exp); }
function sessionOk(req) {
  const m = /(?:^|;\s*)aya_session=([0-9]+)\.([0-9a-f]{64})/.exec(req.headers.cookie || '');
  if (!m || +m[1] < Date.now()) return false;
  return keyMatches(m[2], sign(m[1]));
}
const loginFails = new Map();                   // ip → {n, until, at}: 5 wrong keys = 10 min wait
const LOGIN_FAILS_MAX = 1000;
// Render's proxy appends the real client address to X-Forwarded-For, so the
// LAST entry is the one to trust (the first can be anything the client sent)
function clientIp(req) {
  const xff = String(req.headers['x-forwarded-for'] || '').split(',').map((x) => x.trim()).filter(Boolean);
  return xff.length ? xff[xff.length - 1] : String(req.socket.remoteAddress || '');
}
function pruneLoginFails() {
  const now = Date.now();
  for (const [ip, f] of loginFails)               // a failure counts for 10 min, a lockout until it ends
    if (Math.max(f.until, f.at + 10 * 60e3) < now) loginFails.delete(ip);
  while (loginFails.size > LOGIN_FAILS_MAX) loginFails.delete(loginFails.keys().next().value);   // oldest first
}
// At most one "Failed login attempt" line a minute, so a flood can't push the
// real events out of the 30-entry log; the ones held back are counted in the next
const failLog = { last: 0, pending: 0 };
function logLoginFail() {
  failLog.pending++;
  flushLoginFails();
}
function flushLoginFails() {
  if (!failLog.pending || Date.now() - failLog.last < 60000) return;
  logEvent('privacy', failLog.pending > 1 ? `${failLog.pending} failed login attempts` : 'Failed login attempt');
  failLog.last = Date.now();
  failLog.pending = 0;
}
setInterval(() => { pruneLoginFails(); flushLoginFails(); }, 60000).unref();
// Request bodies for /login, /cmd and /ask: up to `max` bytes, else the request is destroyed
function readBody(req, max, cb) {
  const chunks = [];
  let size = 0, over = false;
  req.on('data', (c) => {
    if (over) return;
    size += c.length;
    if (size > max) { over = true; req.destroy(); return; }
    chunks.push(c);
  });
  req.on('end', () => { if (!over) cb(Buffer.concat(chunks)); });
}
const SMALL_BODY_MAX = 8 * 1024;
function handleLogin(req, res) {
  const ip = clientIp(req), f = loginFails.get(ip);
  if (f && f.until > Date.now()) return send(res, 429, 'text/html; charset=utf-8', loginPage('Too many wrong keys. Try again in a few minutes.'));
  readBody(req, SMALL_BODY_MAX, (body) => {
    const key = new URLSearchParams(body.toString('utf8')).get('key') || '';
    if (!keyMatches(key.trim(), ADMIN_KEY)) {
      const n = (f && f.until <= Date.now() && f.n >= 5 ? 0 : (f ? f.n : 0)) + 1;
      loginFails.delete(ip);                       // re-insert: Map order stays oldest-first for the cap
      loginFails.set(ip, { n, until: n >= 5 ? Date.now() + 10 * 60e3 : 0, at: Date.now() });
      if (loginFails.size > LOGIN_FAILS_MAX) pruneLoginFails();
      logLoginFail();
      return send(res, 401, 'text/html; charset=utf-8', loginPage('That key is not valid.'));
    }
    loginFails.delete(ip);
    res.writeHead(303, { Location: '/', 'Cache-Control': 'no-store',
      'Set-Cookie': `aya_session=${newSession()}; Path=/; Max-Age=${SESSION_DAYS * 86400}; HttpOnly; Secure; SameSite=Strict` });
    res.end();
  });
}

// "Poll now": the display polls /display every 2 s but uploads a frame every
// ~0.5 s, so a command (or a hand sign) waiting for it sets this, and the next
// upload's reply says ",p" — it polls at once instead of up to 2 s later.
let deviceKick = false;

function handleCmd(req, res) {
  if (!sessionOk(req) && !keyMatches(req.headers['x-admin-key'], ADMIN_KEY)) return send(res, 401, 'text/plain', 'not logged in');
  readBody(req, SMALL_BODY_MAX, (raw) => {
    let body;
    try { body = JSON.parse(raw.toString('utf8')); } catch { return send(res, 400, 'text/plain', 'bad json'); }
    const cmd = String(body.cmd || ''), args = (body.args || []).map(String);
    deviceKick = true;
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
    if (cmd === 'restart_all') {       // the display (and its camera) picks it up on its next poll (≤2 s)
      displayState.restart = Date.now();
      logEvent('privacy', 'System restart');
      return send(res, 202, 'text/plain', 'restarting');
    }
    if (cmd === 'shutdown') {          // deep sleep on its next poll; only a touch (or EN / power) wakes it
      displayState.shutdown = Date.now();
      logEvent('restart', 'Shut down from the page · touch AYA to wake her');
      return send(res, 202, 'text/plain', 'shutting down');
    }
    if (cmd === 'view') {              // what the OLED shows: auto rotation, one screen, or camera 2 live
      if (!VIEWS.includes(args[0])) return send(res, 400, 'text/plain', 'view ' + VIEWS.join('|'));
      displayState.view = args[0];
      broadcast('display', publicDisplay());
      return send(res, 202, 'text/plain', 'queued');
    }
    if (cmd === 'ignore') {            // camera zones AYA never counts as motion: 12 rows x 16 bits as 48 hex digits
      if (!/^[0-9a-f]{48}$/.test(args[0] || '')) return send(res, 400, 'text/plain', 'ignore <48 hex digits>');
      displayState.ignore = args[0];
      logEvent('privacy', 'Motion ignore zones updated');
      broadcast('display', publicDisplay());
      return send(res, 202, 'text/plain', 'queued');
    }
    if (cmd === 'zoom2') {             // camera 2 (the display's OV7670): digital zoom ×10
      const z = parseInt(args[0], 10);
      if (!(z === 0 || (z >= 10 && z <= 30))) return send(res, 400, 'text/plain', 'zoom2 0 (auto) or 10..30');
      displayState.zoom2 = z;
      broadcast('display', publicDisplay());
      return send(res, 202, 'text/plain', 'queued');
    }
    if (cmd === 'emotion') {
      if (!EMOTIONS.includes(args[0])) return send(res, 400, 'text/plain', 'unknown emotion');
      displayState.emotion = { id: ++displayState.seq, name: args[0], t: Date.now() };
      broadcast('display', publicDisplay());
      return send(res, 202, 'text/plain', 'queued');
    }
    if (cmd.startsWith('head_')) return headCmd(res, cmd, args);
    send(res, 400, 'text/plain', 'unknown command');
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
  mapActivity(kind, text);
  const e = { t: Date.now(), kind, text };
  activity.unshift(e);
  if (activity.length > LOG_MAX) activity.pop();
  const line = `event: log\ndata: ${JSON.stringify(e)}\n\n`;
  for (const s of metaSubscribers) sseWrite(s, line);
}

const objectSeen = new Map();       // label → last time seen

function trackActivity(meta) {
  const now = Date.now();
  const f = (meta.faces || [])[0];
  if (f) {
    presence.lastFace = now;
    if (!presence.here) { presence.here = true; logEvent('arrive', 'Someone appeared'); }
    const who = f.id === 'known' ? f.name : f.id === 'unknown' ? 'stranger' : null;
    if (who && who !== presence.who) {
      presence.who = who;
      if (f.id === 'known') { logEvent('known', `${who} is here`); captureEvent('known', `${who} is here`); }
      else { logEvent('stranger', 'Unknown person in view'); captureEvent('stranger', 'Unknown person in view'); autoDescribe(); }
    }
  }
  // Objects (YOLOX on the laptop): log a kind when it shows up after 10 min away
  for (const o of Array.isArray(meta.objects) ? meta.objects : []) {
    const label = String(o.label || '').slice(0, 24);
    if (!label) continue;
    if (!objectSeen.has(label) || now - objectSeen.get(label) > 600000) logEvent('object', `Seen: ${label}`);
    objectSeen.set(label, now);
  }
  const g = meta.gesture;           // {name, who, t} from the tracker's hand-sign reader
  if (g && typeof g.t === 'number' && g.t > lastGesture) {
    lastGesture = g.t;
    logEvent('gesture', `${String(g.name).slice(0, 40)}${g.who ? ' from ' + String(g.who).slice(0, 30) : ''}`);
  }
  const r = meta.robot;
  if (r && typeof r.sleeping === 'boolean' && r.sleeping !== presence.sleeping) {
    if (presence.sleeping !== null) logEvent(r.sleeping ? 'sleep' : 'wake', r.sleeping ? 'AYA fell asleep' : 'AYA woke up');
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

// Vision on Render (nothing runs on the laptop): YOLO11n + YuNet + SFace in
// onnxruntime-node, one frame at a time (a busy analyzer drops the frame).
// FACE_DB_PATH / FACE_DB_JSON hold the enrolled faces — never in git.
let localVision = null;
try {
  if (process.env.VISION_OFF === '1') throw new Error('VISION_OFF=1');      // kill switch (Render env var)
  localVision = require('./vision');
  localVision.init({}).then(() => console.log('[vision] ready'), (e) => { console.error('[vision] ' + e.message); localVision = null; });
} catch (e) { console.error('[vision] not available: ' + e.message); }

function handlePush(req, res, url) {
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
    seen.eye2 = Date.now();
    const frame = Buffer.concat(chunks);
    if (!acceptFrame(frame)) return send(res, 400, 'text/plain', 'not a JPEG');
    notePano(url, frame);                          // a panorama frame is also the live picture
    if (localVision && Date.now() - metaHttpAt > 3000)  // (the laptop tracker, when it runs, wins)
      localVision.analyze(frame).then((m) => { if (m) ingestMeta(m); }, () => {});
    noteMapFrame(url, frame);                      // so is a room map frame
    send(res, 200, 'text/plain', String(viewerCount()) + (deviceKick ? ',p' : ''));
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
    metaHttpAt = Date.now();                      // the laptop tracker (if it runs) wins over the local vision for 3 s
    ingestMeta(meta);
    send(res, 204, 'text/plain', '');
  });
}

// The vision result, from the laptop tracker (POST /meta) or from vision.js
// running in this process on each eye2 frame
let metaHttpAt = 0;
function ingestMeta(meta) {
  {
    latestMeta = JSON.stringify(meta);            // re-serialised: only valid JSON reaches viewers
    const f = Array.isArray(meta.faces) && meta.faces[0];       // the face, passed to the display on its poll
    if (f && [f.x, f.y, f.w, f.h].every(Number.isFinite)) {
      boardFace = { x: +((f.x + f.w / 2) * 2 - 1).toFixed(2), y: +((f.y + f.h / 2) * 2 - 1).toFixed(2), s: +f.w.toFixed(3),
                    id: String(f.id || ''), name: String(f.name || '').slice(0, 20), admin: !!f.admin, emo: String(f.emo || ''), t: Date.now() };
    }
    seen.tracker = Date.now();
    if ((Array.isArray(meta.bodies) && meta.bodies.length) || (Array.isArray(meta.faces) && meta.faces.length))
      aiPersonAt = Date.now();                    // the laptop's detector sees someone (person-event check)
    noteSign(meta);
    trackActivity(meta);
    for (const s of metaSubscribers) s.write(`data: ${latestMeta}\n\n`);
  }
}

// The display's poll: GET /display, or POST /display with its 1 KB screen
// buffer (u8g2 page layout: byte = 8 vertical pixels) in the body.
// The board sends its confirmed person detections with each poll
// (X-Person: count;confidence;direction). A rise is a new detection; a lower
// count means the board restarted, so re-baseline.
// ── AYA's scene understanding ───────────────────────────────────────────
// One camera 2 frame goes to an open-weight vision model (Llama 4 Scout) on
// Hugging Face Inference Providers — only when something happens (a person,
// a stranger) or someone asks on the page. Free accounts get a small monthly
// credit, so there's a daily cap, and automatic descriptions leave room for
// questions. HF_TOKEN: a fine-grained token with only "Inference Providers".
const HF_TOKEN = process.env.HF_TOKEN || '';
const VISION_MODEL = process.env.VISION_MODEL || 'meta-llama/Llama-4-Scout-17B-16E-Instruct';
const VISION_DAILY = parseInt(process.env.VISION_DAILY || '30', 10);
const VISION_AUTO_MAX = Math.max(0, VISION_DAILY - 10);   // the last 10 a day are for questions
const VISION_AUTO_GAP_MS = 3 * 60 * 1000;                 // at most one automatic description per 3 min
const vision = { day: '', used: 0, auto: 0, busy: false, lastAuto: 0, err: null };

function visionDay() {
  const d = new Date().toISOString().slice(0, 10);
  if (d !== vision.day) { vision.day = d; vision.used = 0; vision.auto = 0; }
}

async function askVision(question) {
  visionDay();
  if (!HF_TOKEN) throw new Error('AI is not set up on the server (HF_TOKEN missing)');
  if (!latestFrame || Date.now() - latestAt > OFFLINE_AFTER_MS) throw new Error('the camera is offline');
  if (vision.used >= VISION_DAILY) throw new Error(`today's limit of ${VISION_DAILY} AI looks is used up`);
  if (vision.busy) throw new Error('AYA is still looking — try again in a moment');
  vision.busy = true;
  vision.used++;
  try {
    const ask = question
      ? `${question}\nAnswer in one or two short sentences. If the picture can't show it, say so.`
      : 'In one short sentence, say what is happening. Mention people first (how many, what they are doing); say so if nobody is there.';
    const r = await fetch('https://router.huggingface.co/v1/chat/completions', {
      method: 'POST',
      headers: { Authorization: 'Bearer ' + HF_TOKEN, 'Content-Type': 'application/json' },
      body: JSON.stringify({ model: VISION_MODEL, max_tokens: 120, temperature: 0.2, messages: [
        { role: 'system', content: 'You are AYA, a home security camera. The picture is a small 160x120 grayscale frame, so be brief and honest about what is unclear.' },
        { role: 'user', content: [{ type: 'text', text: ask },
          { type: 'image_url', image_url: { url: 'data:image/jpeg;base64,' + latestFrame.toString('base64') } }] }] }),
      signal: AbortSignal.timeout(30000),
    });
    if (!r.ok) throw new Error(`AI service error ${r.status}`);
    const d = await r.json();
    const text = String((d.choices && d.choices[0] && d.choices[0].message && d.choices[0].message.content) || '')
      .replace(/\s+/g, ' ').trim().slice(0, 400);
    if (!text) throw new Error('the AI gave no answer');
    vision.err = null;
    return text;
  } catch (e) {
    vision.err = String(e.message || e).slice(0, 160);
    throw e;
  } finally {
    vision.busy = false;
  }
}

function autoDescribe() {                         // after a person/stranger event
  visionDay();
  if (!HF_TOKEN || vision.auto >= VISION_AUTO_MAX || Date.now() - vision.lastAuto < VISION_AUTO_GAP_MS) return;
  vision.lastAuto = Date.now();
  vision.auto++;
  setTimeout(() => askVision(null).then((t) => {
    logEvent('ai', t);
    const ev = gallery[0];                         // the description belongs with the event's snapshot
    if (ev && Date.now() - ev.t < 20000 && !ev.ai) { ev.ai = t; broadcast('gallery', galleryItem(ev)); }
  }).catch(() => {}), 1500);  // let them walk into view
}

function handleAsk(req, res) {
  if (!sessionOk(req)) return send(res, 401, 'application/json', JSON.stringify({ error: 'not logged in' }));
  readBody(req, SMALL_BODY_MAX, async (raw) => {
    let q;
    try { q = String(JSON.parse(raw.toString('utf8')).q || '').trim().slice(0, 200); }
    catch { return send(res, 400, 'application/json', JSON.stringify({ error: 'bad json' })); }
    try {
      const text = await askVision(q || null);
      send(res, 200, 'application/json', JSON.stringify({ text, left: VISION_DAILY - vision.used }));
    } catch (e) {
      send(res, 503, 'application/json', JSON.stringify({ error: String(e.message || e), left: VISION_DAILY - vision.used }));
    }
  });
}

let personSeen = null;
// AYA's auto-framing (X-AF: "x,y,zoom,locked" in the 80x60 frame, or "off"),
// passed to the page so its video follows the same way as the OLED
let lastAf = null;
function noteAf(req) {
  const v = String(req.headers['x-af'] || '');
  let af = null;
  if (v && v !== 'off') {
    const [x, y, z, t] = v.split(',').map(Number);
    if ([x, y, z].every(Number.isFinite)) af = { x, y, z, t: t === 1 };
  }
  if (JSON.stringify(af) !== JSON.stringify(lastAf)) { lastAf = af; broadcast('af', af || { off: true }); }
}

// The display's "person" is PIR + camera motion: a curtain swaying in the
// fan's draught while the PIR caught warm air scored 99%, and 49 of 62
// person-event photos were curtains. While the laptop tracker is running,
// its detector (YOLO11x) must also see a body or a face within 4 s either
// side; otherwise it's logged as plain motion. Tracker off: as before.
let aiPersonAt = 0;
function notePerson(req) {
  const [n, conf, dir] = String(req.headers['x-person'] || '').split(';');
  const count = parseInt(n, 10);
  if (!Number.isFinite(count)) return;
  if (personSeen !== null && count > personSeen) {
    let text = `Person detected · ${parseInt(conf, 10) || '?'}%`;
    if (dir === 'left' || dir === 'right') text += ` · moving ${dir}`;
    const at = Date.now();
    const confirm = () => {
      const trackerOn = seen.tracker && Date.now() - seen.tracker < 15000;
      if (!trackerOn || Math.abs(aiPersonAt - at) < 4000 || aiPersonAt > at) {
        logEvent('person', trackerOn ? text + ' · AI confirmed' : text);
        captureEvent('person', text);
        autoDescribe();
      } else logEvent('motion', 'Motion (no person seen by the AI)');
    };
    if (seen.tracker && Date.now() - seen.tracker < 15000 && Date.now() - aiPersonAt > 4000) setTimeout(confirm, 4000);   // give the AI a moment
    else confirm();
  }
  personSeen = count;
}

// The display's real screen state (a long touch can switch it): "on,seq",
// where seq counts its local changes — a newer one wins over the page's switch
let screenSeq = 0;
function noteScreen(req) {
  const [on, seq] = String(req.headers['x-screen'] || '').split(',').map(Number);
  if (!Number.isFinite(on) || !Number.isFinite(seq)) return;
  if (seq < screenSeq) screenSeq = seq;           // it restarted: its count starts over
  if (seq > screenSeq) {
    screenSeq = seq;
    const v = on ? 1 : 0;
    if (displayState.screen !== v) {
      displayState.screen = v;
      broadcast('display', publicDisplay());
      logEvent('screen', `Screen turned ${v ? 'on' : 'off'} by touch`);
    }
  }
}

// Events the display decides itself (X-Event: seq;kind;text) — lights on,
// unusual activity for the hour. Sent until replaced, so each seq is logged
// once; seq restarts at 1 when the display reboots.
let lastDeviceEvent = '';
function noteDeviceEvent(req) {
  const v = String(req.headers['x-event'] || '');
  if (!v || v === lastDeviceEvent) return;
  lastDeviceEvent = v;
  const [, kind, ...rest] = v.split(';');
  // The display turns anything outside ASCII into spaces, so its " · " arrives as a run of spaces
  const k = String(kind || '').replace(/[^a-z]/g, '').slice(0, 12),
        text = rest.join(';').replace(/[^\x20-\x7e]/g, '').replace(/ {2,}/g, ' · ').trim().slice(0, 80);
  if (!k || !text) return;
  if (k === 'changed') {                           // "Something changed · view <c>,<r>": mark that cell of the map
    const m = /view (\d+),(\d+)/.exec(text);
    if (m && +m[1] < MAP_MAX_COLS && +m[2] < MAP_MAX_ROWS) { roomMap.changed.set(m[1] + ',' + m[2], Date.now()); mapHint = m[1] + ',' + m[2]; }
  }
  logEvent(k, text);
  mapHint = null;
  if (k === 'unusual' || k === 'changed') captureEvent(k, text);
}

// Sent with the display's first poll after it starts: why it (re)started
function noteBoot(req) {
  const why = String(req.headers['x-boot'] || '').replace(/[^\x20-\x7e]/g, '').slice(0, 60);
  if (why) logEvent('restart', `AYA started · ${why}`);
}

// ── The head: two servos (pan, tilt) on the display board ───────────────
// Page commands wait in `headq` and ride out on the display's poll reply
// until it acks them (X-Head-Ack: the last id it applied). Ids restart with
// the relay, so an ack above the current max id is from before a restart: 0.
const HEAD_MODES = ['follow', 'patrol', 'hold'];
const HEAD_STATES = ['search', 'face', 'motion', 'inspect', 'hold', 'gesture', 'spot', 'pano', 'map', 'centre', '-'];
const HEAD_GESTURES = ['nod', 'shake', 'curious', 'startle', 'droop', 'stretch', 'excited'];
const SPOT_RE = /^[a-z0-9_-]{1,12}$/;
const HEADQ_MAX = 8;
const HEADQ_TTL_MS = 60000;       // a nudge from minutes ago must not fire when the display comes back
const headq = [];                 // {id, op, a, b, name, at}
let headId = 0;
let head = null;                  // {pan, tilt, mode, state, spots: [{name, pan, tilt}], rest, map} from X-Head / X-Spots / X-Map

function headPush(op, a, b, name) {
  headq.push({ id: ++headId, op, a: +a || 0, b: +b || 0, name: name || '', at: Date.now() });
  while (headq.length > HEADQ_MAX) headq.shift();
}

function headCmd(res, cmd, args) {
  const bad = (why) => send(res, 400, 'text/plain', why);
  const num = (v, lo, hi) => { const n = Number(v); return v !== '' && Number.isFinite(n) && n >= lo && n <= hi ? Math.round(n * 1000) / 1000 : null; };
  const spot = String(args[0] || '').trim().toLowerCase();
  switch (cmd) {
    case 'head_mode':
      if (!HEAD_MODES.includes(args[0])) return bad('head_mode follow|patrol|hold');
      headPush('mode', 0, 0, args[0]);
      break;
    case 'head_look': {
      const x = num(args[0], -1, 1), y = num(args[1], -1, 1);
      if (x === null || y === null) return bad('head_look x y (each -1..1)');
      headPush('look', x, y, '');
      break;
    }
    case 'head_nudge': {
      const dp = num(args[0], -45, 45), dt = num(args[1], -45, 45);
      if (dp === null || dt === null) return bad('head_nudge dpan dtilt (each -45..45 degrees)');
      headPush('nudge', dp, dt, '');
      break;
    }
    case 'head_goto': {
      const p = num(args[0], 0, 180), t = num(args[1], 0, 180);
      if (p === null || t === null) return bad('head_goto pan tilt (each 0..180 degrees)');
      headPush('goto', p, t, '');
      break;
    }
    case 'head_spot_save': case 'head_spot_go': case 'head_spot_del':
      if (!SPOT_RE.test(spot)) return bad('spot name: 1-12 of a-z 0-9 _ -');
      headPush(cmd.slice(5), 0, 0, spot);
      break;
    case 'head_gesture':
      if (!HEAD_GESTURES.includes(args[0])) return bad('head_gesture ' + HEAD_GESTURES.join('|'));
      headPush('gesture', 0, 0, args[0]);
      break;
    case 'head_pano':
      headPush('pano', 0, 0, '');
      break;
    case 'head_map':                                     // a full scan of the room, then back to its mode
      headPush('map', 0, 0, '');
      break;
    case 'head_rest_save': case 'head_rest_go':          // save the current position as the rest position / go there
      headPush(cmd.slice(5), 0, 0, '');
      break;
    default:
      return bad('unknown command');
  }
  send(res, 202, 'text/plain', 'queued');
}

function headAck(req) {
  const a = Number(req.headers['x-head-ack']);
  return Number.isInteger(a) && a > 0 && a <= headId ? a : 0;
}

function noteHeadAck(req) {
  const ack = headAck(req), now = Date.now();
  for (let i = headq.length - 1; i >= 0; i--)
    if (headq[i].id <= ack || now - headq[i].at > HEADQ_TTL_MS) headq.splice(i, 1);
}

// X-Head: "pan,tilt,mode,state[,restpan,resttilt]"; X-Spots: "name:pan:tilt;name:pan:tilt" (may be empty)
function noteHead(req) {
  const v = req.headers['x-head'];
  if (v === undefined) return;
  const [p, t, mode, state, rp, rt] = String(v).split(',').map((s) => s.trim());
  const pan = Number(p), tilt = Number(t);
  if (p === '' || t === '' || !Number.isFinite(pan) || !Number.isFinite(tilt)) return;
  const r1 = (n) => Math.round(Math.min(180, Math.max(0, n)) * 10) / 10;
  let spots = head ? head.spots : [];
  if (req.headers['x-spots'] !== undefined) {
    spots = String(req.headers['x-spots']).split(';').map((s) => s.trim().split(':'))
      .filter((a) => a.length === 3 && SPOT_RE.test(a[0].toLowerCase()) && a[1] !== '' && a[2] !== '' && Number.isFinite(+a[1]) && Number.isFinite(+a[2]))
      .slice(0, 24).map((a) => ({ name: a[0].toLowerCase(), pan: r1(+a[1]), tilt: r1(+a[2]) }));
  }
  const h = { pan: r1(pan), tilt: r1(tilt), mode: HEAD_MODES.includes(mode) ? mode : null,
              state: HEAD_STATES.includes(state) ? state : '-', spots,
              rest: rp && rt && Number.isFinite(+rp) && Number.isFinite(+rt) ? { pan: r1(+rp), tilt: r1(+rt) } : null,
              map: mapGeom() };
  if (JSON.stringify(h) !== JSON.stringify(head)) { head = h; broadcast('head', head); }
}

// Hand signs from the tracker (/meta gesture {name, who, t}, hand {x, y, w, h, g}),
// passed to the display once each as sign {k, t, hx} while under 4 s old
let signLast = null;              // {name, t, at}
let signSentT = null;
let handLast = null;              // {hx, at}: the hand's centre x (0..1)
function signKind(name) {
  const s = String(name).toLowerCase();
  if (s.includes('point')) return 'point';
  if (s.includes('wave') || s.includes('palm')) return 'palm';
  if (s.includes('thumbs down') || s.includes('thumb down')) return 'down';
  if (s.includes('thumbs up') || s.includes('thumb up')) return 'up';
  if (s.includes('peace')) return 'peace';
  if (s.includes('love')) return 'love';
  if (s.includes('fist')) return 'fist';
  return null;
}
function noteSign(meta) {
  const h = meta.hand;
  if (h && Number.isFinite(h.x) && Number.isFinite(h.w))
    handLast = { hx: Math.round(Math.min(1, Math.max(0, h.x + h.w / 2)) * 1000) / 1000, at: Date.now() };
  const g = meta.gesture;
  if (g && typeof g.t === 'number' && (!signLast || g.t !== signLast.t)) { signLast = { name: String(g.name || ''), t: g.t, at: Date.now() }; deviceKick = true; }
}
function pendingSign() {
  const s = signLast, now = Date.now();
  // Fresh by arrival time; t itself must also be recent (with some clock skew
  // allowed), so a tracker re-sending an old gesture after a relay restart isn't replayed
  if (!s || s.t === signSentT || now - s.at > 4000 || Math.abs(s.at - s.t) > 15000) return null;
  signSentT = s.t;
  const k = signKind(s.name);
  if (!k) return null;
  return { k, t: s.t, hx: handLast && now - handLast.at < 2000 ? handLast.hx : -1 };
}

// Panoramas: the display uploads each frame with ?pano=<id>&k=<i>&n=<count>.
// The last 5 are kept in memory (a relay restart clears them).
const PANO_KEEP = 5;
const PANO_MAX_FRAMES = 24;
const panos = [];                 // oldest first: {id, t, n, frames: [Buffer|null]}
function panoItem(p) {
  const got = [];
  p.frames.forEach((f, i) => { if (f) got.push(i); });
  return { id: p.id, t: p.t, n: p.n, have: got.length, got };
}
function notePano(url, frame) {
  const id = url.searchParams.get('pano');
  if (id === null || !/^\d{1,12}$/.test(id)) return;
  const k = Number(url.searchParams.get('k')), n = Number(url.searchParams.get('n'));
  if (!Number.isInteger(n) || n < 1 || n > PANO_MAX_FRAMES || !Number.isInteger(k) || k < 0 || k >= n) return;
  let p = panos.find((x) => x.id === +id);
  // The same id with another count, or much later: the display restarted and counts again
  if (p && (p.n !== n || Date.now() - p.t > 10 * 60e3)) { panos.splice(panos.indexOf(p), 1); p = null; }
  if (!p) {
    p = { id: +id, t: Date.now(), n, frames: new Array(n).fill(null) };
    panos.push(p);
    while (panos.length > PANO_KEEP) panos.shift();
  }
  p.frames[k] = frame;
  broadcast('pano', { id: p.id, t: p.t, n: p.n, have: panoItem(p).have, k });
}

// ── Room map ────────────────────────────────────────────────────────────
// While patrolling, the display uploads one frame per grid cell once the head
// has settled there (?map=1&c=&r=&p=&t=); the latest per cell is kept. Its
// X-Map header gives the grid: pan p0..p1 across columns 0..cols-1, tilt t0..t1
// down rows 0..rows-1 (a smaller tilt looks up, so row 0 is the top of the
// room). Activity: people and security events count toward the cell the head
// points at, fading ×0.9 an hour. In memory only.
const MAP_MAX_COLS = 12, MAP_MAX_ROWS = 8;
const MAP_HEAT_KINDS = new Set(['person', 'arrive', 'known', 'stranger', 'unknown', 'motion', 'changed', 'unusual', 'wave']);
const roomMap = { cols: null, rows: null, p0: null, p1: null, t0: null, t1: null,
                  cells: new Map(),       // "c,r" → {jpeg, pan, tilt, t}
                  activity: new Map(),    // "c,r" → {n, last}
                  changed: new Map() };   // "c,r" → when the display last saw something change there
let mapHint = null;                       // the cell a "changed" event names, for its activity
function mapGeom() {
  const m = roomMap;
  return m.cols ? { cols: m.cols, rows: m.rows, p0: m.p0, p1: m.p1, t0: m.t0, t1: m.t1 } : null;
}
function noteMapGeom(req) {
  const v = req.headers['x-map'];
  if (v === undefined) return;
  const a = String(v).split(',').map((x) => x.trim());
  if (a.length !== 6 || a.some((x) => x === '')) return;
  const [cols, rows, p0, p1, t0, t1] = a.map(Number);
  if (!Number.isInteger(cols) || !Number.isInteger(rows) || cols < 1 || cols > MAP_MAX_COLS || rows < 1 || rows > MAP_MAX_ROWS) return;
  if (![p0, p1, t0, t1].every((n) => Number.isFinite(n) && n >= 0 && n <= 180)) return;
  const m = roomMap;
  if (m.cols !== null && (m.cols !== cols || m.rows !== rows)) { m.cells.clear(); m.activity.clear(); m.changed.clear(); }
  Object.assign(m, { cols, rows, p0, p1, t0, t1 });
}
function noteMapFrame(url, frame) {
  if (url.searchParams.get('map') !== '1') return;
  const cs = url.searchParams.get('c') || '', rs = url.searchParams.get('r') || '';
  const ps = url.searchParams.get('p') || '', ts = url.searchParams.get('t') || '';
  if (!/^\d{1,2}$/.test(cs) || !/^\d{1,2}$/.test(rs) || ps.trim() === '' || ts.trim() === '') return;
  const c = +cs, r = +rs, pan = Number(ps), tilt = Number(ts);
  if (c >= MAP_MAX_COLS || r >= MAP_MAX_ROWS || !Number.isFinite(pan) || !Number.isFinite(tilt) ||
      pan < 0 || pan > 180 || tilt < 0 || tilt > 180) return;
  const cell = { jpeg: frame, pan: Math.round(pan * 10) / 10, tilt: Math.round(tilt * 10) / 10, t: Date.now() };
  roomMap.cells.set(c + ',' + r, cell);
  broadcast('map', { c, r, pan: cell.pan, tilt: cell.tilt, t: cell.t });
}
function mapCellAt(pan, tilt) {                   // the cell nearest a head position
  const m = roomMap;
  const idx = (v, a, b, n) => n < 2 || a === b ? 0 : Math.min(n - 1, Math.max(0, Math.round((v - a) / (b - a) * (n - 1))));
  return idx(pan, m.p0, m.p1, m.cols) + ',' + idx(tilt, m.t0, m.t1, m.rows);
}
function mapActivity(kind) {
  if (!MAP_HEAT_KINDS.has(kind)) return;
  const key = mapHint || (head && roomMap.cols ? mapCellAt(head.pan, head.tilt) : null);
  if (!key) return;
  const a = roomMap.activity.get(key) || { n: 0, last: 0 };
  a.n += 1;
  a.last = Date.now();
  roomMap.activity.set(key, a);
}
setInterval(() => {                               // activity fades: ×0.9 an hour
  for (const [k, a] of roomMap.activity) { a.n *= 0.9; if (a.n < 0.05) roomMap.activity.delete(k); }
}, 3600e3).unref();
function mapJson() {
  const keys = new Set([...roomMap.cells.keys(), ...roomMap.activity.keys(), ...roomMap.changed.keys()]);
  const cells = [...keys].map((k) => {
    const [c, r] = k.split(',').map(Number), cell = roomMap.cells.get(k), a = roomMap.activity.get(k);
    return { c, r, pan: cell ? cell.pan : null, tilt: cell ? cell.tilt : null, t: cell ? cell.t : null,
             act: a ? Math.round(a.n * 100) / 100 : 0, changedAt: roomMap.changed.get(k) || null };
  }).sort((x, y) => x.r - y.r || x.c - y.c);
  return { ...(mapGeom() || { cols: null, rows: null, p0: null, p1: null, t0: null, t1: null }), cells };
}

// ── Event gallery ───────────────────────────────────────────────────────
// A person, a stranger or a family member arriving keeps a snapshot — the
// frame at that moment plus up to two more over the next 2 s (whoever it was
// usually walks further into view). Kept in memory: the last 60 events,
// ~3 KB a frame; a relay restart (redeploy) clears them.
const GALLERY_MAX = 60;
const gallery = [];               // newest first: {id, t, kind, text, frames: [Buffer], ai}
let galleryId = 0;
const lastShot = {};              // kind → time, so a burst of detections is one event
function galleryItem(e) { return { id: e.id, t: e.t, kind: e.kind, text: e.text, ai: e.ai, n: e.frames.length }; }
function captureEvent(kind, text) {
  const now = Date.now();
  if (!latestFrame || now - latestAt > OFFLINE_AFTER_MS) return;
  if (kind === 'person' && now - (lastShot.person || 0) < 20000) return;
  lastShot[kind] = now;
  const ev = { id: ++galleryId, t: now, kind, text, frames: [latestFrame], ai: null };
  gallery.unshift(ev);
  if (gallery.length > GALLERY_MAX) gallery.pop();
  broadcast('gallery', galleryItem(ev));
  let tries = 0;
  const more = () => {
    if (latestFrame && latestFrame !== ev.frames[ev.frames.length - 1]) ev.frames.push(latestFrame);
    if (ev.frames.length < 3 && ++tries < 4) setTimeout(more, 700);
    else broadcast('gallery', galleryItem(ev));
  };
  setTimeout(more, 700);
}

// The display keeps a copy of the history on its SD card: it says what it
// last saved (X-Log-Since / X-Shot-Since, ms) and gets what's newer, oldest
// first, a few at a time. No headers (no card) = nothing extra in the reply.
// ── SD card browser ─────────────────────────────────────────────────────
// The page asks for a folder listing or a file; the request rides out on the
// display's next poll reply (sdreq, up to 3 at a time), and the display POSTs
// the result to /sdres. Each page request waits up to 20 s. Photos (.jpg)
// don't change once written, so they're cached here.
const SD_MAX_BYTES = 2 * 1024 * 1024;
const SD_WAIT_MS = 20000;
let sdNextId = 0;
const sdPending = [];             // {id, op, path, at, sentAt, waiters: [resolve]}
const sdJpgCache = new Map();     // path → Buffer (newest last; 300 / 20 MB kept)
const SD_CACHE_MAX_BYTES = 20 * 1024 * 1024;
let sdJpgCacheBytes = 0;
let sdInfo = null;                // {ok, mb, free} from the display's X-SD header

function noteSd(req) {
  const [ok, mb, free] = String(req.headers['x-sd'] || '').split(',').map(Number);
  if (Number.isFinite(ok)) sdInfo = { ok: ok === 1, mb: mb || 0, free: free || 0, t: Date.now() };
}

function sdPathOk(p) {
  return typeof p === 'string' && p.startsWith('/') && p.length < 120 && !p.includes('..') && !/[\\\x00-\x1f]/.test(p);
}

function sdRequest(op, path) {
  return new Promise((resolve) => {
    let r = sdPending.find((x) => x.op === op && x.path === path);
    if (!r) { r = { id: ++sdNextId, op, path, at: Date.now(), sentAt: 0, waiters: [] }; sdPending.push(r); }
    const done = (v) => { clearTimeout(timer); resolve(v); };
    const timer = setTimeout(() => {
      r.waiters = r.waiters.filter((w) => w !== done);
      resolve({ ok: false, status: 504, body: Buffer.from('AYA did not answer in time (is she online?)') });
    }, SD_WAIT_MS);
    r.waiters.push(done);
  });
}

setInterval(() => {                               // drop requests nobody waits for any more
  for (let i = sdPending.length - 1; i >= 0; i--)
    if (!sdPending[i].waiters.length && Date.now() - sdPending[i].at > SD_WAIT_MS) sdPending.splice(i, 1);
}, 5000);

function handleSdRes(req, res, url) {
  const id = Number(url.searchParams.get('id'));
  const chunks = [];
  let size = 0;
  req.on('data', (c) => { size += c.length; if (size > SD_MAX_BYTES) { req.destroy(); return; } chunks.push(c); });
  req.on('end', () => {
    const i = sdPending.findIndex((x) => x.id === id);
    send(res, 200, 'text/plain', 'ok');
    if (i < 0) return;
    const r = sdPending.splice(i, 1)[0];
    const body = Buffer.concat(chunks);
    const ok = req.headers['x-sd-status'] === 'ok';
    if (ok && r.op === 'get' && /\.jpe?g$/i.test(r.path)) {
      if (sdJpgCache.has(r.path)) { sdJpgCacheBytes -= sdJpgCache.get(r.path).length; sdJpgCache.delete(r.path); }
      sdJpgCache.set(r.path, body);
      sdJpgCacheBytes += body.length;
      while (sdJpgCache.size && (sdJpgCache.size > 300 || sdJpgCacheBytes > SD_CACHE_MAX_BYTES)) {
        const k = sdJpgCache.keys().next().value;  // oldest first
        sdJpgCacheBytes -= sdJpgCache.get(k).length;
        sdJpgCache.delete(k);
      }
    }
    for (const w of r.waiters) w({ ok, status: ok ? 200 : 404, body });
  });
}

function sdType(path) {
  return /\.jpe?g$/i.test(path) ? 'image/jpeg' : /\.(jsonl?|txt|csv|log)$/i.test(path) ? 'text/plain; charset=utf-8' : 'application/octet-stream';
}

async function handleSdGet(req, res, url, op) {
  const path = url.searchParams.get('path') || '/';
  if (!sdPathOk(path)) return send(res, 400, 'text/plain', 'bad path');
  if (op === 'get' && sdJpgCache.has(path)) return send(res, 200, 'image/jpeg', sdJpgCache.get(path), { 'Cache-Control': 'private, max-age=86400' });
  if (!seen.display || Date.now() - seen.display > 10000) return send(res, 503, 'text/plain', 'AYA is offline');
  const r = await sdRequest(op, path);
  if (!r.ok) return send(res, r.status, 'text/plain', r.body.toString('utf8').slice(0, 200));
  if (op === 'ls') return send(res, 200, 'application/json', r.body, { 'Cache-Control': 'no-store' });
  const extra = { 'Cache-Control': /\.jpe?g$/i.test(path) ? 'private, max-age=86400' : 'no-store' };
  if (url.searchParams.get('dl') === '1') {
    const name = path.split('/').pop() || 'file';
    const ascii = name.replace(/[^\x20-\x7e]/g, '_').replace(/["\\;]/g, '_');
    extra['Content-Disposition'] = `attachment; filename="${ascii}"; filename*=UTF-8''${encodeURIComponent(name)}`;
  }
  return send(res, 200, sdType(path), r.body, extra);
}

function deviceReply(req) {
  const out = publicDisplay();
  const due = sdPending.filter((r) => r.waiters.length && (!r.sentAt || Date.now() - r.sentAt > 8000)).slice(0, 3);
  if (due.length) {                               // SD card requests from the page
    for (const r of due) r.sentAt = Date.now();
    out.sdreq = due.map((r) => ({ id: r.id, op: r.op, path: r.path }));
  }
  const logSince = Number(req.headers['x-log-since']), shotSince = Number(req.headers['x-shot-since']);
  if (Number.isFinite(logSince) || Number.isFinite(shotSince)) out.now = Date.now();
  if (Number.isFinite(logSince))
    out.log = activity.filter((e) => e.t > logSince).reverse().slice(0, 10).map((e) => ({ t: e.t, kind: e.kind, text: e.text }));
  if (Number.isFinite(shotSince))
    out.shots = gallery.filter((e) => e.t > shotSince).reverse().slice(0, 5).map((e) => ({ t: e.t, kind: e.kind, text: e.text }));
  const ack = headAck(req), hq = headq.filter((e) => e.id > ack);   // head commands not yet applied
  if (hq.length) out.headq = hq.map((e) => ({ id: e.id, op: e.op, a: e.a, b: e.b, name: e.name }));
  const sign = pendingSign();                     // a new hand sign from the tracker (each once)
  if (sign) out.sign = sign;
  return out;
}

// The display says whether nothing is happening (X-Idle: 0|1). /status and
// /snapshot (X-AYA-Idle) pass it on so the laptop's tracker can slow down.
const deviceIdle = { idle: false, t: 0 };
function noteIdle(req) {
  const v = req.headers['x-idle'];
  if (v === '0' || v === '1') { deviceIdle.idle = v === '1'; deviceIdle.t = Date.now(); }
}
function isIdle() { return deviceIdle.idle && Date.now() - deviceIdle.t < 10000; }

function handleDisplayPost(req, res) {
  const chunks = [];
  let size = 0;
  req.on('data', (c) => { size += c.length; if (size > 4096) { req.destroy(); return; } chunks.push(c); });
  req.on('end', () => {
    const buf = Buffer.concat(chunks);
    seen.display = Date.now();
    deviceKick = false;                            // it's polling now
    noteMapGeom(req);                              // the grid and the head first: events below land on the
    noteHead(req);                                 // map cell the head points at now (and the head event carries the grid)
    notePerson(req);
    noteAf(req);
    noteScreen(req);
    noteBoot(req);
    noteSd(req);
    noteDeviceEvent(req);
    noteIdle(req);
    noteHeadAck(req);
    if (buf.length === 1024) {
      const out = Buffer.alloc(1024);
      for (let y = 0; y < 64; y++)
        for (let x = 0; x < 128; x++)
          if (buf[(y >> 3) * 128 + x] & (1 << (y & 7))) out[y * 16 + (x >> 3)] |= 0x80 >> (x & 7);
      const b64 = out.toString('base64');
      oledFrame = b64;
      broadcast('oled', { f: b64 });               // every poll (~2 s), so the page knows it's live
    }
    send(res, 200, 'application/json', JSON.stringify(deviceReply(req)));
  });
}

function handleEvents(req, res) {
  if (metaSubscribers.size >= SSE_MAX_SUBS) return send(res, 503, 'text/plain', 'too many viewers', { 'Retry-After': '30' });
  res.writeHead(200, {
    'Content-Type': 'text/event-stream',
    'Cache-Control': 'no-store',
    'X-Accel-Buffering': 'no',
    Connection: 'keep-alive',
  });
  res.write(': connected\n\n');          // flush headers now — Node holds them until the first write
  if (latestMeta) res.write(`data: ${latestMeta}\n\n`);
  for (const e of [...activity].reverse()) res.write(`event: log\ndata: ${JSON.stringify(e)}\n\n`);
  res.write(`event: display\ndata: ${JSON.stringify(publicDisplay())}\n\n`);
  if (lastAf) res.write(`event: af\ndata: ${JSON.stringify(lastAf)}\n\n`);
  if (head) res.write(`event: head\ndata: ${JSON.stringify(head)}\n\n`);
  if (oledFrame && Date.now() - seen.display < 10000) res.write(`event: oled\ndata: ${JSON.stringify({ f: oledFrame })}\n\n`);
  metaSubscribers.add(res);
  const ping = setInterval(() => res.write(': ping\n\n'), 15000);   // keep proxies from idling it out
  res.on('close', () => { clearInterval(ping); metaSubscribers.delete(res); sseStuckSince.delete(res); });
}

function acceptFrame(frame) {
  if (frame.length < 4 || frame[0] !== 0xff || frame[1] !== 0xd8) return false;
  latestFrame = frame;
  latestSeq++;
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
  // res (not req): req 'close' fires once the request body is consumed, not on disconnect
  const drop = () => streamViewers.delete(res);
  res.on('close', drop);
  res.on('error', drop);
}

function ages() {
  const a = {};
  for (const k in seen) a[k + '_age'] = seen[k] ? Date.now() - seen[k] : null;
  return a;
}

function status() {
  const age = latestAt ? Date.now() - latestAt : null;
  return { online: age !== null && age < OFFLINE_AFTER_MS, lastFrameAgeMs: age, viewers: viewerCount(),
           fps: Math.round(fps() * 10) / 10, width: frameSize && frameSize.w, height: frameSize && frameSize.h,
           idle: isIdle(), head, map: mapGeom(), ...ages(), vision: { on: !!HF_TOKEN, used: (visionDay(), vision.used), limit: VISION_DAILY, err: vision.err } };
}

const server = http.createServer((req, res) => {
  const url = new URL(req.url, 'http://x');
  const key = url.searchParams.get('key');
  const device = keyMatches(key, VIEW_KEY);       // the display board's poll
  const authed = sessionOk(req);                  // a logged-in browser

  if (req.method === 'POST' && url.pathname === '/push') return handlePush(req, res, url);
  if (req.method === 'POST' && url.pathname === '/meta') return handleMeta(req, res);
  if (req.method === 'POST' && url.pathname === '/cmd') return handleCmd(req, res);
  if (req.method === 'POST' && url.pathname === '/login') return handleLogin(req, res);
  if (req.method === 'POST' && url.pathname === '/ask') return handleAsk(req, res);
  if (req.method === 'POST' && url.pathname === '/sdres') {   // the display answering an SD request
    if (!device) return send(res, 401, 'text/plain', 'bad key');
    return handleSdRes(req, res, url);
  }
  if (req.method === 'POST' && url.pathname === '/display') {
    if (!device) return send(res, 401, 'text/plain', 'bad key');
    return handleDisplayPost(req, res);
  }
  if (req.method !== 'GET' && req.method !== 'HEAD') return send(res, 405, 'text/plain', 'method not allowed');

  // ── BEGIN Next.js app ──────────────────────────────────────────────────
  // The dashboard in web/ is a static export copied to next/ (next to this
  // file: `cd web && npm run export`). When that directory exists, `/` serves
  // its index.html (the app shows its own login and calls POST /login), other
  // paths serve the matching file under next/ (immutable cache for /_next/
  // static/), and the old single-page dashboard stays at /classic. API routes
  // always win: a path whose first segment is one of ours never reaches the
  // files. Without next/, everything below behaves as before.
  {
    const fs = require('fs'), path = require('path');
    const NEXT_DIR = path.join(__dirname, 'next');
    const API_SEGMENTS = new Set(['healthz', 'manifest.webmanifest', 'icon.svg', 'logout', 'stream', 'snapshot', 'events', 'display',
      'status', 'sd', 'gallery', 'panos', 'map.json', 'map', 'health', 'pano', 'push', 'meta', 'cmd', 'login', 'ask', 'sdres', 'classic']);
    const NEXT_TYPES = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8',
      '.json': 'application/json', '.txt': 'text/plain; charset=utf-8', '.svg': 'image/svg+xml', '.png': 'image/png', '.jpg': 'image/jpeg',
      '.ico': 'image/x-icon', '.woff2': 'font/woff2', '.woff': 'font/woff', '.webmanifest': 'application/manifest+json', '.map': 'application/json' };
    const nextFile = (rel) => {                       // the file under next/ for a request path, or null
      if (!/^\/[A-Za-z0-9._~\-\/%]*$/.test(rel) || rel.includes('..') || rel.includes('//')) return null;
      let dec;
      try { dec = decodeURIComponent(rel); } catch { return null; }
      if (dec.includes('..') || dec.includes('\0') || dec.includes('\\')) return null;
      const abs = path.resolve(NEXT_DIR, '.' + dec);
      if (abs !== NEXT_DIR && !abs.startsWith(NEXT_DIR + path.sep)) return null;
      return abs;
    };
    const nextServe = (abs, type, cache) => {
      fs.readFile(abs, (err, data) => {
        if (err) return send(res, 404, 'text/plain', 'not found');
        send(res, 200, type, data, cache);
      });
    };
    const nextIndex = nextFile('/index.html');
    const hasNext = nextIndex && fs.existsSync(nextIndex);
    if (hasNext && url.pathname === '/classic')       // the old page, as / used to be
      return send(res, authed ? 200 : 401, 'text/html; charset=utf-8', authed ? viewerPage() : loginPage(''), { 'Referrer-Policy': 'no-referrer' });
    if (hasNext && url.pathname === '/')
      return nextServe(nextIndex, 'text/html; charset=utf-8', { 'Cache-Control': 'no-store', 'Referrer-Policy': 'no-referrer' });
    if (hasNext && !API_SEGMENTS.has(url.pathname.split('/')[1] || '')) {
      const abs = nextFile(url.pathname);
      let st = null;
      try { st = abs && fs.statSync(abs); } catch { st = null; }
      if (st && st.isFile()) {
        const ext = path.extname(abs).toLowerCase();
        const immutable = url.pathname.startsWith('/_next/static/');
        return nextServe(abs, NEXT_TYPES[ext] || 'application/octet-stream',
          { 'Cache-Control': immutable ? 'public, max-age=31536000, immutable' : 'no-cache', 'Referrer-Policy': 'no-referrer' });
      }
    }
  }
  // ── END Next.js app ────────────────────────────────────────────────────

  switch (url.pathname) {
    case '/healthz':
      return send(res, 200, 'text/plain', 'ok');
    case '/manifest.webmanifest':                  // "Add to home screen": opens straight into the viewer
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return send(res, 200, 'application/manifest+json', JSON.stringify({
        name: 'AYA Cam', short_name: 'AYA', display: 'standalone', background_color: '#07090c', theme_color: '#07090c',
        start_url: '/', scope: '/',
        icons: [{ src: '/icon.svg', sizes: 'any', type: 'image/svg+xml', purpose: 'any' }] }));
    case '/icon.svg':
      return send(res, 200, 'image/svg+xml', ICON_SVG, { 'Cache-Control': 'public, max-age=86400' });
    case '/':
      return send(res, authed ? 200 : 401, 'text/html; charset=utf-8', authed ? viewerPage() : loginPage(''),
        { 'Referrer-Policy': 'no-referrer' });
    case '/logout':
      res.writeHead(303, { Location: '/', 'Cache-Control': 'no-store',
        'Set-Cookie': 'aya_session=; Path=/; Max-Age=0; HttpOnly; Secure; SameSite=Strict' });
      return res.end();
    case '/stream':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return handleStream(req, res);
    case '/snapshot':                              // the page, or the laptop's face tracker (X-Cam-Key)
      if (!authed && !keyMatches(req.headers['x-cam-key'], CAM_KEY)) return send(res, 401, 'text/plain', 'bad key');
      if (authed) lastPollAt = Date.now();         // a person on the page (the tracker isn't a viewer:
                                                   // the display slows its uploads when nobody watches)
      if (!latestFrame) return send(res, 503, 'text/plain', 'no frame yet');
      {
        const etag = '"f' + latestSeq + '"', idle = isIdle() ? '1' : '0';
        if (req.headers['if-none-match'] === etag) {
          res.writeHead(304, { ETag: etag, 'X-AYA-Idle': idle, 'Cache-Control': 'no-cache' });
          return res.end();
        }
        return send(res, 200, 'image/jpeg', latestFrame, { ETag: etag, 'X-AYA-Idle': idle, 'Cache-Control': 'no-cache' });
      }
    case '/events':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return handleEvents(req, res);
    case '/display':
      if (!device) return send(res, 401, 'text/plain', 'bad key');
      seen.display = Date.now();                   // only the display board polls this
      return send(res, 200, 'application/json', JSON.stringify(publicDisplay()));
    case '/status':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return send(res, 200, 'application/json', JSON.stringify(status()));
    case '/sd/ls':
    case '/sd/get':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return handleSdGet(req, res, url, url.pathname === '/sd/ls' ? 'ls' : 'get');
    case '/sd/info':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return send(res, 200, 'application/json', JSON.stringify(sdInfo), { 'Cache-Control': 'no-store' });
    case '/gallery':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return send(res, 200, 'application/json', JSON.stringify(gallery.map(galleryItem)), { 'Cache-Control': 'no-store' });
    case '/panos':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return send(res, 200, 'application/json', JSON.stringify(panos.slice().reverse().map(panoItem)), { 'Cache-Control': 'no-store' });
    case '/map.json':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return send(res, 200, 'application/json', JSON.stringify(mapJson()), { 'Cache-Control': 'no-store' });
    case '/health':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return send(res, 200, 'application/json', JSON.stringify({ every: HEALTH_EVERY_MS, samples: healthSamples }));
    default: {
      const g = /^\/gallery\/(\d+)\/(\d)\.jpg$/.exec(url.pathname);   // one snapshot of an event
      if (g) {
        if (!authed) return send(res, 401, 'text/plain', 'bad key');
        const ev = gallery.find((e) => e.id === +g[1]);
        const f = ev && ev.frames[+g[2]];
        if (!f) return send(res, 404, 'text/plain', 'gone');
        return send(res, 200, 'image/jpeg', f, { 'Cache-Control': 'private, max-age=86400' });
      }
      const pm = /^\/pano\/(\d{1,12})\/(\d{1,2})\.jpg$/.exec(url.pathname);   // one panorama frame
      if (pm) {
        if (!authed) return send(res, 401, 'text/plain', 'bad key');
        const p = panos.find((x) => x.id === +pm[1]);
        const f = p && p.frames[+pm[2]];
        if (!f) return send(res, 404, 'text/plain', 'not here');
        return send(res, 200, 'image/jpeg', f, { 'Cache-Control': 'private, max-age=3600' });
      }
      const mm = /^\/map\/(\d{1,2})_(\d{1,2})\.jpg$/.exec(url.pathname);   // one cell of the room map
      if (mm) {
        if (!authed) return send(res, 401, 'text/plain', 'bad key');
        const cell = roomMap.cells.get(+mm[1] + ',' + +mm[2]);
        if (!cell) return send(res, 404, 'text/plain', 'not mapped yet');
        return send(res, 200, 'image/jpeg', cell.jpeg, { 'Cache-Control': 'private, max-age=60' });
      }
      return send(res, 404, 'text/plain', 'not found');
    }
  }
});

// Keep idle HTTP connections longer than Node's 5 s default: the display
// can't reopen its TLS session while its OV7670 runs (no memory), so a
// dropped keep-alive costs it a camera pause.
server.keepAliveTimeout = 65000;
server.headersTimeout = 66000;
server.listen(PORT, () => console.log(`cam relay listening on :${PORT}`));

// One bad request must not take the relay (and every camera viewer) down
process.on('unhandledRejection', (e) => console.error('unhandledRejection:', e));
process.on('uncaughtException', (e) => console.error('uncaughtException:', e));

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
  .live.stale i { background: var(--warn); }
  .stage.stale #feed { opacity: .6; filter: saturate(.5); transition: opacity .4s, filter .4s; }
  .stage.stale .rec i { animation: none; background: var(--warn); }
  @keyframes pulse { 0% { box-shadow: 0 0 0 0 rgba(74,222,128,.55); } 70% { box-shadow: 0 0 0 8px rgba(74,222,128,0); }
                     100% { box-shadow: 0 0 0 0 rgba(74,222,128,0); } }

  .grid { display: grid; grid-template-columns: minmax(0, 1fr) 340px; gap: 16px;
          max-width: 1280px; margin: 0 auto; padding: 0 16px 16px; }
  @media (max-width: 900px) { .grid { grid-template-columns: minmax(0, 1fr); } }

  .stage { position: relative; aspect-ratio: 4 / 3; background: #000; border-radius: var(--radius);
           overflow: hidden; border: 1px solid var(--line); }
  .stage img { position: absolute; inset: 0; width: 100%; height: 100%; object-fit: contain; }
  #overlay { position: absolute; inset: 0; width: 100%; height: 100%; pointer-events: none; }
  .frame { position: absolute; inset: 0; transform-origin: 0 0; transition: transform 1.4s cubic-bezier(.25,.8,.25,1); will-change: transform; }
  .chip.track { color: var(--accent); border-color: rgba(94,234,212,.45); }
  .chip.track i { display: inline-block; width: 6px; height: 6px; border-radius: 50%; background: currentColor; margin-right: 5px; vertical-align: 1px; }
  .chip.scan { color: var(--muted); }
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

  .log { list-style: none; margin: 0; padding: 0; display: grid; gap: 2px; max-height: 340px; overflow-y: auto; }
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
  .btn { background: var(--surface-2); border: 1px solid var(--line); border-radius: 10px; padding: 8px 12px; cursor: pointer; font-size: 13px; }
  .btn.primary { background: var(--accent); color: #04110f; border: 0; font-weight: 700; }
  .btn.danger { color: var(--bad); }
  .health { display: grid; grid-template-columns: repeat(2, 1fr); gap: 6px 12px; margin-top: 12px; font-size: 12px; color: var(--muted); }
  .health b { color: var(--text); font-weight: 600; font-variant-numeric: tabular-nums; }
  .log li.motion i { background: #fb923c; } .log li.privacy i { background: var(--violet); }

  .view-seg { display: flex; flex-wrap: wrap; width: 100%; margin-top: 2px; }
  .view-seg button { flex: 1 1 auto; }
  .emo-grid { display: grid; grid-template-columns: repeat(5, 1fr); gap: 6px; margin-top: 8px; }
  .emo-grid button { background: var(--surface-2); border: 1px solid var(--line); border-radius: 10px; padding: 6px 2px;
                     cursor: pointer; font-size: 11px; color: var(--muted); display: grid; gap: 2px; justify-items: center; }
  .emo-grid button { padding: 9px 4px; font-size: 12.5px; }
  .emo-grid button:hover { border-color: rgba(94,234,212,.4); color: var(--text); }
  .emo-grid button.sent { border-color: var(--accent); color: var(--accent); }
  .msg-box { display: grid; gap: 8px; margin-top: 4px; }
  .msg-box textarea { background: var(--surface-2); color: var(--text); border: 1px solid var(--line); border-radius: 10px;
                      padding: 10px; font: inherit; resize: vertical; min-height: 48px; }
  .msg-box textarea:focus { outline: 2px solid var(--accent); outline-offset: 1px; }
  .msg-row { display: flex; gap: 8px; align-items: center; justify-content: space-between; font-size: 12px; color: var(--muted); }
  .msg-row select { background: var(--surface-2); color: var(--text); border: 1px solid var(--line); border-radius: 8px; padding: 5px; font: inherit; }
  .showing { font-size: 12px; color: var(--accent); min-height: 16px; }
  .log li.message i { background: var(--accent); }
  .sub-h { font-size: 12px; color: var(--muted); text-transform: uppercase; letter-spacing: .08em; margin: 14px 0 4px; }
  .zones { position: absolute; display: grid; grid-template-columns: repeat(16, 1fr); grid-template-rows: repeat(12, 1fr);
           touch-action: none; user-select: none; -webkit-user-select: none; z-index: 2; }
  .zones button { border: 1px solid rgba(94,234,212,.25); background: transparent; padding: 0; cursor: pointer; }
  .zones button.off { background: repeating-linear-gradient(135deg, rgba(248,113,113,.55) 0 5px, rgba(7,9,12,.7) 5px 10px);
                      border-color: rgba(248,113,113,.4); }
  .zone-bar { position: absolute; left: 12px; right: 12px; bottom: 12px; display: flex; flex-wrap: wrap; gap: 8px; z-index: 3;
              align-items: center; justify-content: space-between; padding: 8px 10px; border-radius: 12px;
              background: rgba(7,9,12,.85); border: 1px solid var(--line); font-size: 13px; }
  .zone-bar span { color: var(--muted); }
  .log li.object i { background: #fbbf24; }
  .log li.screen i { background: var(--muted); }
  .log li.unusual i { background: var(--bad); box-shadow: 0 0 6px rgba(248,113,113,.8); } .log li.lights i { background: #fde68a; }
  .tile.unusual .kind { color: var(--bad); }
  .log li.changed i { background: var(--bad); } .tile.changed .kind { color: var(--bad); }
  .gal-seg { margin-bottom: 10px; flex-wrap: wrap; max-width: 100%; }
  .gal { display: grid; grid-template-columns: repeat(auto-fill, minmax(150px, 1fr)); gap: 10px; }
  .gal .slim { grid-column: 1 / -1; }
  .tile { position: relative; padding: 0; border: 1px solid var(--line); border-radius: 10px; overflow: hidden;
          background: var(--surface-2); cursor: pointer; text-align: left; color: var(--text); font: inherit; }
  .tile img { display: block; width: 100%; aspect-ratio: 4 / 3; object-fit: cover; background: #000; }
  .tile .cap { padding: 6px 8px; font-size: 12px; display: grid; gap: 1px; }
  .tile .cap b { font-weight: 600; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .tile .cap span { color: var(--muted); }
  .tile .kind { position: absolute; top: 6px; left: 6px; font-size: 11px; font-weight: 700; padding: 2px 7px;
                border-radius: 999px; background: rgba(7,9,12,.75); }
  .tile.person .kind { color: #fdba74; } .tile.stranger .kind { color: var(--warn); } .tile.known .kind { color: var(--good); }
  .tile .ai-mark { position: absolute; top: 6px; right: 6px; width: 8px; height: 8px; border-radius: 50%; background: #a78bfa; }
  .tile:focus-visible { outline: 2px solid var(--accent); }
  .gal-note { margin-top: 10px; }
  .sd-crumbs { display: flex; flex-wrap: wrap; gap: 4px; align-items: center; margin-bottom: 8px; font-size: 13px; }
  .sd-crumbs button { border: 0; background: var(--surface-2); color: var(--text); padding: 4px 9px; border-radius: 8px; cursor: pointer; font: inherit; }
  .sd-crumbs button:last-child { background: var(--accent-dim); color: var(--accent); }
  .sd-crumbs span { color: var(--muted); }
  .sd-status { margin-bottom: 8px; }
  .sd-list { list-style: none; margin: 0; padding: 0; display: grid; gap: 2px; max-height: 420px; overflow-y: auto; }
  .sd-list li button { width: 100%; display: grid; grid-template-columns: 22px 1fr auto auto; gap: 10px; align-items: center;
                       padding: 8px 10px; border: 0; border-radius: 8px; background: transparent; color: var(--text);
                       cursor: pointer; text-align: left; font: inherit; font-size: 13px; }
  .sd-list li button:hover, .sd-list li button:focus-visible { background: var(--surface-2); outline: none; }
  .sd-list svg { width: 18px; height: 18px; color: var(--muted); }
  .sd-list .dir svg { color: var(--accent); }
  .sd-list .nm { white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .sd-list .sz, .sd-list .dt { color: var(--muted); font-variant-numeric: tabular-nums; font-size: 12px; }
  @media (max-width: 520px) { .sd-list li button { grid-template-columns: 22px 1fr auto; } .sd-list .dt { display: none; } }
  .sd-view { margin-top: 12px; border-top: 1px solid var(--line); padding-top: 12px; }
  .sd-view-head { display: flex; justify-content: space-between; align-items: center; gap: 8px; margin-bottom: 8px; flex-wrap: wrap; }
  .sd-view-head b { word-break: break-all; }
  .sd-view-head a.btn { text-decoration: none; }
  .sd-view img { display: block; width: 100%; max-width: 640px; image-rendering: auto; border-radius: 8px; background: #000; }
  .sd-view pre { margin: 0; max-height: 360px; overflow: auto; font-size: 12px; background: var(--surface-2); padding: 10px; border-radius: 8px; white-space: pre-wrap; }
  .sd-table { width: 100%; border-collapse: collapse; font-size: 13px; }
  .sd-table td { padding: 6px 8px; border-bottom: 1px solid var(--line); vertical-align: top; }
  .sd-table td:first-child { color: var(--muted); white-space: nowrap; font-variant-numeric: tabular-nums; }
  .sd-table td:nth-child(2) { color: var(--muted); white-space: nowrap; }
  .sd-table-wrap { max-height: 380px; overflow: auto; }
  .viewer { border: 1px solid var(--line); border-radius: 14px; padding: 0; background: var(--surface); color: var(--text);
            width: min(640px, calc(100vw - 32px)); }
  .viewer::backdrop { background: rgba(0,0,0,.7); }
  .v-img { position: relative; background: #000; }
  .v-img img { display: block; width: 100%; aspect-ratio: 4 / 3; object-fit: contain; image-rendering: auto; }
  .v-step { position: absolute; bottom: 8px; right: 10px; font-size: 12px; color: #cbd5e1; background: rgba(7,9,12,.7);
            padding: 2px 8px; border-radius: 999px; }
  .v-body { padding: 14px 16px 16px; display: grid; gap: 6px; }
  .v-title { display: flex; align-items: center; gap: 8px; font-size: 15px; }
  .v-title i { width: 9px; height: 9px; border-radius: 50%; background: #fb923c; flex: none; }
  .v-time { color: var(--muted); font-size: 13px; }
  .v-ai { border-left: 3px solid #a78bfa; padding: 6px 10px; background: var(--surface-2); border-radius: 8px; line-height: 1.45; }
  .v-row { display: flex; flex-wrap: wrap; gap: 8px; margin-top: 6px; }
  .v-row .primary { margin-left: auto; }
  .v-row a.btn { text-decoration: none; display: inline-flex; align-items: center; }
  .log li.ai i { background: #a78bfa; box-shadow: 0 0 6px rgba(167,139,250,.7); }
  .ask { display: flex; gap: 8px; }
  .ask input { flex: 1; min-width: 0; background: var(--surface-2); color: var(--text); border: 1px solid var(--line);
    border-radius: 10px; padding: 10px 12px; font: inherit; }
  .ask input:focus { outline: 2px solid var(--accent); outline-offset: 1px; }
  .ask-chips { display: flex; flex-wrap: wrap; gap: 6px; margin-top: 8px; }
  .ask-chips .btn { font-size: 12px; padding: 5px 10px; }
  .ask-a { margin-top: 10px; padding: 10px 12px; border-radius: 10px; background: var(--surface-2);
    border-left: 3px solid #a78bfa; line-height: 1.45; }
  .ask-a.err { border-left-color: var(--bad); color: var(--muted); }
  .ask-a.wait { color: var(--muted); }
  .log li.restart i { background: var(--bad); } .log li.person i { background: #fb923c; box-shadow: 0 0 6px rgba(251,146,60,.8); } .log li.gesture i { background: #f472b6; }

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
  .note { font-size: 11px; color: var(--muted); margin-top: 8px; }

  /* Tabs: the side panel shows one group at a time instead of one long column */
  .tabs { display: flex; gap: 2px; padding: 4px; background: var(--surface); border: 1px solid var(--line);
          border-radius: 12px; position: sticky; top: 0; z-index: 4; }
  .tabs button { flex: 1; border: 0; background: transparent; color: var(--muted); padding: 9px 4px; border-radius: 9px;
                 cursor: pointer; font-size: 13px; font-weight: 600; display: grid; justify-items: center; gap: 1px; }
  .tabs button span { display: grid; place-items: center; }
  .tabs button span svg { width: 18px; height: 18px; }
  .tabs button[aria-selected="true"] { background: var(--accent-dim); color: var(--accent); }
  .pane { display: flex; flex-direction: column; gap: 12px; }
  .side .card { padding: 14px; }
  @media (min-width: 901px) {          /* desktop: the video stays put, only the panel scrolls (if at all) */
    .grid { align-items: start; }
    .video-col { position: sticky; top: 12px; }
    .stage { max-height: calc(100vh - 128px); }
    .side { position: sticky; top: 12px; max-height: calc(100vh - 128px); overflow-y: auto; scrollbar-width: thin; }
  }
  @media (max-width: 900px) { .tabs { top: 0; margin: 0 -16px; border-radius: 0; border-left: 0; border-right: 0; } }
  button:disabled { cursor: not-allowed; }
  .slim { font-size: 13px; color: var(--muted); padding: 6px 0 2px; }
  .hc-empty { font-size: 12px; color: var(--muted); padding: 6px 0 12px; }

  /* System status strip */
  .sys { display: grid; grid-template-columns: repeat(2, 1fr); gap: 8px; }
  .sys.three > div:first-child { grid-column: 1 / -1; }   /* the camera gets the full width */
  .sys div { background: var(--surface-2); border: 1px solid var(--line); border-radius: 12px; padding: 9px 10px;
             display: grid; grid-template-columns: 10px 1fr; column-gap: 8px; align-items: center; font-size: 13px; }
  .sys i { width: 8px; height: 8px; border-radius: 50%; background: var(--muted); grid-row: span 2; }
  .sys .ok i { background: var(--good); box-shadow: 0 0 6px rgba(74,222,128,.7); }
  .sys .warn i { background: var(--warn); } .sys .bad i { background: var(--bad); }
  .sys small { color: var(--muted); font-size: 11px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  /* Toasts instead of alert() boxes */
  .toasts { position: fixed; left: 50%; bottom: 20px; transform: translateX(-50%); display: grid; gap: 8px; z-index: 10;
            pointer-events: none; width: max-content; max-width: calc(100vw - 32px); }
  .toast { padding: 10px 16px; border-radius: 12px; background: var(--surface-2); border: 1px solid var(--line); font-size: 14px;
           box-shadow: 0 8px 24px rgba(0,0,0,.45); animation: tin .25s ease; text-align: center; }
  .toast.ok { border-color: rgba(74,222,128,.45); } .toast.err { border-color: rgba(248,113,113,.55); color: #fecaca; }
  .toast.out { opacity: 0; transform: translateY(6px); transition: opacity .3s, transform .3s; }
  @keyframes tin { from { opacity: 0; transform: translateY(8px); } }
  .kbd { font-size: 11px; color: var(--muted); }
  .kbd b { font-weight: 600; border: 1px solid var(--line); border-radius: 5px; padding: 0 5px; margin: 0 2px; }
  @media (hover: none) { .kbd { display: none; } }

  .foot { max-width: 1280px; margin: 0 auto; padding: 4px 16px 24px; color: var(--muted); font-size: 12px;
          display: flex; justify-content: space-between; gap: 12px; flex-wrap: wrap; }

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

  /* Head (pan-tilt servos) */
  .head-seg { display: flex; width: 100%; }
  .head-seg button { flex: 1 1 0; }
  .head-read { margin: 10px 0 0; font-size: 14px; font-variant-numeric: tabular-nums; }
  .head-read b { font-weight: 600; }
  .head-read small { display: block; color: var(--muted); font-size: 12px; }
  .head-ctl { display: grid; grid-template-columns: minmax(0, 1fr) auto; gap: 14px; align-items: center; margin-top: 10px; }
  .head-pos { position: relative; justify-self: center; width: 100%; max-width: 128px; aspect-ratio: 1; border-radius: 10px;
              border: 1px solid var(--line); overflow: hidden;
              background: linear-gradient(var(--line), var(--line)) 50% 50% / 1px 100% no-repeat,
                          linear-gradient(var(--line), var(--line)) 50% 50% / 100% 1px no-repeat, var(--surface-2); }
  .head-pos i { position: absolute; left: 50%; top: 50%; border-radius: 50%; pointer-events: none; }
  .head-pos .dot { width: 12px; height: 12px; margin: -6px 0 0 -6px; background: var(--accent); z-index: 1;
                   box-shadow: 0 0 0 4px var(--accent-dim), 0 0 10px rgba(94,234,212,.6); transition: left .6s ease, top .6s ease; }
  .head-pos .spot-m { width: 7px; height: 7px; margin: -3.5px 0 0 -3.5px; border: 1.5px solid var(--muted); }
  .head-pos.off .dot { background: var(--muted); box-shadow: none; }
  .head-pos .rest-m { width: 10px; height: 10px; margin: -5px 0 0 -5px; border-radius: 2px; border: 1.5px dashed var(--accent); }
  .head-pos .rest-m[hidden] { display: none; }
  .rest-row { display: flex; gap: 8px; align-items: center; margin-top: 10px; flex-wrap: wrap; }
  .rest-row .step-seg { flex: 1 1 140px; }
  .head-pos .ax { position: absolute; font-size: 9px; color: var(--muted); letter-spacing: .04em; }
  .head-pos .ax.l { left: 4px; bottom: 2px; } .head-pos .ax.r { right: 4px; bottom: 2px; }
  .joy { display: grid; grid-template-columns: repeat(3, 40px); grid-template-rows: repeat(3, 40px); gap: 4px; }
  .joy button { display: grid; place-items: center; padding: 0; border: 1px solid var(--line); border-radius: 10px;
                background: var(--surface-2); color: var(--text); cursor: pointer; }
  .joy button:hover { border-color: rgba(94,234,212,.4); }
  .joy button:active { background: var(--accent-dim); color: var(--accent); }
  .joy button.mid { color: var(--accent); }
  .joy svg { width: 18px; height: 18px; }
  .head-gest { display: grid; grid-template-columns: repeat(4, minmax(0, 1fr)); gap: 6px; }
  .head-gest .btn { padding: 7px 2px; font-size: 12.5px; }
  .spots { display: flex; flex-wrap: wrap; gap: 6px; }
  .spot { display: inline-flex; align-items: center; max-width: 100%; padding: 2px 2px 2px 10px; border-radius: 999px;
          background: var(--surface-2); border: 1px solid var(--line); font-size: 13px; }
  .spot b { font-weight: 600; margin-right: 4px; overflow-wrap: anywhere; }
  .spot button { border: 0; background: transparent; cursor: pointer; border-radius: 999px; padding: 4px 8px; font-size: 12px; color: var(--muted); }
  .spot button:hover { background: var(--accent-dim); color: var(--text); }
  .spot .go { color: var(--accent); font-weight: 600; }
  .spot .del { display: grid; place-items: center; padding: 5px 7px; }
  .spot .del svg { width: 11px; height: 11px; }
  .spot-form { margin-top: 8px; }
  .spot-form .btn { white-space: nowrap; }
  .pano-head { display: flex; align-items: center; justify-content: space-between; gap: 8px; margin-top: 14px; }
  .pano-head .sub-h { margin: 0; }
  .pano-strip { display: flex; gap: 2px; margin-top: 8px; overflow-x: auto; border-radius: 10px; background: #000; scrollbar-width: thin; }
  .pano-strip a, .pano-strip span { flex: none; display: block; height: 84px; aspect-ratio: 4 / 3; }
  .pano-strip img { display: block; width: 100%; height: 100%; object-fit: cover; }
  .pano-strip span { background: var(--surface-2); animation: pwait 1.2s ease-in-out infinite alternate; }
  @keyframes pwait { to { opacity: .45; } }
  .pano-info { font-size: 12px; color: var(--muted); margin-top: 6px; }
  .pano-old { display: flex; flex-wrap: wrap; gap: 6px; margin-top: 8px; }
  .pano-old button { font-size: 12px; padding: 5px 9px; }
  .pano-old button[aria-pressed="true"] { border-color: rgba(94,234,212,.45); color: var(--accent); }
  /* Room map: one picture per patrol stop, row 0 (looking up) at the top */
  .map-scan { display: inline-flex; align-items: center; gap: 6px; padding: 6px 11px; }
  .map-scan svg { width: 15px; height: 15px; }
  .map-wrap { position: relative; }
  .map-grid { display: grid; gap: 3px; }
  .map-tile { position: relative; display: block; min-width: 0; aspect-ratio: 4 / 3; padding: 0; border: 0; border-radius: 5px;
              overflow: hidden; cursor: pointer; background: #000; color: var(--text); font: inherit; }
  .map-tile img { display: block; width: 100%; height: 100%; object-fit: cover; }
  .map-tile.empty { background: repeating-linear-gradient(135deg, var(--surface-2) 0 5px, var(--surface) 5px 10px); }
  .map-tile .heat { position: absolute; inset: 0; background: var(--accent); opacity: 0; pointer-events: none; transition: opacity .6s; }
  .map-tile .cnt { position: absolute; right: 2px; top: 2px; min-width: 14px; padding: 0 3px; border-radius: 999px; line-height: 14px;
                   font-size: 10px; font-weight: 700; text-align: center; color: var(--accent); background: rgba(7,9,12,.82);
                   font-variant-numeric: tabular-nums; pointer-events: none; }
  .map-tile .pill { position: absolute; left: 0; right: 0; bottom: 0; overflow: hidden; text-align: center; white-space: nowrap;
                    line-height: 13px; font-size: 9px; font-weight: 700;
                    color: #fff; background: rgba(220,38,38,.88); pointer-events: none; }
  .map-tile.chg::after { content: ""; position: absolute; inset: 0; border: 2px solid var(--bad); border-radius: inherit; pointer-events: none; }
  .map-tile:hover::before, .map-tile:focus-visible::before { content: ""; position: absolute; inset: 0; z-index: 1;
                    border: 2px solid var(--accent); border-radius: inherit; pointer-events: none; }
  .map-tile:focus-visible { outline: none; }
  .map-marks { position: absolute; inset: 0; pointer-events: none; z-index: 2; }
  .map-marks > span { position: absolute; inset: 0; }
  .map-marks i { position: absolute; transform: translate(-50%, -50%); font-style: normal; }
  .map-head { width: 14px; height: 14px; border-radius: 50%; border: 2px solid var(--accent); background: rgba(7,9,12,.35);
              box-shadow: 0 0 0 2px rgba(7,9,12,.5), 0 0 10px rgba(94,234,212,.75); transition: left .6s ease, top .6s ease; }
  .map-head::before, .map-head::after { content: ""; position: absolute; left: 50%; top: 50%; background: var(--accent); transform: translate(-50%, -50%); }
  .map-head::before { width: 24px; height: 1.5px; } .map-head::after { width: 1.5px; height: 24px; }
  .map-head.off { border-color: var(--muted); box-shadow: 0 0 0 2px rgba(7,9,12,.5); }
  .map-head.off::before, .map-head.off::after { background: var(--muted); }
  .map-spot { width: 7px; height: 7px; border-radius: 50%; border: 1.5px solid #fff; background: rgba(7,9,12,.6); }
  .map-spot b { position: absolute; left: 50%; top: 8px; transform: translateX(-50%); padding: 0 4px; border-radius: 4px; white-space: nowrap;
                font-size: 9.5px; font-weight: 600; line-height: 13px; color: var(--text); background: rgba(7,9,12,.78); }
  .map-rest { width: 9px; height: 9px; border-radius: 2px; border: 1.5px dashed var(--accent); background: rgba(7,9,12,.4); }
  .map-foot { display: flex; flex-wrap: wrap; align-items: center; justify-content: space-between; gap: 6px 10px; margin-top: 8px;
              font-size: 12px; color: var(--muted); }
  .map-foot span { min-width: 0; flex: 1 1 200px; }
  .map-flip { display: inline-flex; align-items: center; gap: 6px; padding: 5px 9px; font-size: 12px; }
  .map-flip svg { width: 14px; height: 14px; }
  .map-flip[aria-pressed="true"] { border-color: rgba(94,234,212,.45); color: var(--accent); }
  .stage.looking { cursor: crosshair; }
  .look-ring { position: absolute; width: 46px; height: 46px; margin: -23px 0 0 -23px; border-radius: 50%; border: 2px solid var(--accent);
               pointer-events: none; z-index: 3; animation: lring .7s ease-out forwards; }
  .look-ring::after { content: ""; position: absolute; left: 50%; top: 50%; width: 6px; height: 6px; margin: -3px 0 0 -3px;
                      border-radius: 50%; background: var(--accent); }
  @keyframes lring { from { transform: scale(.3); opacity: 1; } 60% { opacity: 1; } to { transform: scale(1.5); opacity: 0; } }

  /* Less motion when the system asks for it: no pulsing, blinking, sliding or smooth scrolling */
  @media (prefers-reduced-motion: reduce) {
    html { scroll-behavior: auto; }
    .live.on i, .rec i { animation: none; }
    .frame { transition: none; }
    .log li.new { animation: none; }
    .toast { animation: none; }
    .toast.out { transition: none; }
    .stage.stale #feed { transition: none; }
    .head-pos .dot { transition: none; }
    .pano-strip span { animation: none; }
    .map-head, .map-tile .heat { transition: none; }
    .look-ring { animation: lfade .7s ease-out forwards; }
  }
  @keyframes lfade { to { opacity: 0; } }
`;

const ICON_SVG = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 64 64"><rect width="64" height="64" rx="14" fill="#07090c"/>
  <rect x="9" y="18" width="20" height="26" rx="8" fill="#5eead4"/><rect x="35" y="18" width="20" height="26" rx="8" fill="#5eead4"/>
  <rect x="14" y="23" width="6" height="5" rx="2" fill="#07090c"/><rect x="40" y="23" width="6" height="5" rx="2" fill="#07090c"/></svg>`;

const LOGO = `<svg viewBox="0 0 26 26" fill="#5eead4" aria-hidden="true">
  <rect x="3" y="7" width="8" height="10" rx="3"/><rect x="15" y="7" width="8" height="10" rx="3"/>
  <rect x="5" y="9" width="2.5" height="2" rx="1" fill="#07090c"/><rect x="17" y="9" width="2.5" height="2" rx="1" fill="#07090c"/></svg>`;

function loginPage(error) {
  return `<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1"><meta name="theme-color" content="#07090c">
<title>AYA Cam · Sign in</title><style>${STYLE}</style></head><body>
<div class="login"><form method="post" action="/login">
  <div class="brand"><div class="logo">${LOGO}</div><div><div class="name">AYA</div><div class="tag">Home camera</div></div></div>
  <h1>Sign in</h1>
  <p>Private system. Enter the access key to continue.</p>
  ${error ? `<p class="err">${error}</p>` : ''}
  <input name="key" type="password" placeholder="Access key" autocomplete="current-password" required autofocus aria-label="Access key">
  <button type="submit">Continue</button>
</form></div></body></html>`;
}

function viewerPage() {
  return `<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="theme-color" content="#07090c"><title>AYA Cam</title>
<link rel="manifest" id="manifest-link"><link rel="icon" href="/icon.svg"><link rel="apple-touch-icon" href="/icon.svg">
<meta name="apple-mobile-web-app-capable" content="yes"><meta name="mobile-web-app-capable" content="yes">
<style>${STYLE}</style></head><body>
<header class="top">
  <div class="brand"><div class="logo">${LOGO}</div><div><div class="name">AYA</div><div class="tag">Home camera</div></div></div>
  <div class="top-right"><span class="clock" id="clock"></span><span class="live" id="live"><i></i><span id="live-text">Connecting</span></span></div>
</header>

<main class="grid">
  <section class="video-col" aria-label="Live video">
    <div class="stage" id="stage">
      <div class="frame" id="frame"><img id="feed" alt="Live camera feed">
        <canvas id="overlay" aria-hidden="true"></canvas></div>
      <div class="hud tl"><span class="rec"><i></i>LIVE</span><span class="chip" id="hud-time"></span><span class="chip" id="hud-af" hidden></span></div>
      <div class="hud tr"><span class="chip" id="hud-res">—</span><span class="chip" id="hud-fps">— fps</span></div>
      <div class="offline" id="offline" hidden>
        <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.6" aria-hidden="true">
          <path d="M3 3l18 18M10.6 6H15a2 2 0 0 1 2 2v2l4-3v10M17 17H5a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2"/></svg>
        <b>Camera offline</b><span id="offline-text">Waiting for the camera…</span>
      </div>
      <div class="g-pop" id="g-pop" hidden aria-live="polite"><i class="ring"></i><i class="ring"></i>
        <span class="e" id="g-emoji"></span><span class="t" id="g-text"></span></div>
      <div class="zones" id="zones" hidden aria-label="Ignore zones: tap or drag over areas AYA should not watch"></div>
      <div class="zone-bar" id="zone-bar" hidden>
        <span id="zone-info">Tap or drag over areas to ignore</span>
        <span><button class="btn" id="zone-all">Watch all</button> <button class="btn" id="zone-cancel">Cancel</button>
          <button class="btn primary" id="zone-save">Save</button></span>
      </div>
      <div class="controls" id="stage-controls">
        <button class="icon" id="btn-look" aria-pressed="false" title="Click to look: the head turns to where you click" aria-label="Toggle click to look">
          <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" aria-hidden="true">
            <circle cx="12" cy="12" r="7"/><circle cx="12" cy="12" r="1.2" fill="currentColor"/><path d="M12 2v4M12 18v4M2 12h4M18 12h4"/></svg></button>
        <button class="icon" id="btn-af" aria-pressed="true" title="Auto-framing (follow like the OLED)" aria-label="Toggle auto-framing">
          <svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" aria-hidden="true">
            <path d="M4 8V5a1 1 0 0 1 1-1h3M16 4h3a1 1 0 0 1 1 1v3M20 16v3a1 1 0 0 1-1 1h-3M8 20H5a1 1 0 0 1-1-1v-3"/>
            <circle cx="12" cy="12" r="3"/><path d="M12 7v2M12 15v2M7 12h2M15 12h2"/></svg></button>
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
    <nav class="tabs" role="tablist" aria-label="Panels">
      <button role="tab" id="tab-home" aria-controls="pane-home" data-tab="home" aria-selected="true"><span><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="3" y="3" width="7" height="9" rx="1.5"/><rect x="14" y="3" width="7" height="5" rx="1.5"/><rect x="14" y="12" width="7" height="9" rx="1.5"/><rect x="3" y="16" width="7" height="5" rx="1.5"/></svg></span>Home</button>
      <button role="tab" id="tab-display" aria-controls="pane-display" data-tab="display" aria-selected="false"><span><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="2" y="4" width="20" height="13" rx="2"/><path d="M8 21h8M12 17v4"/></svg></span>Display</button>
      <button role="tab" id="tab-camera" aria-controls="pane-camera" data-tab="camera" aria-selected="false"><span><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M15 10l5-3v10l-5-3z"/><rect x="2" y="6" width="13" height="12" rx="2"/></svg></span>Camera</button>
      <button role="tab" id="tab-events" aria-controls="pane-events" data-tab="events" aria-selected="false"><span><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="3" y="5" width="18" height="14" rx="2"/><circle cx="9" cy="10" r="1.8"/><path d="M21 16l-5-5-9 8"/></svg></span>Events</button>
      <button role="tab" id="tab-health" aria-controls="pane-health" data-tab="health" aria-selected="false"><span><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M3 12h4l3-8 4 16 3-8h4"/></svg></span>Health</button>
    </nav>

    <div class="pane" id="pane-home" data-pane="home" role="tabpanel" aria-labelledby="tab-home">
      <section class="card" aria-label="System">
        <div class="card-head"><h2>System</h2><span class="mood" id="sys-sum">—</span></div>
        <div class="sys three">
          <div id="sys-cam"><i></i><span>Camera</span><small>–</small></div>
          <div id="sys-display"><i></i><span>Display</span><small>–</small></div>
          <div id="sys-tracker"><i></i><span>Face tracker</span><small>–</small></div>
        </div>
      </section>
      <section class="card" aria-label="Activity">
        <div class="card-head"><h2>Activity</h2></div>
        <ol class="log" id="log"><li class="empty">Nothing yet</li></ol>
      </section>
      <section class="card" aria-label="AYA">
        <div class="card-head"><h2>AYA</h2><span class="mood" id="mood">—</span></div>
        <div class="robot-wrap" id="robot-wrap" hidden><canvas id="robot" width="128" height="64" aria-label="AYA's display, live"></canvas></div>
        <div class="slim" id="robot-off">The display's screen shows here while it's online.</div>
        <div class="meters" id="meters" hidden>
          <div class="meter"><span>Energy</span><div class="bar"><span id="m-energy"></span></div><span class="val" id="v-energy">–</span></div>
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

      <section class="card" aria-label="Ask AYA">
        <div class="card-head"><h2>Ask AYA</h2><span class="mood" id="ask-left">—</span></div>
        <form class="ask" id="ask-form">
          <input id="ask-q" maxlength="200" autocomplete="off" placeholder="Is anyone in the room? What's on the table?">
          <button class="btn primary" id="ask-go" type="submit">Ask</button>
        </form>
        <div class="ask-chips"><button class="btn" data-q="">What's happening?</button><button class="btn" data-q="Is anyone there?">Anyone there?</button><button class="btn" data-q="Is the light on?">Light on?</button></div>
        <div class="ask-a" id="ask-a" hidden></div>
      </section>

    </div>

    <div class="pane" id="pane-display" data-pane="display" role="tabpanel" aria-labelledby="tab-display" hidden>
      <section class="card" aria-label="AYA controls">
        <div class="card-head"><h2>Talk to AYA</h2><span class="mood" id="disp-state">—</span></div>
        <div id="aria-controls">
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
            <textarea id="msg" maxlength="120" rows="2" placeholder="Type a message… (e.g. Dinner is ready!)"></textarea>
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
            <button data-e="giggle">Giggle</button><button data-e="wink">Wink</button>
            <button data-e="heart">Love</button><button data-e="surprise">Surprise</button>
            <button data-e="curious">Curious</button><button data-e="think">Think</button>
            <button data-e="shy">Shy</button><button data-e="dizzy">Dizzy</button>
            <button data-e="roll">Eye-roll</button><button data-e="nod">Nod</button>
            <button data-e="squint">Suspicious</button><button data-e="purr">Purr</button>
            <button data-e="yawn">Yawn</button><button data-e="sleep">Sleep</button>
            <button data-e="wake">Wake up</button>
          </div>
        </div>
      </section>
    </div>

    <div class="pane" id="pane-camera" data-pane="camera" role="tabpanel" aria-labelledby="tab-camera" hidden>
      <section class="card" aria-label="Head" id="head-card">
        <div class="card-head"><h2>Head</h2><span class="mood" id="head-state">—</span></div>
        <div class="seg head-seg" id="head-mode" role="group" aria-label="Head mode">
          <button data-m="follow" aria-pressed="false" title="Turns to faces and motion">Follow</button><button data-m="patrol" aria-pressed="false" title="Sweeps the room slowly">Patrol</button><button data-m="hold" aria-pressed="false" title="Stays where you point it">Hold</button>
        </div>
        <div class="head-read"><b id="head-read">Pan – · Tilt –</b><small id="head-sub">Waiting for AYA to report her head</small></div>
        <div class="head-ctl">
          <div class="head-pos" id="head-pos" role="img" aria-label="Head position: pan across, tilt down"><i class="rest-m" id="rest-dot" hidden></i><i class="dot" id="head-dot"></i><span class="ax l">180°</span><span class="ax r">0°</span></div>
          <div class="joy" id="joy" role="group" aria-label="Move the head">
            <span></span><button data-d="up" aria-label="Look up" title="Up 10°"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M6 15l6-6 6 6"/></svg></button><span></span>
            <button data-d="left" aria-label="Look left" title="Left 10°"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M15 6l-6 6 6 6"/></svg></button>
            <button data-d="centre" class="mid" aria-label="Go to the rest position" title="Rest position"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" aria-hidden="true"><circle cx="12" cy="12" r="5"/><circle cx="12" cy="12" r="1" fill="currentColor"/></svg></button>
            <button data-d="right" aria-label="Look right" title="Right 10°"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M9 6l6 6-6 6"/></svg></button>
            <span></span><button data-d="down" aria-label="Look down" title="Down 10°"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M6 9l6 6 6-6"/></svg></button><span></span>
          </div>
        </div>
        <div class="rest-row">
          <div class="seg step-seg" id="joy-step" role="group" aria-label="Joystick step">
            <button data-s="1" aria-pressed="false">1°</button><button data-s="5" aria-pressed="false">5°</button><button data-s="10" aria-pressed="false">10°</button>
          </div>
          <button class="btn" id="rest-save" type="button" title="Use where the head points now as its rest position">Set as rest</button>
        </div>
        <div class="slim" id="rest-info">Rest position: –</div>
        <div class="sub-h">Gestures</div>
        <div class="head-gest" id="head-gest">
          <button class="btn" data-g="nod">Nod</button><button class="btn" data-g="shake">Shake</button><button class="btn" data-g="curious">Curious</button><button class="btn" data-g="excited">Excited</button>
        </div>
        <div class="sub-h">Saved spots</div>
        <div class="spots" id="spots"><span class="slim">No saved spots yet.</span></div>
        <form class="ask spot-form" id="spot-form">
          <input id="spot-name" maxlength="12" autocomplete="off" spellcheck="false" placeholder="door, window, desk" aria-label="Spot name">
          <button class="btn" type="submit">Save current view</button>
        </form>
        <div class="pano-head"><div class="sub-h">Panorama</div><button class="btn" id="pano-go" type="button">Take panorama</button></div>
        <div class="pano-strip" id="pano-strip" hidden></div>
        <div class="pano-info" id="pano-info">No panorama yet. AYA sweeps the room and the pictures appear here.</div>
        <div class="pano-old" id="pano-old"></div>
      </section>
      <section class="card" aria-label="Room map" id="map-card">
        <div class="card-head"><h2>Room map</h2>
          <button class="btn map-scan" id="map-scan" type="button" title="AYA looks at every part of the room once, then goes back to what she was doing"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="3" y="3" width="7" height="7" rx="1.5"/><rect x="14" y="3" width="7" height="7" rx="1.5"/><rect x="3" y="14" width="7" height="7" rx="1.5"/><path d="M14 17.5h7M17.5 14v7"/></svg>Scan room</button></div>
        <div class="map-wrap" id="map-wrap" hidden>
          <div class="map-grid" id="map-grid" role="group" aria-label="Views of the room: tap one to look there"></div>
          <div class="map-marks" id="map-marks" aria-hidden="true"><i class="map-rest" id="map-rest" hidden></i><span id="map-spots"></span><i class="map-head" id="map-head" hidden></i></div>
        </div>
        <div class="slim" id="map-empty">No map yet. Switch the head to Patrol or press Scan room.</div>
        <div class="map-foot" id="map-foot" hidden><span>Brighter = more activity · red = something changed · tap a view to look there</span>
          <button class="btn map-flip" id="map-flip" type="button" aria-pressed="false" title="Mirror the map if it shows the room the wrong way round"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M12 3v18"/><path d="M8 7l-5 5 5 5"/><path d="M16 7l5 5-5 5"/></svg>Flip left-right</button></div>
      </section>
      <section class="card" aria-label="Camera">
        <div class="card-head"><h2>Camera</h2><span class="mood" id="cam-state">—</span></div>
        <div class="slim">The OV7670 on the display board: a picture every few seconds here, live on the OLED.</div>
        <div id="controls">
          <div class="sub-h">Zoom</div>
          <div class="seg view-seg" id="zoom2-seg">
            <button data-v="0">Auto</button><button data-v="10">1×</button><button data-v="15">1.5×</button><button data-v="20">2×</button><button data-v="30">3×</button>
          </div>
          <div class="ctl keep" style="margin-top:8px"><div>Ignore zones<small id="zone-sub">Watching the whole picture</small></div>
            <button class="btn" id="zone-edit">Edit</button></div>
          <div class="ctl keep"><div>Restart system<small>Display + camera, about 20 seconds</small></div><button class="btn danger" id="restart">Restart</button></div>
          <div class="ctl keep"><div>Shut down<small>Screen, camera and WiFi off. Wake AYA by touching her touch sensor (or unplug and replug)</small></div><button class="btn danger" id="shutdown">Shut down</button></div>
          <div class="ctl keep"><div>Session<small>Signed in on this browser for 30 days</small></div><a class="btn" href="/logout">Sign out</a></div>
        </div>
      </section>
    </div>

    <div class="pane" id="pane-events" data-pane="events" role="tabpanel" aria-labelledby="tab-events" hidden>
      <section class="card" aria-label="Events">
        <div class="card-head"><h2>Events</h2><span class="mood" id="gal-count">—</span></div>
        <div class="seg gal-seg" id="gal-seg">
          <button data-k="all" aria-pressed="true">All</button><button data-k="person">People</button>
          <button data-k="stranger">Strangers</button><button data-k="known">Family</button><button data-k="unusual">Unusual</button><button data-k="changed">Changed</button>
        </div>
        <div class="gal" id="gal"><div class="slim">No events yet. Snapshots appear here when AYA detects someone.</div></div>
        <div class="slim gal-note">The last 60 events are kept until the server restarts. Everything is also saved on the SD card below.</div>
      </section>
      <section class="card" aria-label="SD card">
        <div class="card-head"><h2>SD card on AYA</h2><span class="mood" id="sd-info">—</span></div>
        <nav class="sd-crumbs" id="sd-crumbs" aria-label="Folder"></nav>
        <div class="sd-status slim" id="sd-status">Open a folder to browse the card. Each step asks AYA, which takes a few seconds.</div>
        <ul class="sd-list" id="sd-list"></ul>
        <div class="sd-view" id="sd-view" hidden>
          <div class="sd-view-head"><b id="sd-view-name"></b><span><a class="btn" id="sd-dl" download>Download</a> <button class="btn" id="sd-view-close">Close</button></span></div>
          <div id="sd-view-body"></div>
        </div>
      </section>
    </div>
    <dialog class="viewer" id="viewer">
      <div class="v-img"><img id="v-img" alt="Event snapshot"><span class="v-step" id="v-step"></span></div>
      <div class="v-body">
        <div class="v-title"><i id="v-dot"></i><b id="v-text"></b></div>
        <div class="v-time" id="v-time"></div>
        <div class="v-ai" id="v-ai" hidden></div>
        <div class="v-row">
          <button class="btn" id="v-prev" aria-label="Newer event">‹ Newer</button>
          <a class="btn" id="v-dl" download>Download</a>
          <button class="btn" id="v-next" aria-label="Older event">Older ›</button>
          <button class="btn primary" id="v-close">Close</button>
        </div>
      </div>
    </dialog>

    <div class="pane" id="pane-health" data-pane="health" role="tabpanel" aria-labelledby="tab-health" hidden>
      <section class="card" aria-label="Camera health">
        <div class="card-head"><h2>Health</h2>
          <div class="seg" id="h-range"><button data-h="1">1h</button><button data-h="6" aria-pressed="true">6h</button><button data-h="24">24h</button></div></div>
        <div class="h-sum">
          <div>Online<b id="h-online">–</b></div><div>Frames now<b id="h-now">–</b></div><div>Avg fps<b id="h-fps">–</b></div>
        </div>
        <div id="h-charts"></div>
        <div class="note" id="h-note"></div>
      </section>
    </div>
  </aside>
  <div class="h-tip" id="h-tip" hidden></div>
</main>
<footer class="foot"><span>AYA camera (OV7670) · via Render · <span id="viewers">0</span> watching</span>
  <span class="kbd">Keys: <b>1</b>–<b>5</b> tabs · <b>F</b> fullscreen · <b>S</b> snapshot</span></footer>
<div class="toasts" id="toasts" aria-live="polite"></div>

<script>
  // NOTE: this script sits inside a JS template literal in server.js, so every
  // escape is resolved twice. Never write a backslash or a dollar-brace here
  // (use String.fromCharCode(10) for a newline, [.] in regexes). A raw newline
  // inside a string once broke the whole page.
  var q = '';                                        // the login cookie authenticates every request
  var $ = function (id) { return document.getElementById(id); };
  $('manifest-link').href = '/manifest.webmanifest' + q;

  // ── Toasts (instead of alert boxes) ──
  function toast(text, kind) {
    var t = document.createElement('div'); t.className = 'toast ' + (kind || ''); t.textContent = text;
    $('toasts').append(t);
    while ($('toasts').children.length > 3) $('toasts').firstChild.remove();
    setTimeout(function () { t.classList.add('out'); setTimeout(function () { t.remove(); }, 350); }, kind === 'err' ? 4000 : 1800);
  }
  var img = $('feed'), stage = $('stage');

  // ── Video (MJPEG; falls back to polling snapshots) ──
  var polling = false;
  img.onerror = function () {
    if (polling) return;
    polling = true;
    var tick = function () { img.src = '/snapshot' + q + '?t=' + Date.now(); };
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
  // ── Auto-framing: the video zooms/pans to where AYA's OLED is framing ──
  var afOn = true, af = null;
  try { afOn = localStorage.getItem('aya-autoframe') !== '0'; } catch (e) {}
  function applyAf() {
    var fr = $('frame'), chip = $('hud-af');
    $('btn-af').setAttribute('aria-pressed', String(afOn));
    if (!afOn || !af || af.off) { fr.style.transform = 'none'; chip.hidden = true; return; }
    var W = stage.clientWidth, H = stage.clientHeight;
    var nw = img.naturalWidth || 4, nh = img.naturalHeight || 3, k = Math.min(W / nw, H / nh);
    var dw = nw * k, dh = nh * k, ox = (W - dw) / 2, oy = (H - dh) / 2;
    var z = Math.max(1, Math.min(3, af.z || 1));
    var cx = ox + (af.x / 80) * dw, cy = oy + (af.y / 60) * dh;
    var tx = W / 2 - cx * z, ty = H / 2 - cy * z;
    function fit(t, lo, hi) { return lo > hi ? (lo + hi) / 2 : Math.min(hi, Math.max(lo, t)); }   // keep the picture covering the stage
    tx = fit(tx, W - (ox + dw) * z, -ox * z);
    ty = fit(ty, H - (oy + dh) * z, -oy * z);
    fr.style.transform = 'translate(' + tx.toFixed(1) + 'px,' + ty.toFixed(1) + 'px) scale(' + z.toFixed(3) + ')';
    chip.hidden = false;
    chip.className = 'chip ' + (af.t ? 'track' : 'scan');
    chip.innerHTML = af.t ? '<i></i>Tracking' : 'Scanning';
  }
  $('btn-af').onclick = function () {
    afOn = !afOn;
    try { localStorage.setItem('aya-autoframe', afOn ? '1' : '0'); } catch (e) {}
    applyAf();
  };
  window.addEventListener('resize', applyAf);

  var showBoxes = true;
  try { showBoxes = localStorage.getItem('aria-boxes') !== '0'; } catch (e) {}
  var boxBtn = $('btn-overlay');
  boxBtn.setAttribute('aria-pressed', String(showBoxes));
  boxBtn.onclick = function () {
    showBoxes = !showBoxes;
    boxBtn.setAttribute('aria-pressed', String(showBoxes));
    try { localStorage.setItem('aria-boxes', showBoxes ? '1' : '0'); } catch (e) {}
  };

  // ── Tabs (remembered per browser) ──
  function showTab(name) {
    document.querySelectorAll('.tabs button').forEach(function (b) { b.setAttribute('aria-selected', String(b.dataset.tab === name)); });
    document.querySelectorAll('.pane').forEach(function (p) { p.hidden = p.dataset.pane !== name; });
    try { localStorage.setItem('aria-tab', name); } catch (e) {}
    if (name === 'health') { renderHealth(); loadHealth(); }   // charts need a visible width; fresh data on open
    if (name === 'camera') setTimeout(mapLoad, 0);             // after the whole script has run (this runs early on a saved tab)
  }
  document.querySelector('.tabs').addEventListener('click', function (e) {
    var b = e.target.closest('button'); if (b) showTab(b.dataset.tab);
  });
  try { var savedTab = localStorage.getItem('aria-tab'); if (savedTab && document.querySelector('[data-pane="' + savedTab + '"]')) showTab(savedTab); } catch (e) {}

  document.addEventListener('keydown', function (e) {
    if (e.ctrlKey || e.metaKey || e.altKey || /INPUT|TEXTAREA|SELECT/.test(document.activeElement.tagName)) return;
    var tabs = ['home', 'display', 'camera', 'events', 'health'];
    if (e.key >= '1' && e.key <= '5') showTab(tabs[+e.key - 1]);
    else if (e.key === 'f' || e.key === 'F') $('btn-fs').click();
    else if (e.key === 's' || e.key === 'S') { $('btn-snap').click(); toast('Snapshot saved', 'ok'); }
  });

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
      renderSys(s);
      var stale = s.online && s.lastFrameAgeMs > 10000;   // online, but no new picture for a while
      stage.classList.toggle('stale', !!stale);
      if (stale) {
        live.className = 'live stale'; $('live-text').textContent = 'Paused';
        live.title = 'No new picture for ' + ago(s.lastFrameAgeMs);
        off.hidden = true;
        $('cam-state').textContent = 'Paused';
      } else if (s.online) {
        live.title = '';
        live.className = 'live on'; $('live-text').textContent = 'Live';
        off.hidden = true;
        $('hud-fps').textContent = (s.fps || 0).toFixed(1) + ' fps';
        if (s.width) $('hud-res').textContent = s.width + '×' + s.height;
        $('cam-state').textContent = 'Live';
      } else {
        live.className = 'live off'; $('live-text').textContent = 'Offline';
        $('cam-state').textContent = 'Offline';
        off.hidden = false;
        $('offline-text').textContent = s.lastFrameAgeMs === null ? 'Waiting for the camera…'
          : 'Last frame ' + ago(s.lastFrameAgeMs) + ' ago';
      }
    } catch (e) { live.className = 'live off'; $('live-text').textContent = 'Unreachable'; }
  }
  function sysCell(id, cls, text) { var el = $(id); el.className = cls; el.querySelector('small').textContent = text; }
  function renderSys(s) {
    var camOk = s.online;
    sysCell('sys-cam', camOk ? 'ok' : 'bad', camOk ? 'live · ' + (s.width ? s.width + '×' + s.height + ' · ' : '') + 'last frame ' + ago(s.lastFrameAgeMs || 0) + ' ago'
      : s.eye2_age !== null ? 'no frames · ' + ago(s.eye2_age) : 'no frames yet');
    var dispOk = s.display_age !== null && s.display_age < 10000;
    sysCell('sys-display', dispOk ? 'ok' : 'bad', dispOk ? 'online' : s.display_age !== null ? 'offline · ' + ago(s.display_age) : 'not seen');
    if (dispOk !== headLive) { headLive = dispOk; renderHead(); }
    if (s.vision) $('ask-left').textContent = s.vision.on ? (s.vision.limit - s.vision.used) + ' left today' : 'AI not set up';
    var trOk = s.tracker_age !== null && s.tracker_age < 5000;
    sysCell('sys-tracker', trOk ? 'ok' : '', trOk ? 'running' : s.tracker_age !== null ? 'stopped · ' + ago(s.tracker_age) + ' ago' : 'not running');
    var bad = [camOk, dispOk].filter(function (x) { return !x; }).length;
    $('sys-sum').textContent = !bad ? 'All good' : bad + ' offline';
  }
  function ago(ms) {
    var s = Math.round(ms / 1000);
    return s < 60 ? s + 's' : s < 3600 ? Math.round(s / 60) + ' min' : Math.round(s / 3600) + ' h';
  }
  refresh(); setInterval(refresh, 3000);

  // ── Tracker data (faces, ARIA's mood + face) over Server-Sent Events ──
  var EMOJI = { happy: 'Happy', surprise: 'Surprised', sad: 'Sad', angry: 'Annoyed', neutral: '' };
  var EXPR_MOOD = { purr: 'Content', heart: 'Affectionate', yawn: 'Tired', sideeye: 'Sulking',
                    wink: 'Playful', surprise: 'Surprised', think: 'Thinking', curious: 'Curious',
                    squint: 'Suspicious', wake: 'Waking up', nod: 'Acknowledging', giggle: 'Amused',
                    shy: 'Shy', dizzy: 'Dizzy', roll: 'Unimpressed' };
  var meta = null, metaAt = 0, shown = [], handShown = null;
  var es = new EventSource('/events' + q);
  es.onerror = function () { if (es.readyState !== 1) { $('live').className = 'live off'; $('live-text').textContent = 'Reconnecting…'; } };
  var esOpens = 0;
  es.onopen = function () { refresh(); if (esOpens++) { galLoad(); panoLoad(); } };   // a reconnect: fetch events missed meanwhile
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
  es.addEventListener('gallery', function (e) {
    try {
      var ev = JSON.parse(e.data), i = gal.findIndex(function (x) { return x.id === ev.id; });
      if (i >= 0) gal[i] = ev; else { gal.unshift(ev); if (gal.length > 60) gal.pop(); }
      if (!$('viewer').open) galRender();
    } catch (x) {}
  });
  es.addEventListener('af', function (e) { try { af = JSON.parse(e.data); applyAf(); } catch (x) {} });

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
       ['Admin', admin ? f.name + ' present' : 'away']].forEach(function (kv) {
        var d = document.createElement('div'); d.textContent = kv[0] + ' ';
        var b = document.createElement('b'); b.textContent = kv[1]; d.append(b); dt.append(d);
      });
      if (admin) { av.className = 'avatar known admin'; }
    }
    var r = fresh() && meta.robot;
    $('meters').hidden = !r;
    if (r) {
      $('mood').textContent = r.sleeping ? 'Asleep' : EXPR_MOOD[r.expr] ||
        (r.energy < 0.3 ? 'Tired' : r.boredom > 0.5 ? 'Idle' : 'Calm');
      [['energy', r.energy], ['boredom', r.boredom]].forEach(function (m) {
        var v = Math.round((m[1] || 0) * 100);
        $('m-' + m[0]).style.width = v + '%'; $('v-' + m[0]).textContent = v + '%';
      });
    } else {                                   // tracker offline: don't show stale numbers
      $('mood').textContent = '—';
      ['energy', 'boredom'].forEach(function (k) {
        $('m-' + k).style.width = '0'; $('v-' + k).textContent = '–';
      });
    }
  }
  setInterval(render, 1000);

  // ── Activity timeline ──
  function rel(t) {
    var s = Math.round((Date.now() - t) / 1000);
    return s < 45 ? 'just now' : s < 3600 ? Math.round(s / 60) + ' min ago'
      : s < 86400 ? new Date(t).toLocaleTimeString([], { hour: 'numeric', minute: '2-digit' }) : new Date(t).toLocaleDateString();
  }
  setInterval(function () { document.querySelectorAll('#log time[data-t]').forEach(function (x) { x.textContent = rel(+x.dataset.t); }); }, 20000);
  var LOG_MAX = 20, logSeen = new Set(), logSeenOrder = [];
  function addLog(e) {
    var id = e.t + '|' + e.kind + '|' + e.text;   // the server replays its last 30 on every (re)connect
    if (logSeen.has(id)) return;
    logSeen.add(id); logSeenOrder.push(id);
    while (logSeenOrder.length > 100) logSeen.delete(logSeenOrder.shift());
    var list = $('log'), empty = list.querySelector('.empty');
    if (empty) empty.remove();
    var li = document.createElement('li');
    li.className = e.kind + ' new';
    var dot = document.createElement('i');
    var text = document.createElement('span'); text.textContent = e.text;
    var t = document.createElement('time');
    t.dataset.t = e.t; t.title = new Date(e.t).toLocaleString();
    t.textContent = rel(e.t);
    li.append(dot, text, t);
    list.prepend(li);
    while (list.children.length > LOG_MAX) list.lastChild.remove();
  }


  // ── Events: snapshots of people, strangers and family arriving ──
  var gal = [], galKind = 'all', galOpen = -1, galPlay = null;
  var KIND = { person: 'Person', stranger: 'Stranger', known: 'Family', unusual: 'Unusual', changed: 'Changed' };
  function galShown() { return gal.filter(function (e) { return galKind === 'all' || e.kind === galKind; }); }
  function galRender() {
    var list = galShown(), box = $('gal');
    $('gal-count').textContent = gal.length ? gal.length + (gal.length === 1 ? ' event' : ' events') : '—';
    box.textContent = '';
    if (!list.length) {
      var p = document.createElement('div'); p.className = 'slim';
      p.textContent = gal.length ? 'Nothing of this kind yet.' : 'No events yet. Snapshots appear here when AYA detects someone.';
      box.append(p); return;
    }
    list.forEach(function (e, i) {
      var b = document.createElement('button'); b.className = 'tile ' + e.kind; b.type = 'button';
      var img = document.createElement('img'); img.loading = 'lazy'; img.alt = e.text; img.src = '/gallery/' + e.id + '/0.jpg';
      var k = document.createElement('span'); k.className = 'kind'; k.textContent = KIND[e.kind] || e.kind;
      var cap = document.createElement('span'); cap.className = 'cap';
      var t = document.createElement('b'); t.textContent = e.text;
      var w = document.createElement('span'); w.textContent = new Date(e.t).toLocaleString([], { month: 'short', day: 'numeric', hour: 'numeric', minute: '2-digit' });
      cap.append(t, w); b.append(img, k, cap);
      if (e.ai) { var m = document.createElement('i'); m.className = 'ai-mark'; m.title = 'AI description'; b.append(m); }
      b.addEventListener('click', function () { galView(i); });
      box.append(b);
    });
  }
  function galView(i) {
    var list = galShown(); if (!list[i]) return;
    galOpen = i; var e = list[i], f = 0;
    $('v-text').textContent = e.text;
    $('v-time').textContent = new Date(e.t).toLocaleString();
    $('v-ai').hidden = !e.ai; $('v-ai').textContent = e.ai || '';
    $('v-dot').style.background = e.kind === 'stranger' ? 'var(--warn)' : e.kind === 'known' ? 'var(--good)' :
                                   e.kind === 'unusual' || e.kind === 'changed' ? 'var(--bad)' : '#fb923c';
    $('v-prev').disabled = i === 0; $('v-next').disabled = i === list.length - 1;
    function show() {
      $('v-img').src = '/gallery/' + e.id + '/' + f + '.jpg';
      $('v-dl').href = $('v-img').src; $('v-dl').setAttribute('download', 'aya-' + e.kind + '-' + e.id + '-' + (f + 1) + '.jpg');
      $('v-step').textContent = e.n > 1 ? (f + 1) + ' / ' + e.n : '';
    }
    show();
    clearInterval(galPlay);
    if (e.n > 1) galPlay = setInterval(function () { f = (f + 1) % e.n; show(); }, 900);   // the moments, as a loop
    if (!$('viewer').open) $('viewer').showModal();
  }
  $('v-close').addEventListener('click', function () { $('viewer').close(); });
  $('viewer').addEventListener('close', function () { clearInterval(galPlay); galOpen = -1; });
  $('viewer').addEventListener('click', function (e) { if (e.target === $('viewer')) $('viewer').close(); });
  $('v-prev').addEventListener('click', function () { galView(galOpen - 1); });
  $('v-next').addEventListener('click', function () { galView(galOpen + 1); });
  document.addEventListener('keydown', function (e) {
    if (!$('viewer').open) return;
    if (e.key === 'ArrowLeft') galView(galOpen - 1);
    if (e.key === 'ArrowRight') galView(galOpen + 1);
  });
  $('gal-seg').addEventListener('click', function (e) {
    var b = e.target.closest('button'); if (!b) return;
    galKind = b.dataset.k;
    $('gal-seg').querySelectorAll('button').forEach(function (x) { x.setAttribute('aria-pressed', String(x === b)); });
    galRender();
  });
  async function galLoad() {
    try { gal = await (await fetch('/gallery', { cache: 'no-store' })).json(); galRender(); } catch (e) {}
  }
  galLoad();

  // ── SD card browser: listings and files come from AYA via the server ──
  var sdPath = '/', sdBusy = false;
  var ICON = {
    dir: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linejoin="round"><path d="M3 7a2 2 0 0 1 2-2h4l2 2h8a2 2 0 0 1 2 2v8a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2z"/></svg>',
    img: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linejoin="round"><rect x="3" y="5" width="18" height="14" rx="2"/><circle cx="9" cy="10" r="1.6"/><path d="M21 16l-5-5-9 8"/></svg>',
    log: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><path d="M6 3h9l3 3v15H6z"/><path d="M9 10h6M9 14h6M9 18h4"/></svg>',
    file: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linejoin="round"><path d="M6 3h9l3 3v15H6z"/></svg>'
  };
  function sdSize(b) { return b < 1024 ? b + ' B' : b < 1048576 ? (b / 1024).toFixed(1) + ' KB' : (b / 1048576).toFixed(1) + ' MB'; }
  function sdKind(n) { return /[.]jpe?g$/i.test(n) ? 'img' : /[.](jsonl?|txt|log|csv)$/i.test(n) ? 'log' : 'file'; }
  function sdUrl(op, path, dl) { return '/sd/' + op + '?path=' + encodeURIComponent(path) + (dl ? '&dl=1' : ''); }
  function sdJoin(dir, n) { return (dir === '/' ? '' : dir) + '/' + n; }
  function sdCrumbs() {
    var box = $('sd-crumbs'); box.textContent = '';
    var parts = sdPath.split('/').filter(Boolean), acc = '';
    function crumb(label, path) {
      var b = document.createElement('button'); b.type = 'button'; b.textContent = label;
      b.addEventListener('click', function () { sdOpen(path); });
      box.append(b);
    }
    crumb('SD card', '/');
    parts.forEach(function (p) { var sep = document.createElement('span'); sep.textContent = '/'; box.append(sep); acc += '/' + p; crumb(p, acc); });
  }
  async function sdOpen(path) {
    if (sdBusy) return;
    sdBusy = true; sdPath = path; sdCrumbs();
    $('sd-status').textContent = 'Asking AYA for ' + path + ' ...';
    $('sd-list').textContent = '';
    try {
      var r = await fetch(sdUrl('ls', path), { cache: 'no-store' });
      if (!r.ok) { $('sd-status').textContent = 'Could not open: ' + (await r.text()); sdBusy = false; return; }
      var d = await r.json();
      var items = d.entries.slice().sort(function (a, b) { return b.d - a.d || (a.n < b.n ? -1 : 1); });
      if (/^[/]aya[/](log|events)/.test(path)) items.sort(function (a, b) { return b.d - a.d || (a.n < b.n ? 1 : -1); });   // newest first
      $('sd-status').textContent = items.length + (items.length === 1 ? ' item' : ' items') + (d.more ? ' (first 500 shown)' : '');
      items.forEach(function (e) {
        var li = document.createElement('li'), b = document.createElement('button'); b.type = 'button';
        var k = e.d ? 'dir' : sdKind(e.n); b.className = k;
        var ic = document.createElement('span'); ic.innerHTML = ICON[k];
        var nm = document.createElement('span'); nm.className = 'nm'; nm.textContent = e.n;
        var sz = document.createElement('span'); sz.className = 'sz'; sz.textContent = e.d ? '' : sdSize(e.s);
        var dt = document.createElement('span'); dt.className = 'dt'; dt.textContent = e.m && e.m.indexOf('1980') !== 0 ? e.m : '';
        b.append(ic, nm, sz, dt);
        b.addEventListener('click', function () { var p = sdJoin(path, e.n); if (e.d) sdOpen(p); else sdShow(p, e); });
        li.append(b); $('sd-list').append(li);
      });
    } catch (x) { $('sd-status').textContent = 'Could not reach the server.'; }
    sdBusy = false;
  }
  async function sdShow(path, e) {
    var body = $('sd-view-body'), k = sdKind(e.n);
    $('sd-view').hidden = false; $('sd-view-name').textContent = path;
    $('sd-dl').href = sdUrl('get', path, true);
    body.textContent = 'Loading from AYA ...';
    if (k === 'img') {
      var img = new Image(); img.alt = e.n;
      img.onload = function () { body.textContent = ''; body.append(img); };
      img.onerror = function () { body.textContent = 'Could not load this photo from AYA.'; };
      img.src = sdUrl('get', path);
      return;
    }
    if (e.s > 1800000) { body.textContent = 'Too big to show here. Use Download.'; return; }
    try {
      var r = await fetch(sdUrl('get', path), { cache: 'no-store' });
      var text = await r.text();
      if (!r.ok) { body.textContent = 'Could not open: ' + text; return; }
      var lines = text.split(String.fromCharCode(10)).filter(Boolean), rows = [];
      if (/[.]jsonl$/i.test(path)) lines.forEach(function (l) { try { rows.push(JSON.parse(l)); } catch (x) {} });
      body.textContent = '';
      if (rows.length) {                                  // a log or an event index: a table, newest first
        var wrap = document.createElement('div'); wrap.className = 'sd-table-wrap';
        var t = document.createElement('table'); t.className = 'sd-table';
        rows.reverse().forEach(function (o) {
          var tr = document.createElement('tr');
          var a = document.createElement('td'); a.textContent = o.t ? new Date(o.t).toLocaleTimeString([], { hour: 'numeric', minute: '2-digit', second: '2-digit' }) : '';
          var b2 = document.createElement('td'); b2.textContent = o.kind || '';
          var c = document.createElement('td'); c.textContent = (o.text || '') + (o.frames ? '  (' + o.frames + ' photos)' : '');
          tr.append(a, b2, c); t.append(tr);
        });
        wrap.append(t); body.append(wrap);
      } else {
        var pre = document.createElement('pre'); pre.textContent = text.slice(0, 65536); body.append(pre);
      }
    } catch (x) { body.textContent = 'Could not reach the server.'; }
  }
  $('sd-view-close').addEventListener('click', function () { $('sd-view').hidden = true; });
  async function sdInfoLoad() {
    try {
      var i = await (await fetch('/sd/info', { cache: 'no-store' })).json();
      $('sd-info').textContent = !i ? 'AYA has not reported yet' : !i.ok ? 'no card' :
        (i.free ? (i.free / 1024).toFixed(1) + ' GB free of ' : '') + (i.mb / 1024).toFixed(1) + ' GB';
    } catch (x) {}
  }
  sdInfoLoad(); setInterval(sdInfoLoad, 60000);
  sdCrumbs();
  var sdFirst = true;
  document.querySelector('.tabs').addEventListener('click', function (e) {     // open the card the first time Events is shown
    var b = e.target.closest('button'); if (b && b.dataset.tab === 'events' && sdFirst) { sdFirst = false; sdOpen('/aya'); }
  });
  try { if (localStorage.getItem('aria-tab') === 'events') { sdFirst = false; sdOpen('/aya'); } } catch (x) {}

  // ── Ask AYA: one look by the vision model at the current frame ──
  async function ask(q) {
    var a = $('ask-a'), go = $('ask-go');
    a.hidden = false; a.className = 'ask-a wait'; a.textContent = 'Looking…'; go.disabled = true;
    try {
      var r = await fetch('/ask', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ q: q }) });
      var d = await r.json();
      a.className = 'ask-a' + (d.error ? ' err' : ''); a.textContent = d.error || d.text;
      if (typeof d.left === 'number') $('ask-left').textContent = d.left + ' left today';
    } catch (e) { a.className = 'ask-a err'; a.textContent = 'Could not reach AYA.'; }
    go.disabled = false;
  }
  $('ask-form').addEventListener('submit', function (e) { e.preventDefault(); ask($('ask-q').value.trim()); });
  document.querySelectorAll('.ask-chips .btn').forEach(function (b) {
    b.addEventListener('click', function () { $('ask-q').value = b.dataset.q; ask(b.dataset.q); });
  });

  // ── Ignore zones: 16x12 grid over the picture; bit c of row r = ignore ──
  var ZC = 16, ZR = 12, zoneEdit = null, zonePaint = null, zonesEl = $('zones');
  function zonesFromHex(h) {
    var m = [];
    for (var r = 0; r < ZR; r++) { var v = h ? parseInt(h.substr(r * 4, 4), 16) : 0; for (var c = 0; c < ZC; c++) m.push(!!(v & (1 << c))); }
    return m;                                           // true = ignored
  }
  function zonesToHex(m) {
    var out = '';
    for (var r = 0; r < ZR; r++) { var v = 0; for (var c = 0; c < ZC; c++) if (m[r * ZC + c]) v |= 1 << c; out += ('000' + v.toString(16)).slice(-4); }
    return out;
  }
  for (var zi = 0; zi < ZC * ZR; zi++) {
    var zb = document.createElement('button'); zb.type = 'button'; zb.dataset.i = zi;
    zb.setAttribute('aria-label', 'Row ' + (Math.floor(zi / ZC) + 1) + ', column ' + (zi % ZC + 1)); zonesEl.append(zb);
  }
  function placeZones() {                              // over the picture itself (object-fit: contain leaves bars)
    var st = $('stage'), im = $('feed'), W = st.clientWidth, H = st.clientHeight;
    var nw = im.naturalWidth || 4, nh = im.naturalHeight || 3, k = Math.min(W / nw, H / nh);
    zonesEl.style.width = nw * k + 'px'; zonesEl.style.height = nh * k + 'px';
    zonesEl.style.left = (W - nw * k) / 2 + 'px'; zonesEl.style.top = (H - nh * k) / 2 + 'px';
  }
  function drawZones() {
    var n = 0;
    zonesEl.querySelectorAll('button').forEach(function (b, i) { b.classList.toggle('off', zoneEdit[i]); if (zoneEdit[i]) n++; });
    $('zone-info').textContent = n ? n + ' of ' + (ZC * ZR) + ' zones ignored' : 'Tap or drag over areas to ignore';
  }
  function setCell(el) { if (!el || el.parentNode !== zonesEl) return; var i = +el.dataset.i; if (zoneEdit[i] !== zonePaint) { zoneEdit[i] = zonePaint; drawZones(); } }
  zonesEl.addEventListener('pointerdown', function (e) { var b = e.target.closest('button'); if (!b) return; e.preventDefault(); zonePaint = !zoneEdit[+b.dataset.i]; setCell(b); });
  zonesEl.addEventListener('pointermove', function (e) { if (zonePaint !== null) setCell(document.elementFromPoint(e.clientX, e.clientY)); });
  window.addEventListener('pointerup', function () { zonePaint = null; });
  function zoneMode(on) {
    zonesEl.hidden = !on; $('zone-bar').hidden = !on; $('stage-controls').hidden = on;
    if (on) { placeZones(); drawZones(); $('stage').scrollIntoView({ behavior: matchMedia('(prefers-reduced-motion: reduce)').matches ? 'auto' : 'smooth', block: 'center' }); } else zoneEdit = null;
  }
  $('zone-edit').onclick = function () { zoneEdit = zonesFromHex(disp && disp.ignore); zoneMode(true); };
  $('zone-cancel').onclick = function () { zoneMode(false); };
  $('zone-all').onclick = function () { zoneEdit = zoneEdit.map(function () { return false; }); drawZones(); };
  $('zone-save').onclick = async function () {
    if (zoneEdit.every(Boolean)) { toast('Leave at least one zone watched', 'err'); return; }
    var hex = zonesToHex(zoneEdit);
    if (await send('ignore', [hex]) === 202) { if (disp) disp.ignore = hex; renderZoneSub(); zoneMode(false); }
  };
  window.addEventListener('resize', function () { if (zoneEdit) placeZones(); });
  function renderZoneSub() {
    var n = disp && disp.ignore ? zonesFromHex(disp.ignore).filter(Boolean).length : 0;
    $('zone-sub').textContent = n ? 'Ignoring ' + n + ' of ' + (ZC * ZR) + ' zones' : 'Watching the whole picture';
  }

  var SENT = { ignore: 'Ignore zones saved', message: 'Message sent to the display', emotion: 'Sent to the display', view: 'Display updated',
               screen: 'Display switched', restart_all: 'Restarting camera + display…', shutdown: 'Shutting down…', zoom2: 'Camera 2 zoom set',
               head_mode: 'Head mode set', head_look: 'Looking there', head_nudge: 'Moving the head', head_goto: 'Centring the head',
               head_rest_save: 'Rest position saved', head_rest_go: 'Going to the rest position',
               head_spot_save: 'Spot saved', head_spot_go: 'Going to the spot', head_spot_del: 'Spot deleted',
               head_gesture: 'Gesture sent', head_pano: 'Panorama started · pictures appear below',
               head_map: 'Scanning the room'
             };
  async function send(cmd, args, extra, okText) {
    try {
      var body = { cmd: cmd, args: args || [] };
      for (var k in (extra || {})) body[k] = extra[k];
      var r = await fetch('/cmd', { method: 'POST', headers: { 'Content-Type': 'application/json' },
                                    body: JSON.stringify(body) });
      if (r.status === 401) { location.reload(); return 401; }            // signed out: back to the sign-in page
      else if (r.status >= 400) toast('Not accepted: ' + (await r.text()), 'err');
      else toast(okText || SENT[cmd] || 'Sent', 'ok');
      return r.status;
    } catch (e) { toast('Could not reach the server', 'err'); return 0; }
  }
  $('shutdown').onclick = function () {
    if (confirm('Shut AYA down? She stops watching: screen, camera and WiFi go off, and this page cannot wake her. ' +
                'Touch her touch sensor to wake her (or unplug and replug her).')) send('shutdown');
  };
  $('restart').onclick = function () {
    if (confirm('Restart the display and its camera? The picture drops for about 20 seconds.')) send('restart_all');
  };

  // ── Talk to ARIA: display on/off, messages, emotions ──
  var disp = null;
  es.addEventListener('display', function (e) { try { disp = JSON.parse(e.data); renderDisp(); } catch (x) {} });
  function renderDisp() {
    if (!disp) return;
    renderZoneSub();
    $('screen').setAttribute('aria-checked', String(!!disp.screen));
    document.querySelectorAll('#zoom2-seg button').forEach(function (b) {
      b.setAttribute('aria-pressed', String(+b.dataset.v === (disp.zoom2 == null ? 0 : disp.zoom2)));   // Auto unless set
    });
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
  $('zoom2-seg').addEventListener('click', function (e) {
    var b = e.target.closest('button'); if (!b) return;
    if (disp) disp.zoom2 = +b.dataset.v;
    renderDisp();
    send('zoom2', [b.dataset.v]);
  });
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

  // ── Head: the pan-tilt servos (mode, joystick, click to look, spots, gestures, panorama) ──
  var head = null, headLive = false, spotsKey = '';
  var HEAD_STATE = { search: 'Searching', face: 'Following a face', motion: 'Checking motion', hold: 'Holding',
                     inspect: 'Taking a close look', gesture: 'Gesturing', spot: 'At a saved spot', pano: 'Taking a panorama', map: 'Mapping the room', centre: 'Centring', '-': 'Idle' };
  var HEAD_MODE = { follow: 'Follow: turns to faces and motion', patrol: 'Patrol: sweeps the room slowly', hold: 'Hold: stays where you point it' };
  var SVG_X = '<svg viewBox="0 0 12 12" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" aria-hidden="true"><path d="M2 2l8 8M10 2l-8 8"/></svg>';
  es.addEventListener('head', function (e) { try { head = JSON.parse(e.data); renderHead(); } catch (x) {} });
  function pctPan(deg) { return pct(180 - deg); }   // a bigger pan angle looks LEFT: draw it on the left
  function pct(deg) { return Math.max(0, Math.min(100, deg / 180 * 100)).toFixed(1) + '%'; }
  function renderHead() {
    var h = head, box = $('head-pos'), dot = $('head-dot');
    $('head-state').textContent = !h ? '—' : headLive ? 'Live' : 'Offline';
    $('head-mode').querySelectorAll('button').forEach(function (b) { b.setAttribute('aria-pressed', String(!!h && b.dataset.m === h.mode)); });
    $('head-read').textContent = h ? 'Pan ' + Math.round(h.pan) + '° · Tilt ' + Math.round(h.tilt) + '°' +
      (HEAD_STATE[h.state] ? ' · ' + HEAD_STATE[h.state] : '') : 'Pan – · Tilt –';
    $('head-sub').textContent = !h ? 'Waiting for AYA to report her head' : !headLive ? 'Last known position · AYA is offline' : HEAD_MODE[h.mode] || '';
    box.classList.toggle('off', !h || !headLive);
    mapMarks();
    if (h) { dot.style.left = pctPan(h.pan); dot.style.top = pct(h.tilt); }
    var r = h && h.rest, rd = $('rest-dot');
    rd.hidden = !r;
    if (r) { rd.style.left = pctPan(r.pan); rd.style.top = pct(r.tilt); }
    $('rest-info').textContent = r ? 'Rest position: pan ' + Math.round(r.pan) + '° · tilt ' + Math.round(r.tilt) + '° (the middle button goes there)' : 'Rest position: –';
    var spots = h ? h.spots || [] : [], key = JSON.stringify(spots);
    if (key === spotsKey) return;                     // only redraw the spots when they change
    spotsKey = key;
    box.querySelectorAll('.spot-m').forEach(function (m) { m.remove(); });
    var list = $('spots'); list.textContent = '';
    spots.forEach(function (s) {
      var m = document.createElement('i'); m.className = 'spot-m'; m.style.left = pctPan(s.pan); m.style.top = pct(s.tilt); box.append(m);
      var c = document.createElement('span'); c.className = 'spot'; c.title = 'Pan ' + Math.round(s.pan) + '° · Tilt ' + Math.round(s.tilt) + '°';
      var n = document.createElement('b'); n.textContent = s.name;
      var go = document.createElement('button'); go.type = 'button'; go.className = 'go'; go.textContent = 'Go';
      go.setAttribute('aria-label', 'Go to ' + s.name);
      go.addEventListener('click', function () { send('head_spot_go', [s.name]); });
      var del = document.createElement('button'); del.type = 'button'; del.className = 'del'; del.innerHTML = SVG_X;
      del.setAttribute('aria-label', 'Delete ' + s.name); del.title = 'Delete';
      del.addEventListener('click', function () { if (confirm('Delete the saved spot "' + s.name + '"?')) send('head_spot_del', [s.name]); });
      c.append(n, go, del); list.append(c);
    });
    if (!spots.length) { var p = document.createElement('span'); p.className = 'slim'; p.textContent = 'No saved spots yet.'; list.append(p); }
  }
  $('head-mode').addEventListener('click', function (e) {
    var b = e.target.closest('button'); if (!b) return;
    if (head) { head.mode = b.dataset.m; renderHead(); }   // optimistic; the next head event confirms
    send('head_mode', [b.dataset.m]);
  });
  // Tilt direction: this assumes a SMALLER tilt angle looks UP (and the position box
  // draws tilt 0 at the top). If the head moves the wrong way, flip the sign of TILT_UP.
  var TILT_DIR = -1, PAN_DIR = -1, joyStep = 10;   // a bigger pan angle turns AYA LEFT (measured): right = pan down
  try { joyStep = +localStorage.getItem('aya-joystep') || 10; } catch (e) {}
  function applyStep() { $('joy-step').querySelectorAll('button').forEach(function (b) { b.setAttribute('aria-pressed', String(+b.dataset.s === joyStep)); }); }
  applyStep();
  $('joy-step').addEventListener('click', function (e) {
    var b = e.target.closest('button'); if (!b) return;
    joyStep = +b.dataset.s; applyStep();
    try { localStorage.setItem('aya-joystep', String(joyStep)); } catch (x) {}
  });
  $('rest-save').addEventListener('click', function () {
    if (!head) { toast('AYA has not reported her head yet', 'err'); return; }
    if (confirm('Make pan ' + Math.round(head.pan) + '° · tilt ' + Math.round(head.tilt) + '° the rest position?')) send('head_rest_save', []);
  });
  $('joy').addEventListener('click', function (e) {
    var b = e.target.closest('button'); if (!b) return;
    var d = b.dataset.d;
    if (d === 'centre') { send('head_rest_go', []); return; }
    var v = { up: [0, TILT_DIR * joyStep], down: [0, -TILT_DIR * joyStep], left: [-PAN_DIR * joyStep, 0], right: [PAN_DIR * joyStep, 0] }[d];
    if (v) send('head_nudge', v);
  });
  $('head-gest').addEventListener('click', function (e) {
    var b = e.target.closest('button'); if (b) send('head_gesture', [b.dataset.g]);
  });
  $('spot-form').addEventListener('submit', async function (e) {
    e.preventDefault();
    var n = $('spot-name').value.trim().toLowerCase();
    if (!/^[a-z0-9_-]{1,12}$/.test(n)) { toast('Spot names: 1 to 12 letters, digits, - or _', 'err'); return; }
    if (await send('head_spot_save', [n]) === 202) $('spot-name').value = '';
  });

  // Click to look: a click on the picture turns the head there (x, y in -1..1 from the centre)
  var lookOn = false;
  try { lookOn = localStorage.getItem('aya-look') === '1'; } catch (e) {}
  function applyLook() { $('btn-look').setAttribute('aria-pressed', String(lookOn)); stage.classList.toggle('looking', lookOn); }
  applyLook();
  $('btn-look').onclick = function () {
    lookOn = !lookOn;
    try { localStorage.setItem('aya-look', lookOn ? '1' : '0'); } catch (e) {}
    applyLook();
    toast(lookOn ? 'Click to look on: click the video to turn the head' : 'Click to look off');
  };
  stage.addEventListener('click', function (e) {
    if (!lookOn || zoneEdit || e.target.closest('.controls, .zones, .zone-bar, .offline')) return;
    // The image box after the .frame transform (auto-framing zoom/pan), then the picture inside it (object-fit: contain)
    var r = img.getBoundingClientRect(), nw = img.naturalWidth || 4, nh = img.naturalHeight || 3;
    var k = Math.min(r.width / nw, r.height / nh), dw = nw * k, dh = nh * k;
    var x = (e.clientX - r.left - (r.width - dw) / 2) / dw * 2 - 1, y = (e.clientY - r.top - (r.height - dh) / 2) / dh * 2 - 1;
    if (!(Math.abs(x) <= 1 && Math.abs(y) <= 1)) return;   // on the black bars, not the picture
    var sr = stage.getBoundingClientRect(), ring = document.createElement('i');
    ring.className = 'look-ring';
    ring.style.left = (e.clientX - sr.left - stage.clientLeft) + 'px'; ring.style.top = (e.clientY - sr.top - stage.clientTop) + 'px';
    stage.append(ring); setTimeout(function () { ring.remove(); }, 800);
    send('head_look', [x.toFixed(3), y.toFixed(3)]);
  });

  // Panorama: frames arrive one by one over the "pano" event
  var panos = [], panoSel = null;                      // panoSel: id picked from the older ones, null = newest
  function panoTime(t) { return new Date(t).toLocaleTimeString([], { hour: 'numeric', minute: '2-digit' }); }
  function panoCell(p, k) {
    if (p.got.indexOf(k) < 0) { var s = document.createElement('span'); s.title = 'Picture ' + (k + 1) + ' (coming)'; return s; }
    var a = document.createElement('a'); a.href = '/pano/' + p.id + '/' + k + '.jpg?t=' + p.t; a.target = '_blank'; a.rel = 'noopener';
    a.title = 'Picture ' + (k + 1) + ' of ' + p.n;
    var im = document.createElement('img'); im.alt = 'Panorama picture ' + (k + 1); im.src = a.href; a.append(im);
    return a;
  }
  function panoShown() { return panos.find(function (x) { return x.id === panoSel; }) || panos[0]; }
  function panoInfo(p) { $('pano-info').textContent = p ? panoTime(p.t) + ' · ' + p.have + ' of ' + p.n + ' pictures' + (p.have < p.n ? ' so far' : '') :
                                                          'No panorama yet. AYA sweeps the room and the pictures appear here.'; }
  function panoRender() {
    var p = panoShown(), strip = $('pano-strip'), old = $('pano-old');
    strip.textContent = ''; old.textContent = '';
    strip.hidden = !p; panoInfo(p);
    if (!p) return;
    for (var k = 0; k < p.n; k++) strip.append(panoCell(p, k));
    if (panos.length > 1) panos.forEach(function (x, i) {
      var b = document.createElement('button'); b.type = 'button'; b.className = 'btn';
      b.textContent = (i ? '' : 'Latest · ') + panoTime(x.t) + ' · ' + x.have + '/' + x.n;
      b.setAttribute('aria-pressed', String(x === p));
      b.addEventListener('click', function () { panoSel = i ? x.id : null; panoRender(); });
      old.append(b);
    });
  }
  async function panoLoad() {
    try { panos = await (await fetch('/panos', { cache: 'no-store' })).json(); panoRender(); } catch (e) {}
  }
  es.addEventListener('pano', function (e) {
    try {
      var d = JSON.parse(e.data), p = panos.find(function (x) { return x.id === d.id && x.t === d.t; });
      if (typeof d.k !== 'number') { panoLoad(); return; }
      if (!p) {                                          // a new panorama: show it
        panos = panos.filter(function (x) { return x.id !== d.id; });
        p = { id: d.id, t: d.t, n: d.n, have: 0, got: [] };
        panos.unshift(p); if (panos.length > 5) panos.pop();
        panoSel = null; p.got.push(d.k); p.have = d.have; panoRender(); return;
      }
      if (p.got.indexOf(d.k) < 0) p.got.push(d.k);
      p.have = d.have;
      var strip = $('pano-strip');
      if (panoShown() === p && strip.children.length === p.n) { strip.replaceChild(panoCell(p, d.k), strip.children[d.k]); panoInfo(p); }
      else panoRender();
      if (p.have === p.n && panoShown() === p) toast('Panorama ready', 'ok');
    } catch (x) {}
  });
  $('pano-go').onclick = function () { send('head_pano'); };
  panoLoad();

  // ── Room map: the latest picture of each patrol stop, activity and changes on top ──
  // Grid from head.map (live) or /map.json: pan p0..p1 across the columns, tilt t0..t1 down
  // the rows (a smaller tilt looks up, so row 0 is the top). Which way pan runs on screen
  // is unknown, so the map can be flipped left-right (remembered per browser).
  var mapData = { cols: null, rows: null, cells: {} }, mapTiles = {}, mapShape = '', mapMax = 0, mapTimer = null, mapFlip = false;
  var MAP_KINDS = ['person', 'arrive', 'known', 'stranger', 'unknown', 'motion', 'changed', 'unusual', 'wave'];
  // a bigger pan angle turns AYA LEFT on this mount (seen on the first real
  // scan), so the map is drawn flipped unless this browser chose otherwise
  try { mapFlip = localStorage.getItem('aya-mapflip') !== '0'; } catch (e) { mapFlip = true; }
  function mapGeo() {
    var g = head && head.map ? head.map : mapData.cols ? mapData : null;
    var o = { cols: g ? g.cols : 0, rows: g ? g.rows : 0, p0: g && g.p0, p1: g && g.p1, t0: g && g.t0, t1: g && g.t1, known: !!g };
    Object.keys(mapData.cells).forEach(function (k) {   // pictures beyond the grid (or no grid yet): make room
      var c = mapData.cells[k]; if (c.c >= o.cols) o.cols = c.c + 1; if (c.r >= o.rows) o.rows = c.r + 1;
    });
    return o;
  }
  function mapFrac(v, a, b, n) { return n < 2 || a === b ? 0 : (v - a) / (b - a) * (n - 1); }   // fractional cell index
  function mapAim(g, c, r) {                           // where to point the head for a cell
    var cell = mapData.cells[c + ',' + r];
    if (cell && typeof cell.pan === 'number') return [cell.pan, cell.tilt];
    if (!g.known) return null;
    return [g.cols < 2 ? g.p0 : g.p0 + (g.p1 - g.p0) * c / (g.cols - 1), g.rows < 2 ? g.t0 : g.t0 + (g.t1 - g.t0) * r / (g.rows - 1)];
  }
  function mapPlace(el, g, pan, tilt) {
    var fc = mapFrac(pan, g.p0, g.p1, g.cols), fr = mapFrac(tilt, g.t0, g.t1, g.rows);
    if (mapFlip) fc = g.cols - 1 - fc;
    var x = (fc + 0.5) / g.cols * 100, y = (fr + 0.5) / g.rows * 100;
    el.style.left = Math.max(0, Math.min(100, x)).toFixed(2) + '%'; el.style.top = Math.max(0, Math.min(100, y)).toFixed(2) + '%';
  }
  function mapAgo(t) {
    var m = Math.round((Date.now() - t) / 60000);
    return m < 1 ? 'just now' : m < 60 ? m + 'm ago' : m < 1440 ? Math.round(m / 60) + 'h ago' : Math.round(m / 1440) + 'd ago';
  }
  function mapRender() {
    var g = mapGeo(), keys = Object.keys(mapData.cells), grid = $('map-grid');
    var any = keys.some(function (k) { var c = mapData.cells[k]; return c.t || c.act > 0 || c.changedAt; });
    var show = any && g.cols > 0;
    $('map-wrap').hidden = !show; $('map-foot').hidden = !show; $('map-empty').hidden = show;
    $('map-flip').setAttribute('aria-pressed', String(mapFlip));
    if (!show) { mapShape = ''; grid.textContent = ''; mapTiles = {}; return; }
    mapMax = 0;
    keys.forEach(function (k) { mapMax = Math.max(mapMax, mapData.cells[k].act || 0); });
    var shape = g.cols + 'x' + g.rows + (mapFlip ? 'f' : '');
    if (shape !== mapShape) {
      mapShape = shape; grid.textContent = ''; mapTiles = {};
      grid.style.gridTemplateColumns = 'repeat(' + g.cols + ', minmax(0, 1fr))';
      for (var r = 0; r < g.rows; r++) for (var c = 0; c < g.cols; c++) {
        var b = document.createElement('button'); b.type = 'button'; b.className = 'map-tile empty';
        b.dataset.c = c; b.dataset.r = r;
        b.style.gridColumn = String(mapFlip ? g.cols - c : c + 1); b.style.gridRow = String(r + 1);
        var im = document.createElement('img'); im.alt = ''; im.hidden = true; im.decoding = 'async';
        im.onerror = function () { this.hidden = true; this.parentNode.classList.add('empty'); };
        var heat = document.createElement('span'); heat.className = 'heat';
        var cnt = document.createElement('span'); cnt.className = 'cnt'; cnt.hidden = true;
        var pill = document.createElement('span'); pill.className = 'pill'; pill.textContent = 'Changed'; pill.hidden = true;
        b.append(im, heat, cnt, pill);
        grid.append(b);
        mapTiles[c + ',' + r] = { el: b, img: im, heat: heat, cnt: cnt, pill: pill, t: null };
      }
    }
    Object.keys(mapTiles).forEach(mapTile);
    mapMarks();
  }
  function mapTile(k) {
    var o = mapTiles[k]; if (!o) return;
    var cell = mapData.cells[k] || {}, p = k.split(','), act = cell.act || 0;
    if (cell.t && o.t !== cell.t) { o.t = cell.t; o.img.src = '/map/' + p[0] + '_' + p[1] + '.jpg?t=' + cell.t; o.img.hidden = false; o.el.classList.remove('empty'); }
    if (!cell.t) { o.t = null; o.img.hidden = true; o.img.removeAttribute('src'); o.el.classList.add('empty'); }
    o.heat.style.opacity = mapMax > 0 ? (act / mapMax * 0.5).toFixed(2) : '0';
    o.cnt.hidden = act < 1; o.cnt.textContent = String(Math.round(act));
    var chg = !!cell.changedAt && Date.now() - cell.changedAt < 3600000;
    o.el.classList.toggle('chg', chg); o.pill.hidden = !chg;
    o.el.title = 'View ' + p[0] + ',' + p[1] + ' · ' + (cell.t ? 'updated ' + mapAgo(cell.t) : 'no picture yet') +
      (act >= 1 ? ' · ' + Math.round(act) + ' recent events' : '') + (chg ? ' · changed ' + mapAgo(cell.changedAt) : '');
    o.el.setAttribute('aria-label', 'Look at view ' + p[0] + ',' + p[1] + (chg ? ', something changed' : ''));
  }
  var mapMarksKey = '';
  function mapMarks() {
    var g = mapGeo(), hd = $('map-head'), rest = $('map-rest'), box = $('map-spots');
    if ((g.cols + 'x' + g.rows + (mapFlip ? 'f' : '')) !== mapShape && !$('map-wrap').hidden) { mapRender(); return; }
    var on = g.known && !$('map-wrap').hidden && !!head;
    hd.hidden = !on; rest.hidden = !(on && head.rest);
    if (!on) { box.textContent = ''; mapMarksKey = ''; return; }
    mapPlace(hd, g, head.pan, head.tilt);
    hd.classList.toggle('off', !headLive);
    if (head.rest) mapPlace(rest, g, head.rest.pan, head.rest.tilt);
    var key = JSON.stringify([head.spots || [], g, mapFlip]);
    if (key === mapMarksKey) return;
    mapMarksKey = key; box.textContent = '';
    (head.spots || []).forEach(function (s) {
      var m = document.createElement('i'); m.className = 'map-spot';
      var n = document.createElement('b'); n.textContent = s.name; m.append(n);
      mapPlace(m, g, s.pan, s.tilt); box.append(m);
    });
  }
  async function mapLoad() {
    try {
      var d = await (await fetch('/map.json', { cache: 'no-store' })).json(), cells = {};
      (d.cells || []).forEach(function (c) { cells[c.c + ',' + c.r] = c; });
      mapData = { cols: d.cols, rows: d.rows, p0: d.p0, p1: d.p1, t0: d.t0, t1: d.t1, cells: cells };
      mapRender();
    } catch (e) {}
  }
  es.addEventListener('map', function (e) {             // a new picture of one view: refresh just that tile
    try {
      var d = JSON.parse(e.data), k = d.c + ',' + d.r;
      var cell = mapData.cells[k] || { c: d.c, r: d.r, act: 0, changedAt: null };
      cell.pan = d.pan; cell.tilt = d.tilt; cell.t = d.t; mapData.cells[k] = cell;
      if (mapTiles[k] && !$('map-wrap').hidden) mapTile(k); else mapRender();
    } catch (x) {}
  });
  es.addEventListener('log', function (e) {             // activity or a change: fresh counts shortly after
    try {
      if (MAP_KINDS.indexOf(JSON.parse(e.data).kind) < 0 || $('pane-camera').hidden) return;
      clearTimeout(mapTimer); mapTimer = setTimeout(mapLoad, 1500);
    } catch (x) {}
  });
  $('map-grid').addEventListener('click', function (e) {
    var b = e.target.closest('.map-tile'); if (!b) return;
    var c = +b.dataset.c, r = +b.dataset.r, a = mapAim(mapGeo(), c, r);
    if (!a) { toast('AYA has not reported where this view is yet', 'err'); return; }
    send('head_goto', [a[0].toFixed(1), a[1].toFixed(1)], null, 'Looking at view ' + c + ',' + r);
  });
  $('map-flip').addEventListener('click', function () {
    mapFlip = !mapFlip;
    try { localStorage.setItem('aya-mapflip', mapFlip ? '1' : '0'); } catch (x) {}
    mapShape = ''; mapRender();
  });
  $('map-scan').addEventListener('click', function () { send('head_map'); });
  setInterval(function () { if (!$('pane-camera').hidden) mapLoad(); }, 60000);
  mapLoad();

  // ── Health history: online + frame rate ──
  var hData = null, hHours = 6, hCharts = [];
  var METRICS = [
    { key: 'fps', title: 'Frames per second', fmt: function (v) { return v.toFixed(1); }, zero: true },
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
    var on = S.filter(function (x) { return x.on; });
    $('h-online').textContent = S.length ? Math.round(on.length / S.length * 100) + '%' : '–';
    var lastS = hData.samples[hData.samples.length - 1];
    $('h-now').textContent = lastS && lastS.on ? lastS.fps.toFixed(1) + ' fps' : 'offline';
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
      var b = B[k] || (B[k] = { t: 0, n: 0, on: true, fps: 0 });
      b.t += x.t; b.n++; if (!x.on) b.on = false;
      if (x.on) b.fps += x.fps || 0;
    });
    var Sb = B.filter(Boolean).map(function (b) {
      var n = b.n;
      return { t: b.t / n, on: b.on, fps: b.on ? Math.round(b.fps / n * 10) / 10 : null };
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
      if (!vals.length) {                          // nothing to plot: the camera was offline the whole time
        var em = document.createElement('div'); em.className = 'hc-empty'; em.textContent = 'No data — the camera was offline';
        wrap.append(em); box.append(wrap); return;
      }
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
      var xh = svgEl('line', { class: 'xh', y1: 0, y2: H, visibility: 'hidden' });
      var dot = svgEl('circle', { class: 'dot', r: 4, visibility: 'hidden' });
      svg.append(xh, dot);
      hCharts.push({ m: m, xh: xh, dot: dot, X: X, Y: Y });
      svg.addEventListener('pointermove', function (e) { hover(e, svg, Sb, X); });
      svg.addEventListener('pointerleave', unhover);
      wrap.append(svg); box.append(wrap);
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
  // About 100 KB a time: only while the Health tab is showing (showTab loads it once on opening)
  setInterval(function () { if (!document.hidden && !$('pane-health').hidden) loadHealth(); }, 30000);
  window.addEventListener('resize', renderHealth);

  // ── ARIA's live face (the OLED's 128×64 frame, 1 bit per pixel) ──
  var rc = $('robot'), rctx = rc.getContext('2d'), rimg = rctx.createImageData(128, 64), lastFrame = null;
  var oled = null, oledAt = 0;                 // the display's own screen, sent with its polls
  es.addEventListener('oled', function (e) { try { oled = JSON.parse(e.data).f; oledAt = Date.now(); } catch (x) {} });
  function drawRobot() {
    var b64 = (oled && Date.now() - oledAt < 8000 ? oled : null) || (fresh() && meta.face_frame);
    $('robot-off').hidden = !!b64; $('robot-wrap').hidden = !b64;
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
    var objs = showBoxes && meta && Date.now() - metaAt < 2500 ? (meta.objects || []) : [];
    ctx.setLineDash([4, 4]); ctx.lineWidth = 1.5; ctx.strokeStyle = '#fbbf24';
    ctx.font = '600 11px ui-sans-serif, system-ui, sans-serif';
    objs.forEach(function (o) {                          // everything else YOLOX sees (amber, dashed)
      var x = ox + o.x * dw, y = oy + o.y * dh, w = o.w * dw, h = o.h * dh;
      ctx.strokeRect(x, y, w, h);
      var t = o.label + ' ' + Math.round(o.score * 100) + '%', tw = ctx.measureText(t).width + 10;
      ctx.fillStyle = 'rgba(7,9,12,.72)'; ctx.fillRect(x, Math.max(0, y - 16), tw, 16);
      ctx.fillStyle = '#fde68a'; ctx.fillText(t, x + 5, Math.max(12, y - 4));
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
      var hl = hand.g || 'Hand';
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
      var label = (f.id === 'known' ? f.name : f.id === 'unknown' ? 'Stranger' : 'Identifying…') +
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
