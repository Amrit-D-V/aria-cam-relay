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
let brain = null;                 // AYA's brain (brain.js), set up below once everything it uses exists
const activity = [];              // newest first: {t, kind, text}
const presence = { here: false, lastFace: 0, who: null, sleeping: null };

// Health history for the page's charts: a sample every 30 s for 24 h. In
// memory only — a relay restart starts it over.
const HEALTH_EVERY_MS = 30000;
const HEALTH_KEEP = 24 * 3600 * 1000 / HEALTH_EVERY_MS;
const healthSamples = [];         // {t, on, fps, pct?, v?, ma?} (the battery's, while AYA reports it)
let lastGesture = 0;

setInterval(() => {
  const on = status().online;
  const smp = { t: Date.now(), on, fps: on ? Math.round(fps() * 10) / 10 : null };
  if (power && Date.now() - power.t < 60000) Object.assign(smp, { pct: power.pct, v: power.v, ma: power.ma });
  healthSamples.push(smp);
  if (healthSamples.length > HEALTH_KEEP) healthSamples.shift();
}, HEALTH_EVERY_MS);

// What the admin has asked of the OLED display. Ids let the display tell a
// new message/emotion from one it has already shown.
const EMOTIONS = ['giggle', 'wink', 'heart', 'surprise', 'curious', 'think', 'shy', 'dizzy',
                  'roll', 'nod', 'yawn', 'purr', 'squint', 'sleep', 'wake'];
const MSG_MAX = 120;
const VIEWS = ['auto', 'eyes', 'iris', 'clock', 'weather', 'stats', 'detect', 'cam2'];
// view/zoom2 start as null: after a relay restart the display keeps what it shows until someone picks
const displayState = { screen: 1, msg: null, emotion: null, seq: 0, restart: 0, shutdown: 0, view: null, zoom2: null, ignore: null,
                       set: null, anim: null, motion: null };   // motion: {t, f: [[dpan, dtilt, hold ms, speed], …]} a composed head motion   // set: {t, speed, accel, doze} motion/standby settings; anim: {t, name} boot|dead preview
const ANIMS = ['boot', 'dead', 'show'];   // show: the ~35 s showcase for filming

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
           view: displayState.view, zoom2: displayState.zoom2, set: displayState.set, anim: displayState.anim, motion: displayState.motion,
           ignore: displayState.ignore, face: faceForBoard() };
}
// the face for the board: id (a new detection or a repeat) and age (ms since its picture reached the relay;
// the board adds the upload time and places it with its head position back then)
function faceForBoard() {
  if (!boardFace || Date.now() - boardFace.t >= 3000) return null;
  const { ft, t, ...f } = boardFace;
  return { ...f, age: Date.now() - ft + 150 };
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
  req.on('error', () => { over = true; });
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

// One place that applies a command: the dashboard (POST /cmd) and AYA's brain (brain.js) both use it.
// Returns [http code, text]; 202 = queued for the display's next poll.
function applyCmd(cmd, args, body = {}) {
  args = (args || []).map(String);
  const reply = (code, text) => [code, text];
  deviceKick = true;
  // Display commands are kept here for the display to pick up (/display).
  if (cmd === 'screen') {
    if (!['on', 'off'].includes(args[0])) return reply(400, 'screen on|off');
    displayState.screen = args[0] === 'on' ? 1 : 0;
    broadcast('display', publicDisplay());
    return reply(202, 'queued');
  }
  if (cmd === 'message') {
    // The OLED fonts are ASCII: anything else becomes '?'. Blank clears it.
    const text = String(body.text || '').replace(/[\r\n\t]+/g, ' ').replace(/[^\x20-\x7e]/g, '?').trim().slice(0, MSG_MAX);
    const secs = Math.min(Math.max(parseInt(body.secs, 10) || 15, 5), 600);
    displayState.msg = text ? { id: ++displayState.seq, text, secs, t: Date.now() } : null;
    if (text) logEvent('message', `Message: "${text}"`);
    broadcast('display', publicDisplay());
    return reply(202, 'queued');
  }
  if (cmd === 'restart_all') {       // the display (and its camera) picks it up on its next poll (≤2 s)
    displayState.restart = Date.now();
    logEvent('privacy', 'System restart');
    return reply(202, 'restarting');
  }
  if (cmd === 'shutdown') {          // deep sleep on its next poll; only a touch (or EN / power) wakes it
    displayState.shutdown = Date.now();
    logEvent('restart', 'Shut down from the page · touch AYA to wake her');
    return reply(202, 'shutting down');
  }
  if (cmd === 'view') {              // what the OLED shows: auto rotation, one screen, or camera 2 live
    if (!VIEWS.includes(args[0])) return reply(400, 'view ' + VIEWS.join('|'));
    displayState.view = args[0];
    broadcast('display', publicDisplay());
    return reply(202, 'queued');
  }
  if (cmd === 'ignore') {            // camera zones AYA never counts as motion: 12 rows x 16 bits as 48 hex digits
    if (!/^[0-9a-f]{48}$/.test(args[0] || '')) return reply(400, 'ignore <48 hex digits>');
    displayState.ignore = args[0];
    logEvent('privacy', 'Motion ignore zones updated');
    broadcast('display', publicDisplay());
    return reply(202, 'queued');
  }
  if (cmd === 'zoom2') {             // camera 2 (the display's OV7670): digital zoom ×10
    const z = parseInt(args[0], 10);
    if (!(z === 0 || (z >= 10 && z <= 30))) return reply(400, 'zoom2 0 (auto) or 10..30');
    displayState.zoom2 = z;
    broadcast('display', publicDisplay());
    return reply(202, 'queued');
  }
  if (cmd === 'tune') {              // motion and standby settings: {speed °/s, accel °/s², doze min}, any subset
    const num = (v, lo, hi) => (v === undefined || v === null || v === '' ? undefined
      : Number.isFinite(+v) && +v >= lo && +v <= hi ? Math.round(+v) : null);
    const R = { speed: [20, 150], accel: [50, 1000], doze: [0, 1440], pmode: [0, 2], fstyle: [0, 1], fsens: [0, 2], prest: [0, 600],
                sleepq: [0, 240], pmin: [0, 180], pmax: [0, 180], tmin: [0, 180], tmax: [0, 180], invx: [0, 1], invy: [0, 1] };
    const got = {};
    for (const [k, [lo, hi]] of Object.entries(R)) {
      const v = num(body[k], lo, hi);
      if (v === null) return reply(400, `tune ${k}: ${lo}..${hi}`);
      if (v !== undefined) got[k] = v;
    }
    if (body.test !== undefined) { if (!['x', 'y'].includes(body.test)) return reply(400, 'tune test: x|y'); got.test = body.test; }
    if ((got.pmin !== undefined) !== (got.pmax !== undefined) || (got.tmin !== undefined) !== (got.tmax !== undefined))
      return reply(400, 'tune: pmin+pmax and tmin+tmax go together');
    if (!Object.keys(got).length) return reply(400, 'tune: nothing to set');
    const prev = displayState.set || {};
    const { t: _t, test: _x, ...keep } = prev;            // every setting so far rides along (two quick changes both arrive)
    displayState.set = { t: Date.now(), ...keep, ...got };   // (the one-shot "test" only with its own request)
    const pmode = got.pmode;
    if (pmode !== undefined) logEvent('power', `Power mode: ${['performance', 'balanced', 'saver'][pmode]}`);
    broadcast('display', publicDisplay());
    return reply(202, 'queued');
  }
  if (cmd === 'anim') {              // replay the boot screen, the showcase, or preview the dying animation (she restarts after it)
    if (!ANIMS.includes(args[0])) return reply(400, 'anim ' + ANIMS.join('|'));
    displayState.anim = { t: Date.now(), name: args[0] };
    return reply(202, 'queued');
  }
  if (cmd === 'head_seq') {           // a head motion composed by the brain: up to 16 steps relative to where the head is
    const f = Array.isArray(body.frames) ? body.frames.slice(0, 16) : [];
    const ok = (v, lo, hi) => Number.isFinite(+v) && +v >= lo && +v <= hi;
    if (!f.length || !f.every((x) => Array.isArray(x) && ok(x[0], -60, 60) && ok(x[1], -40, 40) && ok(x[2], 0, 3000) && ok(x[3], 10, 150)))
      return reply(400, 'head_seq frames: [[dpan -60..60, dtilt -40..40, hold 0..3000 ms, speed 10..150], …] (1-16)');
    displayState.motion = { t: Date.now(), f: f.map((x) => x.map((v) => Math.round(+v))) };
    return reply(202, 'queued');
  }
  if (cmd === 'emotion') {
    if (!EMOTIONS.includes(args[0])) return reply(400, 'unknown emotion');
    displayState.emotion = { id: ++displayState.seq, name: args[0], t: Date.now() };
    broadcast('display', publicDisplay());
    return reply(202, 'queued');
  }
  if (cmd.startsWith('head_')) return headCmd(cmd, args);
  return reply(400, 'unknown command');
}

function handleCmd(req, res) {
  if (!sessionOk(req) && !keyMatches(req.headers['x-admin-key'], ADMIN_KEY)) return send(res, 401, 'text/plain', 'not logged in');
  readBody(req, SMALL_BODY_MAX, (raw) => {
    let body;
    try { body = JSON.parse(raw.toString('utf8')); } catch { return send(res, 400, 'text/plain', 'bad json'); }
    const [code, text] = applyCmd(String(body.cmd || ''), body.args || [], body);
    send(res, code, 'text/plain', text);
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
  if (brain) brain.onEvent(e);                    // her memory, rules and smart alerts (brain.js)
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
      else { logEvent('stranger', 'Unknown person in view'); captureEvent('stranger', 'Unknown person in view'); }
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
  req.on('error', () => {});
  req.on('end', () => {
    if (res.writableEnded) return;
    seen.eye2 = Date.now();
    const frame = Buffer.concat(chunks);
    if (!acceptFrame(frame)) return send(res, 400, 'text/plain', 'not a JPEG');
    notePano(url, frame);                          // a panorama frame is also the live picture
    noteMapFrame(url, frame);                      // so is a room map frame
    // Head commands ride on this reply too ("N[,p]\n{headq}"): an upload goes out every ~0.1-0.5 s, so a
    // joystick press reaches the servos a round trip sooner than via the poll. X-Head-Ack drops what she applied.
    noteHeadAck(req);
    const ack = headAck(req), hq = req.headers['x-head-ack'] !== undefined ? headq.filter((e) => e.id > ack) : [];
    const extra = {};
    if (hq.length) extra.headq = hq.map((e) => ({ id: e.id, op: e.op, a: e.a, b: e.b, name: e.name }));
    if (req.headers['x-head-ack'] !== undefined) { const f = faceForBoard(); if (f) extra.face = f; }   // faces ride here too: ~3x a second
    const tail = Object.keys(extra).length ? '\n' + JSON.stringify(extra) : '';
    send(res, 200, 'text/plain', String(viewerCount()) + (deviceKick ? ',p' : '') + tail);   // answer first: AYA waits for this
    if (localVision && Date.now() - metaHttpAt > 3000)  // (the laptop tracker, when it runs, wins)
      setImmediate(() => { const ft = Date.now(); localVision.analyze(frame).then((m) => { if (m) ingestMeta(m, ft); }, () => {}); });   // then analyse
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
  req.on('error', () => {});
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
let boardFaceId = 0;
function ingestMeta(meta, frameAt) {                // frameAt: when the analysed picture arrived (Render vision)
  {
    latestMeta = JSON.stringify(meta);            // re-serialised: only valid JSON reaches viewers
    const f = Array.isArray(meta.faces) && meta.faces[0];       // the face, passed to the display on its poll
    if (f && [f.x, f.y, f.w, f.h].every(Number.isFinite)) {
      boardFace = { x: +((f.x + f.w / 2) * 2 - 1).toFixed(2), y: +((f.y + f.h / 2) * 2 - 1).toFixed(2), s: +f.w.toFixed(3),
                    id: String(f.id || ''), name: String(f.name || '').slice(0, 20), admin: !!f.admin, emo: String(f.emo || ''), t: Date.now(),
                    fid: ++boardFaceId, ft: frameAt || Date.now() };
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
// X-Power: "V,mA,mW,mAhUsed,pct,state,hours" (mA < 0 = charging; hours = to full while charging, else left)
// X-Sys: "uptime s,heap KB,block KB,rssi,offline 0|1,cpu MHz,servo speed,servo accel,standby min,power mode 0..2"
let power = null, board = null, tune = null;
function noteSys(req) {
  const pv = req.headers['x-power'];
  if (pv !== undefined) {
    const a = String(pv).split(',');
    const n = (i) => (a[i] !== undefined && a[i] !== '' && Number.isFinite(+a[i]) ? +a[i] : null);
    const st = /^[a-z]{1,12}$/.test(a[5] || '') ? a[5] : null;
    if (n(0) !== null) power = { v: n(0), ma: n(1), mw: n(2), mah_used: n(3), pct: n(4), state: st, hours: n(6), t: Date.now() };
  }
  const tv = req.headers['x-tune'];               // "fstyle,fsens,prest,sleepq,pmin,pmax,tmin,tmax,invx,invy"
  if (tv !== undefined) {
    const a = String(tv).split(',').map(Number);
    if (a.length === 10 && a.every(Number.isFinite))
      tune = { fstyle: a[0], fsens: a[1], prest: a[2], sleepq: a[3], pmin: a[4], pmax: a[5], tmin: a[6], tmax: a[7], invx: a[8], invy: a[9] };
  }
  const sv = req.headers['x-sys'];
  if (sv !== undefined) {
    const a = String(sv).split(',').map((x) => (x !== '' && Number.isFinite(+x) ? +x : null));
    if (a.length >= 9) board = { uptime: a[0], heap_kb: a[1], block_kb: a[2], rssi: a[3], offline: a[4], cpu_mhz: a[5],
                                 servo_speed: a[6], servo_accel: a[7], doze_min: a[8], pmode: a.length > 9 ? a[9] : 0, t: Date.now() };
  }
}

function noteBoot(req) {
  const why = String(req.headers['x-boot'] || '').replace(/[^\x20-\x7e]/g, '').slice(0, 60);
  if (why) logEvent('restart', `AYA started · ${why}`);
}

// ── The head: two servos (pan, tilt) on the display board ───────────────
// Page commands wait in `headq` and ride out on the display's poll reply
// until it acks them (X-Head-Ack: the last id it applied). Ids restart with
// the relay, so an ack above the current max id is from before a restart: 0.
const HEAD_MODES = ['follow', 'patrol', 'hold'];
const HEAD_STATES = ['search', 'face', 'motion', 'inspect', 'hold', 'gesture', 'spot', 'pano', 'map', 'centre', 'rest', '-'];
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

function headCmd(cmd, args) {
  const bad = (why) => [400, why];
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
  return [202, 'queued'];
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
  if (brain) brain.onCapture(ev);                 // an AI description arrives a few seconds later
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

// op 'put' (brain.js only): write `data` (text, at most 2 KB) to a file under /aya/brain/ on the card
function sdRequest(op, path, data) {
  return new Promise((resolve) => {
    let r = op === 'put' ? null : sdPending.find((x) => x.op === op && x.path === path);
    if (!r) { r = { id: ++sdNextId, op, path, data, at: Date.now(), sentAt: 0, waiters: [] }; sdPending.push(r); }
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

let pwSent = '', pwSentAt = 0;
function deviceReply(req) {
  const out = publicDisplay();
  // Requests that only matter when new ride out for a minute, not on every poll forever (the board's
  // heap is small; each reply is parsed whole). It acts on a new t; after a restart it keeps its saved values.
  const fresh = (x, ms) => x && Date.now() - x.t < ms;
  if (!fresh(out.set, 60000)) delete out.set;
  if (!fresh(out.anim, 60000)) delete out.anim;
  if (!fresh(out.motion, 30000)) delete out.motion;
  const due = sdPending.filter((r) => r.waiters.length && (!r.sentAt || Date.now() - r.sentAt > 8000)).slice(0, 3);
  if (due.length) {                               // SD card requests from the page
    for (const r of due) r.sentAt = Date.now();
    out.sdreq = due.map((r) => (r.data !== undefined ? { id: r.id, op: r.op, path: r.path, data: r.data } : { id: r.id, op: r.op, path: r.path }));
  }
  const logSince = Number(req.headers['x-log-since']), shotSince = Number(req.headers['x-shot-since']);
  if (Number.isFinite(logSince) || Number.isFinite(shotSince)) out.now = Date.now();
  if (Number.isFinite(logSince))
    out.log = activity.filter((e) => e.t > logSince).reverse().slice(0, 10).map((e) => ({ t: e.t, kind: e.kind, text: e.text }));
  if (Number.isFinite(shotSince))
    out.shots = gallery.filter((e) => e.t > shotSince).reverse().slice(0, 5).map((e) => ({ t: e.t, kind: e.kind, text: e.text }));
  const ack = headAck(req), hq = headq.filter((e) => e.id > ack);   // head commands not yet applied
  if (hq.length) out.headq = hq.map((e) => ({ id: e.id, op: e.op, a: e.a, b: e.b, name: e.name }));
  if (brain && roomMap.cols === 9 && roomMap.rows === 4) {   // which patrol views are worth a look (brain.js map labels)
    const w = brain.patrolWeights(9, 4);
    if (w && (w !== pwSent || Date.now() - pwSentAt > 300000)) { out.pweights = w; pwSent = w; pwSentAt = Date.now(); }
  }
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
    noteSys(req);
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
           idle: isIdle(), head, map: mapGeom(), ...ages(),
           power: power && { ...power, age: Date.now() - power.t }, board: board && { ...board, age: Date.now() - board.t }, tune, detector: localVision ? localVision.stats() : null };   // Render-side detection: frames, dropped, ms per stage
}

// ── AYA's brain (brain.js): chat with tools, vision, memory, rules, summaries ──
brain = require('./brain')({
  applyCmd,
  status,
  frame: () => (latestFrame ? { buf: latestFrame, at: latestAt } : null),
  logEvent,
  sdGet: (path) => sdRequest('get', path),
  sdPut: (path, text) => sdRequest('put', path, text),
  online: () => !!seen.display && Date.now() - seen.display < 10000,
  broadcast,
  mapCells: () => [...roomMap.cells.entries()].map(([k, v]) => ({ key: k, pan: v.pan, tilt: v.tilt, t: v.t, jpeg: v.jpeg })),
});

function handleBrain(req, res, url) {
  if (!sessionOk(req) && !keyMatches(req.headers['x-admin-key'], ADMIN_KEY)) return send(res, 401, 'text/plain', 'not logged in');
  readBody(req, SMALL_BODY_MAX, async (raw) => {
    let body;
    try { body = JSON.parse(raw.toString('utf8')); } catch { return send(res, 400, 'text/plain', 'bad json'); }
    try {
      if (url.pathname === '/ask') {               // {q, history: [{role, content}]}
        const q = String(body.q || '').trim();
        if (!q) return send(res, 400, 'text/plain', 'ask what?');
        return send(res, 200, 'application/json', JSON.stringify(await brain.ask(q, Array.isArray(body.history) ? body.history : [])));
      }
      if (body.op === 'delete_rule') return send(res, 200, 'application/json', JSON.stringify({ saved: await brain.deleteRule(String(body.id)) }));
      if (body.op === 'delete_note') return send(res, 200, 'application/json', JSON.stringify({ saved: await brain.deleteNote(String(body.id)) }));
      send(res, 400, 'text/plain', 'unknown op');
    } catch (e) { send(res, 503, 'text/plain', e.message); }
  });
}

const server = http.createServer((req, res) => {
  const url = new URL(req.url, 'http://x');
  const key = url.searchParams.get('key');
  const device = keyMatches(key, VIEW_KEY);       // the display board's poll
  const authed = sessionOk(req);                  // a logged-in browser

  if (req.method === 'POST' && url.pathname === '/push') return handlePush(req, res, url);
  if (req.method === 'POST' && url.pathname === '/meta') return handleMeta(req, res);
  if (req.method === 'POST' && url.pathname === '/cmd') return handleCmd(req, res);
  if (req.method === 'POST' && (url.pathname === '/ask' || url.pathname === '/brain')) return handleBrain(req, res, url);
  if (req.method === 'POST' && url.pathname === '/login') return handleLogin(req, res);
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
  // static/). API routes always win: a path whose first segment is one of
  // ours never reaches the files. Without next/, `/` says so.
  {
    const fs = require('fs'), path = require('path');
    const NEXT_DIR = path.join(__dirname, 'next');
    const API_SEGMENTS = new Set(['healthz', 'manifest.webmanifest', 'icon.svg', 'logout', 'stream', 'snapshot', 'events', 'display',
      'status', 'sd', 'gallery', 'panos', 'map.json', 'map', 'health', 'pano', 'push', 'meta', 'cmd', 'login', 'ask', 'sdres', 'brain']);
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
    case '/':                                      // (next/ missing: the dashboard wasn't built)
      return send(res, 503, 'text/plain', 'The dashboard is not built: cd web && npm run export');
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
    case '/brain':                                 // what the brain knows: rules, notes, usage
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return send(res, 200, 'application/json', JSON.stringify(brain.info()));
    case '/brain/brief': {                         // "since you were away"
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      const since = Math.max(Date.now() - 72 * 3600e3, Number(url.searchParams.get('since')) || Date.now() - 3600e3);
      brain.brief(since).then((text) => send(res, 200, 'application/json', JSON.stringify({ since, text })),
                              (e) => send(res, 503, 'text/plain', e.message));
      return;
    }
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
// The dashboard is the Next.js app in web/ (served from next/), with its own sign-in screen. This is
// only what a plain form post to /login gets back (a wrong key, too many tries) or `/` shows when
// next/ hasn't been built.
function loginPage(error) {
  const esc = (t) => String(t).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
  return `<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>AYA · Sign in</title><style>body{font:16px system-ui,sans-serif;background:#07090c;color:#e6edf3;display:grid;place-items:center;min-height:100vh;margin:0}
form{display:grid;gap:12px;width:min(320px,90vw)}input,button{font:inherit;padding:10px;border-radius:10px;border:1px solid #2a3340;background:#11161d;color:inherit}
button{background:#5eead4;color:#04110f;border:0;font-weight:700}.err{color:#f87171}</style></head><body>
<form method="post" action="/login"><h1>AYA</h1>${error ? `<p class="err">${esc(error)}</p>` : ''}
<input name="key" type="password" placeholder="Access key" autocomplete="current-password" required autofocus aria-label="Access key">
<button type="submit">Continue</button></form></body></html>`;
}
