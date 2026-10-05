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
const VIEWS = ['auto', 'sage', 'eyes', 'clock', 'weather', 'stats', 'detect', 'cam2'];
// view/zoom2 start as null: after a relay restart the display keeps what it shows until someone picks
const displayState = { screen: 1, msg: null, emotion: null, seq: 0, restart: 0, view: null, zoom2: null, ignore: null };

function broadcast(event, obj) {
  const line = `event: ${event}\ndata: ${JSON.stringify(obj)}\n\n`;
  for (const s of metaSubscribers) s.write(line);
}

// The face the laptop tracker last saw (from /meta), handed to the display on
// its poll — so the tracker never has to talk to the board directly
let boardFace = null;

function publicDisplay() {
  const m = displayState.msg;
  return { screen: displayState.screen, msg: m && Date.now() - m.t < m.secs * 1000 ? m : null,
           emotion: displayState.emotion, restart: displayState.restart, view: displayState.view, zoom2: displayState.zoom2,
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
const loginFails = new Map();                   // ip → {n, until}: 5 wrong keys = 10 min wait
function clientIp(req) { return String(req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim(); }
function handleLogin(req, res) {
  const ip = clientIp(req), f = loginFails.get(ip);
  if (f && f.until > Date.now()) return send(res, 429, 'text/html; charset=utf-8', loginPage('Too many wrong keys. Try again in a few minutes.'));
  const chunks = [];
  req.on('data', (c) => { chunks.push(c); if (chunks.length > 4) req.destroy(); });
  req.on('end', () => {
    const key = new URLSearchParams(Buffer.concat(chunks).toString('utf8')).get('key') || '';
    if (!keyMatches(key.trim(), ADMIN_KEY)) {
      const n = (f && f.until <= Date.now() && f.n >= 5 ? 0 : (f ? f.n : 0)) + 1;
      loginFails.set(ip, { n, until: n >= 5 ? Date.now() + 10 * 60e3 : 0 });
      logEvent('privacy', 'Failed login attempt');
      return send(res, 401, 'text/html; charset=utf-8', loginPage('That key is not valid.'));
    }
    loginFails.delete(ip);
    res.writeHead(303, { Location: '/', 'Cache-Control': 'no-store',
      'Set-Cookie': `aya_session=${newSession()}; Path=/; Max-Age=${SESSION_DAYS * 86400}; HttpOnly; Secure; SameSite=Strict` });
    res.end();
  });
}

function handleCmd(req, res) {
  if (!sessionOk(req) && !keyMatches(req.headers['x-admin-key'], ADMIN_KEY)) return send(res, 401, 'text/plain', 'not logged in');
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
    if (cmd === 'restart_all') {       // the display (and its camera) picks it up on its next poll (≤2 s)
      displayState.restart = Date.now();
      logEvent('privacy', 'System restart');
      return send(res, 202, 'text/plain', 'restarting');
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
  const e = { t: Date.now(), kind, text };
  activity.unshift(e);
  if (activity.length > LOG_MAX) activity.pop();
  for (const s of metaSubscribers) s.write(`event: log\ndata: ${JSON.stringify(e)}\n\n`);
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
      if (f.id === 'known') logEvent('known', `${who} is here`);
      else { logEvent('stranger', 'Unknown person in view'); autoDescribe(); }
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
    seen.eye2 = Date.now();
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
    const f = Array.isArray(meta.faces) && meta.faces[0];       // the face, passed to the display on its poll
    if (f && [f.x, f.y, f.w, f.h].every(Number.isFinite)) {
      boardFace = { x: +((f.x + f.w / 2) * 2 - 1).toFixed(2), y: +((f.y + f.h / 2) * 2 - 1).toFixed(2), s: +f.w.toFixed(3),
                    id: String(f.id || ''), name: String(f.name || '').slice(0, 20), admin: !!f.admin, emo: String(f.emo || ''), t: Date.now() };
    }
    seen.tracker = Date.now();
    trackActivity(meta);
    for (const s of metaSubscribers) s.write(`data: ${latestMeta}\n\n`);
    send(res, 204, 'text/plain', '');
  });
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
  setTimeout(() => askVision(null).then((t) => logEvent('ai', t)).catch(() => {}), 1500);  // let them walk into view
}

function handleAsk(req, res) {
  if (!sessionOk(req)) return send(res, 401, 'application/json', JSON.stringify({ error: 'not logged in' }));
  const chunks = [];
  req.on('data', (c) => { chunks.push(c); if (chunks.length > 4) req.destroy(); });
  req.on('end', async () => {
    let q;
    try { q = String(JSON.parse(Buffer.concat(chunks).toString('utf8')).q || '').trim().slice(0, 200); }
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

function notePerson(req) {
  const [n, conf, dir] = String(req.headers['x-person'] || '').split(';');
  const count = parseInt(n, 10);
  if (!Number.isFinite(count)) return;
  if (personSeen !== null && count > personSeen) {
    let text = `Person detected · ${parseInt(conf, 10) || '?'}%`;
    if (dir === 'left' || dir === 'right') text += ` · moving ${dir}`;
    logEvent('person', text);
    autoDescribe();
  }
  personSeen = count;
}

function handleDisplayPost(req, res) {
  const chunks = [];
  let size = 0;
  req.on('data', (c) => { size += c.length; if (size > 4096) { req.destroy(); return; } chunks.push(c); });
  req.on('end', () => {
    const buf = Buffer.concat(chunks);
    seen.display = Date.now();
    notePerson(req);
    noteAf(req);
    if (buf.length === 1024) {
      const out = Buffer.alloc(1024);
      for (let y = 0; y < 64; y++)
        for (let x = 0; x < 128; x++)
          if (buf[(y >> 3) * 128 + x] & (1 << (y & 7))) out[y * 16 + (x >> 3)] |= 0x80 >> (x & 7);
      const b64 = out.toString('base64');
      oledFrame = b64;
      broadcast('oled', { f: b64 });               // every poll (~2 s), so the page knows it's live
    }
    send(res, 200, 'application/json', JSON.stringify(publicDisplay()));
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
  res.write(`event: display\ndata: ${JSON.stringify(publicDisplay())}\n\n`);
  if (lastAf) res.write(`event: af\ndata: ${JSON.stringify(lastAf)}\n\n`);
  if (oledFrame && Date.now() - seen.display < 10000) res.write(`event: oled\ndata: ${JSON.stringify({ f: oledFrame })}\n\n`);
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
           ...ages(), vision: { on: !!HF_TOKEN, used: (visionDay(), vision.used), limit: VISION_DAILY, err: vision.err } };
}

const server = http.createServer((req, res) => {
  const url = new URL(req.url, 'http://x');
  const key = url.searchParams.get('key');
  const device = keyMatches(key, VIEW_KEY);       // the display board's poll
  const authed = sessionOk(req);                  // a logged-in browser

  if (req.method === 'POST' && url.pathname === '/push') return handlePush(req, res);
  if (req.method === 'POST' && url.pathname === '/meta') return handleMeta(req, res);
  if (req.method === 'POST' && url.pathname === '/cmd') return handleCmd(req, res);
  if (req.method === 'POST' && url.pathname === '/login') return handleLogin(req, res);
  if (req.method === 'POST' && url.pathname === '/ask') return handleAsk(req, res);
  if (req.method === 'POST' && url.pathname === '/display') {
    if (!device) return send(res, 401, 'text/plain', 'bad key');
    return handleDisplayPost(req, res);
  }
  if (req.method !== 'GET' && req.method !== 'HEAD') return send(res, 405, 'text/plain', 'method not allowed');

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
      lastPollAt = Date.now();
      if (!latestFrame) return send(res, 503, 'text/plain', 'no frame yet');
      return send(res, 200, 'image/jpeg', latestFrame);
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
    case '/health':
      if (!authed) return send(res, 401, 'text/plain', 'bad key');
      return send(res, 200, 'application/json', JSON.stringify({ every: HEALTH_EVERY_MS, samples: healthSamples }));
    default:
      return send(res, 404, 'text/plain', 'not found');
  }
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
  .hours { display: flex; align-items: center; gap: 6px; font-size: 13px; color: var(--muted); }
  .hours select { background: var(--surface-2); color: var(--text); border: 1px solid var(--line); border-radius: 8px; padding: 5px; font: inherit; }
  .btn { background: var(--surface-2); border: 1px solid var(--line); border-radius: 10px; padding: 8px 12px; cursor: pointer; font-size: 13px; }
  .btn.primary { background: var(--accent); color: #04110f; border: 0; font-weight: 700; }
  .btn.danger { color: var(--bad); }
  .health { display: grid; grid-template-columns: repeat(2, 1fr); gap: 6px 12px; margin-top: 12px; font-size: 12px; color: var(--muted); }
  .health b { color: var(--text); font-weight: 600; font-variant-numeric: tabular-nums; }
  .locked { color: var(--muted); font-size: 13px; display: flex; align-items: center; justify-content: space-between; gap: 10px; }
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
  .unlock-form { display: flex; gap: 8px; width: 100%; }
  .unlock-form input { flex: 1; min-width: 0; background: var(--surface-2); color: var(--text); border: 1px solid var(--line);
                       border-radius: 10px; padding: 8px 10px; font: inherit; }
  .locked { flex-wrap: wrap; }
  .lock-link { background: none; border: 0; color: var(--muted); font-size: 12px; cursor: pointer; text-decoration: underline; padding: 0; }
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
      <button role="tab" data-tab="home" aria-selected="true"><span><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="3" y="3" width="7" height="9" rx="1.5"/><rect x="14" y="3" width="7" height="5" rx="1.5"/><rect x="14" y="12" width="7" height="9" rx="1.5"/><rect x="3" y="16" width="7" height="5" rx="1.5"/></svg></span>Home</button>
      <button role="tab" data-tab="display" aria-selected="false"><span><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="2" y="4" width="20" height="13" rx="2"/><path d="M8 21h8M12 17v4"/></svg></span>Display</button>
      <button role="tab" data-tab="camera" aria-selected="false"><span><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M15 10l5-3v10l-5-3z"/><rect x="2" y="6" width="13" height="12" rx="2"/></svg></span>Camera</button>
      <button role="tab" data-tab="health" aria-selected="false"><span><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M3 12h4l3-8 4 16 3-8h4"/></svg></span>Health</button>
    </nav>

    <div class="pane" data-pane="home" role="tabpanel">
      <section class="card" aria-label="System">
        <div class="card-head"><h2>System</h2><span class="mood" id="sys-sum">—</span></div>
        <div class="sys three">
          <div id="sys-cam"><i></i><span>Camera</span><small>–</small></div>
          <div id="sys-display"><i></i><span>Display</span><small>–</small></div>
          <div id="sys-tracker"><i></i><span>Face tracker</span><small>–</small></div>
        </div>
      </section>
      <section class="card" aria-label="AYA">
        <div class="card-head"><h2>AYA</h2><span class="mood" id="mood">—</span></div>
        <div class="robot-wrap" id="robot-wrap" hidden><canvas id="robot" width="128" height="64" aria-label="AYA's display, live"></canvas></div>
        <div class="slim" id="robot-off">The display's screen shows here while it's online.</div>
        <div class="meters" id="meters" hidden>
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

      <section class="card" aria-label="Ask AYA">
        <div class="card-head"><h2>Ask AYA</h2><span class="mood" id="ask-left">—</span></div>
        <form class="ask" id="ask-form">
          <input id="ask-q" maxlength="200" autocomplete="off" placeholder="Is anyone in the room? What's on the table?">
          <button class="btn primary" id="ask-go" type="submit">Ask</button>
        </form>
        <div class="ask-chips"><button class="btn" data-q="">What's happening?</button><button class="btn" data-q="Is anyone there?">Anyone there?</button><button class="btn" data-q="Is the light on?">Light on?</button></div>
        <div class="ask-a" id="ask-a" hidden></div>
      </section>

      <section class="card" aria-label="Activity">
        <div class="card-head"><h2>Activity</h2></div>
        <ol class="log" id="log"><li class="empty">Nothing yet</li></ol>
      </section>
    </div>

    <div class="pane" data-pane="display" role="tabpanel" hidden>
      <section class="card" aria-label="AYA controls">
        <div class="card-head"><h2>Talk to AYA</h2><span class="mood" id="disp-state">—</span></div>
        <div id="aria-controls">
          <div class="ctl"><div>Display<small>Turn the OLED screen on or off</small></div>
            <button class="switch" id="screen" role="switch" aria-checked="true" aria-label="Display on"></button></div>
          <div class="sub-h">Display shows</div>
          <div class="seg view-seg" id="view-seg">
            <button data-v="auto">Auto</button><button data-v="sage">Sage</button><button data-v="eyes">Eyes</button><button data-v="clock">Clock</button>
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

    <div class="pane" data-pane="camera" role="tabpanel" hidden>
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
          <div class="ctl keep"><div>Session<small>Signed in on this browser for 30 days</small></div><a class="btn" href="/logout">Sign out</a></div>
        </div>
      </section>
    </div>

    <div class="pane" data-pane="health" role="tabpanel" hidden>
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
  <span class="kbd">Keys: <b>1</b>–<b>4</b> tabs · <b>F</b> fullscreen · <b>S</b> snapshot</span></footer>
<div class="toasts" id="toasts" aria-live="polite"></div>

<script>
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
    if (name === 'health' && typeof renderHealth === 'function') renderHealth();   // charts need a visible width
  }
  document.querySelector('.tabs').addEventListener('click', function (e) {
    var b = e.target.closest('button'); if (b) showTab(b.dataset.tab);
  });
  try { var savedTab = localStorage.getItem('aria-tab'); if (savedTab && document.querySelector('[data-pane="' + savedTab + '"]')) showTab(savedTab); } catch (e) {}

  document.addEventListener('keydown', function (e) {
    if (e.ctrlKey || e.metaKey || e.altKey || /INPUT|TEXTAREA|SELECT/.test(document.activeElement.tagName)) return;
    var tabs = ['home', 'display', 'camera', 'health'];
    if (e.key >= '1' && e.key <= '4') showTab(tabs[+e.key - 1]);
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
      if (s.online) {
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
  es.onopen = function () { refresh(); };
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
        (r.energy < 0.3 ? 'Tired' : r.boredom > 0.5 ? 'Idle' : r.affection > 0.7 ? 'Engaged' : 'Calm');
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
  function rel(t) {
    var s = Math.round((Date.now() - t) / 1000);
    return s < 45 ? 'just now' : s < 3600 ? Math.round(s / 60) + ' min ago'
      : s < 86400 ? new Date(t).toLocaleTimeString([], { hour: 'numeric', minute: '2-digit' }) : new Date(t).toLocaleDateString();
  }
  setInterval(function () { document.querySelectorAll('#log time[data-t]').forEach(function (x) { x.textContent = rel(+x.dataset.t); }); }, 20000);
  var LOG_MAX = 20;
  function addLog(e) {
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
    if (on) { placeZones(); drawZones(); $('stage').scrollIntoView({ behavior: 'smooth', block: 'center' }); } else zoneEdit = null;
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
               screen: 'Display switched', restart_all: 'Restarting camera + display…', zoom2: 'Camera 2 zoom set',
             };
  async function send(cmd, args, extra) {
    try {
      var body = { cmd: cmd, args: args || [] };
      for (var k in (extra || {})) body[k] = extra[k];
      var r = await fetch('/cmd', { method: 'POST', headers: { 'Content-Type': 'application/json' },
                                    body: JSON.stringify(body) });
      if (r.status === 401) { location.reload(); return 401; }            // signed out: back to the sign-in page
      else if (r.status >= 400) toast('Not accepted: ' + (await r.text()), 'err');
      else toast(SENT[cmd] || 'Sent', 'ok');
      return r.status;
    } catch (e) { toast('Could not reach the server', 'err'); return 0; }
  }
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
  loadHealth(); setInterval(loadHealth, 30000);
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
