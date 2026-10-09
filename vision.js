'use strict';
// AYA's vision pipeline, in the relay: person/object detection (YOLO11n),
// face detection (YuNet) and face recognition (SFace) on each camera frame,
// producing the same "meta" the laptop tracker (esp32/face_tracker_v2.py)
// used to POST to /meta. Pure JS pre/post-processing; onnxruntime-node for
// the three models; jpeg-js to decode the frame.
//
//   const v = require('./vision');
//   await v.init({ modelsDir, faceDb });       // once
//   const meta = await v.analyze(jpegBuffer);  // null if a frame is already being analysed
//   v.stats()                                  // per-stage ms, frames, dropped, backend
//
// Everything that reads the result (handleMeta, trackActivity, the display's
// poll, the page) keeps working unchanged: the meta has exactly the tracker's
// keys and ranges. See VISION.md.

const fs = require('fs');
const path = require('path');
const jpeg = require('jpeg-js');

let ort = null;
try { ort = require('onnxruntime-node'); } catch (e) { console.error('[vision] onnxruntime-node unavailable: ' + e.message); }

// ── Tunables (the tracker's values) ─────────────────────────────────────
const YUNET_CONF = 0.65, YUNET_NMS = 0.3;             // cv2.FaceDetectorYN.create(..., 0.65, 0.3, 5000)
const MIN_FACE_FRAC = 0.07, FACE_AR_MIN = 0.55, FACE_AR_MAX = 1.5;   // is_face_shaped()
const RECOG_THRESHOLD = 0.363;                        // SFace cosine, sface_recognition.MATCH_THRESHOLD
const RECOG_INTERVAL_MS = 950;                        // the recogniser worker ran ~once a second
const YOLO_SIZE = 320, YOLO_CONF = 0.35, YOLO_IOU = 0.45, YOLO_MAX_DET = 300;   // detect_objects(frame, conf=0.35)
const OBJECT_KINDS = new Set(['cat', 'dog', 'bird', 'backpack', 'handbag', 'suitcase', 'umbrella',
  'cell phone', 'bottle', 'cup', 'knife', 'scissors', 'teddy bear', 'sports ball']);
const OBJECT_MIN_SCORE = 0.55, OBJECT_MAX_AREA = 0.35, OBJECT_HISTORY = 5, OBJECT_NEED = 3;
const LOWLIGHT_MEAN = 90, LOWLIGHT_GAMMA = 0.55;      // enhance_lowlight() when frame.mean() < 90
const FACE_CONFIRM_FRAMES = 2, SEARCH_AFTER_MS = 6000, UNKNOWN_AFTER_MS = 3000;
const STALE_MS = 1500;                                // bodies_now()/objects_now() drop results older than this
const TRACK_GAP_MS = 1500;                            // a face seen again within this is the same person

const COCO = ['person', 'bicycle', 'car', 'motorcycle', 'airplane', 'bus', 'train', 'truck', 'boat', 'traffic light',
  'fire hydrant', 'stop sign', 'parking meter', 'bench', 'bird', 'cat', 'dog', 'horse', 'sheep', 'cow', 'elephant', 'bear',
  'zebra', 'giraffe', 'backpack', 'umbrella', 'handbag', 'tie', 'suitcase', 'frisbee', 'skis', 'snowboard', 'sports ball',
  'kite', 'baseball bat', 'baseball glove', 'skateboard', 'surfboard', 'tennis racket', 'bottle', 'wine glass', 'cup',
  'fork', 'knife', 'spoon', 'bowl', 'banana', 'apple', 'sandwich', 'orange', 'broccoli', 'carrot', 'hot dog', 'pizza',
  'donut', 'cake', 'chair', 'couch', 'potted plant', 'bed', 'dining table', 'toilet', 'tv', 'laptop', 'mouse', 'remote',
  'keyboard', 'cell phone', 'microwave', 'oven', 'toaster', 'sink', 'refrigerator', 'book', 'clock', 'vase', 'scissors',
  'teddy bear', 'hair drier', 'toothbrush'];

// ── State ────────────────────────────────────────────────────────────────
const sessions = { yunet: null, sface: null, yolo: null };
const disabled = { yunet: false, sface: false, yolo: false };
let faceDb = { names: [], embeddings: [] };           // embeddings: Float32Array[128] each, L2-normalised
let admins = new Set(['amrit']);
let yoloEvery = 1;
let busy = false;
let ready = false;
const stats = { frames: 0, dropped: 0, errors: 0, backend: 'none', ms: {}, rss: 0 };
const timings = { decode: [], enhance: [], yunet: [], sface: [], yolo: [], total: [] };
function tick(stage, t0) {
  const dt = Number(process.hrtime.bigint() - t0) / 1e6;
  const a = timings[stage]; a.push(dt); if (a.length > 400) a.shift();
  return dt;
}
function summary(a) {
  if (!a.length) return null;
  const s = a.slice().sort((x, y) => x - y);
  const mean = s.reduce((p, c) => p + c, 0) / s.length;
  return { mean: +mean.toFixed(1), p95: +s[Math.min(s.length - 1, Math.floor(s.length * 0.95))].toFixed(1), n: s.length };
}

// Temporal state (the tracker's presence / identity logic)
const st = {
  lastFaceT: -1e12, faceConfirm: 0, present: false, arrivedAt: 0, seenKnown: false,
  track: null,                       // {id, box:[x,y,w,h] px, t, name, conf}  (ByteTrack-style name pinning)
  nextTrackId: 1,
  recog: { name: null, conf: 0, t: 0 },   // _recog_out
  lastRecogT: 0,
  objHist: [],                       // _obj_hist
  lastYolo: { bodies: [], objects: [], t: -1e12 },
  frameIdx: 0,
};

// ── Images: {w, h, bgr: Uint8Array(w*h*3)} ───────────────────────────────
function decodeJpeg(buf) {
  const d = jpeg.decode(buf, { useTArray: true, formatAsRGBA: true, tolerantDecoding: true, maxMemoryUsageInMB: 64 });
  const n = d.width * d.height, bgr = new Uint8Array(n * 3), s = d.data;
  for (let i = 0, j = 0; i < n; i++, j += 4) { bgr[i * 3] = s[j + 2]; bgr[i * 3 + 1] = s[j + 1]; bgr[i * 3 + 2] = s[j]; }
  return { w: d.width, h: d.height, bgr };
}

// Mean over all channels (frame.mean())
function meanOf(img) {
  let s = 0; const a = img.bgr;
  for (let i = 0; i < a.length; i++) s += a[i];
  return s / a.length;
}

// sRGB 8-bit → CIE L* scaled to 0..255 (OpenCV's 8-bit Lab L channel), and back
const GREY_TO_L = new Uint8Array(256), L_TO_GREY = new Uint8Array(256);
(function () {
  const lin = (c) => { c /= 255; return c <= 0.04045 ? c / 12.92 : Math.pow((c + 0.055) / 1.055, 2.4); };
  const Ls = new Float64Array(256);
  for (let i = 0; i < 256; i++) {
    const y = lin(i), f = y > 0.008856 ? Math.cbrt(y) : 7.787 * y + 16 / 116;
    Ls[i] = Math.max(0, 116 * f - 16) * 255 / 100;
    GREY_TO_L[i] = Math.min(255, Math.round(Ls[i]));
  }
  for (let L = 0; L < 256; L++) {          // inverse by nearest
    let best = 0, bd = 1e9;
    for (let i = 0; i < 256; i++) { const d = Math.abs(Ls[i] - L); if (d < bd) { bd = d; best = i; } }
    L_TO_GREY[L] = best;
  }
})();
const GAMMA_LUT = new Uint8Array(256);
for (let i = 0; i < 256; i++) GAMMA_LUT[i] = Math.floor(Math.pow(i / 255, LOWLIGHT_GAMMA) * 255);

// OpenCV CLAHE (clipLimit 4, 8x8 tiles) on one 8-bit plane
function clahe(src, w, h, tilesX = 8, tilesY = 8, clipLimit = 4.0) {
  const tw = Math.ceil(w / tilesX), th = Math.ceil(h / tilesY);      // (frames are 160x120: exact 20x15 tiles)
  const area = tw * th, lutScale = 255 / area;
  const clip = Math.max(1, Math.floor(clipLimit * area / 256));
  const luts = new Uint8Array(tilesX * tilesY * 256);
  const hist = new Int32Array(256);
  for (let ty = 0; ty < tilesY; ty++) for (let tx = 0; tx < tilesX; tx++) {
    hist.fill(0);
    for (let y = ty * th; y < (ty + 1) * th; y++) {
      const yy = Math.min(y, 2 * h - 2 - y);                           // reflect-101 past the edge (never hit at 160x120)
      for (let x = tx * tw; x < (tx + 1) * tw; x++) hist[src[yy * w + Math.min(x, 2 * w - 2 - x)]]++;
    }
    let clipped = 0;
    for (let i = 0; i < 256; i++) if (hist[i] > clip) { clipped += hist[i] - clip; hist[i] = clip; }
    const batch = Math.floor(clipped / 256); let residual = clipped - batch * 256;
    for (let i = 0; i < 256; i++) hist[i] += batch;
    if (residual) { const step = Math.max(Math.floor(256 / residual), 1); for (let i = 0; i < 256 && residual > 0; i += step) { hist[i]++; residual--; } }
    const base = (ty * tilesX + tx) * 256; let sum = 0;
    for (let i = 0; i < 256; i++) { sum += hist[i]; luts[base + i] = Math.min(255, Math.round(sum * lutScale)); }
  }
  const out = new Uint8Array(w * h);
  for (let y = 0; y < h; y++) {
    const tyf = (y + 0.5) / th - 0.5; let ty1 = Math.floor(tyf), ty2 = ty1 + 1; const ya = tyf - ty1;
    ty1 = Math.max(ty1, 0); ty2 = Math.min(ty2, tilesY - 1);
    for (let x = 0; x < w; x++) {
      const txf = (x + 0.5) / tw - 0.5; let tx1 = Math.floor(txf), tx2 = tx1 + 1; const xa = txf - tx1;
      tx1 = Math.max(tx1, 0); tx2 = Math.min(tx2, tilesX - 1);
      const v = src[y * w + x];
      const r = (luts[(ty1 * tilesX + tx1) * 256 + v] * (1 - xa) + luts[(ty1 * tilesX + tx2) * 256 + v] * xa) * (1 - ya) +
                (luts[(ty2 * tilesX + tx1) * 256 + v] * (1 - xa) + luts[(ty2 * tilesX + tx2) * 256 + v] * xa) * ya;
      out[y * w + x] = Math.min(255, Math.round(r));
    }
  }
  return out;
}

// enhance_lowlight(): CLAHE on L (of Lab) then a gamma lift. Frames are grey
// (B=G=R), so L comes straight from the grey level; a colour pixel is scaled
// by the same ratio its luminance changed.
function enhanceLowlight(img) {
  const { w, h, bgr } = img, n = w * h, grey = new Uint8Array(n), L = new Uint8Array(n);
  for (let i = 0; i < n; i++) {
    const b = bgr[i * 3], g = bgr[i * 3 + 1], r = bgr[i * 3 + 2];
    grey[i] = (b === g && g === r) ? b : Math.round(0.114 * b + 0.587 * g + 0.299 * r);
    L[i] = GREY_TO_L[grey[i]];
  }
  const L2 = clahe(L, w, h);
  const out = new Uint8Array(n * 3);
  for (let i = 0; i < n; i++) {
    const g2 = L_TO_GREY[L2[i]];
    if (bgr[i * 3] === bgr[i * 3 + 1] && bgr[i * 3 + 1] === bgr[i * 3 + 2]) { out[i * 3] = out[i * 3 + 1] = out[i * 3 + 2] = GAMMA_LUT[g2]; continue; }
    const k = grey[i] ? g2 / grey[i] : 1;
    for (let c = 0; c < 3; c++) out[i * 3 + c] = GAMMA_LUT[Math.min(255, Math.round(bgr[i * 3 + c] * k))];
  }
  return { w, h, bgr: out };
}

// ── Model loading ────────────────────────────────────────────────────────
async function loadSession(name, file) {
  if (!ort) { disabled[name] = true; return null; }
  try {
    if (!fs.existsSync(file)) throw new Error('missing ' + file);
    const s = await ort.InferenceSession.create(file, {
      graphOptimizationLevel: 'all', intraOpNumThreads: 1, interOpNumThreads: 1,
      executionMode: 'sequential', enableCpuMemArena: true, enableMemPattern: true, logSeverityLevel: 3,
    });
    return s;
  } catch (e) {
    console.error(`[vision] ${name} unavailable (${e.message}) — stage skipped`);
    disabled[name] = true;
    return null;
  }
}

function loadFaceDb(opt) {
  let js = opt.faceDb || null;
  try {
    if (!js && process.env.FACE_DB_JSON) js = JSON.parse(Buffer.from(process.env.FACE_DB_JSON, 'base64').toString('utf8'));
    else if (!js && process.env.FACE_DB_PATH) js = JSON.parse(fs.readFileSync(process.env.FACE_DB_PATH, 'utf8'));
  } catch (e) { console.error('[vision] face DB unreadable: ' + e.message); js = null; }
  const names = [], embs = [];
  if (js && Array.isArray(js.names) && Array.isArray(js.embeddings)) {
    for (let i = 0; i < Math.min(js.names.length, js.embeddings.length); i++) {
      const e = Float32Array.from(js.embeddings[i]);
      if (e.length !== 128) continue;
      let n = 0; for (let k = 0; k < 128; k++) n += e[k] * e[k];
      n = Math.sqrt(n) || 1; for (let k = 0; k < 128; k++) e[k] /= n;
      names.push(String(js.names[i])); embs.push(e);
    }
  }
  faceDb = { names, embeddings: embs };
}

async function init(opt = {}) {
  const modelsDir = opt.modelsDir || process.env.VISION_MODELS_DIR || path.join(__dirname, 'models');
  admins = new Set(String(opt.admins || process.env.VISION_ADMINS || 'Amrit').split(',').map((s) => s.trim().toLowerCase()).filter(Boolean));
  yoloEvery = Math.max(1, Number(opt.yoloEvery || process.env.VISION_YOLO_EVERY || 1) | 0);
  const off = new Set(String(opt.disable || process.env.VISION_DISABLE || '').split(',').map((s) => s.trim()).filter(Boolean));
  for (const k of off) if (k in disabled) disabled[k] = true;
  loadFaceDb(opt);
  if (!disabled.yunet) sessions.yunet = await loadSession('yunet', path.join(modelsDir, 'face_detection_yunet.onnx'));
  if (!disabled.sface) sessions.sface = await loadSession('sface', path.join(modelsDir, 'face_recognition_sface_2021dec.onnx'));
  if (!disabled.yolo) sessions.yolo = await loadSession('yolo', path.join(modelsDir, 'yolo11n.onnx'));
  stats.backend = ort ? 'onnxruntime-node cpu' : 'none';
  ready = true;
  console.log(`[vision] ready: yunet=${!!sessions.yunet} sface=${!!sessions.sface} yolo=${!!sessions.yolo} enrolled=${faceDb.names.length} admins=${[...admins].join(',')}`);
  return { yunet: !!sessions.yunet, sface: !!sessions.sface, yolo: !!sessions.yolo, enrolled: faceDb.names.length };
}

// ── YuNet face detection (OpenCV's FaceDetectorYN decode) ───────────────
// Returns rows [x, y, w, h, 5 x (lx, ly), score] in frame pixels, NMS'd.
async function detectFaces(img, scoreThr = YUNET_CONF, nmsThr = YUNET_NMS) {
  const s = sessions.yunet; if (!s) return [];
  const { w, h, bgr } = img;
  const padW = (Math.floor((w - 1) / 32) + 1) * 32, padH = (Math.floor((h - 1) / 32) + 1) * 32;
  const blob = new Float32Array(3 * padH * padW);                      // zero-padded bottom/right, BGR, 0..255
  for (let c = 0; c < 3; c++) for (let y = 0; y < h; y++) {
    const o = c * padH * padW + y * padW, r = y * w * 3 + c;
    for (let x = 0; x < w; x++) blob[o + x] = bgr[r + x * 3];
  }
  const out = await s.run({ input: new ort.Tensor('float32', blob, [1, 3, padH, padW]) });
  const faces = [];
  for (const stride of [8, 16, 32]) {
    const cols = padW / stride, rows = padH / stride;
    const cls = out['cls_' + stride].data, obj = out['obj_' + stride].data, bb = out['bbox_' + stride].data, kp = out['kps_' + stride].data;
    for (let r = 0; r < rows; r++) for (let c = 0; c < cols; c++) {
      const i = r * cols + c;
      const sc = Math.sqrt(Math.min(1, Math.max(0, cls[i])) * Math.min(1, Math.max(0, obj[i])));
      if (sc < scoreThr) continue;
      const cx = (c + bb[i * 4]) * stride, cy = (r + bb[i * 4 + 1]) * stride;
      const bw = Math.exp(bb[i * 4 + 2]) * stride, bh = Math.exp(bb[i * 4 + 3]) * stride;
      const row = [cx - bw / 2, cy - bh / 2, bw, bh];
      for (let k = 0; k < 5; k++) row.push((c + kp[i * 10 + 2 * k]) * stride, (r + kp[i * 10 + 2 * k + 1]) * stride);
      row.push(sc);
      faces.push(row);
    }
  }
  // cv2.dnn.NMSBoxes on int boxes (Rect2i), greedy by score
  faces.sort((a, b) => b[14] - a[14]);
  const keep = [];
  for (const f of faces) {
    const ax = Math.trunc(f[0]), ay = Math.trunc(f[1]), aw = Math.trunc(f[2]), ah = Math.trunc(f[3]);
    let ok = true;
    for (const k of keep) {
      const bx = Math.trunc(k[0]), by = Math.trunc(k[1]), bw = Math.trunc(k[2]), bh = Math.trunc(k[3]);
      const iw = Math.max(0, Math.min(ax + aw, bx + bw) - Math.max(ax, bx)), ih = Math.max(0, Math.min(ay + ah, by + bh) - Math.max(ay, by));
      const inter = iw * ih, uni = aw * ah + bw * bh - inter;
      if (uni > 0 && inter / uni > nmsThr) { ok = false; break; }
    }
    if (ok) keep.push(f);
  }
  return keep;
}

function headYaw(r) {                      // head_yaw(): nose offset from the eyes' midpoint over the eye distance
  const rex = r[4], lex = r[6], nx = r[8], d = Math.abs(lex - rex);
  if (d < 1) return 0;
  return Math.max(-1, Math.min(1, (nx - (rex + lex) / 2) / d * 2));
}

// ── SFace recognition (OpenCV's FaceRecognizerSF alignCrop + feature) ───
const SFACE_DST = [[38.2946, 51.6963], [73.5318, 51.5014], [56.0252, 71.7366], [41.5493, 92.3655], [70.7299, 92.2041]];
const SFACE_DST_MEAN = [56.0262, 71.9008];
function similarityTransform(src) {       // src: 5 x [x, y] → 2x3 affine mapping src → the 112x112 template
  let mx = 0, my = 0;
  for (const p of src) { mx += p[0]; my += p[1]; }
  mx /= 5; my /= 5;
  let a00 = 0, a01 = 0, a10 = 0, a11 = 0, vr = 0;
  for (let i = 0; i < 5; i++) {
    const sx = src[i][0] - mx, sy = src[i][1] - my, dx = SFACE_DST[i][0] - SFACE_DST_MEAN[0], dy = SFACE_DST[i][1] - SFACE_DST_MEAN[1];
    a00 += dx * sx; a01 += dx * sy; a10 += dy * sx; a11 += dy * sy; vr += sx * sx + sy * sy;
  }
  a00 /= 5; a01 /= 5; a10 /= 5; a11 /= 5; vr /= 5;
  // Umeyama: the rotation closest to A (= U diag(1, sign det) Vt) and scale = trace(diag(S) d) / var
  const th = Math.atan2(a10 - a01, a00 + a11), cs = Math.cos(th), sn = Math.sin(th);
  const scale = ((a00 + a11) * cs + (a10 - a01) * sn) / vr;
  const m00 = scale * cs, m01 = -scale * sn, m10 = scale * sn, m11 = scale * cs;
  return [m00, m01, SFACE_DST_MEAN[0] - (m00 * mx + m01 * my), m10, m11, SFACE_DST_MEAN[1] - (m10 * mx + m11 * my)];
}
// warpAffine(src, M, 112x112): bilinear, zero border; returns CHW float BGR
function alignCrop(img, row, size = 112) {
  const M = similarityTransform([[row[4], row[5]], [row[6], row[7]], [row[8], row[9]], [row[10], row[11]], [row[12], row[13]]]);
  const det = M[0] * M[4] - M[1] * M[3];
  const i00 = M[4] / det, i01 = -M[1] / det, i10 = -M[3] / det, i11 = M[0] / det;
  const i02 = -(i00 * M[2] + i01 * M[5]), i12 = -(i10 * M[2] + i11 * M[5]);
  const { w, h, bgr } = img, out = new Float32Array(3 * size * size), plane = size * size;
  for (let y = 0; y < size; y++) for (let x = 0; x < size; x++) {
    const sx = i00 * x + i01 * y + i02, sy = i10 * x + i11 * y + i12;
    const x0 = Math.floor(sx), y0 = Math.floor(sy), fx = sx - x0, fy = sy - y0;
    for (let c = 0; c < 3; c++) {
      const px = (xx, yy) => (xx < 0 || yy < 0 || xx >= w || yy >= h) ? 0 : bgr[(yy * w + xx) * 3 + c];
      const v = (px(x0, y0) * (1 - fx) + px(x0 + 1, y0) * fx) * (1 - fy) + (px(x0, y0 + 1) * (1 - fx) + px(x0 + 1, y0 + 1) * fx) * fy;
      out[c * plane + y * size + x] = v;
    }
  }
  return out;
}
async function embedFace(img, row) {      // L2-normalised 128-d SFace feature, or null
  const s = sessions.sface; if (!s) return null;
  const crop = alignCrop(img, row);
  const out = await s.run({ data: new ort.Tensor('float32', crop, [1, 3, 112, 112]) });
  const f = Float32Array.from(out.fc1.data);
  let n = 0; for (let k = 0; k < 128; k++) n += f[k] * f[k];
  n = Math.sqrt(n) + 1e-9; for (let k = 0; k < 128; k++) f[k] /= n;
  return f;
}
function matchFace(emb) {                 // {name|null, score}: best cosine over the enrolled DB, threshold 0.363
  let best = -1, bi = -1;
  for (let i = 0; i < faceDb.embeddings.length; i++) {
    const e = faceDb.embeddings[i]; let d = 0;
    for (let k = 0; k < 128; k++) d += e[k] * emb[k];
    if (d > best) { best = d; bi = i; }
  }
  if (bi < 0) return { name: null, score: 0 };
  return { name: best >= RECOG_THRESHOLD ? faceDb.names[bi] : null, score: +best.toFixed(3) };
}

// ── YOLO11n objects (ultralytics letterbox + decode + per-class NMS) ─────
// Returns [{label, score, box:[x, y, w, h] px}] best first.
async function detectObjects(img) {
  const s = sessions.yolo; if (!s) return [];
  const { w, h, bgr } = img, S = YOLO_SIZE;
  const gain = Math.min(S / h, S / w), nw = Math.round(w * gain), nh = Math.round(h * gain);
  const padX = Math.round((S - nw) / 2 - 0.1), padY = Math.round((S - nh) / 2 - 0.1);
  const blob = new Float32Array(3 * S * S).fill(114 / 255), plane = S * S;
  const sx = w / nw, sy = h / nh;                                     // cv2.resize INTER_LINEAR, then BGR→RGB, /255
  for (let y = 0; y < nh; y++) {
    const fy = Math.min(h - 1, Math.max(0, (y + 0.5) * sy - 0.5)), y0 = Math.floor(fy), y1 = Math.min(h - 1, y0 + 1), wy = fy - y0;
    for (let x = 0; x < nw; x++) {
      const fx = Math.min(w - 1, Math.max(0, (x + 0.5) * sx - 0.5)), x0 = Math.floor(fx), x1 = Math.min(w - 1, x0 + 1), wx = fx - x0;
      const o = (y + padY) * S + x + padX;
      for (let c = 0; c < 3; c++) {
        const v = (bgr[(y0 * w + x0) * 3 + c] * (1 - wx) + bgr[(y0 * w + x1) * 3 + c] * wx) * (1 - wy) +
                  (bgr[(y1 * w + x0) * 3 + c] * (1 - wx) + bgr[(y1 * w + x1) * 3 + c] * wx) * wy;
        blob[(2 - c) * plane + o] = v / 255;
      }
    }
  }
  const out = await s.run({ images: new ort.Tensor('float32', blob, [1, 3, S, S]) });
  const o = out[Object.keys(out)[0]], d = o.data, nc = o.dims[1] - 4, na = o.dims[2];
  const cands = [];
  for (let i = 0; i < na; i++) {
    let best = 0, bc = -1;
    for (let c = 0; c < nc; c++) { const v = d[(4 + c) * na + i]; if (v > best) { best = v; bc = c; } }
    if (best <= YOLO_CONF) continue;
    const cx = d[i], cy = d[na + i], bw = d[2 * na + i], bh = d[3 * na + i];
    cands.push({ c: bc, s: best, x1: cx - bw / 2, y1: cy - bh / 2, x2: cx + bw / 2, y2: cy + bh / 2 });
  }
  cands.sort((a, b) => b.s - a.s);
  const keep = [];
  for (const a of cands) {
    let ok = true;
    for (const k of keep) {
      if (k.c !== a.c) continue;
      const iw = Math.max(0, Math.min(a.x2, k.x2) - Math.max(a.x1, k.x1)), ih = Math.max(0, Math.min(a.y2, k.y2) - Math.max(a.y1, k.y1));
      const inter = iw * ih, uni = (a.x2 - a.x1) * (a.y2 - a.y1) + (k.x2 - k.x1) * (k.y2 - k.y1) - inter;
      if (inter / uni > YOLO_IOU) { ok = false; break; }
    }
    if (ok) { keep.push(a); if (keep.length >= YOLO_MAX_DET) break; }
  }
  return keep.map((a) => {                                            // scale_boxes: un-pad, un-scale, clip
    const x1 = Math.min(w, Math.max(0, (a.x1 - padX) / gain)), y1 = Math.min(h, Math.max(0, (a.y1 - padY) / gain));
    const x2 = Math.min(w, Math.max(0, (a.x2 - padX) / gain)), y2 = Math.min(h, Math.max(0, (a.y2 - padY) / gain));
    return { label: COCO[a.c] || String(a.c), score: +a.s.toFixed(3), box: [Math.trunc(x1), Math.trunc(y1), Math.trunc(x2 - x1), Math.trunc(y2 - y1)] };
  });
}

function iouF(a, b) {
  const ix = Math.max(0, Math.min(a.x + a.w, b.x + b.w) - Math.max(a.x, b.x));
  const iy = Math.max(0, Math.min(a.y + a.h, b.y + b.h) - Math.max(a.y, b.y));
  const inter = ix * iy, uni = a.w * a.h + b.w * b.h - inter;
  return uni > 0 ? inter / uni : 0;
}
function stableObjects(raw) {              // _stable_objects(): same kind, overlapping, in 3 of the last 5 passes
  st.objHist.push(raw);
  if (st.objHist.length > OBJECT_HISTORY) st.objHist.splice(0, st.objHist.length - OBJECT_HISTORY);
  const keep = [];
  for (const o of raw) {
    let hits = 0;
    for (const past of st.objHist) if (past.some((p) => p.label === o.label && iouF(p, o) > 0.3)) hits++;
    if (hits >= OBJECT_NEED) keep.push(o);
  }
  return keep.slice(0, 6);
}

const r3 = (v) => Math.round(v * 1000) / 1000;

// ── The frame → meta ─────────────────────────────────────────────────────
async function analyze(jpegBuf, opt = {}) {
  if (!ready || busy) { stats.dropped++; return null; }
  busy = true;
  const T0 = process.hrtime.bigint();
  const now = Number.isFinite(opt.t) ? opt.t : Date.now();
  try {
    let t0 = process.hrtime.bigint();
    let img = decodeJpeg(jpegBuf);
    tick('decode', t0);
    const w = img.w, h = img.h;
    t0 = process.hrtime.bigint();
    if (meanOf(img) < LOWLIGHT_MEAN) img = enhanceLowlight(img);
    tick('enhance', t0);
    st.frameIdx++;

    // Faces (YuNet at native size), gated like the tracker's is_face_shaped
    t0 = process.hrtime.bigint();
    const rows = await detectFaces(img);
    const dnnFaces = [];
    let yaw = 0, bestArea = 0;
    for (const r of rows) {
      let x1 = Math.max(0, Math.trunc(r[0])), y1 = Math.max(0, Math.trunc(r[1]));
      const bw = Math.min(w - x1, Math.trunc(r[2])), bh = Math.min(h - y1, Math.trunc(r[3]));
      if (bw <= 0 || bh <= 0 || bw / w < MIN_FACE_FRAC) continue;
      const ar = bw / bh;
      if (ar < FACE_AR_MIN || ar > FACE_AR_MAX) continue;
      dnnFaces.push({ x: x1, y: y1, w: bw, h: bh, row: r });
      if (bw * bh > bestArea) { bestArea = bw * bh; yaw = headYaw(r); }
    }
    tick('yunet', t0);
    const face = dnnFaces.length ? dnnFaces.reduce((a, b) => (b.w * b.h > a.w * a.h ? b : a)) : null;

    // Same person as last frame? (ByteTrack stood in for this on the laptop)
    if (face) {
      const tr = st.track;
      const same = tr && now - tr.t <= TRACK_GAP_MS && iouF(tr.box, face) > 0.2;
      if (same) { tr.box = { x: face.x, y: face.y, w: face.w, h: face.h }; tr.t = now; }
      else st.track = { id: st.nextTrackId++, box: { x: face.x, y: face.y, w: face.w, h: face.h }, t: now, name: null, conf: 0 };
      if (!same) st.recog = { name: null, conf: 0, t: 0 };            // a new face: don't carry the last person's name over
    }

    // Recognition (~once a second, sooner on a face we haven't named yet)
    if (face && sessions.sface && faceDb.names.length) {
      const due = !st.track.tried || now - st.lastRecogT >= (st.track.name ? RECOG_INTERVAL_MS : Math.min(RECOG_INTERVAL_MS, 300));
      if (due) {
        t0 = process.hrtime.bigint();
        st.lastRecogT = now; st.track.tried = true;
        try {
          const emb = await embedFace(img, face.row);
          const m = emb ? matchFace(emb) : { name: null, score: 0 };
          st.recog = { name: m.name, conf: m.score, t: now };
        } catch (e) { if (!analyze._warned) { analyze._warned = true; console.error('[vision] recognition error (treating as unknown): ' + e.message); } st.recog = { name: null, conf: 0, t: now }; }
        tick('sface', t0);                                            // timed only when it runs
      }
    }

    // People + objects (every frame, or every Nth with the last result reused while fresh)
    t0 = process.hrtime.bigint();
    if (sessions.yolo && (st.frameIdx % yoloEvery === 0 || now - st.lastYolo.t > STALE_MS)) {
      let bodies = [], objects = [];
      try {
        const found = await detectObjects(img);
        bodies = found.filter((o) => o.label === 'person').map((p) => [r3(p.box[0] / w), r3(p.box[1] / h), r3(p.box[2] / w), r3(p.box[3] / h)]);
        const raw = found.filter((o) => OBJECT_KINDS.has(o.label) && o.score >= OBJECT_MIN_SCORE)
          .map((o) => ({ label: o.label, score: o.score, x: r3(o.box[0] / w), y: r3(o.box[1] / h), w: r3(o.box[2] / w), h: r3(o.box[3] / h) }))
          .filter((o) => o.w * o.h <= OBJECT_MAX_AREA);
        objects = stableObjects(raw);
      } catch (e) { stats.errors++; if (!detectObjects._warned) { detectObjects._warned = true; console.error('[vision] body detection error: ' + e.message); } }
      st.lastYolo = { bodies, objects, t: now };
    }
    tick('yolo', t0);
    const fresh = now - st.lastYolo.t < STALE_MS;
    const bodies = fresh ? st.lastYolo.bodies : [], objects = fresh ? st.lastYolo.objects : [];

    // Presence (the tracker's present / seen_known / arrived_at)
    const hasFace = !!face;
    if (hasFace) { st.lastFaceT = now; st.faceConfirm++; } else st.faceConfirm = 0;
    if (hasFace && !st.present && st.faceConfirm >= FACE_CONFIRM_FRAMES) { st.present = true; st.seenKnown = false; st.arrivedAt = now; }
    else if (st.present && now - st.lastFaceT > SEARCH_AFTER_MS) { st.present = false; st.track = null; st.recog = { name: null, conf: 0, t: 0 }; }

    // Name: a fresh recognition names the track; a miss keeps the track's last name (anti-flicker)
    let recName = st.recog.name, recConf = st.recog.conf;
    if (hasFace) {
      if (recName) { st.track.name = recName; st.track.conf = recConf; }
      else if (st.track.name) { recName = st.track.name; recConf = st.track.conf; }
    }
    if (recName) st.seenKnown = true;

    const meta = { faces: [], n: dnnFaces.length, bodies, objects, gesture: null, hand: null, robot: null, face_frame: null };
    if (hasFace) {
      const enrolled = faceDb.names.length > 0 && !!sessions.sface;
      const ident = recName ? 'known'
        : (st.present && enrolled && !st.seenKnown && now - st.arrivedAt > UNKNOWN_AFTER_MS) ? 'unknown' : 'identifying';
      const isAdmin = !!recName && admins.has(recName.toLowerCase());
      meta.faces.push({
        x: r3(face.x / w), y: r3(face.y / h), w: r3(face.w / w), h: r3(face.h / h),
        id: ident, name: recName || '', emo: 'neutral',
        look: Math.abs(yaw) < 0.25 ? 1 : 0, admin: isAdmin,
      });
    }
    stats.frames++;
    return meta;
  } catch (e) {
    stats.errors++;
    if (!analyze._err) { analyze._err = true; console.error('[vision] analyze failed: ' + (e && e.stack || e)); }
    return null;
  } finally {
    tick('total', T0);
    busy = false;
  }
}

function getStats() {
  const ms = {};
  for (const k of Object.keys(timings)) { const s = summary(timings[k]); if (s) ms[k] = s; }
  return { frames: stats.frames, dropped: stats.dropped, errors: stats.errors, backend: stats.backend, ms,
    stages: { yunet: !!sessions.yunet, sface: !!sessions.sface, yolo: !!sessions.yolo }, enrolled: faceDb.names.length,
    rssMB: Math.round(process.memoryUsage().rss / 1048576), busy };
}

function resetState() {                   // for tests: forget presence / tracks / object history
  Object.assign(st, { lastFaceT: -1e12, faceConfirm: 0, present: false, arrivedAt: 0, seenKnown: false, track: null,
    recog: { name: null, conf: 0, t: 0 }, lastRecogT: 0, objHist: [], lastYolo: { bodies: [], objects: [], t: -1e12 }, frameIdx: 0 });
}

module.exports = { init, analyze, stats: getStats, resetState,
  _internal: { decodeJpeg, enhanceLowlight, clahe, detectFaces, embedFace, matchFace, alignCrop, detectObjects, headYaw, sessions } };
