'use strict';
// AYA's brain: a language model (Groq, OpenAI-compatible API) that can use AYA's abilities as tools.
//
//   - Chat (POST /ask): plain-language questions and commands. The model calls tools — move the head,
//     look and describe, read the event memory, change modes, show a message, add a rule… — and answers.
//   - Seeing: describes the current camera frame (a vision model), on request and for gallery events.
//   - Memory: every event (activity log) kept here, reloaded from AYA's SD card (/aya/log/<day>.jsonl)
//     after a relay restart; "notes" she was told to remember.
//   - Smart alerts: motion with no person seen gets a look by the vision model; only notable things alert.
//   - Rules: plain-language rules ("if someone comes in after 11 pm, alert me and look at the door"),
//     turned into structured triggers/actions by the model and run on each event.
//   - Summaries: "since you were away" (GET /brain/brief) and a nightly digest.
// Rules and notes are saved on AYA's SD card (/aya/brain/*.json, written through the display's poll);
// Render's free disk doesn't survive a restart.
//
// Env: GROQ_API_KEY (required), GROQ_MODEL (default qwen/qwen3.8-27b: tools + vision),
//      GROQ_TEXT_MODEL (fallback for text-only work), GROQ_BASE (tests), GROQ_RPM / GROQ_RPD (budget),
//      AYA_TZ (default Asia/Kolkata).

const KEY = process.env.GROQ_API_KEY || '';
const BASE = process.env.GROQ_BASE || 'https://api.groq.com/openai/v1';
const MODEL = process.env.GROQ_MODEL || 'qwen/qwen3.8-27b';
const TEXT_MODEL = process.env.GROQ_TEXT_MODEL || 'openai/gpt-oss-120b';
const RPM = +process.env.GROQ_RPM || 25;
const RPD = +process.env.GROQ_RPD || 900;
const TZ = process.env.AYA_TZ || 'Asia/Kolkata';

const MEM_MAX = 5000;
const RULES_FILE = '/aya/brain/rules.json', NOTES_FILE = '/aya/brain/notes.json', MAP_FILE = '/aya/brain/map.json';
const MOODS = { nod: ['nod', null], shake: ['shake', null], think: ['curious', 'think'], happy: ['nod', 'giggle'], sad: [null, 'shy'] };

module.exports = function createBrain(ctx) {
  // ctx: { applyCmd(cmd,args,body)→[code,text], status()→obj, frame()→{buf,at}|null, logEvent(kind,text),
  //        sdGet(path)→Promise<{ok,body}>, sdPut(path,text)→Promise<{ok,body}>, online()→bool,
  //        broadcast(event,obj), healthSamples()→[] }
  const memory = [];                 // oldest first: {t, kind, text}
  let rules = [];                    // {id, text, kinds[], from, to, battery_below, cooldown_min, actions[], last}
  let notes = [];                    // {id, text, t}
  const labels = new Map();          // room-map view "c,r" → {label, desc, interest 0-3, t}: what's in each view
  let loaded = false, loading = false;
  const usage = { calls: [], day: '', today: 0, errors: 0, lastError: '' };
  let modelOk = null;                // did the vision/tool model answer last time
  let lastMoveAt = 0;

  // ── time ──
  const fmt = (t, opt) => new Intl.DateTimeFormat('en-IN', { timeZone: TZ, ...opt }).format(new Date(t));
  const clock = (t) => fmt(t, { hour: '2-digit', minute: '2-digit', hour12: false });
  const stamp = (t) => fmt(t, { weekday: 'short', day: 'numeric', month: 'short', hour: '2-digit', minute: '2-digit', hour12: false });
  const dayKey = (t) => fmt(t, { year: 'numeric', month: '2-digit', day: '2-digit' }).split('/').reverse().join('-');   // en-IN: dd/mm/yyyy
  const minutesOfDay = (t) => { const [h, m] = clock(t).split(':').map(Number); return h * 60 + m; };

  // ── budget ──
  function budget(auto) {
    const now = Date.now(), d = dayKey(now);
    if (usage.day !== d) { usage.day = d; usage.today = 0; }
    usage.calls = usage.calls.filter((t) => now - t < 60000);
    const rpm = auto ? Math.floor(RPM / 2) : RPM, rpd = auto ? Math.floor(RPD * 0.6) : RPD;   // leave room for chat
    return usage.calls.length < rpm && usage.today < rpd;
  }

  // ── the model ──
  async function llm(messages, { tools, model = MODEL, maxTokens = 700, auto = false, json = false } = {}) {
    if (!KEY) throw new Error('no GROQ_API_KEY set on Render');
    if (!budget(auto)) throw new Error('AI budget used up for now (free tier limit); try again in a minute');
    usage.calls.push(Date.now()); usage.today++;
    const body = { model, messages, temperature: 0.3, max_completion_tokens: maxTokens };
    if (tools) { body.tools = tools; body.tool_choice = 'auto'; }
    if (json) body.response_format = { type: 'json_object' };
    if (/qwen/i.test(model)) body.reasoning_format = 'hidden';
    let r, txt;
    for (let attempt = 0; attempt < 2; attempt++) {
      r = await fetch(BASE + '/chat/completions', {
        method: 'POST', headers: { Authorization: 'Bearer ' + KEY, 'Content-Type': 'application/json' },
        body: JSON.stringify(body), signal: AbortSignal.timeout(45000),
      });
      txt = await r.text();
      if (r.ok) break;
      if (r.status === 400 && /reasoning_format/i.test(txt) && body.reasoning_format) { delete body.reasoning_format; continue; }
      break;
    }
    if (!r.ok) {
      usage.errors++; usage.lastError = `${r.status} ${txt.slice(0, 160)}`;
      if (model === MODEL) modelOk = false;
      throw new Error(`AI error ${r.status}: ${txt.slice(0, 200)}`);
    }
    if (model === MODEL) modelOk = true;
    const msg = JSON.parse(txt).choices[0].message;
    if (typeof msg.content === 'string') msg.content = msg.content.replace(/<think>[\s\S]*?<\/think>\s*/g, '').trim();
    return msg;
  }

  // ── memory ──
  function remember(e) {
    if (!e || !e.t || !e.kind) return;
    const last = memory[memory.length - 1];
    if (last && e.t < last.t) {                       // older (a backfill): keep the list in time order, no duplicates
      if (memory.some((m) => m.t === e.t && m.kind === e.kind)) return;
      memory.push({ t: e.t, kind: e.kind, text: String(e.text || '').slice(0, 200) });
      memory.sort((a, b) => a.t - b.t);
    } else memory.push({ t: e.t, kind: e.kind, text: String(e.text || '').slice(0, 200) });
    while (memory.length > MEM_MAX) memory.shift();
  }

  async function loadFromCard() {                     // the card's copy of the log, and rules/notes
    if (loaded || loading || !ctx.online()) return;
    loading = true;
    try {
      for (let d = 2; d >= 0; d--) {
        const r = await ctx.sdGet(`/aya/log/${dayKey(Date.now() - d * 86400e3)}.jsonl`);
        if (!r.ok) continue;
        for (const line of r.body.toString('utf8').split('\n')) {
          try { const e = JSON.parse(line); if (e && e.t) remember(e); } catch { /* a partial line */ }
        }
      }
      const rr = await ctx.sdGet(RULES_FILE);
      if (rr.ok) try { rules = JSON.parse(rr.body.toString('utf8')).filter((x) => x && x.id); } catch { /* keep */ }
      const nn = await ctx.sdGet(NOTES_FILE);
      if (nn.ok) try { notes = JSON.parse(nn.body.toString('utf8')).filter((x) => x && x.id); } catch { /* keep */ }
      const mm = await ctx.sdGet(MAP_FILE);           // {"c,r": [label, interest, desc, t]}
      if (mm.ok) try { for (const [k, v] of Object.entries(JSON.parse(mm.body.toString('utf8')))) labels.set(k, { label: v[0], interest: v[1], desc: v[2], t: v[3] || 0 }); } catch { /* keep */ }
      loaded = true;
      console.log(`[brain] loaded ${memory.length} events, ${rules.length} rules, ${notes.length} notes from AYA's card`);
    } catch (e) { console.error('[brain] load: ' + e.message); }
    loading = false;
  }
  setInterval(loadFromCard, 20000);
  setTimeout(loadFromCard, 8000);

  async function save(file, list) {                    // compact JSON, under the board's 2 KB limit
    if (file === MAP_FILE) {                          // (an object: drop descriptions, then views, until it fits)
      const obj = list[0] || {};
      let s = JSON.stringify(obj);
      if (s.length > 2000) { for (const k in obj) obj[k][2] = ''; s = JSON.stringify(obj); }
      while (s.length > 2000) { delete obj[Object.keys(obj)[0]]; s = JSON.stringify(obj); }
      return (await ctx.sdPut(file, s)).ok;
    }
    let s = JSON.stringify(list);
    while (s.length > 2000 && list.length) { list.shift(); s = JSON.stringify(list); }
    const r = await ctx.sdPut(file, s);
    return r.ok;
  }

  function eventsSince(t, kinds, query, limit = 60) {
    let list = memory.filter((e) => e.t >= t && (!kinds || !kinds.length || kinds.includes(e.kind)));
    if (query) { const q = query.toLowerCase(); list = list.filter((e) => (e.kind + ' ' + e.text).toLowerCase().includes(q)); }
    const counts = {};
    for (const e of list) counts[e.kind] = (counts[e.kind] || 0) + 1;
    return { total: list.length, counts, events: list.slice(-limit).map((e) => `${stamp(e.t)} [${e.kind}] ${e.text}`) };
  }

  // ── seeing ──
  async function describe(question, auto = false) {
    if (lastMoveAt) {                                  // after a head move, wait for a picture taken after it settled
      const want = lastMoveAt + 1600;
      for (let i = 0; i < 25; i++) { const f = ctx.frame(); if (f && f.at > want) break; await new Promise((r) => setTimeout(r, 200)); }
    }
    const f = ctx.frame();
    if (!f || Date.now() - f.at > 15000) throw new Error('the camera has no fresh picture (AYA offline or the camera is restarting)');
    return seeImage(f.buf, question, auto);
  }
  async function seeImage(buf, question, auto, maxTokens = 220) {
    const msg = await llm([
      { role: 'system', content: 'You are the eyes of AYA, a small desk robot. The image is her camera: 160x120 pixels, grayscale, low quality, often dim. Describe only what is actually visible, briefly and concretely. If unsure, say so. No speculation about identity.' },
      { role: 'user', content: [
        { type: 'text', text: question || 'What do you see? One or two short sentences.' },
        { type: 'image_url', image_url: { url: 'data:image/jpeg;base64,' + buf.toString('base64') } },
      ] },
    ], { maxTokens, auto });
    return msg.content || '(no description)';
  }

  // ── tools ──
  const HEAD_DIRS = { left: [1, 0], right: [-1, 0], up: [0, -1], down: [0, 1] };   // matches the dashboard's joystick (PAN_DIR/TILT_DIR)
  const TOOLS = [
    fn('get_status', 'AYA\'s current state: battery, WiFi, uptime, head position and mode, who is in view, camera.', {}),
    fn('get_events', 'Search her memory of events (arrivals, people, strangers, motion, lights, power, restarts…).',
      { hours: num('How far back, in hours (default 24, max 72)'), kinds: { type: 'array', items: { type: 'string' }, description: 'Only these kinds, e.g. person, arrive, leave, stranger, known, motion, lights, power, restart, changed, alert, ai' },
        query: str('Text to search for') }),
    fn('look', 'Look through her camera now and describe what is visible. Use after moving the head to see a place.', { question: str('What to look for or ask about the picture') }, []),
    fn('move_head', 'Turn her head. Give a direction (+ degrees), or exact pan/tilt angles (0-180), or a saved spot name, or "rest".',
      { direction: { type: 'string', enum: ['left', 'right', 'up', 'down'] }, degrees: num('For direction: 5-45 (default 20)'),
        pan: num('0-180'), tilt: num('0-180'), spot: str('A saved spot name, or "rest"') }, []),
    fn('set_head_mode', 'follow = turns to faces/motion, patrol = sweeps the room, hold = stays still.', { mode: { type: 'string', enum: ['follow', 'patrol', 'hold'] } }, ['mode']),
    fn('gesture', 'A head gesture.', { name: { type: 'string', enum: ['nod', 'shake', 'curious', 'startle', 'stretch', 'excited', 'droop'] } }, ['name']),
    fn('scan_room', 'Look at every part of the room once (builds the room map), then go back to the mode.', {}),
    fn('show_message', 'Show a short text on her screen.', { text: str('ASCII, up to 120 characters'), seconds: num('5-600 (default 30)') }, ['text']),
    fn('set_expression', 'An expression on her face.', { name: { type: 'string', enum: ['giggle', 'wink', 'heart', 'surprise', 'curious', 'think', 'shy', 'dizzy', 'roll', 'nod', 'squint', 'purr', 'yawn', 'sleep', 'wake'] } }, ['name']),
    fn('set_screen', 'What her screen shows (iris = a single glowing iris), or turn it on/off.', { view: { type: 'string', enum: ['auto', 'eyes', 'iris', 'clock', 'weather', 'stats', 'detect', 'cam2', 'on', 'off'] } }, ['view']),
    fn('set_face', 'Her face style on the eyes screen: original (her animated eyes), pill, orb, status (clock), lens, wave, radar, viewfinder, iris, dots, lines.',
      { style: { type: 'string', enum: ['original', 'pill', 'orb', 'status', 'lens', 'wave', 'radar', 'viewfinder', 'iris', 'dots', 'lines'] } }, ['style']),
    fn('set_power_mode', 'performance (full speed), balanced, or saver (longest battery).', { mode: { type: 'string', enum: ['performance', 'balanced', 'saver'] } }, ['mode']),
    fn('showcase', 'Her ~40 s eyes + head performance (for filming).', {}),
    fn('perform_motion', 'Compose and play a new head motion from a description: "dance", "look around nervously", "act sleepy", "a happy wiggle", "pretend to search the floor".', { description: str('The motion, in plain words') }, ['description']),
    fn('look_at', 'Turn to a thing or place in the room by name ("the door", "the window", "my desk"), using her map of the room.', { thing: str('What to look at') }, ['thing']),
    fn('add_rule', 'Save a standing rule given in plain language, e.g. "if someone comes in after 11 pm, alert me and look at the door".', { text: str('The rule, in the owner\'s words') }, ['text']),
    fn('list_rules', 'List the saved rules.', {}),
    fn('delete_rule', 'Delete a rule by id.', { id: str('Rule id') }, ['id']),
    fn('remember', 'Save a fact the owner wants her to remember (about the home, people, preferences).', { fact: str('The fact') }, ['fact']),
    fn('forget', 'Delete a remembered fact by id.', { id: str('Note id') }, ['id']),
  ];
  function fn(name, description, properties, required) {
    return { type: 'function', function: { name, description, parameters: { type: 'object', properties, required: required || [] } } };
  }
  function num(d) { return { type: 'number', description: d }; }
  function str(d) { return { type: 'string', description: d }; }

  function cmd(c, args, body) {
    const [code, text] = ctx.applyCmd(c, args || [], body || {});
    return code < 300 ? 'done' : 'failed: ' + text;
  }

  async function runTool(name, a, actions) {
    a = a || {};
    switch (name) {
      case 'get_status': return JSON.stringify(statusSummary());
      case 'get_events': {
        const h = Math.min(72, Math.max(0.1, +a.hours || 24));
        return JSON.stringify(eventsSince(Date.now() - h * 3600e3, a.kinds, a.query));
      }
      case 'look': { const d = await describe(a.question); actions.push('looked'); return d; }
      case 'move_head': {
        let r;
        if (a.spot) r = a.spot.toLowerCase() === 'rest' ? cmd('head_rest_go') : cmd('head_spot_go', [a.spot.toLowerCase()]);
        else if (a.direction) {
          const [p, t] = HEAD_DIRS[a.direction], deg = Math.min(45, Math.max(5, +a.degrees || 20));
          r = cmd('head_nudge', [p * deg, t * deg]);
        } else if (Number.isFinite(+a.pan) && Number.isFinite(+a.tilt)) r = cmd('head_goto', [+a.pan, +a.tilt]);
        else return 'give a direction, pan+tilt, or a spot';
        lastMoveAt = Date.now();
        actions.push('moved the head');
        return r + ' (the picture is ready about 2 s after a move; call look to see)';
      }
      case 'set_head_mode': actions.push('head mode ' + a.mode); return cmd('head_mode', [a.mode]);
      case 'gesture': actions.push(a.name); return cmd('head_gesture', [a.name]);
      case 'scan_room': actions.push('room scan'); lastMoveAt = Date.now(); return cmd('head_map');
      case 'show_message': actions.push('message'); return cmd('message', [], { text: String(a.text || ''), secs: +a.seconds || 30 });
      case 'set_expression': actions.push(a.name); return cmd('emotion', [a.name]);
      case 'set_screen': actions.push('screen ' + a.view);
        return a.view === 'on' || a.view === 'off' ? cmd('screen', [a.view]) : cmd('view', [a.view]);
      case 'set_face': {
        const i = ['original', 'pill', 'orb', 'status', 'lens', 'wave', 'radar', 'viewfinder', 'iris', 'dots', 'lines'].indexOf(a.style);
        if (i < 0) return 'unknown style';
        actions.push('face: ' + a.style); cmd('view', ['eyes']);
        return cmd('tune', [], { face: i });
      }
      case 'set_power_mode': actions.push('power ' + a.mode);
        return cmd('tune', [], { pmode: { performance: 0, balanced: 1, saver: 2 }[a.mode] });
      case 'showcase': actions.push('showcase'); return cmd('anim', ['show']);
      case 'perform_motion': { const r = await compose(a.description); actions.push('motion: ' + String(a.description).slice(0, 24)); return r; }
      case 'look_at': {
        const hit = findInMap(a.thing);
        if (!hit) {
          if (!labels.size) { cmd('head_map'); lastMoveAt = Date.now(); return 'I have not mapped the room yet; I started a room scan. Ask again in a few minutes.'; }
          return 'I could not find that in my map of the room. Known views: ' + [...labels.values()].map((l) => l.label).filter((x, i, arr) => arr.indexOf(x) === i).join(', ');
        }
        const r = cmd('head_goto', [hit.pan, hit.tilt]); lastMoveAt = Date.now();
        actions.push('looked at ' + hit.label);
        return `${r}: turned to the view labelled "${hit.label}" (${hit.desc}). Call look to see it now.`;
      }
      case 'add_rule': { const r = await makeRule(a.text); actions.push('rule added'); return JSON.stringify(r); }
      case 'list_rules': return JSON.stringify(rules.map((r) => ({ id: r.id, text: r.text })));
      case 'delete_rule': {
        const n = rules.length; rules = rules.filter((r) => r.id !== a.id);
        if (rules.length === n) return 'no such rule';
        save(RULES_FILE, rules).catch(() => {}); actions.push('rule deleted'); return 'deleted';
      }
      case 'remember': {
        const n = { id: 'n' + Date.now().toString(36), text: String(a.fact || '').slice(0, 200), t: Date.now() };
        notes.push(n); save(NOTES_FILE, notes).catch(() => {});      // (to AYA's card in the background)
        actions.push('remembered'); return 'saved';
      }
      case 'forget': {
        const n = notes.length; notes = notes.filter((x) => x.id !== a.id);
        if (notes.length === n) return 'no such note';
        save(NOTES_FILE, notes).catch(() => {}); actions.push('forgot'); return 'deleted';
      }
      default: return 'unknown tool';
    }
  }

  function statusSummary() {
    const s = ctx.status(), b = s.board || {}, p = s.power || {}, h = s.head || {};
    const since = Date.now() - 24 * 3600e3;
    return {
      time: stamp(Date.now()), online: s.display_age !== null && s.display_age < 10000, camera_live: !!s.online,
      battery: p.pct != null ? { percent: p.pct, state: p.state, volts: p.v, hours: p.hours } : 'unknown',
      wifi_dbm: b.rssi, uptime_min: b.uptime != null ? Math.round(b.uptime / 60) : null, offline_mode: !!b.offline,
      head: { pan: h.pan, tilt: h.tilt, mode: h.mode, doing: h.state, spots: (h.spots || []).map((x) => x.name) },
      power_mode: ['performance', 'balanced', 'saver'][b.pmode || 0], head_speed: b.servo_speed,
      people_in_view: s.idle === false ? 'maybe' : 'none seen recently',
      restarts_24h: memory.filter((e) => e.t >= since && e.kind === 'restart').length,
    };
  }

  // ── chat ──
  function systemPrompt() {
    const s = statusSummary();
    return [
      'You are AYA, a small desk robot and home camera: an OLED face with expressive eyes, a pan/tilt head, a',
      'low-resolution grayscale camera (160x120), PIR and other sensors, on a battery. You live on the owner\'s desk',
      'in India (time zone ' + TZ + '). You speak like a capable, calm assistant with a little personality (think JARVIS):',
      'short, clear answers, no filler. You can act through your tools: use them instead of guessing. For "what do',
      'you see / is anyone there" use look; to see a place, move_head (or a spot) then look. For history use get_events.',
      'Never invent events, people or readings. If a tool fails, say what went wrong. Keep answers under 80 words',
      'unless asked for detail. Don\'t describe your tools; just use them.',
      'End every final answer with exactly one body-language tag, which your head and eyes act out: [nod] (yes, done,',
      'agreed), [shake] (no, can\'t), [think] (unsure, pondering), [happy] (glad, playful), [sad] (sorry, bad news) or [none].',
      'For a head motion the owner describes (dance, wiggle, act scared…) use perform_motion; for "look at the X" use look_at.',
      'Now: ' + JSON.stringify(s),
      notes.length ? 'Things the owner asked you to remember: ' + notes.map((n) => `[${n.id}] ${n.text}`).join('; ') : '',
      rules.length ? 'Your standing rules: ' + rules.map((r) => `[${r.id}] ${r.text}`).join('; ') : '',
    ].filter(Boolean).join('\n');
  }

  async function ask(q, history) {
    const actions = [];
    ctx.applyCmd('emotion', ['think']);                // she ponders while the model works
    const messages = [{ role: 'system', content: systemPrompt() }];
    for (const m of (history || []).slice(-8)) if ((m.role === 'user' || m.role === 'assistant') && m.content) messages.push({ role: m.role, content: String(m.content).slice(0, 1500) });
    messages.push({ role: 'user', content: String(q).slice(0, 1500) });
    for (let round = 0; round < 6; round++) {
      const msg = await llm(messages, { tools: TOOLS });
      if (!msg.tool_calls || !msg.tool_calls.length) {
        let answer = msg.content || '…';
        const m = /\[(nod|shake|think|happy|sad|none)\]\s*$/i.exec(answer);
        answer = answer.replace(/\s*\[(nod|shake|think|happy|sad|none)\]\s*/gi, ' ').trim();
        const mood = m ? m[1].toLowerCase() : 'none';
        if (MOODS[mood] && !actions.some((x) => x.startsWith('motion'))) {   // act it out (not over a motion she was asked for)
          const [g, e] = MOODS[mood];
          if (e) ctx.applyCmd('emotion', [e]);
          if (g) ctx.applyCmd('head_gesture', [g]);
        }
        return { answer, actions, mood };
      }
      messages.push({ role: 'assistant', content: msg.content || '', tool_calls: msg.tool_calls });
      for (const tc of msg.tool_calls) {
        let out;
        try { out = await runTool(tc.function.name, JSON.parse(tc.function.arguments || '{}'), actions); }
        catch (e) { out = 'error: ' + e.message; }
        messages.push({ role: 'tool', tool_call_id: tc.id, content: String(out).slice(0, 4000) });
      }
    }
    return { answer: 'I ran out of steps on that one. Try asking more simply.', actions };
  }

  // ── composed head motions ──
  async function compose(description) {
    const msg = await llm([
      { role: 'system', content: 'You choreograph the head of a small desk robot (two hobby servos: pan and tilt). Reply with JSON only: ' +
        '{"frames":[[dpan,dtilt,hold_ms,speed],...],"expression":"giggle"|"surprise"|"curious"|"think"|"shy"|"dizzy"|"yawn"|"wink"|"squint"|null}. ' +
        'Each frame is a target RELATIVE to where the head starts: dpan -60..60 degrees (positive = her left), dtilt -40..40 ' +
        '(positive = DOWN, negative = up), hold_ms 0..3000 (pause after arriving), speed 20..150 deg/s (calm 30-50, lively 80-120, ' +
        'snappy 150). 3 to 16 frames, under 12 s in total, ending with [0,0,0,40] to return to the start. Make it expressive ' +
        'and readable: clear poses, rhythm, a mix of big and small moves.' },
      { role: 'user', content: String(description).slice(0, 200) },
    ], { model: TEXT_MODEL, json: true, maxTokens: 500 });
    let j;
    try { j = JSON.parse(msg.content); } catch { throw new Error('could not compose that motion'); }
    const cl = (v, a, b) => Math.min(b, Math.max(a, Math.round(+v || 0)));
    const frames = (Array.isArray(j.frames) ? j.frames : []).filter(Array.isArray).slice(0, 16)
      .map((f) => [cl(f[0], -60, 60), cl(f[1], -40, 40), cl(f[2], 0, 3000), cl(f[3] || 60, 20, 150)]);
    if (frames.length < 2) throw new Error('that motion came out empty');
    const last = frames[frames.length - 1];
    if (last[0] || last[1]) { if (frames.length >= 16) frames.pop(); frames.push([0, 0, 0, 40]); }   // always end where it began
    const [code, text] = ctx.applyCmd('head_seq', [], { frames });
    if (code >= 300) throw new Error(text);
    if (j.expression) ctx.applyCmd('emotion', [String(j.expression)]);
    const secs = frames.reduce((s, f, i) => s + f[2] / 1000 + Math.hypot(f[0] - (frames[i - 1] || [0, 0])[0], f[1] - (frames[i - 1] || [0, 0])[1]) / f[3], 0);
    return `playing a ${frames.length}-step motion (~${secs.toFixed(1)} s)`;
  }

  // ── the room: what each map view shows (labelled by the vision model, a couple at a time) ──
  async function labelSome() {
    if (!KEY || !ctx.online() || !budget(true)) return;
    const cells = ctx.mapCells().filter((c) => c.jpeg && (!labels.has(c.key) || labels.get(c.key).t < c.t - 6 * 3600e3))
      .sort((a, b) => (labels.has(a.key) ? 1 : 0) - (labels.has(b.key) ? 1 : 0));
    for (const c of cells.slice(0, 2)) {
      try {
        const d = await seeImage(c.jpeg, 'This is one view from a home camera robot that sweeps the room. Reply JSON only: ' +
          '{"label":"1-3 words for the main thing in view (door, window, desk, bed, sofa, shelf, wall, ceiling, floor, cupboard, tv, ...)",' +
          '"desc":"under 8 words","interest":0-3} where interest is how worth watching it is for a home camera: 0 = blank wall/ceiling/' +
          'nothing, 1 = ordinary, 2 = where people sit or things happen, 3 = a door, window or entrance.', true, 120);
        const m = /\{[\s\S]*\}/.exec(d); if (!m) continue;
        const j = JSON.parse(m[0]);
        labels.set(c.key, { label: String(j.label || '?').toLowerCase().slice(0, 20), desc: String(j.desc || '').slice(0, 40),
                            interest: Number.isFinite(+j.interest) ? Math.min(3, Math.max(0, Math.round(+j.interest))) : 1, t: Date.now() });
      } catch { break; }
    }
    if (cells.length) {
      const obj = {};
      for (const [k, v] of labels) obj[k] = [v.label, v.interest, v.desc.slice(0, 24), v.t];
      save(MAP_FILE, Object.entries(obj).length ? [obj] : []).catch(() => {});
    }
  }
  setInterval(() => { labelSome().catch(() => {}); }, +process.env.BRAIN_LABEL_MS || 90000);

  function findInMap(thing) {
    const words = String(thing || '').toLowerCase().replace(/\b(the|my|a|an|at|to)\b/g, ' ').split(/\W+/).filter((w) => w.length > 2);
    if (!words.length) return null;
    const cells = new Map(ctx.mapCells().map((c) => [c.key, c]));
    let best = null, score = 0;
    for (const [k, l] of labels) {
      const hay = (l.label + ' ' + l.desc).toLowerCase();
      const sc = words.filter((w) => hay.includes(w)).length * 10 + l.interest;
      const c = cells.get(k);
      if (sc >= 10 && sc > score && c) { score = sc; best = { ...l, pan: c.pan, tilt: c.tilt }; }
    }
    return best;
  }

  function patrolWeights(cols, rows) {
    if (labels.size < 6) return null;                 // not enough of the room known yet: patrol everything
    let w = '';
    for (let r = 0; r < rows; r++) for (let c = 0; c < cols; c++) { const l = labels.get(c + ',' + r); w += l ? l.interest : 1; }
    return /[1-3]/.test(w) ? w : null;
  }

  // ── rules ──
  const RULE_KINDS = ['arrive', 'leave', 'person', 'known', 'stranger', 'motion', 'lights', 'changed', 'unusual', 'wave', 'power', 'restart', 'ai'];
  async function makeRule(text) {
    const spots = ((ctx.status().head || {}).spots || []).map((x) => x.name);
    const msg = await llm([
      { role: 'system', content: 'Convert a home-robot rule into JSON. Reply with JSON only: {"kinds":[event kinds that trigger it],' +
        '"from":"HH:MM" or null,"to":"HH:MM" or null (local time window, may wrap midnight),"battery_below":number or null,' +
        '"cooldown_min":number (default 10),"actions":[{"type":"alert"|"look_spot"|"look"|"gesture"|"message"|"head_mode","arg":string}],' +
        '"summary":"the rule in one short sentence"}. Event kinds: ' + RULE_KINDS.join(', ') + ' (arrive = someone appeared, ' +
        'person = a person detected, stranger = unknown face, known = a known face, motion = motion without a person, ' +
        'lights = lights switched on, changed = something in the room changed, power = battery events). ' +
        'Actions: alert (arg = message), look_spot (arg = one of the saved spots: ' + (spots.join(', ') || 'none') + ', or "rest"), ' +
        'look (describe the camera view and alert with it), gesture (nod/shake/curious/excited), message (arg = text for her screen), ' +
        'head_mode (follow/patrol/hold). For battery rules use kinds ["power"] plus battery_below.' },
      { role: 'user', content: text },
    ], { model: TEXT_MODEL, json: true, maxTokens: 400 });
    let spec;
    try { spec = JSON.parse(msg.content); } catch { throw new Error('could not understand that rule'); }
    const rule = {
      id: 'r' + Date.now().toString(36), text: String(spec.summary || text).slice(0, 140),
      kinds: (spec.kinds || []).filter((k) => RULE_KINDS.includes(k)),
      from: /^\d{1,2}:\d{2}$/.test(spec.from || '') ? spec.from : null, to: /^\d{1,2}:\d{2}$/.test(spec.to || '') ? spec.to : null,
      battery_below: Number.isFinite(+spec.battery_below) && spec.battery_below !== null ? +spec.battery_below : null,
      cooldown_min: Math.min(1440, Math.max(1, +spec.cooldown_min || 10)),
      actions: (spec.actions || []).filter((x) => x && ['alert', 'look_spot', 'look', 'gesture', 'message', 'head_mode'].includes(x.type))
        .slice(0, 4).map((x) => ({ type: x.type, arg: String(x.arg || '').slice(0, 100) })),
      last: 0,
    };
    if (!rule.kinds.length || !rule.actions.length) throw new Error('that rule has no trigger or no action I can do');
    rules.push(rule);
    save(RULES_FILE, rules).catch(() => {});           // (to AYA's card in the background)
    return { id: rule.id, rule: rule.text, triggers: rule.kinds, window: rule.from ? `${rule.from}-${rule.to}` : 'any time', actions: rule.actions };
  }

  const hm = (s) => { const [h, m] = s.split(':').map(Number); return h * 60 + m; };
  function inWindow(r, t) {
    if (!r.from || !r.to) return true;
    const m = minutesOfDay(t), a = hm(r.from), b = hm(r.to);
    return a <= b ? m >= a && m < b : m >= a || m < b;
  }

  async function runRules(e) {
    for (const r of rules) {
      if (!r.kinds.includes(e.kind) || !inWindow(r, e.t)) continue;
      if (r.battery_below != null) { const p = ctx.status().power; if (!p || p.pct == null || p.pct >= r.battery_below) continue; }
      if (r.last && e.t - r.last < r.cooldown_min * 60000) continue;
      r.last = e.t;
      for (const a of r.actions) {
        try {
          if (a.type === 'alert') ctx.logEvent('alert', `Rule: ${a.arg || r.text}`);
          else if (a.type === 'look_spot') { a.arg === 'rest' ? cmd('head_rest_go') : cmd('head_spot_go', [a.arg]); lastMoveAt = Date.now(); }
          else if (a.type === 'gesture') cmd('head_gesture', [a.arg]);
          else if (a.type === 'message') cmd('message', [], { text: a.arg, secs: 60 });
          else if (a.type === 'head_mode') cmd('head_mode', [a.arg]);
          else if (a.type === 'look') { const d = await describe(null, true); ctx.logEvent('alert', `Rule "${r.text}": ${d}`); }
        } catch (err) { ctx.logEvent('alert', `Rule "${r.text}" fired, but: ${err.message}`); }
      }
    }
  }

  // ── events in ──
  let lastAutoLook = 0;
  function onEvent(e) {
    remember(e);
    if (e.kind === 'alert' || e.kind === 'ai') return;          // our own
    runRules(e).catch(() => {});
    if (e.kind === 'motion' && KEY && Date.now() - lastAutoLook > 180000 && budget(true)) {   // smart alert: worth a look?
      lastAutoLook = Date.now();
      describe('Is there a person, an animal, or anything unusual in this picture? Reply as JSON: {"notable":true|false,"what":"short description"}', true)
        .then((d) => {
          const m = /\{[\s\S]*\}/.exec(d); if (!m) return;
          const j = JSON.parse(m[0]);
          if (j.notable) ctx.logEvent('ai', `AI looked at the motion: ${String(j.what).slice(0, 140)}`);
        }).catch(() => {});
    }
  }

  let lastCaption = 0;
  function onCapture(ev) {                            // a gallery event: give it a description
    if (!KEY || Date.now() - lastCaption < 60000 || !budget(true)) return;
    if (!['person', 'stranger', 'known', 'unusual', 'changed'].includes(ev.kind)) return;
    lastCaption = Date.now();
    describe('Describe this moment from a home camera in one short sentence.', true)
      .then((d) => { ev.ai = d; ctx.broadcast('gallery', { id: ev.id, t: ev.t, kind: ev.kind, text: ev.text, ai: ev.ai, n: ev.frames.length }); })
      .catch(() => {});
  }

  // ── summaries ──
  const briefCache = new Map();
  async function brief(since) {
    const ev = eventsSince(since, null, null, 120);
    if (!ev.total) return 'Nothing happened while you were away.';
    const key = since + ':' + ev.total;
    if (briefCache.has(key)) return briefCache.get(key);
    const msg = await llm([
      { role: 'system', content: 'You are AYA, a home camera robot. Summarise what happened for the owner who just came back. Plain, short (max 5 bullet points), most important first: people/strangers, unusual things, alerts, power or health problems. Use local times. No preamble.' },
      { role: 'user', content: `Since ${stamp(since)} (${ev.total} events, counts ${JSON.stringify(ev.counts)}):\n` + ev.events.join('\n') },
    ], { model: TEXT_MODEL, maxTokens: 350 });
    const out = msg.content || 'No summary.';
    briefCache.set(key, out);
    if (briefCache.size > 20) briefCache.delete(briefCache.keys().next().value);
    return out;
  }

  let digestDay = '';
  setInterval(async () => {                          // nightly digest at 21:30 local time
    const now = Date.now(), d = dayKey(now);
    if (!KEY || digestDay === d || minutesOfDay(now) < 21 * 60 + 30) return;
    digestDay = d;
    const start = now - minutesOfDay(now) * 60000;
    if (!eventsSince(start).total) return;
    try { ctx.logEvent('ai', 'Today: ' + (await brief(start)).replace(/\n+/g, ' ').slice(0, 400)); } catch { /* next night */ }
  }, 60000);

  // ── HTTP ──
  function info() {
    return { enabled: !!KEY, model: MODEL, text_model: TEXT_MODEL, model_ok: modelOk, loaded_from_card: loaded,
             memory_events: memory.length, map_views_labelled: labels.size,
             map: [...labels.entries()].map(([k, l]) => ({ view: k, label: l.label, interest: l.interest })), rules: rules.map((r) => ({ id: r.id, text: r.text })), notes: notes.map((n) => ({ id: n.id, text: n.text })),
             usage: { last_minute: usage.calls.filter((t) => Date.now() - t < 60000).length, today: usage.today, per_minute: RPM, per_day: RPD, errors: usage.errors, last_error: usage.lastError } };
  }

  return {
    onEvent, onCapture, info, brief, patrolWeights,
    ask: async (q, history) => ask(q, history),
    deleteRule: async (id) => { rules = rules.filter((r) => r.id !== id); return save(RULES_FILE, rules); },
    deleteNote: async (id) => { notes = notes.filter((n) => n.id !== id); return save(NOTES_FILE, notes); },
  };
};
