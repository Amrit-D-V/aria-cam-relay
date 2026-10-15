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
const RULES_FILE = '/aya/brain/rules.json', NOTES_FILE = '/aya/brain/notes.json';

module.exports = function createBrain(ctx) {
  // ctx: { applyCmd(cmd,args,body)→[code,text], status()→obj, frame()→{buf,at}|null, logEvent(kind,text),
  //        sdGet(path)→Promise<{ok,body}>, sdPut(path,text)→Promise<{ok,body}>, online()→bool,
  //        broadcast(event,obj), healthSamples()→[] }
  const memory = [];                 // oldest first: {t, kind, text}
  let rules = [];                    // {id, text, kinds[], from, to, battery_below, cooldown_min, actions[], last}
  let notes = [];                    // {id, text, t}
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
      loaded = true;
      console.log(`[brain] loaded ${memory.length} events, ${rules.length} rules, ${notes.length} notes from AYA's card`);
    } catch (e) { console.error('[brain] load: ' + e.message); }
    loading = false;
  }
  setInterval(loadFromCard, 20000);
  setTimeout(loadFromCard, 8000);

  async function save(file, list) {                    // compact JSON, under the board's 2 KB limit
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
    const msg = await llm([
      { role: 'system', content: 'You are the eyes of AYA, a small desk robot. The image is her camera: 160x120 pixels, grayscale, low quality, often dim. Describe only what is actually visible, briefly and concretely. If unsure, say so. No speculation about identity.' },
      { role: 'user', content: [
        { type: 'text', text: question || 'What do you see? One or two short sentences.' },
        { type: 'image_url', image_url: { url: 'data:image/jpeg;base64,' + f.buf.toString('base64') } },
      ] },
    ], { maxTokens: 220, auto });
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
    fn('set_screen', 'What her screen shows, or turn it on/off.', { view: { type: 'string', enum: ['auto', 'eyes', 'clock', 'weather', 'stats', 'detect', 'cam2', 'on', 'off'] } }, ['view']),
    fn('set_power_mode', 'performance (full speed), balanced, or saver (longest battery).', { mode: { type: 'string', enum: ['performance', 'balanced', 'saver'] } }, ['mode']),
    fn('showcase', 'Her ~40 s eyes + head performance (for filming).', {}),
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
      case 'set_power_mode': actions.push('power ' + a.mode);
        return cmd('tune', [], { pmode: { performance: 0, balanced: 1, saver: 2 }[a.mode] });
      case 'showcase': actions.push('showcase'); return cmd('anim', ['show']);
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
      'Now: ' + JSON.stringify(s),
      notes.length ? 'Things the owner asked you to remember: ' + notes.map((n) => `[${n.id}] ${n.text}`).join('; ') : '',
      rules.length ? 'Your standing rules: ' + rules.map((r) => `[${r.id}] ${r.text}`).join('; ') : '',
    ].filter(Boolean).join('\n');
  }

  async function ask(q, history) {
    const actions = [];
    const messages = [{ role: 'system', content: systemPrompt() }];
    for (const m of (history || []).slice(-8)) if ((m.role === 'user' || m.role === 'assistant') && m.content) messages.push({ role: m.role, content: String(m.content).slice(0, 1500) });
    messages.push({ role: 'user', content: String(q).slice(0, 1500) });
    for (let round = 0; round < 6; round++) {
      const msg = await llm(messages, { tools: TOOLS });
      if (!msg.tool_calls || !msg.tool_calls.length) return { answer: msg.content || '…', actions };
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
             memory_events: memory.length, rules: rules.map((r) => ({ id: r.id, text: r.text })), notes: notes.map((n) => ({ id: n.id, text: n.text })),
             usage: { last_minute: usage.calls.filter((t) => Date.now() - t < 60000).length, today: usage.today, per_minute: RPM, per_day: RPD, errors: usage.errors, last_error: usage.lastError } };
  }

  return {
    onEvent, onCapture, info, brief,
    ask: async (q, history) => ask(q, history),
    deleteRule: async (id) => { rules = rules.filter((r) => r.id !== id); return save(RULES_FILE, rules); },
    deleteNote: async (id) => { notes = notes.filter((n) => n.id !== id); return save(NOTES_FILE, notes); },
  };
};
