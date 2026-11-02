const http = require('http');
const fs = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;
const PUBLIC = path.join(__dirname, 'public');
const MIME = { '.html': 'text/html; charset=utf-8', '.jpg': 'image/jpeg', '.png': 'image/png', '.js': 'text/javascript', '.css': 'text/css' };

// Arena floor (in background-image pixel coordinates, 1254x1254)
const CX = 630, CY = 640, RX = 410, RY = 335;
const SPEED = 300, TICK = 30, MAX_PLAYERS = 50;

const server = http.createServer((req, res) => {
  const url = req.url.split('?')[0];
  if (url === '/healthz') { res.writeHead(200); return res.end('ok'); }
  const file = path.normalize(path.join(PUBLIC, url === '/' ? 'index.html' : url));
  if (!file.startsWith(PUBLIC)) { res.writeHead(403); return res.end(); }
  fs.readFile(file, (err, data) => {
    if (err) { res.writeHead(404); return res.end('Not found'); }
    res.writeHead(200, { 'Content-Type': MIME[path.extname(file)] || 'application/octet-stream', 'Cache-Control': 'no-cache' });
    res.end(data);
  });
});

const wss = new WebSocketServer({ server, maxPayload: 1024 });
const players = new Map();
let nextId = 1;

const clean = (s, n) => String(s || '').replace(/[\u0000-\u001f<>]/g, '').trim().slice(0, n);
const send = (ws, o) => ws.readyState === 1 && ws.send(JSON.stringify(o));
const broadcast = o => { const m = JSON.stringify(o); for (const p of players.values()) if (p.ws.readyState === 1) p.ws.send(m); };

// ================= game state =================
const CHAT_TTL = 10 * 60 * 1000;          // chat logs older than 10 min are deleted
const ROUND_MS = 4 * 60 * 1000;           // a round lasts 4 minutes      // round: 5s full arena, then a 40s shrinking safe zone
const chatLog = [];                        // {name,text,ts,sys}
let phase = 'lobby', roundStart = 0, deathCounter = 0;

const joinedList = () => [...players.values()].filter(p => p.joined);

function addChat(e) {
  e.ts = Date.now();
  chatLog.push(e);
  broadcast({ t: 'chat', id: e.id, name: e.name, text: e.text, sys: e.sys ? 1 : 0 });
}
const sysChat = text => addChat({ name: 'System', text, sys: true });
function pruneChat() { const lim = Date.now() - CHAT_TTL; while (chatLog.length && chatLog[0].ts < lim) chatLog.shift(); }
setInterval(pruneChat, 15000);

// ---- lobby -> countdown -> round -> lobby ----
function checkReady() {
  if (phase !== 'lobby') return;
  const list = joinedList();
  if (list.length >= 2 && list.every(p => p.ready)) {
    phase = 'countdown';
    broadcast({ t: 'countdown', ms: 2000 });
    setTimeout(startRound, 2000);
  }
}
function startRound() {
  if (phase !== 'countdown') return;
  const parts = joinedList().filter(p => p.ready);
  if (parts.length < 2) {
    phase = 'lobby';
    joinedList().forEach(p => p.ready = false);
    broadcast({ t: 'countdown', ms: 0 });
    return sysChat('Round cancelled: not enough players.');
  }
  phase = 'round'; roundStart = Date.now(); arrows.clear();
  parts.forEach((p, i) => {
    const a = -Math.PI / 2 + i * 2 * Math.PI / parts.length;   // evenly spaced on the outer edge
    p.lx = p.x; p.ly = p.y;
    p.x = CX + Math.cos(a) * RX * 0.92; p.y = CY + Math.sin(a) * RY * 0.92;
    p.dx = p.dy = 0; p.role = 1; p.inRound = true; p.ready = false; p.deathOrder = 0; p.hist = [];
    resetCombat(p);
  });
  joinedList().forEach(p => { if (!p.inRound) p.role = 2; });  // late joiners spectate
  broadcast({ t: 'tp' });
  sysChat('⚔️ Round started with ' + parts.length + ' players!');
}
function checkRoundEnd() {
  if (phase !== 'round') return;
  const alive = [...players.values()].filter(p => p.role === 1);
  if (alive.length > 1) return;
  let winner = alive[0];
  if (!winner) winner = [...players.values()].filter(p => p.inRound).sort((a, b) => b.deathOrder - a.deathOrder)[0];
  endRound(winner);
}
function endRound(winner, tied) {
  phase = 'lobby'; arrows.clear();
  for (const p of players.values()) {
    if (p.inRound) { p.x = p.lx; p.y = p.ly; }      // back to where they were in the lobby
    p.role = 0; p.inRound = false; p.ready = false; p.dx = p.dy = 0; p.hist = [];
    resetCombat(p);
  }
  broadcast({ t: 'tp' });
  if (tied && tied.length) { const names = tied.join(', '); sysChat('⏱ Time is up! 2nd place: ' + names); broadcast({ t: 'winner', name: names, second: true }); }
  else if (winner) { sysChat('🏆 1st place: ' + winner.name); broadcast({ t: 'winner', name: winner.name }); }
  else sysChat('Round ended with no winner.');
}

// ---- combat ----
const RAD = Math.PI / 180;
const BASE = { hp: 1000, dmg: 150, reduce: 0, atkCd: 600 };                          // every class without custom stats
const CLASS_STATS = {
  Knight: { hp: 1000, dmg: 150, reduce: 0.2, atkCd: 700 },   // passive [Armor]: -20% damage taken; attack every 0.7s
  Archer: { hp: 1000, dmg: 180, reduce: 0, atkCd: 800 }     // shoots an arrow every 0.8s for 180
};
const statsOf = p => CLASS_STATS[p.cls] || BASE;
const ARROW = { speed: 800, range: 700, radius: 28 };      // ground px/s, ground px, hit radius
const ATK = { range: 75, span: 100 * RAD };                            // melee basic attack (F)
const KNIGHT = {
  Q: { cd: 8000, range: 150, span: 120 * RAD, dmg: 250, stun: 1000 },   // range = 2x basic attack
  E: { cd: 12000, dur: 3000, reduce: 0.7, speed: 1.4 },                 // -70% damage taken, +40% speed
  R: { cd: 25000, swords: 8, ring: 130, radius: 55, dmg: 200, slow: 0.7, slowMs: 2000 }
};

function setAim(p, a) {
  if (!Number.isFinite(a)) return;
  p.aim = Math.atan2(Math.sin(a), Math.cos(a));
  if (Math.abs(Math.cos(p.aim)) > 0.2) p.face = Math.cos(p.aim) > 0 ? 1 : -1;   // sprite faces the cursor side
}
// ---- lag compensation ----
// The attacker sees targets ~(RTT + smoothing) in the past, and their own character at its predicted position.
// So hits are judged from the position the attacker reports (within a tolerance) against where targets WERE.
const HIST_MS = 700, TOL = 110, MAX_LAG = 300, VIEW_DELAY = 50;
function posAt(t, time) {
  const h = t.hist;
  if (!h.length || time >= h[h.length - 1].t) return { x: t.x, y: t.y };
  if (time <= h[0].t) return { x: h[0].x, y: h[0].y };
  for (let i = h.length - 1; i > 0; i--) {
    if (h[i - 1].t <= time) {
      const a = h[i - 1], b = h[i], f = (time - a.t) / ((b.t - a.t) || 1);
      return { x: a.x + (b.x - a.x) * f, y: a.y + (b.y - a.y) * f };
    }
  }
  return { x: h[0].x, y: h[0].y };
}
const lagOf = m => Math.min(MAX_LAG, Math.max(0, (Number(m && m.rt) || 0) + VIEW_DELAY));
function originOf(p, m) {
  const x = Number(m && m.x), y = Number(m && m.y);
  if (!Number.isFinite(x) || !Number.isFinite(y) || Math.hypot(x - p.x, y - p.y) > TOL) return { x: p.x, y: p.y };
  return { x, y };
}

// ---- arrows ----
const arrows = new Map(); let arrowSeq = 0;
function segDist(px, py, ax, ay, bx, by) {
  const vx = bx - ax, vy = by - ay, l2 = vx * vx + vy * vy;
  const k = l2 ? Math.max(0, Math.min(1, ((px - ax) * vx + (py - ay) * vy) / l2)) : 0;
  return Math.hypot(px - (ax + k * vx), py - (ay + k * vy));
}
function endArrow(ar) { arrows.delete(ar.id); broadcast({ t: 'arrowEnd', id: ar.id }); }
function moveArrow(ar, step, time) {          // advances the arrow; returns the target it hit (judged at `time`)
  const nx = ar.x + Math.cos(ar.a) * step, ngy = ar.gy + Math.sin(ar.a) * step;
  let hit = null, best = 1e9;
  if (phase === 'round') for (const t of players.values()) {
    if (t.id === ar.owner || !t.joined || t.role !== 1) continue;
    const tp = posAt(t, time);
    if (segDist(tp.x, tp.y / 0.8, ar.x, ar.gy, nx, ngy) > ARROW.radius) continue;
    const d = Math.hypot(tp.x - ar.x, tp.y / 0.8 - ar.gy);
    if (d < best) { best = d; hit = t; }
  }
  if (!hit) { ar.x = nx; ar.gy = ngy; ar.left -= step; }
  return hit;
}
function spawnArrow(p, dmg, o, lag, now) {
  const id = ++arrowSeq;
  const ar = { id, owner: p.id, x: o.x, gy: o.y / 0.8, a: p.aim, dmg, left: ARROW.range };
  let adv = 0, hit = null;
  const steps = lag > 0 ? Math.ceil(lag / 33) : 0, stepMs = steps ? lag / steps : 0;
  for (let i = 1; i <= steps && !hit; i++) {         // replay the time the shooter already "lived" against old target positions
    const step = Math.min(ARROW.speed * stepMs / 1000, ar.left);
    hit = moveArrow(ar, step, now - lag + i * stepMs);
    if (!hit) adv += step;
  }
  broadcast({ t: 'arrow', id, by: p.id, x: o.x, y: o.y, a: p.aim, spd: ARROW.speed, range: ARROW.range, adv });
  if (hit) { dmgTo(hit, dmg, now); broadcast({ t: 'arrowEnd', id }); checkRoundEnd(); return; }
  arrows.set(id, ar);
}
function stepArrows(dt, now) {
  let any = false;
  for (const ar of arrows.values()) {
    const hit = moveArrow(ar, Math.min(ARROW.speed * dt, ar.left), now);
    if (hit) { dmgTo(hit, ar.dmg, now); endArrow(ar); any = true; continue; }
    const ex = (ar.x - CX) / RX, ey = (ar.gy * 0.8 - CY) / RY;
    if (ar.left <= 0 || ex * ex + ey * ey > 1.15) endArrow(ar);
  }
  if (any) checkRoundEnd();
}

function resetCombat(p) {
  p.mh = p.hp = statsOf(p).hp;
  p.atkReady = p.cdQ = p.cdE = p.cdR = 0;
  p.stunUntil = p.guardUntil = p.slowUntil = 0;
  for (const k of ['Q', 'E', 'R']) send(p.ws, { t: 'cd', k, ms: 0 });
}
function killPlayer(p) { p.hp = 0; p.role = 2; p.dx = p.dy = 0; p.moving = false; p.deathOrder = ++deathCounter; }
function dmgTo(t, amount, now) {
  let cut = statsOf(t).reduce;                       // Armor: 20%
  if (now < t.guardUntil) cut += KNIGHT.E.reduce;    // Guard Rush: +70% (added together -> 90% total)
  const d = Math.max(1, Math.round(amount * (1 - Math.min(cut, 0.95))));
  t.hp -= d;
  broadcast({ t: 'hit', id: t.id, dmg: d });
  if (t.hp <= 0) killPlayer(t);
}
const targetsOf = p => phase !== 'round' ? [] : [...players.values()].filter(t => t !== p && t.joined && t.role === 1);
function inConeAt(ox, oy, aim, tx, ty, range, span) {   // ground plane: y is stretched by 1/0.8
  const dx = tx - ox, dy = (ty - oy) / 0.8, d = Math.hypot(dx, dy);
  if (d > range + 10) return false;
  if (d < 10) return true;
  let diff = Math.abs(Math.atan2(dy, dx) - aim);
  if (diff > Math.PI) diff = 2 * Math.PI - diff;
  return diff <= span / 2;
}
const canAct = (p, now) => p.joined && p.role !== 2 && now >= p.stunUntil;

function doAttack(p, m) {
  const now = Date.now();
  if (!canAct(p, now) || now < p.atkReady) return;
  const st = statsOf(p), o = originOf(p, m), lag = lagOf(m);
  p.atkReady = now + st.atkCd;
  if (p.cls === 'Archer') { spawnArrow(p, st.dmg, o, lag, now); return; }
  broadcast({ t: 'fx', type: 'cone', by: p.id, x: o.x, y: o.y, a: p.aim, span: ATK.span, r: ATK.range, c: 'rgba(255,255,255,.6)', dur: 220 });
  for (const t of targetsOf(p)) {
    const tp = posAt(t, now - lag);
    if (inConeAt(o.x, o.y, p.aim, tp.x, tp.y, ATK.range, ATK.span)) dmgTo(t, st.dmg, now);
  }
  checkRoundEnd();
}
function doSkill(p, k, m) {
  const now = Date.now();
  if (p.cls !== 'Knight' || !KNIGHT[k] || !canAct(p, now) || now < p['cd' + k]) return;
  const S = KNIGHT[k], o = originOf(p, m), lag = lagOf(m);
  p['cd' + k] = now + S.cd; send(p.ws, { t: 'cd', k, ms: S.cd });
  if (k === 'Q') {
    broadcast({ t: 'fx', type: 'cone', by: p.id, x: o.x, y: o.y, a: p.aim, span: S.span, r: S.range, c: 'rgba(255,214,107,.65)', dur: 380 });
    for (const t of targetsOf(p)) {
      const tp = posAt(t, now - lag);
      if (inConeAt(o.x, o.y, p.aim, tp.x, tp.y, S.range, S.span)) { dmgTo(t, S.dmg, now); if (t.role === 1) t.stunUntil = now + S.stun; }
    }
  } else if (k === 'E') {
    p.guardUntil = now + S.dur;
  } else {
    broadcast({ t: 'fx', type: 'swords', x: o.x, y: o.y, r: S.ring, ar: S.radius, n: S.swords, dur: 900 });
    const gy = o.y / 0.8;
    for (let n = 0; n < S.swords; n++) {
      const a = n * 2 * Math.PI / S.swords, sx = o.x + Math.cos(a) * S.ring, sy = gy + Math.sin(a) * S.ring;
      for (const t of targetsOf(p)) {
        const tp = posAt(t, now - lag);
        if (t.role !== 1 || Math.hypot(tp.x - sx, tp.y / 0.8 - sy) > S.radius + 10) continue;
        dmgTo(t, S.dmg, now);
        if (t.role === 1) t.slowUntil = now + S.slowMs;
      }
    }
  }
  checkRoundEnd();
}

function checkTimeout(now) {
  if (phase !== 'round' || now - roundStart < ROUND_MS) return;
  endRound(null, [...players.values()].filter(p => p.role === 1).map(p => p.name));
}


// ================= connections =================
wss.on('connection', ws => {
  if (players.size >= MAX_PLAYERS) { send(ws, { t: 'full' }); return ws.close(); }
  const id = nextId++;
  const a = Math.random() * Math.PI * 2, r = Math.random() * 0.5;
  const p = { id, ws, name: 'Player' + id, hue: Math.floor(Math.random() * 360),
    x: CX + Math.cos(a) * RX * r, y: CY + Math.sin(a) * RY * r, face: 1, dx: 0, dy: 0, lastChat: 0, alive: true,
    joined: false, cls: '', ready: false, role: 0, inRound: false, lx: 0, ly: 0, deathOrder: 0,
    hp: 1000, mh: 1000, atkReady: 0, cdQ: 0, cdE: 0, cdR: 0, stunUntil: 0, guardUntil: 0, slowUntil: 0, aim: 0, hist: [] };
  players.set(id, p);
  pruneChat();
  send(ws, { t: 'hello', id, arena: { CX, CY, RX, RY } });
  send(ws, { t: 'history', log: chatLog.map(c => ({ name: c.name, text: c.text, sys: c.sys ? 1 : 0, age: Date.now() - c.ts })) });

  ws.on('pong', () => { p.alive = true; });
  ws.on('message', raw => {
    let m; try { m = JSON.parse(raw); } catch { return; }
    if (m.t === 'join') {
      p.name = clean(m.name, 14) || p.name;
      if (!p.joined) { p.joined = true; if (phase === 'round') p.role = 2; }   // joined mid-round -> spectate
      return;
    }
    if (m.t === 'ping') { send(ws, { t: 'pong', c: m.c }); return; }
    if (!p.joined) return;
    if (m.t === 'input') {
      p.dx = Math.sign(Number(m.dx) || 0); p.dy = Math.sign(Number(m.dy) || 0);
      if (m.a !== undefined) setAim(p, Number(m.a));
    } else if (m.t === 'aim') {
      setAim(p, Number(m.a));
    } else if (m.t === 'chat') {
      const now = Date.now(), text = clean(m.text, 60);
      if (text && now - p.lastChat > 800) { p.lastChat = now; addChat({ id, name: p.name, text }); }
    } else if (m.t === 'class') {
      if (phase === 'lobby' && ['Knight', 'Archer', 'Shielder', 'Assassin'].includes(m.cls)) { p.cls = m.cls; resetCombat(p); }
    } else if (m.t === 'atk') {
      if (m.a !== undefined) setAim(p, Number(m.a));
      doAttack(p, m);
    } else if (m.t === 'skill') {
      if (m.a !== undefined) setAim(p, Number(m.a));
      doSkill(p, String(m.k), m);
    } else if (m.t === 'ready') {
      if (phase !== 'lobby' || joinedList().length < 2) return;     // needs 2+ players
      p.ready = !p.ready; checkReady();
    }
  });
  ws.on('close', () => {
    players.delete(id); broadcast({ t: 'leave', id });
    if (phase === 'lobby') checkReady(); else if (phase === 'round') checkRoundEnd();
  });
  ws.on('error', () => {});
});

// ================= simulation =================
let last = Date.now();
setInterval(() => {
  const now = Date.now(), dt = Math.min((now - last) / 1000, 0.1); last = now;
  for (const p of players.values()) {
    if (!p.joined) continue;
    let { dx, dy } = p;
    if (p.role === 2 || now < p.stunUntil) dx = dy = 0;
    if (dx || dy) {
      const l = Math.hypot(dx, dy); dx /= l; dy /= l;
      const spd = SPEED * (now < p.guardUntil ? KNIGHT.E.speed : 1) * (now < p.slowUntil ? KNIGHT.R.slow : 1);
      p.x += dx * spd * dt; p.y += dy * spd * dt * 0.8;
      const nx = (p.x - CX) / RX, ny = (p.y - CY) / RY, d = Math.hypot(nx, ny);
      if (d > 1) { p.x = CX + nx / d * RX; p.y = CY + ny / d * RY; }
    }
    p.moving = !!(dx || dy);
    p.hist.push({ t: now, x: p.x, y: p.y });
    while (p.hist.length && p.hist[0].t < now - HIST_MS) p.hist.shift();
  }
  checkTimeout(now);
  stepArrows(dt, now);
  const list = [];
  for (const p of players.values()) {
    if (!p.joined) continue;
    list.push({ id: p.id, name: p.name, hue: p.hue, x: Math.round(p.x * 10) / 10, y: Math.round(p.y * 10) / 10,
      f: p.face, a: Math.round(p.aim * 100) / 100, m: p.moving ? 1 : 0, c: p.cls, r: p.ready ? 1 : 0, o: p.role,
      hp: Math.max(0, Math.round(p.hp)), mh: p.mh, su: Math.max(0, p.stunUntil - now), gd: now < p.guardUntil ? 1 : 0, sl: now < p.slowUntil ? 1 : 0 });
  }
  broadcast({ t: 'state', ph: phase, left: phase === 'round' ? Math.max(0, ROUND_MS - (now - roundStart)) : 0, p: list });
}, 1000 / TICK);

// Drop dead connections
setInterval(() => {
  for (const p of players.values()) {
    if (!p.alive) { p.ws.terminate(); continue; }
    p.alive = false; p.ws.ping();
  }
}, 30000);

server.listen(PORT, () => console.log('Sky Colosseum running on port ' + PORT));
