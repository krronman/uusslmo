const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;
const PUBLIC = path.join(__dirname, 'public');
const MIME = { '.html': 'text/html; charset=utf-8', '.jpg': 'image/jpeg', '.png': 'image/png', '.js': 'text/javascript', '.css': 'text/css', '.txt': 'text/plain; charset=utf-8' };

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
const ROUND_MS = 4 * 60 * 1000;           // a round lasts 4 minutes
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
  Knight: { hp: 1200, dmg: 150, reduce: 0.2, atkCd: 700 },   // passive [Armor]: -20% damage taken; attack every 0.7s
  Archer: { hp: 1000, dmg: 180, reduce: 0, atkCd: 800 },    // shoots an arrow every 0.8s for 180
  Shielder: { hp: 1600, dmg: 80, reduce: 0, atkCd: 800 },  // tank; its defence comes from the shield (see SHIELDER)
  Assassin: { hp: 1000, dmg: 135, reduce: 0, atkCd: 600 },  // fast melee striker; see ASSASSIN
  Gumiho: { hp: 1100, dmg: 130, reduce: 0, atkCd: 700 }     // ranged mage (3.5 radpx orb); see GUMIHO
};
const statsOf = p => CLASS_STATS[p.cls] || BASE;
const RADPX = 112.5;                                       // 1 "radpx" = radius of a character's basic attack range (ground px). Use it for all range numbers.
const MAP = 1254;                                          // background image size (the whole map)
const ARROW = { speed: 800, range: 5 * RADPX, radius: 28 };   // Archer arrows: ground px/s, range = 5 radpx, hit radius
const ARCHER = {
  charge: { maxMs: 2000, min: 0.5, max: 1.5 },                          // passive [Bowstring]: dmg & speed 50% -> 150% over 0-2s of charge
  Q: { cd: 11000, arrows: 7, step: 10 * RAD, dmg: 130, invis: 1500 },   // [Arrow Rain]: 7-arrow fan + 1.5s invisibility
  E: { cd: 15000, dur: 4000 },                                          // [Haste]: 4s of instant (no-charge) 100% arrows
  R: { cd: 25000, dmg: 380, stun: 1000, scale: 8, radius: 90 }   // [Dragon Slayer]: 8x piercing arrow that flies until it is completely off the map
};
const ATK = { range: 1 * RADPX, span: 100 * RAD };         // melee basic attack (F) - every non-Archer class
const KNIGHT = {
  Q: { cd: 8000, range: 2 * RADPX, span: 120 * RAD, dmg: 250, stun: 1000 },   // range = 2 radpx
  E: { cd: 12000, dur: 3000, reduce: 0.7, speed: 1.4 },                 // -70% damage taken, +40% speed
  R: { cd: 25000, swords: 8, ring: 195, radius: 1 * RADPX, cRadius: 2.5 * RADPX, dmg: 200, slow: 0.7, slowMs: 2000 }   // ring & per-sword radius = 1.5x (was 130 / 55)
};

const SHIELDER = {
  span: 90 * RAD, block: 0.8,                                           // passive [방패]: hits from the front 100 deg arc deal -80%
  Q: { cd: 12000, radius: 2.5 * RADPX, ms: 3000, slow: 0.8, stop: 45 },   // [도발]: taunt everyone within 2.5 radpx for 3s, they walk at 80% speed towards you
  E: { cd: 11000, dist: 3.5 * RADPX, dashMs: 450, dmg: 200, hit: 55, kb: RADPX, kbMs: 300, stun: 500 },   // [실드 태클]: dash 3.5 radpx in 0.3s (raise dashMs = slower; 0.45s = a clearly visible dash, not a teleport), 200 dmg, knock back + 0.5s airborne
  R: { cd: 25000, dur: 7000, reduce: 0.3, reflect: 0.4, speed: 0.85 }   // [혼 가드]: 7s, unblocked dmg -30%, blocked dmg 0, reflect melee 40%, deflect projectiles, own speed -15%
};

const ASSASSIN = {                                                       // passive [피어스]: every hit ignores the target's damage reduction (see dmgTo)
  Q: { cd: 12000, range: 2 * RADPX, width: 45, dmg: 250, markMs: 3000, mark: 0.2 },   // [소드 샤우트]: thrust 2 radpx, 250 dmg, target takes +20% damage for 3s
  E: { cd: 10000, dur: 2500, speed: 1.15 },                                           // [은신]: invisible 2.5s, +15% speed; attacking ends it
  R: { cd: 25000, radius: RADPX, dmg: 250, asMs: 3000, as: 0.1, asPerHit: 0.1 }       // [암살]: blink to the cursor, 250 dmg within 1 radpx, then +10% attack speed (+10% per enemy hit) for 3s
};
const GUMIHO = {
  atk: { range: 3.5 * RADPX, speed: 1020, radius: 30 },                    // basic attack: a magic orb, 3.5 radpx
  fire: { chance: 0.75, max: 5, pick: 55, lift: 25 },                      // passive [여우불]: 60% on every orb landing, at most 5, cursor pick radius, hover height
  eff: { dmg: 120, tick: 20, tickMs: 500, ms: 2000, radius: 2 * RADPX },  // the Foxfire "effect": 120 damage + 20 every 0.5s for 2s, blast radius 2 radpx
  Q: { cd: 8000 },                                                        // [요술]
  E: { cd: 12000, pullMs: 500, dmg: 120, rad: 0.5 * RADPX },                                // [미수옥]
  R: { cd: 25000, radius: 2.5 * RADPX, ms: 3000, speed: 0.8, stop: 45 }   // [매혹]: charm for 3s, they walk towards you at 80% speed
};
const atkSpeed = (p, now) => now < p.asUntil ? 1 + p.asBonus : 1;           // attack speed multiplier (Assassin R buff)
const breakStealth = p => { if (p.cls === 'Assassin') p.invisUntil = 0; };   // an Assassin's attack ends its invisibility

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
function offMapRange(x, y, a, sc) {      // ground distance an arrow must fly until its whole sprite is outside the map image
  const L = 14 * 5 * sc, half = 3 * 5 * sc / 2;           // sprite length / half thickness on screen (PX = 5), same maths as the client
  const th = Math.atan2(0.8 * Math.sin(a), Math.cos(a)), ux = Math.cos(th), uy = Math.sin(th), nx = -uy, ny = ux;
  for (let d = 0; d < 4000; d += 10) {
    const tx = x + Math.cos(a) * (d + 28), ty = y + Math.sin(a) * (d + 28) * 0.8 - 30;   // arrow tip on screen
    const cs = [[0, 1], [L, 1], [0, -1], [L, -1]].map(([l, sd]) => [tx - ux * l + nx * sd * half, ty - uy * l + ny * sd * half]);
    if (cs.every(c => c[0] < 0) || cs.every(c => c[0] > MAP) || cs.every(c => c[1] < 0) || cs.every(c => c[1] > MAP)) return d;
  }
  return 4000;
}
function endArrow(ar) { arrows.delete(ar.id); broadcast({ t: 'arrowEnd', id: ar.id }); }
function moveArrow(ar, step, time) {          // advances the arrow; returns the targets it hit (judged at `time`)
  const nx = ar.x + Math.cos(ar.a) * step, ngy = ar.gy + Math.sin(ar.a) * step;
  const found = [];
  if (phase === 'round') for (const t of players.values()) {
    if (t.id === ar.owner || !t.joined || t.role !== 1 || ar.hitIds.has(t.id)) continue;
    const tp = posAt(t, time);
    if (segDist(tp.x, tp.y / 0.8, ar.x, ar.gy, nx, ngy) > ar.radius) continue;
    found.push({ t, d: Math.hypot(tp.x - ar.x, tp.y / 0.8 - ar.gy) });
  }
  found.sort((a, b) => a.d - b.d);
  if (ar.pierce) {                             // piercing: hits everyone on the way once and keeps flying
    for (const f of found) ar.hitIds.add(f.t.id);
    ar.x = nx; ar.gy = ngy; ar.left -= step;
    return found.map(f => f.t);
  }
  if (found.length) return [found[0].t];       // normal arrow: stops at the first enemy
  ar.x = nx; ar.gy = ngy; ar.left -= step;
  return [];
}
function arrowHit(ar, t, now) {                  // returns true when a Horn Guard shield turned the arrow around
  const inDir = ar.a + Math.PI;                 // direction (from the target) the arrow came from
  if (t.cls === 'Shielder' && now < t.hornUntil && shieldBlocks(t, { dir: inDir })) { deflectArrow(ar, t); return true; }
  dmgTo(t, ar.dmg, now, { dir: inDir, kill: players.get(ar.owner) });
  if (ar.stun && t.role === 1) t.stunUntil = now + ar.stun;
  if (ar.orb && ar.eff) { const g = players.get(ar.owner); if (g) foxHit(t, now, g, GUMIHO.eff.dmg, { dir: inDir, kill: g }); }   // the empowered orb also carries the Foxfire effect
  return false;
}
function deflectArrow(ar, t) {                  // [혼 가드]: the arrow flies back the way it came and now belongs to the Shielder
  broadcast({ t: 'arrowEnd', id: ar.id });
  ar.owner = t.id; ar.a = Math.atan2(-Math.sin(ar.a), -Math.cos(ar.a)); ar.hitIds = new Set();
  ar.left = ar.noArena ? offMapRange(ar.x, ar.gy * 0.8, ar.a, ar.sc) : ARROW.range;
  broadcast({ t: 'arrow', id: ar.id, by: t.id, x: ar.x, y: ar.gy * 0.8, a: ar.a, spd: ar.spd, range: ar.left, adv: 0, sc: ar.sc, kd: 'refl' });
  broadcast({ t: 'hit', id: t.id, dmg: 0, bl: 2 });
}
// spec: { a, dmg, spd, kind, range?, radius?, pierce?, stun?, sc? }
function spawnArrow(p, o, lag, now, spec) {
  const id = ++arrowSeq;
  const ar = { id, owner: p.id, x: o.x, gy: o.y / 0.8, a: spec.a, dmg: spec.dmg, spd: spec.spd, radius: spec.radius || ARROW.radius,
    orb: !!spec.orb, eff: !!spec.eff, boom: spec.boom || 0, pierce: !!spec.pierce, noArena: !!spec.noArena, sc: spec.sc || 1, stun: spec.stun || 0, hitIds: new Set(), left: spec.range || ARROW.range };
  let adv = 0, ended = false;
  const pending = [];
  const steps = lag > 0 ? Math.ceil(lag / 33) : 0, stepMs = steps ? lag / steps : 0;
  for (let i = 1; i <= steps && !ended; i++) {       // replay the time the shooter already "lived" against old target positions
    const step = Math.min(ar.spd * stepMs / 1000, ar.left);
    const hits = moveArrow(ar, step, now - lag + i * stepMs);
    pending.push(...hits);
    if (!ar.pierce && hits.length) ended = true; else adv += step;
  }
  broadcast({ t: 'arrow', id, by: p.id, x: o.x, y: o.y, a: spec.a, spd: ar.spd, range: ar.left + adv, adv, sc: spec.sc || 1, kd: spec.kind || 'atk', bm: spec.boom || 0 });
  let deflected = false;
  for (const t of pending) if (arrowHit(ar, t, now)) { deflected = true; break; }
  if (ended && !deflected) { broadcast({ t: 'arrowEnd', id }); orbLand(ar, pending[0], now); } else arrows.set(id, ar);
  if (pending.length) checkRoundEnd();
}
function stepArrows(dt, now) {
  let any = false;
  for (const ar of arrows.values()) {
    const hits = moveArrow(ar, Math.min(ar.spd * dt, ar.left), now);
    let deflected = false;
    for (const t of hits) { any = true; if (arrowHit(ar, t, now)) { deflected = true; break; } }
    if (deflected) continue;                                     // turned around: keeps flying
    if (!ar.pierce && hits.length) { endArrow(ar); orbLand(ar, hits[0], now); continue; }
    const ex = (ar.x - CX) / RX, ey = (ar.gy * 0.8 - CY) / RY;
    if (ar.left <= 0 || (!ar.noArena && ex * ex + ey * ey > 1.15)) { endArrow(ar); orbLand(ar, null, now); }
  }
  if (any) checkRoundEnd();
}

function resetCombat(p) {
  p.mh = p.hp = statsOf(p).hp;
  p.atkReady = p.cdQ = p.cdE = p.cdR = 0;
  p.stunUntil = p.guardUntil = p.slowUntil = 0;
  p.chargeStart = p.hasteUntil = p.invisUntil = 0;
  p.tauntUntil = p.tauntBy = p.kbUntil = p.hornUntil = 0; p.dash = null;
  p.markUntil = p.asUntil = p.asBonus = 0;
  p.fires = []; p.qNext = false; p.eNext = 0; p.pull = null; p.lastBy = 0; p.charmUntil = p.charmBy = p.burnUntil = p.burnNext = 0;
  for (const k of ['Q', 'E', 'R']) send(p.ws, { t: 'cd', k, ms: 0 });
}
function killPlayer(p) {
  const was = p.role === 1, k = was && p.lastBy && Date.now() - p.lastByT < 10000 ? players.get(p.lastBy) : null;
  p.hp = 0; p.role = 2; p.dx = p.dy = 0; p.moving = false; p.deathOrder = ++deathCounter;
  if (was) broadcast({ t: 'kill', k: k ? k.id : 0, kn: k ? k.name : '', kc: k ? k.cls : '', v: p.id, vn: p.name, vc: p.cls });
}
function shieldBlocks(t, src) {                      // does an attack from `src` hit the Shielder's shield?
  if (t.cls !== 'Shielder' || !src) return false;    // src: {x,y} = where the attack comes from, or {dir} = incoming direction (ground plane)
  let dir = src.dir;
  if (dir === undefined) {
    if (!src.basic) return false;                    // only basic melee attacks (src.basic) and projectiles (src.dir) can be blocked
    const dx = src.x - t.x, dy = (src.y - t.y) / 0.8;
    if (Math.hypot(dx, dy) < 10) return false;
    dir = Math.atan2(dy, dx);
  }
  return Math.abs(Math.atan2(Math.sin(dir - t.aim), Math.cos(dir - t.aim))) <= SHIELDER.span / 2;
}
// src (optional): { x, y, by } for melee/area attacks (by = the attacker), { dir } for projectiles. Without it nothing can be blocked.
function dmgTo(t, amount, now, src) {
  const pierce = !!(src && src.by && src.by.cls === 'Assassin');   // Assassin passive [피어스]: ignores every damage reduction and invincibility
  if (!pierce && now < (t.invulnUntil || 0)) return;               // (hook for future invincibility skills - none exist yet)
  let cut = 0, blocked = false;
  if (!pierce) {
    cut = statsOf(t).reduce;                         // Armor: 20%
    if (now < t.guardUntil) cut += KNIGHT.E.reduce;  // Guard Rush: +70% (added together -> 90% total)
    blocked = shieldBlocks(t, src);
    if (blocked) cut += SHIELDER.block;              // [방패]: -80% from the front
    else if (t.cls === 'Shielder' && now < t.hornUntil) cut += SHIELDER.R.reduce;   // [혼 가드]: unblocked damage -30%
  }
  let d = (blocked && now < t.hornUntil) ? 0 : Math.max(1, Math.round(amount * (1 - Math.min(cut, 0.95))));   // [혼 가드]: damage the shield blocks is fully nullified
  if (d > 0 && now < t.markUntil) d = Math.round(d * (1 + ASSASSIN.Q.mark));   // [소드 샤우트] mark: +20% damage taken (not a reduction, so it always applies)
  t.hp -= d;
  if (src && (src.by || src.kill)) { t.lastBy = (src.by || src.kill).id; t.lastByT = now; }
  broadcast({ t: 'hit', id: t.id, dmg: d, bl: blocked ? 1 : 0 });
  if (blocked && src.by && now < t.hornUntil && src.by.role === 1) {              // [혼 가드]: a blocked melee hit hurts the attacker (40% of the attack's damage)
    const back = Math.round(amount * SHIELDER.R.reflect);
    if (back > 0) dmgTo(src.by, back, now, { kill: t });
  }
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
const canAct = (p, now) => p.joined && p.role !== 2 && now >= p.stunUntil && now >= p.charmUntil;   // a charmed player cannot attack or use skills

function archerAttack(p, m, now) {              // F released (charged shot) or F pressed during Haste (instant shot)
  const st = statsOf(p), o = originOf(p, m), lag = lagOf(m), C = ARCHER.charge;
  let f = 1;                                    // damage & speed multiplier
  if (now >= p.hasteUntil) {
    if (!p.chargeStart) return;                 // nothing was being charged
    const ch = Math.min(now - p.chargeStart, C.maxMs);
    f = C.min + (C.max - C.min) * ch / C.maxMs;
  }
  p.chargeStart = 0;
  if (now < p.atkReady - 60) return;            // small slack for network jitter
  p.atkReady = now + st.atkCd;
  spawnArrow(p, o, lag, now, { a: p.aim, dmg: Math.round(st.dmg * f), spd: ARROW.speed * f, kind: 'atk' });
}
function doAttack(p, m) {
  const now = Date.now();
  if (!canAct(p, now)) return;
  if (p.cls === 'Archer') return archerAttack(p, m, now);
  if (p.cls === 'Gumiho') return gumihoAttack(p, m, now);
  if (now < p.atkReady) return;
  const st = statsOf(p), o = originOf(p, m), lag = lagOf(m);
  p.atkReady = now + st.atkCd / atkSpeed(p, now);
  breakStealth(p);
  broadcast({ t: 'fx', type: 'cone', by: p.id, x: o.x, y: o.y, a: p.aim, span: ATK.span, r: ATK.range, c: 'rgba(255,255,255,.6)', dur: 220 });
  for (const t of targetsOf(p)) {
    const tp = posAt(t, now - lag);
    if (inConeAt(o.x, o.y, p.aim, tp.x, tp.y, ATK.range, ATK.span)) dmgTo(t, st.dmg, now, { x: o.x, y: o.y, by: p, basic: true });
  }
  checkRoundEnd();
}
function doSkill(p, k, m) {
  const now = Date.now();
  if (!['Q', 'E', 'R'].includes(k) || !canAct(p, now) || now < p['cd' + k]) return;
  if (p.cls === 'Knight') knightSkill(p, k, m, now);
  else if (p.cls === 'Archer') archerSkill(p, k, m, now);
  else if (p.cls === 'Shielder') shielderSkill(p, k, m, now);
  else if (p.cls === 'Assassin') assassinSkill(p, k, m, now);
  else if (p.cls === 'Gumiho') gumihoSkill(p, k, m, now);
}
function archerSkill(p, k, m, now) {
  const S = ARCHER[k], o = originOf(p, m), lag = lagOf(m);
  p['cd' + k] = now + S.cd; send(p.ws, { t: 'cd', k, ms: S.cd });
  if (k === 'Q') {
    for (let i = 0; i < S.arrows; i++) {
      const a = p.aim + (i - (S.arrows - 1) / 2) * S.step;
      spawnArrow(p, o, lag, now, { a, dmg: S.dmg, spd: ARROW.speed, kind: 'Q' });
    }
    p.invisUntil = now + S.invis;
  } else if (k === 'E') {
    p.hasteUntil = now + S.dur; p.chargeStart = 0;
  } else {
    spawnArrow(p, o, lag, now, { a: p.aim, dmg: S.dmg, spd: ARROW.speed, range: offMapRange(o.x, o.y, p.aim, S.scale), noArena: true, radius: S.radius, pierce: true, stun: S.stun, sc: S.scale, kind: 'R' });
  }
}
// ---- Gumiho ----
const clampArena = pt => { const nx = (pt.x - CX) / RX, ny = (pt.y - CY) / RY, d = Math.hypot(nx, ny); return d > 0.97 ? { x: CX + nx / d * 0.97 * RX, y: CY + ny / d * 0.97 * RY } : { x: pt.x, y: pt.y }; };
let fireSeq = 0;
function spawnFoxfire(g, pos) {                       // at most 5; a 6th removes the oldest
  const c = clampArena(pos);
  g.fires.push({ id: ++fireSeq, x: c.x, y: c.y });
  while (g.fires.length > GUMIHO.fire.max) g.fires.shift();
}
function orbLand(ar, hitT, now) {                     // passive [여우불]: where the orb lands (on an enemy or at the end of its range) 60% to leave a Foxfire
  if (!ar.orb || phase !== 'round') return;
  const g = players.get(ar.owner);
  if (!g || g.cls !== 'Gumiho' || g.role !== 1) return;
  if (ar.boom) {                                      // [미수옥]-empowered orb: blasts where it lands, radius +1.5 radpx and damage +150 per collected Foxfire
    const at = hitT ? { x: hitT.x, y: hitT.y } : { x: ar.x, y: ar.gy * 0.8 }, rad = ar.boom * GUMIHO.E.rad;
    broadcast({ t: 'fx', type: 'ring', x: at.x, y: at.y, r: rad, c: '#7fe9ff', dur: 700 });
    for (const t of targetsOf(g)) if (t !== hitT && Math.hypot(t.x - at.x, (t.y - at.y) / 0.8) <= rad) dmgTo(t, ar.dmg, now, { x: at.x, y: at.y, kill: g });
    checkRoundEnd();
    if (phase !== 'round') return;
  }
  if (!hitT || Math.random() >= GUMIHO.fire.chance) return;   // Foxfire only where the orb hit an enemy (never in mid-air / at max range)
  spawnFoxfire(g, { x: hitT.x, y: hitT.y });
}
function foxHit(t, now, by, dmg, src) {               // the Foxfire effect: damage now + burning (20 every 0.5s for 2s; re-applying refreshes it)
  dmgTo(t, dmg, now, src);
  if (t.role !== 1) return;
  t.burnUntil = now + GUMIHO.eff.ms; t.burnNext = now + GUMIHO.eff.tickMs; t.burnBy = by.id;
}
function foxBlast(p, at, now, lag, dmg) {
  broadcast({ t: 'fx', type: 'ring', x: at.x, y: at.y, r: GUMIHO.eff.radius, c: '#7fe9ff', dur: 600 });
  for (const t of targetsOf(p)) {
    const tp = posAt(t, now - lag);
    if (Math.hypot(tp.x - at.x, (tp.y - at.y) / 0.8) <= GUMIHO.eff.radius) foxHit(t, now, p, dmg, { x: at.x, y: at.y, kill: p });
  }
}
function gumihoAttack(p, m, now) {
  if (now < p.atkReady) return;
  const st = statsOf(p), o = originOf(p, m), lag = lagOf(m);
  p.atkReady = now + st.atkCd;
  const eff = p.qNext, n = p.eNext || 0; p.qNext = false; p.eNext = 0;   // Q with no Foxfire left: carries the effect; E: n collected Foxfires empower it
  spawnArrow(p, o, lag, now, { a: p.aim, dmg: st.dmg + n * GUMIHO.E.dmg, boom: n, spd: GUMIHO.atk.speed, range: GUMIHO.atk.range, radius: GUMIHO.atk.radius, kind: 'orb', orb: true, eff });
}
function gumihoSkill(p, k, m, now) {
  const G = GUMIHO, o = originOf(p, m), lag = lagOf(m);
  if (k === 'Q') {                                    // [요술]
    let target = null;
    if (p.fires.length) {                             // the Foxfire under the cursor is the one to teleport to
      const cx = Number(m && m.cx), cy = Number(m && m.cy);
      let best = G.fire.pick;
      for (const f of p.fires) { const d = Math.hypot(cx - f.x, cy - (f.y - G.fire.lift)); if (d <= best) { best = d; target = f; } }
      if (!target) return;                            // nothing under the cursor: nothing happens (no cooldown)
    }
    p.cdQ = now + G.Q.cd; send(p.ws, { t: 'cd', k, ms: G.Q.cd });
    if (target) {
      p.fires.splice(p.fires.indexOf(target), 1);
      broadcast({ t: 'fx', type: 'dash', x: o.x, y: o.y, x2: target.x, y2: target.y, c: 'rgba(120,230,255,.6)', dur: 350 });
      p.x = target.x; p.y = target.y;
      send(p.ws, { t: 'warp', x: p.x, y: p.y });
    }
    if (p.fires.length) {                             // the nearest remaining Foxfire explodes
      let nf = null, nd = Infinity;
      for (const f of p.fires) { const d = Math.hypot(f.x - p.x, (f.y - p.y) / 0.8); if (d < nd) { nd = d; nf = f; } }
      p.fires.splice(p.fires.indexOf(nf), 1);
      foxBlast(p, nf, now, lag, G.eff.dmg);
    } else p.qNext = true;                            // none left: the next attack carries the effect
  } else if (k === 'E') {                             // [미수옥]
    if (!p.fires.length) return;                      // nothing to pull (no cooldown)
    p.cdE = now + G.E.cd; send(p.ws, { t: 'cd', k, ms: G.E.cd });
    const list = p.fires.splice(0);
    p.eNext = list.length;                            // the next basic attack is empowered
    broadcast({ t: 'fx', type: 'pull', x: o.x, y: o.y, pts: list.map(f => [Math.round(f.x), Math.round(f.y)]), dur: G.E.pullMs });
  } else {                                            // [매혹]
    p.cdR = now + G.R.cd; send(p.ws, { t: 'cd', k, ms: G.R.cd });
    broadcast({ t: 'fx', type: 'ring', x: o.x, y: o.y, r: G.R.radius, c: '#ff8fc0', dur: 700 });
    for (const t of targetsOf(p)) {
      const tp = posAt(t, now - lag);
      if (Math.hypot(tp.x - o.x, (tp.y - o.y) / 0.8) > G.R.radius) continue;
      t.charmUntil = now + G.R.ms; t.charmBy = p.id; t.chargeStart = 0;
    }
  }
  checkRoundEnd();
}
function assassinSkill(p, k, m, now) {
  const S = ASSASSIN[k], o = originOf(p, m), lag = lagOf(m);
  p['cd' + k] = now + S.cd; send(p.ws, { t: 'cd', k, ms: S.cd });
  if (k === 'E') { p.invisUntil = now + S.dur; return; }                // [은신]
  breakStealth(p);                                                       // Q and R are attacks
  if (k === 'Q') {                                                       // [소드 샤우트]: a long, narrow thrust
    const a = p.aim, gx = o.x, gy = o.y / 0.8, ex = gx + Math.cos(a) * S.range, ey = gy + Math.sin(a) * S.range;
    broadcast({ t: 'fx', type: 'thrust', x: o.x, y: o.y, a, len: S.range, w: S.width, dur: 320 });
    for (const t of targetsOf(p)) {
      const tp = posAt(t, now - lag);
      if (segDist(tp.x, tp.y / 0.8, gx, gy, ex, ey) > S.width) continue;
      dmgTo(t, S.dmg, now, { x: o.x, y: o.y, by: p });
      if (t.role === 1) t.markUntil = now + S.markMs;
    }
  } else {                                                               // [암살]: blink to the cursor, then strike everything around the landing point
    let tx = Number(m && m.cx), ty = Number(m && m.cy) + 30;            // the client sends the cursor; the body centre sits 30px above the feet
    if (!Number.isFinite(tx) || !Number.isFinite(ty)) { tx = o.x + Math.cos(p.aim) * 2 * RADPX; ty = o.y + Math.sin(p.aim) * 2 * RADPX * 0.8; }
    const nx = (tx - CX) / RX, ny = (ty - CY) / RY, d = Math.hypot(nx, ny);
    if (d > 1) { tx = CX + nx / d * RX; ty = CY + ny / d * RY; }         // stay inside the arena
    broadcast({ t: 'fx', type: 'dash', x: o.x, y: o.y, x2: tx, y2: ty, c: 'rgba(190,120,255,.6)', dur: 380 });
    p.x = tx; p.y = ty;
    send(p.ws, { t: 'warp', x: tx, y: ty });
    broadcast({ t: 'fx', type: 'ring', x: tx, y: ty, r: S.radius, c: '#c98bff', dur: 500 });
    let n = 0;
    for (const t of targetsOf(p)) {
      const tp = posAt(t, now - lag);
      if (Math.hypot(tp.x - tx, (tp.y - ty) / 0.8) > S.radius) continue;
      dmgTo(t, S.dmg, now, { x: tx, y: ty, by: p }); n++;
    }
    p.asUntil = now + S.asMs; p.asBonus = S.as + S.asPerHit * n;         // +10%, and +10% more for every enemy hit
  }
  checkRoundEnd();
}
function dashHits(p, D, px, py, now) {            // enemies touched by the dasher between its previous and current position
  let any = false;
  for (const t of targetsOf(p)) {
    if (D.hit.has(t.id)) continue;
    const tp = posAt(t, now - D.lag);
    if (segDist(tp.x, tp.y / 0.8, px, py / 0.8, p.x, p.y / 0.8) > SHIELDER.E.hit) continue;
    D.hit.add(t.id); any = true;
    const S = SHIELDER.E;
    dmgTo(t, S.dmg, now, { x: D.sx, y: D.sy, by: p });
    if (t.role !== 1) continue;
    t.stunUntil = Math.max(t.stunUntil, now + S.stun);                           // launched into the air
    const v = S.kb / (S.kbMs / 1000);
    t.kbUntil = now + S.kbMs; t.kbx = Math.cos(D.a) * v; t.kby = Math.sin(D.a) * v;   // ...and pushed along the dash
  }
  return any;
}
function shielderSkill(p, k, m, now) {
  const S = SHIELDER[k], o = originOf(p, m), lag = lagOf(m);
  p['cd' + k] = now + S.cd; send(p.ws, { t: 'cd', k, ms: S.cd });
  if (k === 'Q') {                                   // [도발]
    broadcast({ t: 'fx', type: 'ring', x: o.x, y: o.y, r: S.radius, dur: 700 });
    for (const t of targetsOf(p)) {
      const tp = posAt(t, now - lag);
      if (Math.hypot(tp.x - o.x, (tp.y - o.y) / 0.8) <= S.radius) { t.tauntUntil = now + S.ms; t.tauntBy = p.id; }
    }
  } else if (k === 'E') {                            // [실드 태클]
    const a = p.aim, gx = o.x, gy = o.y / 0.8;
    const inside = d => { const nx = (gx + Math.cos(a) * d - CX) / RX, ny = ((gy + Math.sin(a) * d) * 0.8 - CY) / RY; return nx * nx + ny * ny <= 1; };
    let len = S.dist;
    while (len > 0 && !inside(len)) len -= 5;        // stop at the arena edge
    len = Math.max(0, len);
    const ex = gx + Math.cos(a) * len, egy = gy + Math.sin(a) * len;
    broadcast({ t: 'fx', type: 'dash', by: p.id, x: o.x, y: o.y, x2: ex, y2: egy * 0.8, a, span: ATK.span, dur: S.dashMs + 150, follow: 1 });
    p.x = o.x; p.y = o.y;
    p.dash = { sx: o.x, sy: o.y, ex, ey: egy * 0.8, a, t0: now, ms: S.dashMs, lag, hit: new Set() };   // moved a little every tick by the simulation
  } else {                                           // [혼 가드]
    p.hornUntil = now + S.dur;
  }
  checkRoundEnd();
}
function knightSkill(p, k, m, now) {
  const S = KNIGHT[k], o = originOf(p, m), lag = lagOf(m);
  p['cd' + k] = now + S.cd; send(p.ws, { t: 'cd', k, ms: S.cd });
  if (k === 'Q') {
    broadcast({ t: 'fx', type: 'cone', by: p.id, x: o.x, y: o.y, a: p.aim, span: S.span, r: S.range, c: 'rgba(255,214,107,.65)', dur: 380 });
    for (const t of targetsOf(p)) {
      const tp = posAt(t, now - lag);
      if (inConeAt(o.x, o.y, p.aim, tp.x, tp.y, S.range, S.span)) { dmgTo(t, S.dmg, now, { x: o.x, y: o.y, by: p }); if (t.role === 1) t.stunUntil = now + S.stun; }
    }
  } else if (k === 'E') {
    p.guardUntil = now + S.dur;
  } else {
    broadcast({ t: 'fx', type: 'swords', x: o.x, y: o.y, r: S.ring, ar: S.radius, cr: S.cRadius, n: S.swords, dur: 900 });
    const gy = o.y / 0.8, sw = [];
    for (let n = 0; n < S.swords; n++) { const a = n * 2 * Math.PI / S.swords; sw.push({ x: o.x + Math.cos(a) * S.ring, y: gy + Math.sin(a) * S.ring, r: S.radius }); }
    sw.push({ x: o.x, y: gy, r: S.cRadius });                           // the big sword in the centre
    for (const s of sw) {
      for (const t of targetsOf(p)) {
        const tp = posAt(t, now - lag);
        if (t.role !== 1 || Math.hypot(tp.x - s.x, tp.y / 0.8 - s.y) > s.r + 10) continue;
        dmgTo(t, S.dmg, now, { x: o.x, y: o.y, by: p });
        if (t.role === 1) t.slowUntil = now + S.slowMs;
      }
    }
  }
  checkRoundEnd();
}

function checkTimeout(now) {
  if (phase !== 'round' || now - roundStart < ROUND_MS) return;
  endRound(null, [...players.values()].filter(p => p.role === 1).map(p => p.name));   // everyone still alive shares 2nd place
}

// ================= accounts (Upstash Redis REST; in-memory fallback for local testing only) =================
const UP_URL = process.env.UPSTASH_REDIS_REST_URL, UP_TOKEN = process.env.UPSTASH_REDIS_REST_TOKEN;
const KEY = 'mpvp:', SESSION_TTL = 30 * 24 * 3600, LOCK_FAILS = 8, LOCK_SEC = 600;
async function upstash(...cmd) {
  const r = await fetch(UP_URL, { method: 'POST', headers: { Authorization: 'Bearer ' + UP_TOKEN, 'Content-Type': 'application/json' },
    body: JSON.stringify(cmd), signal: AbortSignal.timeout(8000) });
  const j = await r.json().catch(() => ({}));
  if (!r.ok || j.error) throw new Error('upstash: ' + (j.error || r.status));
  return j.result;
}
const mem = new Map();
const memGet = k => { const e = mem.get(k); if (!e) return null; if (e.exp && e.exp < Date.now()) { mem.delete(k); return null; } return e; };
const db = (UP_URL && UP_TOKEN) ? {
  get: k => upstash('GET', KEY + k),
  set: (k, v) => upstash('SET', KEY + k, v),
  setnx: async (k, v) => (await upstash('SET', KEY + k, v, 'NX')) === 'OK',
  setex: (k, sec, v) => upstash('SET', KEY + k, v, 'EX', sec),
  del: k => upstash('DEL', KEY + k),
  incr: k => upstash('INCR', KEY + k),
  expire: (k, sec) => upstash('EXPIRE', KEY + k, sec)
} : {
  get: async k => { const e = memGet(k); return e ? e.v : null; },
  set: async (k, v) => { mem.set(k, { v }); },
  setnx: async (k, v) => { if (memGet(k)) return false; mem.set(k, { v }); return true; },
  setex: async (k, sec, v) => { mem.set(k, { v, exp: Date.now() + sec * 1000 }); },
  del: async k => { mem.delete(k); },
  incr: async k => { const e = memGet(k), n = (e ? Number(e.v) : 0) + 1; mem.set(k, { v: String(n), exp: e && e.exp }); return n; },
  expire: async (k, sec) => { const e = memGet(k); if (e) e.exp = Date.now() + sec * 1000; }
};
console.log((UP_URL && UP_TOKEN) ? 'Accounts: Upstash Redis' : 'WARNING: UPSTASH_REDIS_REST_URL / UPSTASH_REDIS_REST_TOKEN not set - accounts live in memory and are LOST on restart');

const scryptHex = (pw, salt) => new Promise((res, rej) => crypto.scrypt(pw, salt, 64, (e, k) => e ? rej(e) : res(k.toString('hex'))));
const sha = s => crypto.createHash('sha256').update(s).digest('hex');
const safeEq = (a, b) => { const x = Buffer.from(String(a)), y = Buffer.from(String(b)); return x.length === y.length && crypto.timingSafeEqual(x, y); };
const DUMMY_SALT = '0'.repeat(32);
const normId = s => { s = String(s || '').trim().toLowerCase(); return /^[a-z0-9_]{4,16}$/.test(s) ? s : ''; };
const isToken = t => typeof t === 'string' && /^[0-9a-f]{64}$/.test(t);

const rates = new Map();                                   // per-IP limits (in memory): key -> {n, t}
function rateOk(key, max, windowMs) {
  const now = Date.now(); let h = rates.get(key);
  if (!h || now - h.t > windowMs) { h = { n: 0, t: now }; rates.set(key, h); }
  return ++h.n <= max;
}
setInterval(() => { const lim = Date.now() - 3600 * 1000; for (const [k, h] of rates) if (h.t < lim) rates.delete(k); }, 60000);

const authFail = (p, err, extra) => send(p.ws, Object.assign({ t: 'auth', ok: 0, err }, extra));
function kickOld(userId, except) {                          // one live session per account: the newest login wins
  for (const q of [...players.values()]) if (q !== except && q.user === userId) {
    q.user = null; q.joined = false; send(q.ws, { t: 'kicked' }); try { q.ws.close(); } catch {}
  }
}
// ---- titles (granted by the admin account, equipped by the owner; stored in Upstash) ----
const ADMIN_ID = 'admin', OBS_ID = 'server', MAX_TITLES = 15;   // OBS_ID: viewer-only account (no character, not counted, never affects the game)
const isHex = c => typeof c === 'string' && /^#[0-9a-fA-F]{6}$/.test(c);
async function loadTitles(id) {
  try {
    const raw = await db.get('titles:' + id); let list = raw ? JSON.parse(raw) : [];
    if (!Array.isArray(list)) list = [];
    const eq = await db.get('eqtitle:' + id);
    return { list, eq: list.some(t => t.id === eq) ? eq : null };
  } catch (e) { console.error('titles load failed:', e.message); return { list: [], eq: null }; }
}
const titleOf = p => { const t = p.titles.find(t => t.id === p.eq); return t ? { x: t.text, c: t.color, cs: t.cols || 0 } : null; };
const pushTitle = p => broadcast({ t: 'ttl', id: p.id, tt: titleOf(p) || 0 });       // everybody learns what p wears
const sendTinfo = p => send(p.ws, { t: 'tinfo', list: p.titles, eq: p.eq });
async function equipTitle(p, id) {
  const now = Date.now();
  if (!p.user) return;
  if (now - p.lastEquip < 300 || (id !== null && (typeof id !== 'string' || !p.titles.some(t => t.id === id)))) return sendTinfo(p);   // refused: resync the client
  p.lastEquip = now;
  if (id) await db.set('eqtitle:' + p.user, id); else await db.del('eqtitle:' + p.user);
  p.eq = id; sendTinfo(p); pushTitle(p);
}
let admLock = Promise.resolve();                           // admin edits run one after another
const adminTitle = (p, m) => { const run = admLock.then(() => adminTitleRun(p, m)); admLock = run.catch(() => {}); return run; };
async function adminTitleRun(p, m) {
  const reply = (ok, msg, extra) => send(p.ws, Object.assign({ t: 'tadmin', ok, msg }, extra));
  const target = normId(m.target);
  if (!target) return reply(0, '대상 아이디가 올바르지 않습니다.');
  const raw = await db.get('user:' + target);
  if (!raw) return reply(0, '존재하지 않는 아이디입니다.');
  const rec = JSON.parse(raw), lraw = await db.get('titles:' + target);
  let list = lraw ? JSON.parse(lraw) : [], msg = '조회했습니다.';
  if (m.t === 'tgrant') {
    const text = Array.from(clean(m.text, 24)).slice(0, 12).join(''), chars = Array.from(text);
    let cols = null;
    if (m.cols !== undefined && m.cols !== null) {                       // per-character colours: one hex colour for every character
      if (!Array.isArray(m.cols) || m.cols.length !== chars.length || !m.cols.every(isHex)) return reply(0, '글자별 색상이 올바르지 않습니다.');
      cols = m.cols.map(c => c.toLowerCase());
    }
    const color = isHex(m.color) ? m.color.toLowerCase() : cols ? cols[0] : null;
    if (!text) return reply(0, '칭호를 입력해 주세요.');
    if (!color) return reply(0, '색상이 올바르지 않습니다.');
    if (list.length >= MAX_TITLES) return reply(0, '칭호는 최대 ' + MAX_TITLES + '개까지 부여할 수 있습니다.');
    list.push(cols ? { id: crypto.randomBytes(4).toString('hex'), text, color, cols } : { id: crypto.randomBytes(4).toString('hex'), text, color });
    await db.set('titles:' + target, JSON.stringify(list));
    msg = '[' + text + '] 칭호를 ' + rec.nick + '님에게 부여했습니다.';
  } else if (m.t === 'trevoke') {
    const i = list.findIndex(t => t.id === m.id);
    if (i < 0) return reply(0, '해당 칭호가 없습니다.');
    const [gone] = list.splice(i, 1);
    await db.set('titles:' + target, JSON.stringify(list));
    if (await db.get('eqtitle:' + target) === gone.id) await db.del('eqtitle:' + target);
    msg = '[' + gone.text + '] 칭호를 삭제했습니다.';
  }
  for (const q of players.values()) if (q.user === target) {   // update the target right away if they are online
    q.titles = list; if (!list.some(t => t.id === q.eq)) q.eq = null;
    sendTinfo(q); pushTitle(q);
  }
  reply(1, msg, { target, nick: rec.nick, list });
}
async function loginOk(p, rec, token) {
  kickOld(rec.id, p);
  p.user = rec.id; p.name = rec.nick;
  if (rec.id === OBS_ID) {                                  // observer: stays joined=false -> not in the state list, online count, ready check or targets
    p.obs = true; p.titles = []; p.eq = null;
    send(p.ws, { t: 'auth', ok: 1, name: rec.nick, token, admin: 0, obs: 1 });
    const all = {};
    for (const q of players.values()) if (q.joined) { const tt = titleOf(q); if (tt) all[q.id] = tt; }
    return send(p.ws, { t: 'ttls', m: all });
  }
  const ti = await loadTitles(rec.id);
  p.titles = ti.list; p.eq = ti.eq;
  if (!p.joined) { p.joined = true; if (phase === 'round') p.role = 2; }   // joined mid-round -> spectate
  send(p.ws, { t: 'auth', ok: 1, name: rec.nick, token, admin: rec.id === ADMIN_ID ? 1 : 0 });
  sendTinfo(p);
  const all = {};                                          // what everybody else is wearing
  for (const q of players.values()) if (q.joined && q !== p) { const tt = titleOf(q); if (tt) all[q.id] = tt; }
  send(p.ws, { t: 'ttls', m: all });
  if (titleOf(p)) pushTitle(p);
}
async function newSession(id) {
  const token = crypto.randomBytes(32).toString('hex');
  await db.setex('sess:' + sha(token), SESSION_TTL, id);   // only a hash of the token is stored
  return token;
}
async function handleAuth(p, m, ip) {
  if (p.user || p.authBusy) return;
  p.authBusy = true;
  try {
    if (!rateOk('a:' + ip, 40, 60000)) return authFail(p, '시도가 너무 많습니다. 잠시 후 다시 시도해 주세요.');
    if (m.t === 'resume') {                                  // automatic login with the saved session token
      const tk = m.token;
      const id = isToken(tk) ? await db.get('sess:' + sha(tk)) : null;
      const raw = id ? await db.get('user:' + id) : null;
      if (!raw) return authFail(p, '', { resume: 1 });
      await db.expire('sess:' + sha(tk), SESSION_TTL);
      return await loginOk(p, JSON.parse(raw), tk);
    }
    const id = normId(m.id), pw = String(m.pw || '');
    if (!id) return authFail(p, '아이디는 영문 소문자·숫자·_ 4~16자로 입력해 주세요.');
    if (pw.length < 6 || pw.length > 64) return authFail(p, '비밀번호는 6~64자로 입력해 주세요.');
    if (m.t === 'signup') {
      const nick = clean(m.name, 14);
      if (nick.length < 2) return authFail(p, '닉네임은 2~14자로 입력해 주세요.');
      if (nick.toLowerCase() === 'system') return authFail(p, '사용할 수 없는 닉네임입니다.');
      if (!rateOk('s:' + ip, 30, 3600 * 1000)) return authFail(p, '가입 시도가 너무 많습니다. 나중에 다시 시도해 주세요.');
      const salt = crypto.randomBytes(16).toString('hex');
      const rec = { id, nick, salt, hash: await scryptHex(pw, salt), created: Date.now() };
      if (!await db.setnx('user:' + id, JSON.stringify(rec))) return authFail(p, '이미 사용 중인 아이디입니다.');
      if (!await db.setnx('nick:' + nick.toLowerCase(), id)) { await db.del('user:' + id); return authFail(p, '이미 사용 중인 닉네임입니다.'); }
      return await loginOk(p, rec, await newSession(id));
    }
    // login
    const fk = 'fail:' + id;
    if ((Number(await db.get(fk)) || 0) >= LOCK_FAILS) return authFail(p, '로그인 시도가 너무 많습니다. 10분 후 다시 시도해 주세요.');
    const raw = await db.get('user:' + id), rec = raw && JSON.parse(raw);
    const h = await scryptHex(pw, rec ? rec.salt : DUMMY_SALT);   // same work whether or not the account exists
    if (!rec || !safeEq(h, rec.hash)) {
      if (await db.incr(fk) === 1) await db.expire(fk, LOCK_SEC);
      return authFail(p, '아이디 또는 비밀번호가 올바르지 않습니다.');
    }
    await db.del(fk);
    return await loginOk(p, rec, await newSession(id));
  } finally { p.authBusy = false; }
}

// ================= connections =================
wss.on('connection', (ws, req) => {
  const ip = String((req && req.headers && req.headers['x-forwarded-for']) || (req && req.socket && req.socket.remoteAddress) || '?').split(',')[0].trim();
  if (players.size >= MAX_PLAYERS) { send(ws, { t: 'full' }); return ws.close(); }
  const id = nextId++;
  const a = Math.random() * Math.PI * 2, r = Math.random() * 0.5;
  const p = { id, ws, name: 'Player' + id, hue: Math.floor(Math.random() * 360),
    x: CX + Math.cos(a) * RX * r, y: CY + Math.sin(a) * RY * r, face: 1, dx: 0, dy: 0, lastChat: 0, alive: true,
    joined: false, cls: '', ready: false, role: 0, inRound: false, lx: 0, ly: 0, deathOrder: 0,
    hp: 1000, mh: 1000, atkReady: 0, cdQ: 0, cdE: 0, cdR: 0, stunUntil: 0, guardUntil: 0, slowUntil: 0, chargeStart: 0, hasteUntil: 0, invisUntil: 0, tauntUntil: 0, tauntBy: 0, kbUntil: 0, hornUntil: 0, dash: null, markUntil: 0, asUntil: 0, asBonus: 0, fires: [], qNext: false, pull: null, charmUntil: 0, charmBy: 0, burnUntil: 0, burnNext: 0, titles: [], eq: null, lastEquip: 0, aim: 0, hist: [] };
  players.set(id, p);
  pruneChat();
  send(ws, { t: 'hello', id, arena: { CX, CY, RX, RY } });
  send(ws, { t: 'history', log: chatLog.map(c => ({ name: c.name, text: c.text, sys: c.sys ? 1 : 0, age: Date.now() - c.ts })) });

  ws.on('pong', () => { p.alive = true; });
  ws.on('message', raw => {
    let m; try { m = JSON.parse(raw); } catch { return; }
    if (!m || typeof m !== 'object') return;
    if (m.t === 'signup' || m.t === 'login' || m.t === 'resume') {
      handleAuth(p, m, ip).catch(err => { console.error('auth error:', err.message); authFail(p, '서버 오류가 발생했습니다. 잠시 후 다시 시도해 주세요.'); });
      return;
    }
    if (m.t === 'logout') {
      if (isToken(m.token)) db.del('sess:' + sha(m.token)).catch(() => {});
      try { ws.close(); } catch {}
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
      if (phase === 'lobby' && ['Knight', 'Archer', 'Shielder', 'Assassin', 'Gumiho'].includes(m.cls)) { p.cls = m.cls; resetCombat(p); }
    } else if (m.t === 'tequip') {
      equipTitle(p, m.id === null ? null : m.id).catch(e => console.error('equip:', e.message));
    } else if (m.t === 'tgrant' || m.t === 'tlist' || m.t === 'trevoke') {
      if (p.user === ADMIN_ID) adminTitle(p, m).catch(e => { console.error('admin title:', e.message); send(ws, { t: 'tadmin', ok: 0, msg: '서버 오류가 발생했습니다.' }); });
    } else if (m.t === 'charge') {                       // Archer starts pulling the bowstring
      const now = Date.now();
      if (p.cls === 'Archer' && canAct(p, now) && now >= p.hasteUntil && now >= p.atkReady - 60) p.chargeStart = now;
    } else if (m.t === 'ccancel') {
      p.chargeStart = 0;
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
  let needEnd = false;
  for (const p of players.values()) {
    if (!p.joined) continue;
    let { dx, dy } = p;
    if (p.role === 2 || now < p.stunUntil || now < p.charmUntil) { dx = dy = 0; p.chargeStart = 0; }
    if (p.dash) {                                                         // [실드 태클] in progress: no steering, the path is fixed
      const D = p.dash;
      if (p.role !== 1) p.dash = null;                                    // only death/spectating stops it (stun & charm do not)
      else {
        const px = p.x, py = p.y, f = Math.min(1, (now - D.t0) / D.ms);
        p.x = D.sx + (D.ex - D.sx) * f; p.y = D.sy + (D.ey - D.sy) * f;
        if (dashHits(p, D, px, py, now)) needEnd = true;
        if (f >= 1) p.dash = null;
      }
      dx = dy = 0;
    }
    let tauntMul = 1;
    if (!p.dash && now < p.tauntUntil && p.role === 1 && now >= p.stunUntil) {      // [도발]: forced to walk towards the Shielder at 80% speed
      const src = players.get(p.tauntBy);
      if (src && src.joined && src.role === 1) {
        const vx = src.x - p.x, vy = (src.y - p.y) / 0.8, d = Math.hypot(vx, vy);
        if (d > SHIELDER.Q.stop) { dx = vx / d; dy = vy / d; } else dx = dy = 0;
        tauntMul = SHIELDER.Q.slow;
      } else p.tauntUntil = 0;
    }
    if (!p.dash && now < p.charmUntil && p.role === 1 && now >= p.stunUntil) {      // [매혹]: walks towards the Gumiho, cannot attack
      const src = players.get(p.charmBy);
      if (src && src.joined && src.role === 1) {
        const vx = src.x - p.x, vy = (src.y - p.y) / 0.8, d = Math.hypot(vx, vy);
        if (d > GUMIHO.R.stop) { dx = vx / d; dy = vy / d; } else dx = dy = 0;
        tauntMul = GUMIHO.R.speed;
      } else p.charmUntil = 0;
    }
    if (p.role === 1 && p.burnUntil) {                                    // burning: 20 damage every 0.5s (the last tick lands exactly when the effect ends)
      while (p.role === 1 && p.burnNext <= p.burnUntil && now >= p.burnNext) { dmgTo(p, GUMIHO.eff.tick, now, { kill: players.get(p.burnBy) }); p.burnNext += GUMIHO.eff.tickMs; needEnd = true; }
    }
    if (p.pull && now >= p.pull.t0 + GUMIHO.E.pullMs) {                   // [미수옥]: the pulled Foxfires explode together
      const P = p.pull; p.pull = null;
      if (p.role === 1) {
        broadcast({ t: 'fx', type: 'ring', x: P.x, y: P.y, r: GUMIHO.eff.radius, c: '#7fe9ff', dur: 700 });
        for (const t of targetsOf(p)) if (Math.hypot(t.x - P.x, (t.y - P.y) / 0.8) <= GUMIHO.eff.radius) foxHit(t, now, p, GUMIHO.E.dmg * P.n, { x: P.x, y: P.y });
        needEnd = true;
      }
    }
    if (now < p.kbUntil && p.role === 1) {                                // [실드 태클] knockback
      p.x += p.kbx * dt; p.y += p.kby * dt * 0.8;
      const nx = (p.x - CX) / RX, ny = (p.y - CY) / RY, d = Math.hypot(nx, ny);
      if (d > 1) { p.x = CX + nx / d * RX; p.y = CY + ny / d * RY; }
    }
    if (dx || dy) {
      const l = Math.hypot(dx, dy); dx /= l; dy /= l;
      const spd = SPEED * (now < p.guardUntil ? KNIGHT.E.speed : 1) * (now < p.slowUntil ? KNIGHT.R.slow : 1) * tauntMul * (now < p.hornUntil ? SHIELDER.R.speed : 1) * (p.cls === 'Assassin' && now < p.invisUntil ? ASSASSIN.E.speed : 1);
      p.x += dx * spd * dt; p.y += dy * spd * dt * 0.8;
      const nx = (p.x - CX) / RX, ny = (p.y - CY) / RY, d = Math.hypot(nx, ny);
      if (d > 1) { p.x = CX + nx / d * RX; p.y = CY + ny / d * RY; }
    }
    p.moving = !!(dx || dy);
    p.hist.push({ t: now, x: p.x, y: p.y });
    while (p.hist.length && p.hist[0].t < now - HIST_MS) p.hist.shift();
  }
  if (needEnd) checkRoundEnd();
  checkTimeout(now);
  stepArrows(dt, now);
  const list = [], hidden = [];
  for (const p of players.values()) {
    if (!p.joined) continue;
    const iv = now < p.invisUntil;
    if (iv && !p.wasIv) { p.hideX = p.x; p.hideY = p.y; }                // remember where they vanished
    p.wasIv = iv;
    const e = { id: p.id, name: p.name, hue: p.hue, x: Math.round(p.x * 10) / 10, y: Math.round(p.y * 10) / 10,
      f: p.face, a: Math.round(p.aim * 100) / 100, m: p.moving ? 1 : 0, c: p.cls, r: p.ready ? 1 : 0, o: p.role,
      hp: Math.max(0, Math.round(p.hp)), mh: p.mh, su: Math.max(0, p.stunUntil - now), gd: now < p.guardUntil ? 1 : 0, sl: now < p.slowUntil ? 1 : 0,
      hs: now < p.hasteUntil ? 1 : 0, iv: iv ? 1 : 0, hn: now < p.hornUntil ? 1 : 0, ta: p.role === 1 && now < p.tauntUntil ? 1 : 0, kb: now < p.kbUntil ? 1 : 0, ds: p.dash ? 1 : 0,
      mk: now < p.markUntil ? 1 : 0, as: now < p.asUntil ? p.asBonus : 0, cm: p.role === 1 && now < p.charmUntil ? 1 : 0, bn: p.role === 1 && now < p.burnUntil ? 1 : 0, qn: (p.qNext || p.eNext) ? 1 : 0,
      cg: p.chargeStart ? Math.max(1, Math.min(now - p.chargeStart, ARCHER.charge.maxMs)) : 0 };
    list.push(e);
    hidden.push(iv ? Object.assign({}, e, { x: Math.round(p.hideX * 10) / 10, y: Math.round(p.hideY * 10) / 10, a: 0, m: 0, cg: 0 }) : e);   // what everybody ELSE gets: no live position of an invisible player
  }
  const ff = [];
  for (const p of players.values()) if (p.joined) for (const f of p.fires) ff.push({ id: f.id, o: p.id, x: Math.round(f.x), y: Math.round(f.y) });   // every Foxfire is visible to everybody
  const head = { t: 'state', ph: phase, left: phase === 'round' ? Math.max(0, ROUND_MS - (now - roundStart)) : 0, ff };
  if (!list.some(e => e.iv)) { broadcast(Object.assign(head, { p: list })); return; }
  const common = JSON.stringify(Object.assign({}, head, { p: hidden }));
  for (const q of players.values()) {
    if (q.ws.readyState !== 1) continue;
    if (q.joined && now < q.invisUntil) q.ws.send(JSON.stringify(Object.assign({}, head, { p: hidden.map((e, i) => list[i].id === q.id ? list[i] : e) })));   // an invisible player still sees itself
    else q.ws.send(common);
  }
}, 1000 / TICK);

// Drop dead connections
setInterval(() => {
  for (const p of players.values()) {
    if (!p.alive) { p.ws.terminate(); continue; }
    p.alive = false; p.ws.ping();
  }
}, 30000);

server.listen(PORT, () => console.log('Geolgani PvP running on port ' + PORT));
