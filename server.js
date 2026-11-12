const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;
const PUBLIC = path.join(__dirname, 'public');
const MIME = { '.html': 'text/html; charset=utf-8', '.jpg': 'image/jpeg', '.png': 'image/png', '.js': 'text/javascript', '.css': 'text/css', '.txt': 'text/plain; charset=utf-8' };

const ARENAS = [{ CX: 630, CY: 640, RX: 410, RY: 335 }, { CX: 630, CY: 600, RX: 460, RY: 370 }];
let mapId = 0, { CX, CY, RX, RY } = ARENAS[0];
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
const send = (ws, o) => ws && ws.readyState === 1 && ws.send(JSON.stringify(o));
let curTint = null;
const broadcast = o => { if (curTint && (o.t === 'fx' || o.t === 'arrow') && !o.tint) o.tint = curTint; const m = JSON.stringify(o); for (const p of players.values()) if (p.ws.readyState === 1) p.ws.send(m); };

const CHAT_TTL = 10 * 60 * 1000;
const ROUND_MS = 4 * 60 * 1000;
const chatLog = [];
let phase = 'lobby', roundStart = 0, deathCounter = 0;

const joinedList = () => [...players.values()].filter(p => p.joined);
function setMap(id) {
  mapId = id; ({ CX, CY, RX, RY } = ARENAS[id]);
  for (const p of players.values()) { const c = clampArena({ x: p.x, y: p.y }); p.x = c.x; p.y = c.y; p.hist = []; }
  broadcast({ t: 'map', id, arena: { CX, CY, RX, RY } });
}

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
  phase = 'round'; roundStart = Date.now(); arrows.clear(); bombs.clear(); units.clear(); balls.length = 0;
  parts.forEach((p, i) => {
    const a = -Math.PI / 2 + i * 2 * Math.PI / parts.length;
    p.lx = p.x; p.ly = p.y;
    p.x = CX + Math.cos(a) * RX * 0.92; p.y = CY + Math.sin(a) * RY * 0.92;
    p.dx = p.dy = 0; p.role = 1; p.inRound = true; p.ready = false; p.deathOrder = 0; p.hist = [];
    resetCombat(p);
  });
  joinedList().forEach(p => { if (!p.inRound) p.role = 2; });
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
  phase = 'lobby'; arrows.clear(); bombs.clear(); units.clear(); balls.length = 0;
  for (const p of players.values()) {
    if (p.inRound) { p.x = p.lx; p.y = p.ly; }
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
const BASE = { hp: 1000, dmg: 150, reduce: 0, atkCd: 600 };
const CLASS_STATS = {
  Knight: { hp: 1200, dmg: 150, reduce: 0.2, atkCd: 700 },
  Archer: { hp: 1000, dmg: 180, reduce: 0, atkCd: 800 },
  Shielder: { hp: 1600, dmg: 80, reduce: 0, atkCd: 800 },
  Assassin: { hp: 1000, dmg: 135, reduce: 0, atkCd: 600 },
  Gumiho: { hp: 1100, dmg: 130, reduce: 0, atkCd: 700 },
  Gambler: { hp: 1000, dmg: 180, reduce: 0, atkCd: 600 },
  SwordMaster: { hp: 1200, dmg: 160, reduce: 0, atkCd: 600 },
  Tower: { hp: 2200, dmg: 100, reduce: 0, atkCd: 2000 },
  Gamer: { hp: 1000, dmg: 150, reduce: 0, atkCd: 700 }
};
const statsOf = p => p.cls === 'Financier' ? { hp: 1000, dmg: p.fDmg || 90, reduce: 0, atkCd: 900 } : p.cls === 'Lucifer' ? { hp: lForm(p).hp, dmg: lForm(p).dmg, reduce: 0, atkCd: p.lf === 'd' && Date.now() < p.libUntil ? LUC.lib.atkCd : lForm(p).atkCd } : CLASS_STATS[p.cls] || BASE;
const RADPX = 112.5;
const MAP = 1254;
const ARROW = { speed: 800, range: 5 * RADPX, radius: 28 };
const ARCHER = {
  charge: { maxMs: 2000, min: 0.5, max: 1.5 },
  Q: { cd: 11000, arrows: 7, step: 10 * RAD, dmg: 130, invis: 1500 },
  E: { cd: 15000, dur: 4000, chargeMul: 0.3 },
  R: { cd: 25000, dmg: 380, stun: 1000, scale: 8, radius: 90 }
};
const ATK = { range: 1 * RADPX, span: 100 * RAD };
const SM = {
  atk: { need: 4, needAwk: 2, auraDmg: 180, kb: 1 * RADPX, kbMs: 250 },
  Q: { cd: 12000, dmg: 100, pct: 0.15, spd: 1500, range: 6 * RADPX, radius: 1.5 * RADPX },
  E: { cd: 0, cdAwk: 0, mult: 0.5, multAwk: 0.8, dash: 2 * RADPX, dashMs: 200, dashDir: 1 },
  R: { cd: 25000, dur: 10000 }
};
const KNIGHT = {
  Q: { cd: 8000, range: 2 * RADPX, span: 120 * RAD, dmg: 250, stun: 1000 },
  E: { cd: 12000, dur: 3000, reduce: 0.4, speed: 1.15 },
  R: { cd: 25000, swords: 8, ring: 195, radius: 1 * RADPX, cRadius: 2.5 * RADPX, dmg: 120, cdmg: 220, slow: 0.7, slowMs: 2000 }
};

const SHIELDER = {
  span: 90 * RAD, block: 0.8,
  Q: { cd: 12000, radius: 2.5 * RADPX, ms: 2000, slow: 0.8, stop: 45 },
  E: { cd: 11000, dist: 3.5 * RADPX, dashMs: 450, dmg: 200, hit: 55, kb: RADPX, kbMs: 300, stun: 500 },
  R: { cd: 25000, dur: 6000, reduce: 0.3, reflect: 0.4, speed: 0.85 }
};

const ASSASSIN = {
  Q: { cd: 8000, range: 2 * RADPX, width: 45, dmg: 250, markMs: 3000, mark: 0.2 },
  E: { cd: 10000, dur: 2500, speed: 1.15 },
  R: { cd: 25000, radius: RADPX, dmg: 250 }
};
const GUMIHO = {
  atk: { range: 3.5 * RADPX, speed: 1020, radius: 30 },
  fire: { chance: 0.70, max: 5, pick: 55, lift: 25 },
  eff: { dmg: 120, ms: 2000, radius: 2 * RADPX },
  Q: { cd: 8000 },
  E: { cd: 12000, pullMs: 500, dmg: 120, rad: 0.6 * RADPX },
  R: { cd: 25000, radius: 2.5 * RADPX, ms: 2500, speed: 0.8, stop: 45 }
};
const BURN = { tick: 35, tickMs: 1000 };
const LUC = {
  base: { hp: 1300, dmg: 150, atkCd: 900, range: 4 * RADPX, spd: 900, radius: 0.3 * RADPX },
  angel: { hp: 1300, dmg: 130, atkCd: 800, range: 4 * RADPX, spd: 900, radius: 0.3 * RADPX },
  devil: { hp: 1300, dmg: 180, atkCd: 1000, range: 4 * RADPX, spd: 900, radius: 0.3 * RADPX },
  G: { cd: 30000, atkCut: 1000, skillCut: 1500, afterCd: 5000 },
  Q: { cd: 10000, range: 3 * RADPX, dmg: 270, spd: 800, radius: 0.3 * RADPX, sc: 1.6 },
  E: { cd: 10000, range: 3 * RADPX, dmg: 120, spd: 800, radius: 0.3 * RADPX, sc: 1.6, burnMs: 4000 },
  beam: { cd: 15000, ms: 1500, tickMs: 100, dmg: 30, heal: 10, half: 50, pad: 400 },
  sanct: { cd: 18000, ms: 2000, r: 1.5 * RADPX },
  pure: { cd: 25000, r0: 0.5 * RADPX, r1: 1.5 * RADPX, delay: 200, ms: 1700, tickMs: 100, dmg: 50, heal: 20 },
  mark: { ms: 2500, amp: 0.1, ampLib: 0.15, defCut: 0.2, max: 1, maxLib: 3 },
  bomb: { cd: 10000, libCd: 4000, spd: 380, r: RADPX, dmg: 50, tickMs: 500, lift: 1000, small: { r: 0.7 * RADPX, dmg: 25, fan: 20 * RAD } },
  absorb: { cd: 14000, libCd: 4000, pct: 0.25, heal: 0.6, healLib: 0.85 },
  lib: { cd: 25000, ms: 10000, speed: 1.2, atkCd: 800 }
};
const ANGEL = { regen: 20 };
const GAMBLER = {
  range: 4 * RADPX, spd: 1100, radius: 24, chambers: 6, reloadMs: 4000,
  Q: { cd: 10000 },
  E: { cd: 3000, self: 200, buffDmg: 300, buffMs: 5000 },
  R: { cd: 25000, all: 400, self: 200, plusDmg: 100, selfHeal: 300, allHeal: 150, fastMs: 5000, fast: 1.2, endOnF: true }
};
const lForm = p => p.lf === 'a' ? LUC.angel : p.lf === 'd' ? LUC.devil : LUC.base;
const atkSpeed = (p, now) => now < p.asUntil ? 1 + p.asBonus : 1;
const breakStealth = p => { if (p.cls === 'Assassin' || (p.cls === 'Gamer' && p.gInvis)) { p.invisUntil = 0; p.gInvis = false; } };

function setAim(p, a) {
  if (!Number.isFinite(a)) return;
  p.aim = Math.atan2(Math.sin(a), Math.cos(a));
  if (Math.abs(Math.cos(p.aim)) > 0.2) p.face = Math.cos(p.aim) > 0 ? 1 : -1;
}
// ---- lag compensation ----

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
function offMapRange(x, y, a, sc) {
  const L = 14 * 5 * sc, half = 3 * 5 * sc / 2;
  const th = Math.atan2(0.8 * Math.sin(a), Math.cos(a)), ux = Math.cos(th), uy = Math.sin(th), nx = -uy, ny = ux;
  for (let d = 0; d < 4000; d += 10) {
    const tx = x + Math.cos(a) * (d + 28), ty = y + Math.sin(a) * (d + 28) * 0.8 - 30;
    const cs = [[0, 1], [L, 1], [0, -1], [L, -1]].map(([l, sd]) => [tx - ux * l + nx * sd * half, ty - uy * l + ny * sd * half]);
    if (cs.every(c => c[0] < 0) || cs.every(c => c[0] > MAP) || cs.every(c => c[1] < 0) || cs.every(c => c[1] > MAP)) return d;
  }
  return 4000;
}
function endArrow(ar) { arrows.delete(ar.id); broadcast({ t: 'arrowEnd', id: ar.id }); }
function moveArrow(ar, step, time) {
  const nx = ar.x + Math.cos(ar.a) * step, ngy = ar.gy + Math.sin(ar.a) * step;
  const found = [];
  if (phase === 'round') for (const t of [...players.values(), ...units.values()]) {
    if (t.id === ar.owner || t.owner === ar.owner || !(t.unit || t.joined) || t.role !== 1 || ar.hitIds.has(t.id)) continue;
    const tp = posAt(t, time);
    if (segDist(tp.x, tp.y / 0.8, ar.x, ar.gy, nx, ngy) > ar.radius + (t.hr || 0)) continue;
    found.push({ t, d: Math.hypot(tp.x - ar.x, tp.y / 0.8 - ar.gy) });
  }
  found.sort((a, b) => a.d - b.d);
  if (ar.pierce) {
    for (const f of found) ar.hitIds.add(f.t.id);
    ar.x = nx; ar.gy = ngy; ar.left -= step;
    return found.map(f => f.t);
  }
  if (found.length) return [found[0].t];
  ar.x = nx; ar.gy = ngy; ar.left -= step;
  return [];
}
function arrowHit(ar, t, now) {
  const inDir = ar.a + Math.PI;
  const type = ar.type || (ar.orb ? 'magic' : 'phys');
  if (type === 'phys' && t.cls === 'Shielder' && now < t.hornUntil && shieldBlocks(t, { dir: inDir })) { deflectArrow(ar, t); return true; }
  dmgTo(t, ar.hpPct ? ar.dmg + Math.round(t.hp * ar.hpPct) : ar.dmg, now, { dir: inDir, kill: players.get(ar.owner), type });
  if (ar.stun && t.role === 1) t.stunUntil = now + ar.stun;
  if (ar.luc) lucHit(ar, t, now);
  if (ar.orb && ar.eff) { const g = players.get(ar.owner); if (g) foxHit(t, now, g, GUMIHO.eff.dmg, { dir: inDir, kill: g, type: 'magic' }); }
  return false;
}
function deflectArrow(ar, t) {
  broadcast({ t: 'arrowEnd', id: ar.id });
  ar.owner = t.id; ar.a = Math.atan2(-Math.sin(ar.a), -Math.cos(ar.a)); ar.hitIds = new Set();
  ar.left = ar.noArena ? offMapRange(ar.x, ar.gy * 0.8, ar.a, ar.sc) : ar.r0;
  broadcast({ t: 'arrow', id: ar.id, by: t.id, x: ar.x, y: ar.gy * 0.8, a: ar.a, spd: ar.spd, range: ar.left, adv: 0, sc: ar.sc, kd: ar.kd, bm: ar.boom });
  broadcast({ t: 'hit', id: t.id, dmg: 0, bl: 2 });
}

function spawnArrow(p, o, lag, now, spec) {
  const id = ++arrowSeq;
  const ar = { id, owner: p.id, x: o.x, gy: o.y / 0.8, a: spec.a, dmg: spec.dmg, spd: spec.spd, radius: spec.radius || ARROW.radius, type: spec.type || '', luc: spec.luc || '', kd: spec.kind || 'atk', r0: spec.range || ARROW.range,
    orb: !!spec.orb, eff: !!spec.eff, boom: spec.boom || 0, pierce: !!spec.pierce, noArena: !!spec.noArena, sc: spec.sc || 1, stun: spec.stun || 0, hpPct: spec.hpPct || 0, hitIds: new Set(), left: spec.range || ARROW.range };
  let adv = 0, ended = false;
  const pending = [];
  const steps = lag > 0 ? Math.ceil(lag / 33) : 0, stepMs = steps ? lag / steps : 0;
  for (let i = 1; i <= steps && !ended; i++) {
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
    const stp = Math.min(ar.spd * dt, ar.left);
    if (sanctBlocked(ar.owner, ar.x, ar.gy, ar.x + Math.cos(ar.a) * stp, ar.gy + Math.sin(ar.a) * stp, now)) { endArrow(ar); continue; }
    const hits = moveArrow(ar, stp, now);
    let deflected = false;
    for (const t of hits) { any = true; if (arrowHit(ar, t, now)) { deflected = true; break; } }
    if (deflected) continue;
    if (!ar.pierce && hits.length) { endArrow(ar); orbLand(ar, hits[0], now); continue; }
    const ex = (ar.x - CX) / RX, ey = (ar.gy * 0.8 - CY) / RY;
    if (ar.left <= 0 || (!ar.noArena && ex * ex + ey * ey > 1.15)) { endArrow(ar); orbLand(ar, null, now); }
  }
  if (any) checkRoundEnd();
}

function resetCombat(p) {
  p.lf = ''; p.lPend = p.lUsed = false; p.beam = p.pure = p.sanct = null; p.libUntil = p.dmUntil = 0; p.dmList = [];
  p.mh = p.hp = statsOf(p).hp;
  p.atkReady = p.cdQ = p.cdE = p.cdR = 0;
  p.stunUntil = p.guardUntil = p.slowUntil = 0;
  p.chargeStart = p.hasteUntil = p.invisUntil = 0;
  p.tauntUntil = p.tauntBy = p.kbUntil = p.hornUntil = 0; p.dash = null;
  p.markUntil = p.asUntil = p.asBonus = 0;
  p.fires = []; p.qNext = false; p.eNext = 0; p.lastBy = 0; p.charmUntil = p.charmBy = p.burnUntil = p.burnNext = 0;
  p.fDmg = 90; p.finNext = Date.now() + 5000; p.insUntil = p.depUntil = 0; p.insAcc = 0; p.stkNext = 0; p.buyDealt = 0; p.buyHp0 = 0;
  if (p.buy) send(p.ws, { t: 'stk', id: 0 }); p.buy = 0;
  p.hr = p.cls === 'Tower' ? TOWER.hr : 0; p.towerRUntil = 0; p.mercNext = Date.now() + TOWER.merc.ms;
  for (const u of units.values()) if (u.owner === p.id) units.delete(u.id);
  p.smN = 0; p.smAura = false; p.smAwkUntil = 0; p.smLast = null; p.smSaved = false;
  p.ch = null; p.chi = 0; p.reloadUntil = 0; p.myTurn = false; p.gbUntil = p.gbPlusUntil = p.fastUntil = 0;
  p.gCopy = []; p.gSlots = 1; p.gNext = 0; p.gCheatUntil = p.gtUntil = 0; p.gtint = ''; p.gInvis = p.gPierce = false; send(p.ws, { t: 'gc', l: [], s: 1, ch: 0 });
  for (const k of ['Q', 'E', 'R']) send(p.ws, { t: 'cd', k, ms: 0 });
  if (p.cls === 'Gambler') loadRevolver(p); else send(p.ws, { t: 'rv', n: 0 });
  if (p.cls === 'Lucifer' && phase === 'round') { p.cdR = Date.now() + LUC.G.cd; send(p.ws, { t: 'cd', k: 'R', ms: LUC.G.cd }); }
}
function killPlayer(p) {
  const was = p.role === 1, k = was && p.lastBy && Date.now() - p.lastByT < 10000 ? players.get(p.lastBy) : null;
  p.hp = 0; p.role = 2; p.dx = p.dy = 0; p.moving = false; p.deathOrder = ++deathCounter;
  if (was) broadcast({ t: 'kill', k: k ? k.id : 0, kn: k ? k.name : '', kc: k ? k.cls : '', v: p.id, vn: p.name, vc: p.cls });
}
function shieldBlocks(t, src) {
  if (t.cls !== 'Shielder' || !src) return false;
  let dir = src.dir;
  if (dir === undefined) {
    if (!src.basic) return false;
    const dx = src.x - t.x, dy = (src.y - t.y) / 0.8;
    if (Math.hypot(dx, dy) < 10) return false;
    dir = Math.atan2(dy, dx);
  }
  return Math.abs(Math.atan2(Math.sin(dir - t.aim), Math.cos(dir - t.aim))) <= SHIELDER.span / 2;
}

function dmgTo(t, amount, now, src) {
  if (inSanct(t, now)) return;
  const type = (src && src.type) || (src && src.by && (src.by.cls === 'Assassin' || src.by.gPierce) ? 'pierce' : 'phys');
  const pierce = type === 'pierce', magic = type === 'magic';
  if (!pierce && now < (t.invulnUntil || 0)) return;
  let cut = 0, blocked = false;
  if (!pierce && !magic) {
    cut = statsOf(t).reduce;
    if (now < t.guardUntil) cut += KNIGHT.E.reduce;
    blocked = shieldBlocks(t, src);
    if (blocked) cut += SHIELDER.block;
    else if (t.cls === 'Shielder' && now < t.hornUntil) cut += SHIELDER.R.reduce;
    if (now < t.dmUntil) cut *= 1 - LUC.mark.defCut;
  }
  let d = (blocked && now < t.hornUntil) ? 0 : Math.max(1, Math.round(amount * (1 - Math.min(cut, 0.95))));
  if (d > 0 && now < t.markUntil) d = Math.round(d * (1 + ASSASSIN.Q.mark));
  if (d > 0 && now < t.dmUntil) { const mo = players.get(t.dmBy); d = Math.round(d * (1 + (mo && now < mo.libUntil ? LUC.mark.ampLib : LUC.mark.amp))); }
  t.hp -= d;
  if (now < (t.insUntil || 0)) t.insAcc += d;
  const atkr = src && (src.by || src.kill);
  if (atkr && !t.unit && atkr.id !== t.id) for (const f of players.values()) if (f.cls === 'Financier' && f.buy === atkr.id) f.buyDealt += d;
  if (src && (src.by || src.kill)) { t.lastBy = (src.by || src.kill).id; t.lastByT = now; }
  broadcast({ t: 'hit', id: t.id, dmg: d, bl: blocked ? 1 : 0 });
  if (blocked && src.by && now < t.hornUntil && src.by.role === 1) {
    const back = Math.round(amount * SHIELDER.R.reflect);
    if (back > 0) dmgTo(src.by, back, now, { kill: t });
  }
  if (t.hp <= 0) { if (t.unit) units.delete(t.id); else killPlayer(t); }
}
const units = new Map(); let unitSeq = 0; const balls = [];
const targetsOf = p => phase !== 'round' ? [] : [...players.values(), ...units.values()].filter(t => t !== p && (t.unit ? t.owner !== p.id : (t.joined && t.role === 1)));
function inConeAt(ox, oy, aim, tx, ty, range, span, ext = 0) {
  const dx = tx - ox, dy = (ty - oy) / 0.8, d = Math.hypot(dx, dy);
  if (d > range + 10 + ext) return false;
  if (d < 10) return true;
  let diff = Math.abs(Math.atan2(dy, dx) - aim);
  if (diff > Math.PI) diff = 2 * Math.PI - diff;
  return diff <= span / 2;
}
const canAct = (p, now) => p.joined && p.role !== 2 && now >= p.stunUntil && now >= p.charmUntil && now >= (p.reloadUntil || 0);

const chargeMax = (p, now) => ARCHER.charge.maxMs * (now < p.hasteUntil ? ARCHER.E.chargeMul : 1);
function archerAttack(p, m, now) {
  const st = statsOf(p), o = originOf(p, m), lag = lagOf(m), C = ARCHER.charge;
  let f = 1;
  if (!p.chargeStart) return;
  const em = chargeMax(p, now), ch = Math.min(now - p.chargeStart, em);
  f = C.min + (C.max - C.min) * ch / em;
  p.chargeStart = 0;
  if (now < p.atkReady - 60) return;
  p.atkReady = now + st.atkCd;
  spawnArrow(p, o, lag, now, { a: p.aim, dmg: Math.round(st.dmg * f), spd: ARROW.speed * f, kind: 'atk' });
}
function doAttack(p, m) {
  const now = Date.now();
  if (!canAct(p, now)) return;
  if (p.cls === 'Archer') return archerAttack(p, m, now);
  if (p.cls === 'Gumiho') return gumihoAttack(p, m, now);
  if (p.cls === 'Lucifer') return luciferAttack(p, m, now);
  if (p.cls === 'Gambler') return gamblerAttack(p, m, now);
  if (p.cls === 'SwordMaster') return swordmasterAttack(p, m, now);
  if (p.cls === 'Gamer') return gamerAttack(p, m, now);
  if (now < p.atkReady) return;
  const st = statsOf(p), o = originOf(p, m), lag = lagOf(m);
  p.atkReady = now + st.atkCd / atkSpeed(p, now);
  breakStealth(p);
  const reach = ATK.range + (p.hr || 0);
  broadcast({ t: 'fx', type: 'cone', by: p.id, x: o.x, y: o.y, a: p.aim, span: ATK.span, r: reach, c: 'rgba(255,255,255,.6)', dur: 220 });
  for (const t of targetsOf(p)) {
    const tp = posAt(t, now - lag);
    if (inConeAt(o.x, o.y, p.aim, tp.x, tp.y, reach, ATK.span, t.hr || 0)) dmgTo(t, st.dmg, now, { x: o.x, y: o.y, by: p, basic: true });
  }
  if (p.cls === 'Tower' && now < p.towerRUntil) for (const sd of [-1, 1]) {
    const off = TOWER.R.gap * sd;
    spawnArrow(p, { x: o.x - Math.sin(p.aim) * off, y: o.y + Math.cos(p.aim) * off * 0.8 }, lag, now, { a: p.aim, dmg: TOWER.R.dmg, spd: ARROW.speed, range: TOWER.R.range, kind: 'tarr' });
  }
  checkRoundEnd();
}
function doSkill(p, k, m) {
  const now = Date.now();
  if (!['Q', 'E', 'R'].includes(k) || !canAct(p, now)) return;
  if (now < p['cd' + k] && !(p.cls === 'Gamer' && k === 'Q' && p.gCopy && p.gCopy.length)) return;
  if (p.cls === 'Knight') knightSkill(p, k, m, now);
  else if (p.cls === 'Archer') archerSkill(p, k, m, now);
  else if (p.cls === 'Shielder') shielderSkill(p, k, m, now);
  else if (p.cls === 'Assassin') assassinSkill(p, k, m, now);
  else if (p.cls === 'Gumiho') gumihoSkill(p, k, m, now);
  else if (p.cls === 'Lucifer') luciferSkill(p, k, m, now);
  else if (p.cls === 'Gambler') gamblerSkill(p, k, m, now);
  else if (p.cls === 'SwordMaster') swordmasterSkill(p, k, m, now);
  else if (p.cls === 'Tower') towerSkill(p, k, m, now);
  else if (p.cls === 'Financier') financierSkill(p, k, m, now);
  else if (p.cls === 'Gamer') gamerSkill(p, k, m, now);
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
    p.hasteUntil = now + S.dur;
  } else {
    spawnArrow(p, o, lag, now, { a: p.aim, dmg: S.dmg, spd: ARROW.speed, range: offMapRange(o.x, o.y, p.aim, S.scale), noArena: true, radius: S.radius, pierce: true, stun: S.stun, sc: S.scale, kind: 'R' });
  }
}
// ---- Gumiho ----
const clampArena = pt => { const nx = (pt.x - CX) / RX, ny = (pt.y - CY) / RY, d = Math.hypot(nx, ny); return d > 0.97 ? { x: CX + nx / d * 0.97 * RX, y: CY + ny / d * 0.97 * RY } : { x: pt.x, y: pt.y }; };
let fireSeq = 0;
function spawnFoxfire(g, pos) {
  const c = clampArena(pos);
  g.fires.push({ id: ++fireSeq, x: c.x, y: c.y });
  while (g.fires.length > GUMIHO.fire.max) g.fires.shift();
}
function orbLand(ar, hitT, now) {
  if (!ar.orb || phase !== 'round') return;
  const g = players.get(ar.owner);
  if (!g || g.cls !== 'Gumiho' || g.role !== 1) return;
  if (ar.boom) {
    const at = hitT ? { x: hitT.x, y: hitT.y } : { x: ar.x, y: ar.gy * 0.8 }, rad = ar.boom * GUMIHO.E.rad;
    broadcast({ t: 'fx', type: 'ring', x: at.x, y: at.y, r: rad, c: '#7fe9ff', dur: 700 });
    for (const t of targetsOf(g)) if (t !== hitT && Math.hypot(t.x - at.x, (t.y - at.y) / 0.8) <= rad) dmgTo(t, ar.dmg, now, { x: at.x, y: at.y, kill: g, type: 'magic' });
    checkRoundEnd();
    if (phase !== 'round') return;
  }
  if (!hitT || Math.random() >= GUMIHO.fire.chance) return;
  spawnFoxfire(g, { x: hitT.x, y: hitT.y });
}
function foxHit(t, now, by, dmg, src) {
  dmgTo(t, dmg, now, src);
  applyBurn(t, by, GUMIHO.eff.ms, now);
}
function foxBlast(p, at, now, lag, dmg) {
  broadcast({ t: 'fx', type: 'ring', x: at.x, y: at.y, r: GUMIHO.eff.radius, c: '#7fe9ff', dur: 600 });
  for (const t of targetsOf(p)) {
    const tp = posAt(t, now - lag);
    if (Math.hypot(tp.x - at.x, (tp.y - at.y) / 0.8) <= GUMIHO.eff.radius) foxHit(t, now, p, dmg, { x: at.x, y: at.y, kill: p, type: 'magic' });
  }
}
function gumihoAttack(p, m, now) {
  if (now < p.atkReady) return;
  const st = statsOf(p), o = originOf(p, m), lag = lagOf(m);
  p.atkReady = now + st.atkCd;
  const eff = p.qNext, n = p.eNext || 0; p.qNext = false; p.eNext = 0;
  spawnArrow(p, o, lag, now, { a: p.aim, dmg: st.dmg + n * GUMIHO.E.dmg, boom: n, spd: GUMIHO.atk.speed, range: GUMIHO.atk.range, radius: GUMIHO.atk.radius, kind: 'orb', orb: true, eff });
}
function gumihoSkill(p, k, m, now) {
  const G = GUMIHO, o = originOf(p, m), lag = lagOf(m);
  if (k === 'Q') {
    let target = null;
    if (p.fires.length) {
      const cx = Number(m && m.cx), cy = Number(m && m.cy);
      let best = G.fire.pick;
      for (const f of p.fires) { const d = Math.hypot(cx - f.x, cy - (f.y - G.fire.lift)); if (d <= best) { best = d; target = f; } }
      if (!target) return;
    }
    p.cdQ = now + G.Q.cd; send(p.ws, { t: 'cd', k, ms: G.Q.cd });
    if (target) {
      p.fires.splice(p.fires.indexOf(target), 1);
      broadcast({ t: 'fx', type: 'dash', x: o.x, y: o.y, x2: target.x, y2: target.y, c: 'rgba(120,230,255,.6)', dur: 350 });
      p.x = target.x; p.y = target.y;
      send(p.ws, { t: 'warp', x: p.x, y: p.y });
    }
    if (p.fires.length) {
      let nf = null, nd = Infinity;
      for (const f of p.fires) { const d = Math.hypot(f.x - p.x, (f.y - p.y) / 0.8); if (d < nd) { nd = d; nf = f; } }
      p.fires.splice(p.fires.indexOf(nf), 1);
      foxBlast(p, nf, now, lag, G.eff.dmg);
    } else p.qNext = true;
  } else if (k === 'E') {
    if (!p.fires.length) return;
    p.cdE = now + G.E.cd; send(p.ws, { t: 'cd', k, ms: G.E.cd });
    const list = p.fires.splice(0);
    p.eNext = list.length;
    broadcast({ t: 'fx', type: 'pull', x: o.x, y: o.y, pts: list.map(f => [Math.round(f.x), Math.round(f.y)]), dur: G.E.pullMs });
  } else {
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
  if (k === 'E') { p.invisUntil = now + S.dur; return; }
  breakStealth(p);
  if (k === 'Q') {
    const a = p.aim, gx = o.x, gy = o.y / 0.8, ex = gx + Math.cos(a) * S.range, ey = gy + Math.sin(a) * S.range;
    broadcast({ t: 'fx', type: 'thrust', x: o.x, y: o.y, a, len: S.range, w: S.width, dur: 320 });
    for (const t of targetsOf(p)) {
      const tp = posAt(t, now - lag);
      if (segDist(tp.x, tp.y / 0.8, gx, gy, ex, ey) > S.width) continue;
      dmgTo(t, S.dmg, now, { x: o.x, y: o.y, by: p });
      if (t.role === 1) t.markUntil = now + S.markMs;
    }
  } else {
    let tx = Number(m && m.cx), ty = Number(m && m.cy) + 30;
    if (!Number.isFinite(tx) || !Number.isFinite(ty)) { tx = o.x + Math.cos(p.aim) * 2 * RADPX; ty = o.y + Math.sin(p.aim) * 2 * RADPX * 0.8; }
    const nx = (tx - CX) / RX, ny = (ty - CY) / RY, d = Math.hypot(nx, ny);
    if (d > 1) { tx = CX + nx / d * RX; ty = CY + ny / d * RY; }
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
    if (n > 0) { p.cdQ = 0; send(p.ws, { t: 'cd', k: 'Q', ms: 0 }); }
  }
  checkRoundEnd();
}
function dashHits(p, D, px, py, now) {
  let any = false;
  for (const t of targetsOf(p)) {
    if (D.hit.has(t.id)) continue;
    const tp = posAt(t, now - D.lag);
    if (segDist(tp.x, tp.y / 0.8, px, py / 0.8, p.x, p.y / 0.8) > SHIELDER.E.hit) continue;
    D.hit.add(t.id); any = true;
    const S = SHIELDER.E;
    dmgTo(t, S.dmg, now, { x: D.sx, y: D.sy, by: p });
    if (t.role !== 1) continue;
    t.stunUntil = Math.max(t.stunUntil, now + S.stun);
    const v = S.kb / (S.kbMs / 1000);
    t.kbUntil = now + S.kbMs; t.kbx = Math.cos(D.a) * v; t.kby = Math.sin(D.a) * v;
  }
  return any;
}
function shielderSkill(p, k, m, now) {
  const S = SHIELDER[k], o = originOf(p, m), lag = lagOf(m);
  p['cd' + k] = now + S.cd; send(p.ws, { t: 'cd', k, ms: S.cd });
  if (k === 'Q') {
    broadcast({ t: 'fx', type: 'ring', x: o.x, y: o.y, r: S.radius, dur: 700 });
    for (const t of targetsOf(p)) {
      const tp = posAt(t, now - lag);
      if (Math.hypot(tp.x - o.x, (tp.y - o.y) / 0.8) <= S.radius) { t.tauntUntil = now + S.ms; t.tauntBy = p.id; }
    }
  } else if (k === 'E') {
    const a = p.aim, gx = o.x, gy = o.y / 0.8;
    const inside = d => { const nx = (gx + Math.cos(a) * d - CX) / RX, ny = ((gy + Math.sin(a) * d) * 0.8 - CY) / RY; return nx * nx + ny * ny <= 1; };
    let len = S.dist;
    while (len > 0 && !inside(len)) len -= 5;
    len = Math.max(0, len);
    const ex = gx + Math.cos(a) * len, egy = gy + Math.sin(a) * len;
    broadcast({ t: 'fx', type: 'dash', by: p.id, x: o.x, y: o.y, x2: ex, y2: egy * 0.8, a, span: ATK.span, dur: S.dashMs + 150, follow: 1 });
    p.x = o.x; p.y = o.y;
    p.dash = { sx: o.x, sy: o.y, ex, ey: egy * 0.8, a, t0: now, ms: S.dashMs, lag, hit: new Set() };
  } else {
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
      if (inConeAt(o.x, o.y, p.aim, tp.x, tp.y, S.range, S.span, t.hr || 0)) { dmgTo(t, S.dmg, now, { x: o.x, y: o.y, by: p }); if (t.role === 1) t.stunUntil = now + S.stun; }
    }
  } else if (k === 'E') {
    p.guardUntil = now + S.dur;
  } else {
    broadcast({ t: 'fx', type: 'swords', x: o.x, y: o.y, r: S.ring, ar: S.radius, cr: S.cRadius, n: S.swords, dur: 900 });
    const gy = o.y / 0.8, sw = [];
    for (let n = 0; n < S.swords; n++) { const a = n * 2 * Math.PI / S.swords; sw.push({ x: o.x + Math.cos(a) * S.ring, y: gy + Math.sin(a) * S.ring, r: S.radius, d: S.dmg }); }
    sw.push({ x: o.x, y: gy, r: S.cRadius, d: S.cdmg });
    for (const s of sw) {
      for (const t of targetsOf(p)) {
        const tp = posAt(t, now - lag);
        if (t.role !== 1 || Math.hypot(tp.x - s.x, tp.y / 0.8 - s.y) > s.r + 10) continue;
        dmgTo(t, s.d, now, { x: o.x, y: o.y, by: p });
        if (t.role === 1) t.slowUntil = now + S.slowMs;
      }
    }
  }
  checkRoundEnd();
}

const bombs = new Map();
const heal = (p, n) => { p.hp = Math.min(p.mh, p.hp + n); };
const cleanse = p => { p.burnUntil = p.stunUntil = p.slowUntil = p.tauntUntil = p.charmUntil = p.kbUntil = p.markUntil = p.dmUntil = 0; };
function applyBurn(t, by, ms, now) {
  if (t.role !== 1) return;
  if (!(now < t.burnUntil)) t.burnNext = now + BURN.tickMs;
  t.burnUntil = now + ms; t.burnBy = by.id;
}
function wallDist(x, gy, a) {
  const px = (x - CX) / RX, py = (gy * 0.8 - CY) / RY, ax = Math.cos(a) / RX, ay = Math.sin(a) * 0.8 / RY;
  const A = ax * ax + ay * ay, B = 2 * (px * ax + py * ay), C = px * px + py * py - 1, D = B * B - 4 * A * C;
  return D < 0 ? 0 : Math.max(0, (-B + Math.sqrt(D)) / (2 * A));
}
function sanctBlocked(owner, x0, gy0, x1, gy1, now) {
  for (const p of players.values()) {
    const S = p.sanct;
    if (S && p.id !== owner && now < S.until && segDist(S.x, S.y / 0.8, x0, gy0, x1, gy1) <= S.r) return true;
  }
  return false;
}
function inSanct(t, now) { const S = t.sanct; return !!S && now < S.until && Math.hypot(t.x - S.x, (t.y - S.y) / 0.8) <= S.r; }
function devilMark(p, t, now) {
  if (t.role !== 1) return;
  const max = now < p.libUntil ? LUC.mark.maxLib : LUC.mark.max;
  p.dmList = (p.dmList || []).filter(id => { const q = players.get(id); return q && q.role === 1 && now < q.dmUntil && q.dmBy === p.id; });
  if (p.dmList.includes(t.id)) return;
  if (p.dmList.length >= max) { const old = players.get(p.dmList.shift()); if (old) old.dmUntil = 0; }
  t.dmUntil = now + LUC.mark.ms; t.dmBy = p.id; p.dmList.push(t.id);
}
function lucTransform(p, form, now) {
  p.lf = form; p.lPend = false;
  p.mh = statsOf(p).hp; heal(p, 300);
  cleanse(p); p.beam = p.pure = null;
  p.cdQ = p.cdE = p.cdR = 0;
  for (const k of ['Q', 'E', 'R']) send(p.ws, { t: 'cd', k, ms: 0 });
  broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 1.4 * RADPX, c: form === 'a' ? '#fff59a' : '#ff3a3a', dur: 700 });
  const S = form === 'a' ? LUC.Q : LUC.E, luc = form === 'a' ? 'Q' : 'E', kind = form === 'a' ? 'lsq' : 'lse';
  for (let i = 0; i < 8; i++) {
    const a = Math.atan2(Math.sin(p.aim + i * Math.PI / 4), Math.cos(p.aim + i * Math.PI / 4));
    spawnArrow(p, { x: p.x, y: p.y }, 0, now, { a, dmg: S.dmg, spd: S.spd, range: S.range, radius: S.radius, kind, type: 'magic', luc, sc: S.sc });
  }
}
function lucHit(ar, t, now) {
  const p = players.get(ar.owner);
  if (p && p.cls === 'Gamer' && p.role === 1) { if (ar.luc === 'E') applyBurn(t, p, LUC.E.burnMs, now); return; }
  if (!p || p.cls !== 'Lucifer' || p.role !== 1) return;
  const cut = ms => { if (!p.lUsed) { p.cdR = Math.max(now, p.cdR - ms); send(p.ws, { t: 'cd', k: 'R', ms: p.cdR - now }); } };
  if (ar.luc === 'Q' || ar.luc === 'E') {
    cut(LUC.G.skillCut);
    if (ar.luc === 'E') applyBurn(t, p, LUC.E.burnMs, now);
    if (p.lPend) lucTransform(p, ar.luc === 'Q' ? 'a' : 'd', now);
  } else if (ar.luc === 'atk') {
    cut(LUC.G.atkCut);
    if (p.lf === 'd') devilMark(p, t, now);
  }
}
function luciferAttack(p, m, now) {
  if (now < p.atkReady) return;
  const st = statsOf(p), F = lForm(p), o = originOf(p, m), lag = lagOf(m);
  p.atkReady = now + st.atkCd / atkSpeed(p, now);
  spawnArrow(p, o, lag, now, { a: p.aim, dmg: st.dmg, spd: F.spd, range: F.range, radius: F.radius, kind: 'lbase', type: p.lf === 'd' ? 'phys' : 'magic', luc: 'atk' });
}
function spawnBomb(p, o, a, r, dmg, lift, now) {
  const id = ++arrowSeq, len = wallDist(o.x, o.y / 0.8, a);
  bombs.set(id, { id, owner: p.id, x: o.x, gy: o.y / 0.8, a, r, dmg, lift, t0: now, len, d: 0, next: new Map() });
  broadcast({ t: 'arrow', id, by: p.id, x: o.x, y: o.y, a, spd: LUC.bomb.spd, range: len, adv: 0, sc: r / RADPX, kd: 'bomb' });
}
function endBomb(b) { bombs.delete(b.id); broadcast({ t: 'arrowEnd', id: b.id }); }
function stepBombs(now) {
  let any = false;
  for (const b of bombs.values()) {
    const own = players.get(b.owner);
    if (!own || own.role !== 1 || phase !== 'round') { endBomb(b); continue; }
    const d = Math.min(b.len, LUC.bomb.spd * (now - b.t0) / 1000), px = b.x + Math.cos(b.a) * d, pgy = b.gy + Math.sin(b.a) * d;
    if (sanctBlocked(b.owner, b.x + Math.cos(b.a) * b.d, b.gy + Math.sin(b.a) * b.d, px, pgy, now)) { endBomb(b); continue; }
    b.d = d;
    for (const t of targetsOf(own)) {
      if (Math.hypot(t.x - px, t.y / 0.8 - pgy) > b.r + 15) continue;
      const nx = b.next.get(t.id);
      if (nx !== undefined && now < nx) continue;
      if (nx === undefined && b.lift) t.stunUntil = Math.max(t.stunUntil, now + LUC.bomb.lift);
      b.next.set(t.id, now + LUC.bomb.tickMs);
      dmgTo(t, b.dmg, now, { x: px, y: pgy * 0.8, kill: own, type: 'phys' });
      devilMark(own, t, now); any = true;
    }
    if (d >= b.len) endBomb(b);
  }
  if (any) checkRoundEnd();
}
function mapRayLen(x, y, a) {
  for (let d = 0; d < 4000; d += 10) {
    const px = x + Math.cos(a) * d, py = y + Math.sin(a) * d * 0.8;
    if (px < 0 || px > MAP || py < 0 || py > MAP) return d;
  }
  return 4000;
}
function stepSanct(now) {
  for (const o of players.values()) {
    const S = o.sanct;
    if (!S) continue;
    if (now >= S.until || o.role !== 1) { o.sanct = null; continue; }
    for (const t of targetsOf(o)) {
      const dx = t.x - S.x, dy = (t.y - S.y) / 0.8, d = Math.hypot(dx, dy), R = S.r + 18;
      if (d >= R) continue;
      const ux = d > 1 ? dx / d : 1, uy = d > 1 ? dy / d : 0, c = clampArena({ x: S.x + ux * R, y: S.y + uy * R * 0.8 });
      t.x = c.x; t.y = c.y;
    }
  }
}
function stepLucifer(p, now) {
  let end = false;
  const B = p.beam;
  if (B) {
    if (p.role !== 1) p.beam = null;
    else {
      const c = Math.cos(B.a), s = Math.sin(B.a);
      const inB = q => { const dx = q.x - B.x, dy = (q.y - B.y) / 0.8, al = dx * c + dy * s, pp = -dx * s + dy * c; return al >= 0 && al <= B.len && Math.abs(pp) <= LUC.beam.half; };
      while (B.next < B.until && now >= B.next) {
        B.next += LUC.beam.tickMs;
        for (const t of targetsOf(p)) if (inB(t)) { dmgTo(t, LUC.beam.dmg, now, { x: B.x, y: B.y, kill: p, type: 'magic' }); end = true; }
        if (inB(p)) heal(p, LUC.beam.heal);
      }
      if (now >= B.until) p.beam = null;
    }
  }
  const P = p.pure;
  if (P) {
    if (p.role !== 1) p.pure = null;
    else {
      while (P.next < P.until && now >= P.next) {
        const r = P.next - P.t0 < LUC.pure.delay ? LUC.pure.r0 : LUC.pure.r1;
        P.next += LUC.pure.tickMs;
        for (const t of targetsOf(p)) if (Math.hypot(t.x - P.x, (t.y - P.y) / 0.8) <= r + 15) { dmgTo(t, LUC.pure.dmg, now, { x: P.x, y: P.y, kill: p, type: 'magic' }); end = true; }
        if (Math.hypot(p.x - P.x, (p.y - P.y) / 0.8) <= r + 15) { heal(p, LUC.pure.heal); cleanse(p); }
      }
      if (now >= P.until) p.pure = null;
    }
  }
  return end;
}
function luciferSkill(p, k, m, now) {
  const o = originOf(p, m), cd = ms => { p['cd' + k] = now + ms; send(p.ws, { t: 'cd', k, ms }); };
  const shot = (S, luc, kind) => {
    cd(p.lPend ? LUC.G.afterCd : S.cd);
    spawnArrow(p, o, lagOf(m), now, { a: p.aim, dmg: S.dmg, spd: S.spd, range: S.range, radius: S.radius, kind, type: 'magic', luc, sc: S.sc });
  };
  if (p.lf === '') {
    if (k === 'Q') shot(LUC.Q, 'Q', 'lsq');
    else if (k === 'E') shot(LUC.E, 'E', 'lse');
    else {
      if (p.lUsed) return;
      p.lUsed = p.lPend = true;
      p.cdQ = p.cdE = 0; send(p.ws, { t: 'cd', k: 'Q', ms: 0 }); send(p.ws, { t: 'cd', k: 'E', ms: 0 });
      p.cdR = now + 1e7; send(p.ws, { t: 'cd', k: 'R', ms: 1e7 });
      broadcast({ t: 'fx', type: 'ring', x: o.x, y: o.y, r: RADPX, c: '#ffe9a8', dur: 600 });
    }
  } else if (p.lf === 'a') {
    if (k === 'Q') {
      const len = mapRayLen(o.x, o.y, p.aim) + LUC.beam.pad;
      cd(LUC.beam.cd); p.beam = { x: o.x, y: o.y, a: p.aim, len, next: now, until: now + LUC.beam.ms };
      broadcast({ t: 'fx', type: 'beam', x: o.x, y: o.y, a: p.aim, len, w: LUC.beam.half * 2, dur: LUC.beam.ms });
    } else if (k === 'E') {
      cd(LUC.sanct.cd); p.sanct = { x: o.x, y: o.y, r: LUC.sanct.r, until: now + LUC.sanct.ms, t: now };
      broadcast({ t: 'fx', type: 'sanct', x: o.x, y: o.y, r: LUC.sanct.r, dur: LUC.sanct.ms });
      stepSanct(now);
    } else {
      cd(LUC.pure.cd); p.pure = { x: o.x, y: o.y, t0: now, next: now, until: now + LUC.pure.ms };
      broadcast({ t: 'fx', type: 'pillar', x: o.x, y: o.y, r0: LUC.pure.r0, r1: LUC.pure.r1, delay: LUC.pure.delay, dur: LUC.pure.ms });
    }
  } else {
    const lib = now < p.libUntil;
    if (k === 'Q') {
      cd(lib ? LUC.bomb.libCd : LUC.bomb.cd);
      spawnBomb(p, o, p.aim, LUC.bomb.r, LUC.bomb.dmg, true, now);
      if (lib) for (const s of [-1, 1]) spawnBomb(p, o, p.aim + s * LUC.bomb.small.fan, LUC.bomb.small.r, LUC.bomb.small.dmg, false, now);
    } else if (k === 'E') {
      const list = targetsOf(p).filter(t => now < t.dmUntil && t.dmBy === p.id);
      if (!list.length) return;
      cd(lib ? LUC.absorb.libCd : LUC.absorb.cd);
      let total = 0;
      for (const t of list) {
        const before = t.hp;
        broadcast({ t: 'fx', type: 'dash', x: t.x, y: t.y, x2: p.x, y2: p.y, c: 'rgba(255,60,80,.6)', dur: 350 });
        dmgTo(t, Math.round(before * LUC.absorb.pct), now, { x: p.x, y: p.y, kill: p, type: 'pierce' });
        total += Math.max(0, Math.min(before, before - t.hp)); t.dmUntil = 0;
      }
      p.dmList = [];
      heal(p, Math.round(total * (lib ? LUC.absorb.healLib : LUC.absorb.heal)));
    } else {
      cd(LUC.lib.cd); p.libUntil = now + LUC.lib.ms;
      for (const kk of ['Q', 'E']) {
        const cap = now + (kk === 'Q' ? LUC.bomb.libCd : LUC.absorb.libCd);
        if (p['cd' + kk] > cap) { p['cd' + kk] = cap; send(p.ws, { t: 'cd', k: kk, ms: cap - now }); }
      }
      broadcast({ t: 'fx', type: 'ring', x: o.x, y: o.y, r: 1.2 * RADPX, c: '#ff3a3a', dur: 700 });
    }
  }
  checkRoundEnd();
}
// ---- Financier ----
const FIN = {
  passive: { ms: 5000, mul: 1.02 },
  Q: { cd: 500, cost: 100, pick: 48 },
  E: { cd: 15000, min: 200, cost: 200, ms: 2000 },
  R: { cd: 25000, ms: 10000, drain: 70, hpMul: 1.2, heal: 1000, atkMul: 1.1 }
};
const stockPL = (f, t) => (f.buyDealt + (t.hp - f.buyHp0)) / 100;
function stockClear(p) { if (p.buy) send(p.ws, { t: 'stk', id: 0 }); p.buy = 0; }
function stepIns(p, now) {
  if (p.insUntil && now >= p.insUntil) {
    const a = Math.round(p.insAcc); p.insUntil = 0; p.insAcc = 0;
    heal(p, a); fxTxt(p.x, p.y - 30, '🛡️ +' + a, '#9dffb0');
  }
}
function stepFinancier(p, now) {
  for (let i = 0; i < 4 && now >= p.finNext; i++) { p.finNext += FIN.passive.ms; p.mh *= FIN.passive.mul; p.hp *= FIN.passive.mul; p.fDmg *= FIN.passive.mul; }
  stepIns(p, now);
  if (p.depUntil) {
    while (p.depNext <= p.depUntil && now >= p.depNext) { p.hp = Math.max(1, p.hp - FIN.R.drain); p.depNext += 1000; }
    if (now >= p.depUntil) {
      p.depUntil = 0; p.mh *= FIN.R.hpMul; heal(p, FIN.R.heal); p.fDmg *= FIN.R.atkMul;
      fxTxt(p.x, p.y - 30, '🏦 만기!', '#ffe08a');
      broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 1.4 * RADPX, c: '#ffd66b', dur: 700 });
    }
  }
  if (p.buy) {
    const t = players.get(p.buy);
    if (!t || t.role !== 1) stockClear(p);
    else if (now >= p.stkNext) { p.stkNext = now + 200; send(p.ws, { t: 'stk', id: t.id, n: t.name, pl: Math.round(stockPL(p, t) * 100) / 100 }); }
  }
}
function financierSkill(p, k, m, now) {
  const cd = ms => { p['cd' + k] = now + ms; send(p.ws, { t: 'cd', k, ms }); };
  if (k === 'Q') {
    if (p.buy) {
      const t = players.get(p.buy);
      if (!t || t.role !== 1) return stockClear(p);
      const pl = stockPL(p, t), gain = Math.max(0, 100 + pl);
      cd(FIN.Q.cd); heal(p, gain); p.fDmg *= Math.max(0.1, 1 + pl / 100); stockClear(p);
      fxTxt(p.x, p.y - 30, '📈 ' + (pl >= 0 ? '+' : '') + pl.toFixed(1) + '% · +' + Math.round(gain) + ' HP', pl >= 0 ? '#9dffb0' : '#ff8a8a');
    } else {
      const cx = Number(m && m.cx), cy = Number(m && m.cy);
      if (!Number.isFinite(cx) || !Number.isFinite(cy) || p.hp <= FIN.Q.cost) return;
      let best = null, bd = 1e9;
      for (const t of players.values()) {
        if (t === p || !t.joined || t.role !== 1) continue;
        const d = Math.hypot(t.x - cx, t.y - 24 - cy);
        if (d <= FIN.Q.pick + (t.hr || 0) * 1.4 && d < bd) { bd = d; best = t; }
      }
      if (!best) return;
      cd(FIN.Q.cd); p.hp -= FIN.Q.cost; p.buy = best.id; p.buyDealt = 0; p.buyHp0 = best.hp; p.stkNext = 0;
      fxTxt(p.x, p.y - 30, '-' + FIN.Q.cost, '#ff8a8a');
    }
  } else if (k === 'E') {
    if (p.hp <= FIN.E.min) return;
    cd(FIN.E.cd); p.hp -= FIN.E.cost; p.insUntil = now + FIN.E.ms; p.insAcc = 0;
    broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 1.1 * RADPX, c: '#7fe0ff', dur: 600 });
  } else {
    cd(FIN.R.cd); p.depUntil = now + FIN.R.ms; p.depNext = now + 1000;
    broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 1.3 * RADPX, c: '#ffd66b', dur: 600 });
    fxTxt(p.x, p.y - 30, '🏦 정기적금', '#ffe08a');
  }
}
// ---- Tower ----
const TOWER = {
  hr: 36, maxUnits: 12,
  merc: { ms: 8000, msAwk: 3000 },
  Q: { cd: 10000, dmg: 220, radius: 1.5 * RADPX, speed: 800 },
  E: { cd: 15000, heal: 0.2 },
  R: { cd: 25000, dur: 10000, dmg: 150, range: 4 * RADPX, gap: 22 },
  INF: { hp: 350, dmg: 50, atkCd: 700, speed: SPEED * 0.8, range: 1 * RADPX },
  ARC: { hp: 200, dmg: 60, atkCd: 1000, speed: SPEED * 0.7, range: 3 * RADPX, keep: 2.4 * RADPX },
  aggro: 6 * RADPX
};
function spawnUnit(p, type, now) {
  let n = 0; for (const u of units.values()) if (u.owner === p.id) n++;
  if (n >= TOWER.maxUnits) return;
  const D = type === 'i' ? TOWER.INF : TOWER.ARC, a = Math.random() * Math.PI * 2, r = 1.2 * RADPX + Math.random() * 40;
  const c = clampArena({ x: p.x + Math.cos(a) * r, y: p.y + Math.sin(a) * r * 0.8 });
  const u = { id: 100000 + (++unitSeq), unit: true, ut: type, cls: type === 'i' ? 'UnitInf' : 'UnitArc', owner: p.id, name: '', x: c.x, y: c.y, hp: D.hp, mh: D.hp, role: 1, joined: true, hist: [],
    aim: 0, face: 1, moving: false, atkReady: now + 400, stunUntil: 0, slowUntil: 0, kbUntil: 0, kbx: 0, kby: 0, tauntUntil: 0, tauntBy: 0, tgt: 0, ws: null, hr: 0 };
  units.set(u.id, u);
  broadcast({ t: 'fx', type: 'ring', x: u.x, y: u.y, r: 0.6 * RADPX, c: '#ffe08a', dur: 400 });
}
const gdist = (a, b) => Math.hypot(a.x - b.x, (a.y - b.y) / 0.8);
function stepUnits(dt, now) {
  for (const u of units.values()) {
    const own = players.get(u.owner);
    if (phase !== 'round' || !own || own.role !== 1) { units.delete(u.id); continue; }
    const D = u.ut === 'i' ? TOWER.INF : TOWER.ARC;
    let dx = 0, dy = 0, mul = 1;
    if (now >= u.stunUntil) {
      const enemies = targetsOf(own).filter(t => t.role === 1 && now >= (t.invisUntil || 0));
      let tgt = null;
      if (now < u.tauntUntil) { const s = players.get(u.tauntBy); if (s && s.role === 1) { tgt = s; mul = SHIELDER.Q.slow; } }
      if (!tgt) tgt = enemies.find(t => t.id === u.tgt && gdist(u, t) <= TOWER.aggro * 1.4) || null;
      if (!tgt) { let best = TOWER.aggro; for (const t of enemies) { const d = gdist(u, t); if (d < best) { best = d; tgt = t; } } }
      u.tgt = tgt ? tgt.id : 0;
      if (tgt) {
        const d = gdist(u, tgt), a = Math.atan2((tgt.y - u.y) / 0.8, tgt.x - u.x), ux = Math.cos(a), uy = Math.sin(a);
        u.aim = a; u.face = ux >= 0 ? 1 : -1;
        if (u.ut === 'i') {
          if (d > D.range + (tgt.hr || 0) - 12) { dx = ux; dy = uy; }
          else if (now >= u.atkReady) {
            u.atkReady = now + D.atkCd;
            broadcast({ t: 'fx', type: 'cone', by: u.id, x: u.x, y: u.y, a, span: ATK.span, r: D.range, c: 'rgba(255,255,255,.5)', dur: 220 });
            dmgTo(tgt, D.dmg, now, { x: u.x, y: u.y, by: own, basic: true });
            checkRoundEnd();
          }
        } else {
          if (d > D.range * 0.92) { dx = ux; dy = uy; }
          else if (d < D.keep) { dx = -ux; dy = -uy; }
          if (d <= D.range && now >= u.atkReady) {
            u.atkReady = now + D.atkCd;
            spawnArrow(own, { x: u.x, y: u.y }, 0, now, { a, dmg: D.dmg, spd: ARROW.speed, range: D.range, kind: 'tarr' });
          }
        }
      } else if (gdist(u, own) > 2.5 * RADPX) {
        const d = gdist(u, own); dx = (own.x - u.x) / d; dy = ((own.y - u.y) / 0.8) / d;
        u.face = dx >= 0 ? 1 : -1;
      }
      for (const v of units.values()) {
        if (v === u) continue;
        const d = gdist(u, v);
        if (d > 0 && d < 34) { dx += (u.x - v.x) / d * 0.6; dy += ((u.y - v.y) / 0.8) / d * 0.6; }
      }
    }
    if (now < u.kbUntil) {
      u.x += u.kbx * dt; u.y += u.kby * dt * 0.8;
      const nx = (u.x - CX) / RX, ny = (u.y - CY) / RY, d = Math.hypot(nx, ny);
      if (d > 1) { u.x = CX + nx / d * RX; u.y = CY + ny / d * RY; }
    }
    const l = Math.hypot(dx, dy);
    if (l > 0.01) {
      dx /= l; dy /= l;
      const spd = D.speed * mul * (now < u.slowUntil ? KNIGHT.R.slow : 1);
      u.x += dx * spd * dt; u.y += dy * spd * dt * 0.8;
      const nx = (u.x - CX) / RX, ny = (u.y - CY) / RY, d = Math.hypot(nx, ny);
      if (d > 0.97) { u.x = CX + nx / d * 0.97 * RX; u.y = CY + ny / d * 0.97 * RY; }
      u.moving = true;
    } else u.moving = false;
    u.hist.push({ t: now, x: u.x, y: u.y });
    while (u.hist.length && u.hist[0].t < now - HIST_MS) u.hist.shift();
  }
}
function stepBalls(now) {
  for (let i = balls.length - 1; i >= 0; i--) {
    const b = balls[i];
    if (now < b.at) continue;
    balls.splice(i, 1);
    const own = players.get(b.owner);
    curTint = b.tint || null; broadcast({ t: 'fx', type: 'ring', x: b.x, y: b.y, r: TOWER.Q.radius, c: '#ff9a3c', dur: 450 }); curTint = null;
    if (!own || phase !== 'round') continue;
    for (const t of targetsOf(own)) if (Math.hypot(t.x - b.x, (t.y - b.y) / 0.8) <= TOWER.Q.radius + (t.hr || 0)) dmgTo(t, TOWER.Q.dmg, now, { x: b.x, y: b.y, by: own, type: 'phys' });
    checkRoundEnd();
  }
}
function towerSkill(p, k, m, now) {
  const T = TOWER, o = originOf(p, m);
  const cd = ms => { p['cd' + k] = now + ms; send(p.ws, { t: 'cd', k, ms }); };
  if (k === 'Q') {
    cd(T.Q.cd);
    let tx = Number(m && m.cx), ty = Number(m && m.cy);
    if (!Number.isFinite(tx) || !Number.isFinite(ty)) { tx = o.x + Math.cos(p.aim) * 5 * RADPX; ty = o.y + Math.sin(p.aim) * 5 * RADPX * 0.8; }
    const c = clampArena({ x: tx, y: ty }), ms = Math.max(350, Math.round(Math.hypot(c.x - o.x, (c.y - o.y) / 0.8) / T.Q.speed * 1000));
    balls.push({ owner: p.id, x: c.x, y: c.y, at: now + ms, tint: curTint });
    broadcast({ t: 'fx', type: 'cannon', x0: o.x, y0: o.y, x1: c.x, y1: c.y, dur: ms });
  } else if (k === 'E') {
    cd(T.E.cd);
    heal(p, (p.mh - p.hp) * T.E.heal);
    spawnUnit(p, 'i', now);
    broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 1.2 * RADPX, c: '#7dffb2', dur: 600 });
    fxTxt(p.x, p.y - 40, '🔧 수리', '#9dffb0');
  } else {
    cd(T.R.cd);
    p.towerRUntil = now + T.R.dur;
    p.mercNext = Math.min(p.mercNext || Infinity, now + T.merc.msAwk);
    broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 1.6 * RADPX, c: '#ffb04a', dur: 700 });
    fxTxt(p.x, p.y - 40, '🛡️ 항전', '#ffd08a');
  }
}
// ---- Sword Master ----
const smNeed = (p, now) => now < p.smAwkUntil ? SM.atk.needAwk : SM.atk.need;
function knockFrom(t, o, dist, ms, now) {
  const a = Math.atan2((t.y - o.y) / 0.8, t.x - o.x), v = dist / (ms / 1000);
  t.kbUntil = now + ms; t.kbx = Math.cos(a) * v; t.kby = Math.sin(a) * v;
}
function smStrike(p, o, lag, now, aura, mult) {
  const base = aura ? SM.atk.auraDmg : statsOf(p).dmg, dmg = Math.round(base * mult);
  broadcast({ t: 'fx', type: 'smslash', by: p.id, x: o.x, y: o.y, a: p.aim, span: ATK.span, r: ATK.range, aura: aura ? 1 : 0, echo: mult < 1 ? 1 : 0, dur: 280 });
  for (const t of targetsOf(p)) {
    const tp = posAt(t, now - lag);
    if (!inConeAt(o.x, o.y, p.aim, tp.x, tp.y, ATK.range, ATK.span, t.hr || 0)) continue;
    dmgTo(t, dmg, now, { x: o.x, y: o.y, by: p, basic: true, type: aura ? 'magic' : 'phys' });
    if (aura && t.role === 1) knockFrom(t, o, SM.atk.kb, SM.atk.kbMs, now);
  }
  checkRoundEnd();
}
function smCastQ(p, o, lag, now, mult) {
  const Q = SM.Q;
  spawnArrow(p, o, lag, now, { a: p.aim, dmg: Math.round(Q.dmg * mult), hpPct: Q.pct * mult, spd: Q.spd, range: Q.range, radius: Q.radius, pierce: true, kind: 'smq', type: 'magic' });
}
function swordmasterAttack(p, m, now) {
  if (now < p.atkReady) return;
  const o = originOf(p, m), lag = lagOf(m);
  p.atkReady = now + statsOf(p).atkCd;
  const aura = !!p.smAura;
  if (aura) p.smAura = false;
  else if (++p.smN >= smNeed(p, now)) { p.smAura = true; p.smN = 0; }
  p.smLast = { k: 'atk', aura }; p.smSaved = false;
  smStrike(p, o, lag, now, aura, 1);
}
function swordmasterSkill(p, k, m, now) {
  const o = originOf(p, m), lag = lagOf(m), awk = now < p.smAwkUntil;
  const cd = (key, ms) => { p['cd' + key] = now + ms; send(p.ws, { t: 'cd', k: key, ms }); };
  if (k === 'Q') {
    cd('Q', SM.Q.cd); smCastQ(p, o, lag, now, 1); p.smLast = { k: 'Q' }; p.smSaved = false;
  } else if (k === 'E') {
    const L = p.smLast; if (!L) return;
    if (p.smSaved) return fxTxt(p.x, p.y, '공격 후 사용 가능', '#cfcfcf');
    p.smSaved = true;
    const mult = awk ? SM.E.multAwk : SM.E.mult;
    cd('E', awk ? SM.E.cdAwk : SM.E.cd);
    broadcast({ t: 'fx', type: 'ring', x: o.x, y: o.y, r: 0.7 * RADPX, c: '#8fe3ff', dur: 450 });
    const o2 = { x: p.x, y: p.y };
    if (L.k === 'Q') smCastQ(p, o2, 0, now, mult);
    else {
      smStrike(p, o2, 0, now, L.aura, mult);
      if (L.aura) {
        const v = SM.E.dash / (SM.E.dashMs / 1000) * SM.E.dashDir;
        p.kbUntil = now + SM.E.dashMs; p.kbx = Math.cos(p.aim) * v; p.kby = Math.sin(p.aim) * v;
      }
    }
  } else {
    cd('R', SM.R.cd); p.smAwkUntil = now + SM.R.dur;
    if (p.smN >= SM.atk.needAwk && !p.smAura) { p.smAura = true; p.smN = 0; }
    if (p.cdE > now + SM.E.cdAwk) cd('E', SM.E.cdAwk);
    broadcast({ t: 'fx', type: 'ring', x: o.x, y: o.y, r: 1.6 * RADPX, c: '#ff9ad5', dur: 700 });
    fxTxt(p.x, p.y, '✨ 각성', '#ffb3e6');
  }
}
// ---- Gambler ----
function sendRv(p) {
  const rest = p.ch ? p.ch.slice(p.chi) : [], live = rest.filter(Boolean).length;
  send(p.ws, { t: 'rv', n: p.ch ? p.ch.length : 0, i: p.chi, live, blank: rest.length - live, rl: p.reloadUntil ? Math.max(0, p.reloadUntil - Date.now()) : 0 });
}
function loadRevolver(p) {
  p.ch = Array.from({ length: GAMBLER.chambers }, () => Math.random() < 0.5);
  p.chi = 0; p.reloadUntil = 0; sendRv(p);
}
function fireChamber(p, now) {
  if (!p.ch) loadRevolver(p);
  const live = p.ch[p.chi++];
  if (p.chi >= p.ch.length) { p.reloadUntil = now + GAMBLER.reloadMs; p.myTurn = false; }
  sendRv(p);
  return live;
}
const fxTxt = (x, y, s, c) => broadcast({ t: 'fx', type: 'txt', x, y, s, c, dur: 900 });
function gamblerDmg(p, now) {
  const st = statsOf(p);
  return (now < p.gbUntil ? Math.max(st.dmg, GAMBLER.E.buffDmg) : st.dmg) + (now < p.gbPlusUntil ? GAMBLER.R.plusDmg : 0);
}
function gamblerAttack(p, m, now) {
  if (now < p.atkReady) return;
  const st = statsOf(p), o = originOf(p, m), lag = lagOf(m);
  if (!p.ch) loadRevolver(p);
  p.atkReady = now + st.atkCd;
  if (p.myTurn && phase === 'round') return rouletteShot(p, false, now);
  const live = fireChamber(p, now);
  if (!live) return broadcast({ t: 'fx', type: 'puff', g: p.id, x: o.x, y: o.y, a: p.aim, dur: 450 });
  spawnArrow(p, o, lag, now, { a: p.aim, dmg: gamblerDmg(p, now), spd: GAMBLER.spd, range: GAMBLER.range, radius: GAMBLER.radius, kind: 'gbullet', type: 'phys' });
}
function rouletteShot(p, self, now) {
  const R = GAMBLER.R, live = fireChamber(p, now);
  if (self || R.endOnF) p.myTurn = false;
  broadcast({ t: 'fx', type: 'puff', g: p.id, x: p.x, y: p.y, a: p.aim, dur: 450 });
  if (self) {
    if (live) { fxTxt(p.x, p.y, '💥 실탄!', '#ff6b6b'); dmgTo(p, R.self, now, { type: 'pierce' }); }
    else { fxTxt(p.x, p.y, '공포탄! 강화', '#9dffb0'); p.gbPlusUntil = p.fastUntil = now + R.fastMs; heal(p, R.selfHeal); }
  } else if (live) {
    fxTxt(p.x, p.y, '💥 실탄!', '#ff6b6b');
    for (const t of targetsOf(p)) dmgTo(t, R.all, now, { x: p.x, y: p.y, by: p, type: 'pierce' });
  } else {
    fxTxt(p.x, p.y, '공포탄…', '#cfcfcf');
    for (const t of targetsOf(p)) { t.fastUntil = now + R.fastMs; heal(t, R.allHeal); fxTxt(t.x, t.y, '+' + R.allHeal, '#9dffb0'); }
  }
  checkRoundEnd();
}
function gamblerSkill(p, k, m, now) {
  const G = GAMBLER, cd = ms => { p['cd' + k] = now + ms; send(p.ws, { t: 'cd', k, ms }); };
  if (!p.ch) loadRevolver(p);
  if (k === 'Q') {
    cd(G.Q.cd);
    for (let i = p.chi; i < p.ch.length; i++) p.ch[i] = !p.ch[i];
    sendRv(p);
    fxTxt(p.x, p.y, '🔄 밀수', '#ffd66b');
  } else if (k === 'E') {
    if (phase !== 'round') return;
    cd(G.E.cd);
    if (p.myTurn) return rouletteShot(p, true, now);
    const live = fireChamber(p, now);
    if (live) { fxTxt(p.x, p.y, '💥 실탄!', '#ff6b6b'); dmgTo(p, G.E.self, now, { type: 'pierce' }); }
    else { fxTxt(p.x, p.y, '🍀 공포탄! 실탄 ' + G.E.buffDmg, '#9dffb0'); p.gbUntil = now + G.E.buffMs; }
  } else {
    if (phase !== 'round') return;
    cd(G.R.cd);
    loadRevolver(p);
    p.cdE = 0; send(p.ws, { t: 'cd', k: 'E', ms: 0 });
    p.myTurn = true;
    broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: RADPX, c: '#ff4b4b', dur: 700 });
    fxTxt(p.x, p.y, '🎲 내 차례', '#ff8a8a');
  }
  checkRoundEnd();
}
// ---- Gamer ----
const GAMER = {
  atk: { range: 4 * RADPX },
  Q: { cd: 10000 },
  E: { cd: 15000, potion: 250, windMs: 4000, wind: 0.5 },
  R: { cd: 25000, dur: 10000 }
};
const GFN = { Knight: knightSkill, Archer: archerSkill, Shielder: shielderSkill, Assassin: assassinSkill, Lucifer: luciferSkill, SwordMaster: swordmasterSkill, Tower: towerSkill, Financier: financierSkill };
const GCOPY = [
  { cls: 'Knight', k: 'Q', n: '검격' }, { cls: 'Knight', k: 'E', n: '수호 돌진' },
  { cls: 'Archer', k: 'Q', n: '애로우 레인' },
  { cls: 'Shielder', k: 'Q', n: '도발' }, { cls: 'Shielder', k: 'E', n: '실드 태클' },
  { cls: 'Assassin', k: 'Q', n: '소드 샤우트' }, { cls: 'Assassin', k: 'E', n: '은신' },
  { cls: 'Lucifer', k: 'Q', n: '라이트 샷', lf: '' }, { cls: 'Lucifer', k: 'E', n: '파이어 샷', lf: '' },
  { cls: 'Lucifer', k: 'Q', n: '라이트 빔', lf: 'a' }, { cls: 'Lucifer', k: 'E', n: '성역', lf: 'a' },
  { cls: 'Lucifer', k: 'Q', n: '화염탄', lf: 'd' },
  { cls: 'SwordMaster', k: 'Q', n: '검기' }, { cls: 'SwordMaster', k: 'E', n: '세이브' },
  { cls: 'Tower', k: 'Q', n: '포격' }, { cls: 'Tower', k: 'E', n: '수리' },
  { cls: 'Financier', k: 'E', n: '보험' }
];
function randTint() {
  const h = Math.random() * 360, s = 0.85, l = 0.55, a = s * Math.min(l, 1 - l);
  const f = n => { const k = (n + h / 30) % 12; return Math.round(255 * (l - a * Math.max(-1, Math.min(k - 3, 9 - k, 1)))).toString(16).padStart(2, '0'); };
  return '#' + f(0) + f(8) + f(4);
}
const sendGc = (p, now) => send(p.ws, { t: 'gc', l: (p.gCopy || []).map(e => e.n), s: p.gSlots || 1, ch: Math.max(0, (p.gCheatUntil || 0) - (now || Date.now())) });
function gamerAttack(p, m, now) {
  if (now < p.atkReady) return;
  const st = statsOf(p), o = originOf(p, m), lag = lagOf(m);
  p.atkReady = now + st.atkCd / atkSpeed(p, now);
  breakStealth(p);
  const ranged = p.gNext === 1;
  p.gNext = ranged ? 0 : 1;
  if (ranged) {
    spawnArrow(p, o, lag, now, { a: p.aim, dmg: st.dmg, spd: ARROW.speed, range: GAMER.atk.range, kind: 'atk', type: 'magic' });
    return;
  }
  broadcast({ t: 'fx', type: 'cone', by: p.id, x: o.x, y: o.y, a: p.aim, span: ATK.span, r: ATK.range, c: 'rgba(255,255,255,.6)', dur: 220 });
  for (const t of targetsOf(p)) {
    const tp = posAt(t, now - lag);
    if (inConeAt(o.x, o.y, p.aim, tp.x, tp.y, ATK.range, ATK.span, t.hr || 0)) dmgTo(t, st.dmg, now, { x: o.x, y: o.y, by: p, basic: true, type: 'magic' });
  }
  checkRoundEnd();
}
function castCopied(p, e, m, now) {
  const keep = { Q: p.cdQ, E: p.cdE, R: p.cdR }, lf0 = p.lf, tint = randTint();
  p['cd' + e.k] = 0; p.gPierce = e.cls === 'Assassin'; p.lf = e.lf || ''; curTint = tint;
  try { GFN[e.cls](p, e.k, m, now); } finally { curTint = null; }
  const fired = p['cd' + e.k] > 0;
  p.gPierce = false; p.lf = lf0;
  for (const k of ['Q', 'E', 'R']) { p['cd' + k] = keep[k]; send(p.ws, { t: 'cd', k, ms: Math.max(0, keep[k] - now) }); }
  if (fired) {
    if (e.cls === 'Assassin' && e.k === 'E') p.gInvis = true; else if (e.cls === 'Archer') p.gInvis = false;
    const u = e.cls === 'Knight' && e.k === 'E' ? p.guardUntil : e.cls === 'Financier' ? p.insUntil : 0;
    if (u) { p.gtint = tint; p.gtUntil = u; }
  }
  return fired;
}
function gamerSkill(p, k, m, now) {
  const G = GAMER;
  if (k === 'Q') {
    if (p.gCopy.length) {
      const list = p.gCopy; p.gCopy = [];
      for (const e of list) if (!castCopied(p, e, m, now)) p.gCopy.push(e);
      sendGc(p, now);
      checkRoundEnd();
      return;
    }
    const have = new Set();
    for (const q of players.values()) if (q !== p && q.joined && q.cls !== 'Gamer') have.add(q.cls);
    const pool = GCOPY.filter(e => have.has(e.cls));
    if (!pool.length) return fxTxt(p.x, p.y - 30, '복사할 스킬이 없습니다', '#cfcfcf');
    const got = [];
    for (let i = 0, n = Math.min(p.gSlots, pool.length); i < n; i++) got.push(pool.splice(Math.floor(Math.random() * pool.length), 1)[0]);
    p.gCopy = got;
    const ms = now < p.gCheatUntil ? 0 : G.Q.cd;
    p.cdQ = now + ms; send(p.ws, { t: 'cd', k: 'Q', ms });
    sendGc(p, now);
    broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 1.1 * RADPX, c: '#ffd66b', dur: 500 });
    fxTxt(p.x, p.y - 40, '📋 ' + got.map(e => e.n).join(' + '), '#ffe08a');
  } else if (k === 'E') {
    p.cdE = now + G.E.cd; send(p.ws, { t: 'cd', k: 'E', ms: G.E.cd });
    const all = now < p.gCheatUntil, opts = ['slot', 'potion', 'wind'], pick = all ? opts : [opts[Math.floor(Math.random() * 3)]], msg = [];
    for (const o of pick) {
      if (o === 'slot') { p.gSlots = 2; msg.push('🎰 Extra Slot'); }
      else if (o === 'potion') { heal(p, G.E.potion); msg.push('🧪 Health Potion'); }
      else { p.asUntil = now + G.E.windMs; p.asBonus = G.E.wind; msg.push('🌪 Wind Rune'); }
    }
    sendGc(p, now);
    broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 1.2 * RADPX, c: '#9dffb0', dur: 600 });
    fxTxt(p.x, p.y - 40, msg.join(' · '), '#9dffb0');
  } else {
    p.cdR = now + G.R.cd; send(p.ws, { t: 'cd', k: 'R', ms: G.R.cd });
    p.gCheatUntil = now + G.R.dur; p.cdQ = 0; send(p.ws, { t: 'cd', k: 'Q', ms: 0 });
    sendGc(p, now);
    broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 1.5 * RADPX, c: '#ff6bd5', dur: 700 });
    fxTxt(p.x, p.y - 40, '💻 치트', '#ff9be8');
  }
}
function checkTimeout(now) {
  if (phase !== 'round' || now - roundStart < ROUND_MS) return;
  endRound(null, [...players.values()].filter(p => p.role === 1).map(p => p.name));
}

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

const rates = new Map();
function rateOk(key, max, windowMs) {
  const now = Date.now(); let h = rates.get(key);
  if (!h || now - h.t > windowMs) { h = { n: 0, t: now }; rates.set(key, h); }
  return ++h.n <= max;
}
setInterval(() => { const lim = Date.now() - 3600 * 1000; for (const [k, h] of rates) if (h.t < lim) rates.delete(k); }, 60000);

const authFail = (p, err, extra) => send(p.ws, Object.assign({ t: 'auth', ok: 0, err }, extra));
function kickOld(userId, except) {
  for (const q of [...players.values()]) if (q !== except && q.user === userId) {
    q.user = null; q.joined = false; send(q.ws, { t: 'kicked' }); try { q.ws.close(); } catch {}
  }
}
// ---- titles (granted by the admin account, equipped by the owner; stored in Upstash) ----
const ADMIN_ID = 'admin', OBS_ID = 'server', MAX_TITLES = 15;
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
const pushTitle = p => broadcast({ t: 'ttl', id: p.id, tt: titleOf(p) || 0 });
const sendTinfo = p => send(p.ws, { t: 'tinfo', list: p.titles, eq: p.eq });
async function equipTitle(p, id) {
  const now = Date.now();
  if (!p.user) return;
  if (now - p.lastEquip < 300 || (id !== null && (typeof id !== 'string' || !p.titles.some(t => t.id === id)))) return sendTinfo(p);
  p.lastEquip = now;
  if (id) await db.set('eqtitle:' + p.user, id); else await db.del('eqtitle:' + p.user);
  p.eq = id; sendTinfo(p); pushTitle(p);
}
let admLock = Promise.resolve();
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
    if (m.cols !== undefined && m.cols !== null) {
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
  for (const q of players.values()) if (q.user === target) {
    q.titles = list; if (!list.some(t => t.id === q.eq)) q.eq = null;
    sendTinfo(q); pushTitle(q);
  }
  reply(1, msg, { target, nick: rec.nick, list });
}
async function loginOk(p, rec, token) {
  kickOld(rec.id, p);
  p.user = rec.id; p.name = rec.nick;
  if (rec.id === OBS_ID) {
    p.obs = true; p.titles = []; p.eq = null;
    send(p.ws, { t: 'auth', ok: 1, name: rec.nick, token, admin: 0, obs: 1 });
    const all = {};
    for (const q of players.values()) if (q.joined) { const tt = titleOf(q); if (tt) all[q.id] = tt; }
    return send(p.ws, { t: 'ttls', m: all });
  }
  const ti = await loadTitles(rec.id);
  p.titles = ti.list; p.eq = ti.eq;
  if (!p.joined) { p.joined = true; if (phase === 'round') p.role = 2; }
  send(p.ws, { t: 'auth', ok: 1, name: rec.nick, token, admin: rec.id === ADMIN_ID ? 1 : 0 });
  sendTinfo(p);
  const all = {};
  for (const q of players.values()) if (q.joined && q !== p) { const tt = titleOf(q); if (tt) all[q.id] = tt; }
  send(p.ws, { t: 'ttls', m: all });
  if (titleOf(p)) pushTitle(p);
}
async function newSession(id) {
  const token = crypto.randomBytes(32).toString('hex');
  await db.setex('sess:' + sha(token), SESSION_TTL, id);
  return token;
}
async function handleAuth(p, m, ip) {
  if (p.user || p.authBusy) return;
  p.authBusy = true;
  try {
    if (!rateOk('a:' + ip, 40, 60000)) return authFail(p, '시도가 너무 많습니다. 잠시 후 다시 시도해 주세요.');
    if (m.t === 'resume') {
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

    const fk = 'fail:' + id;
    if ((Number(await db.get(fk)) || 0) >= LOCK_FAILS) return authFail(p, '로그인 시도가 너무 많습니다. 10분 후 다시 시도해 주세요.');
    const raw = await db.get('user:' + id), rec = raw && JSON.parse(raw);
    const h = await scryptHex(pw, rec ? rec.salt : DUMMY_SALT);
    if (!rec || !safeEq(h, rec.hash)) {
      if (await db.incr(fk) === 1) await db.expire(fk, LOCK_SEC);
      return authFail(p, '아이디 또는 비밀번호가 올바르지 않습니다.');
    }
    await db.del(fk);
    return await loginOk(p, rec, await newSession(id));
  } finally { p.authBusy = false; }
}

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
  send(ws, { t: 'hello', id, map: mapId, arena: { CX, CY, RX, RY } });
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
      if (phase === 'lobby' && ['Knight', 'Archer', 'Shielder', 'Assassin', 'Gumiho', 'Lucifer', 'Gambler', 'SwordMaster', 'Tower', 'Financier', 'Gamer'].includes(m.cls)) { p.cls = m.cls; resetCombat(p); }
    } else if (m.t === 'map') {
      if (p.user === ADMIN_ID && phase === 'lobby' && Number.isInteger(m.id) && ARENAS[m.id] && m.id !== mapId) { setMap(m.id); sysChat(p.name + ' changed the map.'); }
    } else if (m.t === 'tequip') {
      equipTitle(p, m.id === null ? null : m.id).catch(e => console.error('equip:', e.message));
    } else if (m.t === 'tgrant' || m.t === 'tlist' || m.t === 'trevoke') {
      if (p.user === ADMIN_ID) adminTitle(p, m).catch(e => { console.error('admin title:', e.message); send(ws, { t: 'tadmin', ok: 0, msg: '서버 오류가 발생했습니다.' }); });
    } else if (m.t === 'charge') {
      const now = Date.now();
      if (p.cls === 'Archer' && canAct(p, now) && now >= p.atkReady - 60) p.chargeStart = now;
    } else if (m.t === 'ccancel') {
      p.chargeStart = 0;
    } else if (m.t === 'atk') {
      if (m.a !== undefined) setAim(p, Number(m.a));
      doAttack(p, m);
    } else if (m.t === 'skill') {
      if (m.a !== undefined) setAim(p, Number(m.a));
      doSkill(p, String(m.k), m);
    } else if (m.t === 'ready') {
      if (phase !== 'lobby' || joinedList().length < 2) return;
      p.ready = !p.ready; checkReady();
    }
  });
  ws.on('close', () => {
    players.delete(id); broadcast({ t: 'leave', id });
    if (phase === 'lobby') checkReady(); else if (phase === 'round') checkRoundEnd();
  });
  ws.on('error', () => {});
});

let last = Date.now();
setInterval(() => {
  const now = Date.now(), dt = Math.min((now - last) / 1000, 0.1); last = now;
  let needEnd = false;
  for (const p of players.values()) {
    if (!p.joined) continue;
    let { dx, dy } = p;
    if (p.role === 2 || now < p.stunUntil || now < p.charmUntil) { dx = dy = 0; p.chargeStart = 0; }
    if (p.dash) {
      const D = p.dash;
      if (p.role !== 1) p.dash = null;
      else {
        const px = p.x, py = p.y, f = Math.min(1, (now - D.t0) / D.ms);
        p.x = D.sx + (D.ex - D.sx) * f; p.y = D.sy + (D.ey - D.sy) * f;
        if (dashHits(p, D, px, py, now)) needEnd = true;
        if (f >= 1) p.dash = null;
      }
      dx = dy = 0;
    }
    let tauntMul = 1;
    if (!p.dash && now < p.tauntUntil && p.role === 1 && now >= p.stunUntil) {
      const src = players.get(p.tauntBy);
      if (src && src.joined && src.role === 1) {
        const vx = src.x - p.x, vy = (src.y - p.y) / 0.8, d = Math.hypot(vx, vy);
        if (d > SHIELDER.Q.stop) { dx = vx / d; dy = vy / d; } else dx = dy = 0;
        tauntMul = SHIELDER.Q.slow;
      } else p.tauntUntil = 0;
    }
    if (!p.dash && now < p.charmUntil && p.role === 1 && now >= p.stunUntil) {
      const src = players.get(p.charmBy);
      if (src && src.joined && src.role === 1) {
        const vx = src.x - p.x, vy = (src.y - p.y) / 0.8, d = Math.hypot(vx, vy);
        if (d > GUMIHO.R.stop) { dx = vx / d; dy = vy / d; } else dx = dy = 0;
        tauntMul = GUMIHO.R.speed;
      } else p.charmUntil = 0;
    }
    if (p.role === 1 && p.burnUntil) {
      while (p.role === 1 && p.burnNext <= p.burnUntil && now >= p.burnNext) { dmgTo(p, BURN.tick, now, { kill: players.get(p.burnBy), type: 'phys' }); p.burnNext += BURN.tickMs; needEnd = true; }
    }
    if ((p.cls === 'Lucifer' || p.cls === 'Gamer') && (p.beam || p.pure) && stepLucifer(p, now)) needEnd = true;
    if (p.cls === 'Gamer' && p.role === 1 && phase === 'round' && p.insUntil) stepIns(p, now);
    if (p.cls === 'Lucifer' && p.lf === 'a' && p.role === 1 && phase === 'round') heal(p, ANGEL.regen * dt);
    if (p.cls === 'Gambler' && p.reloadUntil && now >= p.reloadUntil) loadRevolver(p);
    if (p.cls === 'Tower' && p.role === 1 && phase === 'round' && now >= p.mercNext) {
      spawnUnit(p, Math.random() < 0.5 ? 'i' : 'a', now);
      p.mercNext = now + (now < p.towerRUntil ? TOWER.merc.msAwk : TOWER.merc.ms);
    }
    if (p.cls === 'Financier' && p.role === 1 && phase === 'round') stepFinancier(p, now);
    if (now < p.kbUntil && p.role === 1) {
      p.x += p.kbx * dt; p.y += p.kby * dt * 0.8;
      const nx = (p.x - CX) / RX, ny = (p.y - CY) / RY, d = Math.hypot(nx, ny);
      if (d > 1) { p.x = CX + nx / d * RX; p.y = CY + ny / d * RY; }
    }
    if (dx || dy) {
      const l = Math.hypot(dx, dy); dx /= l; dy /= l;
      const spd = SPEED * (now < p.guardUntil ? KNIGHT.E.speed : 1) * (now < p.slowUntil ? KNIGHT.R.slow : 1) * tauntMul * (now < p.hornUntil ? SHIELDER.R.speed : 1) * ((p.cls === 'Assassin' || (p.cls === 'Gamer' && p.gInvis)) && now < p.invisUntil ? ASSASSIN.E.speed : 1) * (now < p.libUntil ? LUC.lib.speed : 1) * (now < p.fastUntil ? GAMBLER.R.fast : 1);
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
  stepSanct(now);
  stepArrows(dt, now);
  stepBombs(now);
  stepUnits(dt, now); stepBalls(now);
  const list = [], hidden = [];
  for (const p of players.values()) {
    if (!p.joined) continue;
    const iv = now < p.invisUntil;
    if (iv && !p.wasIv) { p.hideX = p.x; p.hideY = p.y; }
    p.wasIv = iv;
    const e = { id: p.id, name: p.name, hue: p.hue, x: Math.round(p.x * 10) / 10, y: Math.round(p.y * 10) / 10,
      f: p.face, a: Math.round(p.aim * 100) / 100, m: p.moving ? 1 : 0, c: p.cls, r: p.ready ? 1 : 0, o: p.role,
      hp: Math.max(0, Math.round(p.hp)), mh: Math.round(p.mh), su: Math.max(0, p.stunUntil - now), gd: now < p.guardUntil ? 1 : 0, sl: now < p.slowUntil ? 1 : 0,
      hs: now < p.hasteUntil ? 1 : 0, iv: iv ? 1 : 0, hn: now < p.hornUntil ? 1 : 0, ta: p.role === 1 && now < p.tauntUntil ? 1 : 0, kb: now < p.kbUntil ? 1 : 0, ds: p.dash ? 1 : 0,
      mk: now < p.markUntil ? 1 : 0, as: now < p.asUntil ? p.asBonus : 0, cm: p.role === 1 && now < p.charmUntil ? 1 : 0, bn: p.role === 1 && now < p.burnUntil ? 1 : 0, qn: (p.qNext || p.eNext) ? 1 : 0, lf: p.lf || '', lb: now < p.libUntil ? 1 : 0, dm: p.role === 1 && now < p.dmUntil ? 1 : 0,
      cg: p.chargeStart ? Math.max(1, Math.round(Math.min(now - p.chargeStart, chargeMax(p, now)) / chargeMax(p, now) * ARCHER.charge.maxMs)) : 0,
      rl: p.reloadUntil && now < p.reloadUntil ? 1 : 0, mt: p.myTurn ? 1 : 0, gb: now < p.gbUntil || now < p.gbPlusUntil ? 1 : 0, fs: now < p.fastUntil ? 1 : 0, sa: p.smAura ? 1 : 0, sk: now < p.smAwkUntil ? 1 : 0, tr: now < p.towerRUntil ? 1 : 0, ins: now < p.insUntil ? 1 : 0, dp: now < p.depUntil ? 1 : 0, gm: p.gNext | 0, gt: now < p.gtUntil ? p.gtint : '' };
    list.push(e);
    hidden.push(iv ? Object.assign({}, e, { x: Math.round(p.hideX * 10) / 10, y: Math.round(p.hideY * 10) / 10, a: 0, m: 0, cg: 0 }) : e);
  }
  for (const u of units.values()) {
    const e = { id: u.id, name: '', hue: 0, x: Math.round(u.x * 10) / 10, y: Math.round(u.y * 10) / 10, f: u.face, a: Math.round(u.aim * 100) / 100, m: u.moving ? 1 : 0, c: u.cls, ut: u.ut, ow: u.owner, r: 0, o: 1,
      hp: Math.max(0, Math.round(u.hp)), mh: u.mh, su: Math.max(0, u.stunUntil - now), sl: now < u.slowUntil ? 1 : 0, kb: now < u.kbUntil ? 1 : 0 };
    list.push(e); hidden.push(e);
  }
  const ff = [];
  for (const p of players.values()) if (p.joined) for (const f of p.fires) ff.push({ id: f.id, o: p.id, x: Math.round(f.x), y: Math.round(f.y) });
  const head = { t: 'state', ph: phase, left: phase === 'round' ? Math.max(0, ROUND_MS - (now - roundStart)) : 0, ff };
  if (!list.some(e => e.iv)) { broadcast(Object.assign(head, { p: list })); return; }
  const common = JSON.stringify(Object.assign({}, head, { p: hidden }));
  for (const q of players.values()) {
    if (q.ws.readyState !== 1) continue;
    if (q.joined && now < q.invisUntil) q.ws.send(JSON.stringify(Object.assign({}, head, { p: hidden.map((e, i) => list[i].id === q.id ? list[i] : e) })));
    else q.ws.send(common);
  }
}, 1000 / TICK);

setInterval(() => {
  for (const p of players.values()) {
    if (!p.alive) { p.ws.terminate(); continue; }
    p.alive = false; p.ws.ping();
  }
}, 30000);

server.listen(PORT, () => console.log('Geolgani PvP running on port ' + PORT));
