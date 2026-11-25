const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 3000;
const PUBLIC = path.join(__dirname, 'public');
const MIME = { '.html': 'text/html; charset=utf-8', '.jpg': 'image/jpeg', '.png': 'image/png', '.js': 'text/javascript', '.css': 'text/css', '.txt': 'text/plain; charset=utf-8', '.json': 'application/json; charset=utf-8' };

const ARENA_BASE = [{ CX: 630, CY: 640, RX: 410, RY: 335 }, { CX: 630, CY: 600, RX: 460, RY: 370 }, { CX: 768, CY: 512, RX: 768, RY: 512 }];
let mapScale = 1;
const ARENAS = ARENA_BASE.map(a => ({ ...a }));
let mapId = 1, { CX, CY, RX, RY } = ARENAS[1];
// ---- map 3 collision ----
const MAPDIM = [[1254, 1254], [1254, 1254], [1536, 1024]];
let COL = null, Q = null, SEEN = null, PAR = null, bfsStamp = 0;
try {
  const j = JSON.parse(fs.readFileSync(path.join(PUBLIC, 'map3_col.json'), 'utf8')), g = new Uint8Array(j.w * j.h);
  let k = 0, v = 0; for (const n of j.rle) { if (v) g.fill(1, k, k + n); k += n; v ^= 1; }
  const near = new Int32Array(g.length).fill(-1), q = new Int32Array(g.length); let qh = 0, qt = 0;
  for (let i = 0; i < g.length; i++) if (g[i]) { near[i] = i; q[qt++] = i; }
  while (qh < qt) {
    const i = q[qh++], x = i % j.w, y = (i / j.w) | 0;
    for (let d = 0; d < 4; d++) { const nx = x + [1, -1, 0, 0][d], ny = y + [0, 0, 1, -1][d]; if (nx < 0 || ny < 0 || nx >= j.w || ny >= j.h) continue; const ni = ny * j.w + nx; if (near[ni] < 0) { near[ni] = near[i]; q[qt++] = ni; } }
  }
  COL = { w: j.w, h: j.h, c: j.c, g, near }; Q = new Int32Array(g.length); SEEN = new Uint32Array(g.length); PAR = new Int32Array(g.length);
} catch (e) { console.error('map3 collision load failed:', e.message); }
const solidMap = () => mapId === 2 && !!COL;
const ndist = (nx, ny) => mapId === 2 ? Math.max(Math.abs(nx), Math.abs(ny)) : Math.hypot(nx, ny);
function walkAt(x, y) {
  if (!solidMap()) return true;
  const c = COL.c * mapScale, i = Math.floor(x / c), j = Math.floor(y / c);
  return i >= 0 && j >= 0 && i < COL.w && j < COL.h && COL.g[j * COL.w + i] === 1;
}
function snapWalk(x, y) {
  if (walkAt(x, y)) return { x, y };
  const c = COL.c * mapScale, i = Math.min(COL.w - 1, Math.max(0, Math.floor(x / c))), j = Math.min(COL.h - 1, Math.max(0, Math.floor(y / c))), n = COL.near[j * COL.w + i];
  return n < 0 ? { x, y } : { x: ((n % COL.w) + 0.5) * c, y: (((n / COL.w) | 0) + 0.5) * c };
}
function slideTo(x0, y0, x1, y1) {
  if (!solidMap()) return { x: x1, y: y1 };
  if (!walkAt(x0, y0)) { const s0 = snapWalk(x0, y0); x0 = s0.x; y0 = s0.y; }
  const dx = x1 - x0, dy = y1 - y0, n = Math.max(1, Math.ceil(Math.hypot(dx, dy) / 4));
  let x = x0, y = y0;
  for (let s = 1; s <= n; s++) {
    const tx = x0 + dx * s / n, ty = y0 + dy * s / n;
    if (walkAt(tx, ty)) { x = tx; y = ty; } else if (walkAt(tx, y)) x = tx; else if (walkAt(x, ty)) y = ty; else break;
  }
  return { x, y };
}
function losClear(x0, y0, x1, y1) {
  const n = Math.ceil(Math.hypot(x1 - x0, y1 - y0) / 6);
  for (let s = 1; s < n; s++) if (!walkAt(x0 + (x1 - x0) * s / n, y0 + (y1 - y0) * s / n)) return false;
  return true;
}
const BDX = [1, -1, 0, 0, 1, 1, -1, -1], BDY = [0, 0, 1, -1, 1, -1, 1, -1];
function pathDirTo(o, tx, ty) {
  const w = COL.w, h = COL.h, c = COL.c * mapScale;
  const cellOf = (x, y) => { const i = Math.min(w - 1, Math.max(0, Math.floor(x / c))), j = Math.min(h - 1, Math.max(0, Math.floor(y / c))), k = j * w + i; return COL.g[k] ? k : COL.near[k]; };
  const s = cellOf(o.x, o.y), g = cellOf(tx, ty);
  if (s < 0 || g < 0 || s === g) return null;
  const st = ++bfsStamp; let qh = 0, qt = 0, found = false; Q[qt++] = g; SEEN[g] = st; PAR[g] = -1;
  while (qh < qt && !found) {
    const k = Q[qh++], x = k % w, y = (k / w) | 0;
    for (let d = 0; d < 8; d++) {
      const nx = x + BDX[d], ny = y + BDY[d]; if (nx < 0 || ny < 0 || nx >= w || ny >= h) continue;
      const nk = ny * w + nx; if (!COL.g[nk] || SEEN[nk] === st) continue;
      if (d > 3 && (!COL.g[y * w + nx] || !COL.g[ny * w + x])) continue;
      SEEN[nk] = st; PAR[nk] = k; Q[qt++] = nk; if (nk === s) { found = true; break; }
    }
  }
  if (!found) return null;
  let k = PAR[s], best = k;
  for (let i = 0; i < 6 && k >= 0; i++) { const wx = ((k % w) + 0.5) * c, wy = (((k / w) | 0) + 0.5) * c; if (!losClear(o.x, o.y, wx, wy)) break; best = k; k = PAR[k]; }
  if (best < 0) return null;
  const wx = ((best % w) + 0.5) * c, wy = (((best / w) | 0) + 0.5) * c, vx = wx - o.x, vy = (wy - o.y) / 0.8, l = Math.hypot(vx, vy) || 1;
  return { x: vx / l, y: vy / l };
}
function steer(o, t, ux, uy, now) {
  if (!solidMap()) return { x: ux, y: uy };
  if (losClear(o.x, o.y, t.x, t.y)) { o.pdT = 0; return { x: ux, y: uy }; }
  if (now < (o.pdT || 0)) return { x: o.pdx, y: o.pdy };
  const d = pathDirTo(o, t.x, t.y);
  o.pdT = now + 150; o.pdx = d ? d.x : ux; o.pdy = d ? d.y : uy;
  return { x: o.pdx, y: o.pdy };
}
function ringPos(a, r) {
  if (!solidMap()) return { x: CX + Math.cos(a) * RX * r, y: CY + Math.sin(a) * RY * r };
  const sc = mapScale; return snapWalk((770 + Math.cos(a) * 290 * r) * sc, (655 + Math.sin(a) * 105 * r) * sc);
}
function applyDims() { MAP = MAPDIM[mapId][0] * mapScale; MAPH = MAPDIM[mapId][1] * mapScale; }

const SPEED = 300, TICK = 30, MAX_PLAYERS = 50, MAX_SOCKETS = 200, MAX_PER_IP = 8, AUTH_TIMEOUT = Number(process.env.AUTH_TIMEOUT_MS) || 20000, RATE_PER_S = 100, RATE_BURST = 200, PROTO = 2;
const TRUST_PROXY = process.env.TRUST_PROXY !== '0';
const ipConns = new Map();
function clientIp(req) {
  const xf = req && req.headers && req.headers['x-forwarded-for'];
  if (TRUST_PROXY && xf) { const parts = String(xf).split(',').map(x => x.trim()).filter(Boolean); if (parts.length) return parts[parts.length - 1]; }
  return String((req && req.socket && req.socket.remoteAddress) || '?');
}

const zlib = require('zlib');
const GZ = new Set(['.html', '.js', '.css', '.txt', '.json', '.svg']);
const fileCache = new Map();
const SEC_HEADERS = { 'X-Content-Type-Options': 'nosniff', 'Referrer-Policy': 'same-origin', 'X-Frame-Options': 'DENY' };
if (process.env.CSP !== 'off') SEC_HEADERS['Content-Security-Policy'] = "default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline' https://fonts.googleapis.com https://cdn.jsdelivr.net; font-src 'self' data: https://fonts.gstatic.com https://cdn.jsdelivr.net; img-src 'self' data: blob:; media-src 'self' data: blob:; connect-src 'self' ws: wss:; frame-ancestors 'none'; base-uri 'self'; form-action 'self'";
const server = http.createServer((req, res) => {
  let url;
  try { url = decodeURIComponent(req.url.split('?')[0]); } catch (e) { res.writeHead(400); return res.end(); }
  if (url === '/healthz') { res.writeHead(200); return res.end('ok'); }
  const file = path.normalize(path.join(PUBLIC, url === '/' ? 'index.html' : url));
  if (!file.startsWith(PUBLIC + path.sep) || /(^|[\\/])\./.test(path.relative(PUBLIC, file))) { res.writeHead(403); return res.end(); }
  fs.stat(file, (err, st) => {
    if (err || !st.isFile()) { res.writeHead(404); return res.end('Not found'); }
    const ext = path.extname(file), etag = '"' + st.size.toString(16) + '-' + Math.floor(st.mtimeMs).toString(16) + '"', zip = GZ.has(ext);
    const hdr = Object.assign({ 'Content-Type': MIME[ext] || 'application/octet-stream', 'Cache-Control': 'no-cache', ETag: etag }, SEC_HEADERS);
    if (zip) hdr.Vary = 'Accept-Encoding';
    if (req.headers['if-none-match'] === etag) { res.writeHead(304, hdr); return res.end(); }
    const gz = zip && /\bgzip\b/.test(req.headers['accept-encoding'] || '');
    const out = c => { if (gz) hdr['Content-Encoding'] = 'gzip'; res.writeHead(200, hdr); res.end(gz ? c.gz : c.raw); };
    const c = fileCache.get(file);
    if (c && c.etag === etag) return out(c);
    fs.readFile(file, (e2, data) => {
      if (e2) { res.writeHead(404); return res.end('Not found'); }
      const nc = { etag, raw: data, gz: zip ? zlib.gzipSync(data, { level: 6 }) : null };
      if (data.length < 5e6) fileCache.set(file, nc);
      out(nc);
    });
  });
});

const wss = new WebSocketServer({ server, maxPayload: 1024, perMessageDeflate: false });
const players = new Map();
// ---- training dummies ----
const dummies = [-101, -102, -103].map(id => ({ id, unit: true, dummy: true, owner: -1, role: 1, joined: true, hist: [], hr: 26, x: 0, y: 0, hp: 1e5, mh: 1e5, cls: '', team: 0, sum: 0, last: 0, lastT: 0, stunUntil: 0, charmUntil: 0, slowUntil: 0, kbUntil: 0 }));
function placeDummies() { [-0.42, 0, 0.42].forEach((f, i) => { const d = dummies[i]; if (solidMap()) { const q = snapWalk((690 + i * 100) * mapScale, 560 * mapScale); d.x = q.x; d.y = q.y; } else { d.x = CX + f * RX; d.y = CY - 0.38 * RY; } d.stunUntil = d.slowUntil = d.kbUntil = 0; }); }
function dummyHit(t, d, now) { if (now - t.lastT > 3000) t.sum = 0; t.sum += d; t.last = d; t.lastT = now; }
const inPlay = p => !!p && p.joined && (p.role === 1 || (p.role === 0 && phase !== 'round'));
const PRACT = () => phase === 'round' || phase === 'lobby';
let nextId = 1;

const clean = (s, n) => String(s || '').replace(/[\u0000-\u001f<>]/g, '').trim().slice(0, n);
let outN = 0, curSk = null;
const send = (ws, o) => { if (o && o.t === 'cd') outN++; return ws && ws.readyState === 1 && ws.send(JSON.stringify(o)); };
let curTint = null;
const STATE_BUF = 64 * 1024, EV_BUF = 256 * 1024, KILL_BUF = 4 * 1024 * 1024;
const sendState = (ws, msg) => { if (ws.readyState === 1 && ws.bufferedAmount < STATE_BUF) ws.send(msg); };
const BATCH_T = new Set(['fx', 'arrow', 'arrowEnd', 'hit']);
let evq = [], evTimer = null;
function flushEv() {
  evTimer = null; if (!evq.length) return;
  const q0 = evq, m = JSON.stringify(q0.length === 1 ? q0[0] : { t: 'ev', l: q0 }); evq = [];
  const fz = pbFogZones(), now = Date.now();
  for (const p of players.values()) {
    if (!(p.ws && p.ws.readyState === 1 && (p.user || p.guest))) continue;
    const bz = fz.length ? pbBlind(p, now, fz) : null;
    if (p.ws.bufferedAmount > EV_BUF) { if (p.ws.bufferedAmount > KILL_BUF) { try { p.ws.terminate(); } catch (e) {} } continue; }
    if (bz && bz.length) { const l = q0.filter(e => pbEvVisible(e, bz)); if (l.length) p.ws.send(JSON.stringify(l.length === 1 ? l[0] : { t: 'ev', l })); }
    else p.ws.send(m);
  }
}
const broadcast = o => {
  outN++;
  if (curSk && (o.t === 'fx' || o.t === 'arrow')) { o.sp = curSk.p; o.sq = curSk.q; }
  if (curTint && (o.t === 'fx' || o.t === 'arrow') && !o.tint) o.tint = curTint;
  if (BATCH_T.has(o.t)) { evq.push(o); if (!evTimer) evTimer = setImmediate(flushEv); return; }
  const m = JSON.stringify(o); for (const p of players.values()) if (p.ws && p.ws.readyState === 1 && p.ws.bufferedAmount < EV_BUF * 2) p.ws.send(m);
};

const CHAT_TTL = 10 * 60 * 1000;
let ROUND_MS = 4 * 60 * 1000;
const chatLog = [];
let phase = 'lobby', roundStart = 0, deathCounter = 0;

const joinedList = () => [...players.values()].filter(p => p.joined);
// ---- team mode ----
let gameMode = 'ffa', bossId = 0;
const BOSS_CAP = { dmg: 2, spd: 1.5 };
const TEAM_NAME = { 1: 'Red', 2: 'Blue' };
const tmOf = t => t ? (t.unit ? ((players.get(t.owner) || {}).team || 0) : (t.team || 0)) : 0;
const sameTeam = (a, b) => gameMode !== 'ffa' && !!tmOf(a) && tmOf(a) === tmOf(b);
function pushMap() {
  for (const p of players.values()) { const c = clampArena({ x: p.x, y: p.y }); p.x = c.x; p.y = c.y; p.hist = []; }
  broadcast({ t: 'map', id: mapId, scale: mapScale, arena: { CX, CY, RX, RY } });
}
const saveMapCfg = () => db.set('mapcfg', JSON.stringify({ id: mapId, scale: mapScale, rt: ROUND_MS })).catch(e => console.error('mapcfg save failed:', e.message));
function setMap(id) { mapId = id; ({ CX, CY, RX, RY } = ARENAS[id]); applyDims(); pushMap(); saveMapCfg(); }
function setScale(sc) {
  const r = sc / mapScale; mapScale = sc; applyDims();
  ARENA_BASE.forEach((a, i) => { for (const k in a) ARENAS[i][k] = a[k] * sc; });
  ({ CX, CY, RX, RY } = ARENAS[mapId]);
  for (const p of players.values()) { p.x *= r; p.y *= r; if (p.lx !== undefined) { p.lx *= r; p.ly *= r; } }
  pushMap(); saveMapCfg();
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
    joinedList().forEach(p => p.ready = !!p.ai);
    broadcast({ t: 'countdown', ms: 0 });
    return sysChat('Round cancelled: not enough players.');
  }
  let bossMult = 0;
  if (gameMode === 'boss') {
    const boss = parts.find(q => q.id === bossId);
    if (!boss) {
      phase = 'lobby';
      joinedList().forEach(p => p.ready = !!p.ai);
      broadcast({ t: 'countdown', ms: 0 });
      return sysChat('Round cancelled: no Boss designated.');
    }
    parts.forEach(q => q.team = q === boss ? 1 : 2); bossMult = (parts.length - 1) / 2;
  }
  if (gameMode === 'team') {
    const cnt = { 1: 0, 2: 0 };
    parts.forEach(p => { if (p.team) cnt[p.team]++; });
    parts.filter(p => !p.team).sort(() => Math.random() - 0.5).forEach(p => { p.team = cnt[1] <= cnt[2] ? 1 : 2; cnt[p.team]++; });
    if (!cnt[1] || !cnt[2]) {
      phase = 'lobby';
      joinedList().forEach(p => p.ready = !!p.ai);
      broadcast({ t: 'countdown', ms: 0 });
      return sysChat('Round cancelled: both teams need at least one player.');
    }
  }
  phase = 'round'; roundStart = Date.now(); arrows.clear(); bombs.clear(); units.clear(); soulOrbs.clear(); balls.length = 0; planets.length = 0; galaxies.length = 0; pbZones.length = 0; pbWalls.length = 0; pbTimers.length = 0;
  const order = parts.slice(); for (let i = order.length - 1; i > 0; i--) { const j = Math.floor(Math.random() * (i + 1)); [order[i], order[j]] = [order[j], order[i]]; }
  const rot = Math.random() * Math.PI * 2;
  order.forEach((p, i) => {
    let a = rot + i * 2 * Math.PI / order.length;
    if (gameMode !== 'ffa') { const side = order.filter(q => q.team === p.team); a = (p.team === 1 ? Math.PI : 0) + (side.indexOf(p) - (side.length - 1) / 2) * 0.45; }
    p.lx = p.x; p.ly = p.y;
    { const sp = ringPos(a, 0.92); p.x = sp.x; p.y = sp.y; }
    p.dx = p.dy = 0; p.role = 1; p.inRound = true; p.ready = false; p.deathOrder = 0; p.hist = [];
    resetCombat(p);
    if (bossMult && p.id === bossId) { p.pw = Math.min(bossMult, BOSS_CAP.dmg); p.bm = Math.min(bossMult, BOSS_CAP.spd); p.mh = p.hp = Math.round(p.mh * (parts.length - 1) * 2); }
  });
  joinedList().forEach(p => { if (!p.inRound) p.role = 2; });
  broadcast({ t: 'tp' });
  sysChat('⚔️ Round started with ' + parts.length + ' players!');
}
function checkRoundEnd() {
  if (phase !== 'round') return;
  const alive = [...players.values()].filter(p => p.role === 1 && !p.skel);
  if (gameMode !== 'ffa') {
    if (new Set(alive.map(p => p.team)).size > 1) return;
    let team = alive[0] && alive[0].team;
    if (!team) { const last = [...players.values()].filter(p => p.inRound).sort((a, b) => b.deathOrder - a.deathOrder)[0]; team = last && last.team; }
    return endRound(null, null, team);
  }
  if (alive.length > 1) return;
  let winner = alive[0];
  if (!winner) winner = [...players.values()].filter(p => p.inRound).sort((a, b) => b.deathOrder - a.deathOrder)[0];
  endRound(winner);
}
function endRound(winner, tied, teamWin, draw) {
  const tw = teamWin ? [...players.values()].filter(p => p.inRound && p.team === teamWin && (p.user || p.guest) && !p.obs) : [];
  const gw = !tied && winner && (winner.user || winner.guest) && !winner.obs && winner.inRound ? winner : null;
  phase = 'lobby'; arrows.clear(); bombs.clear(); units.clear(); soulOrbs.clear(); balls.length = 0;
  for (const q of [...players.values()]) if (q.skel) { players.delete(q.id); broadcast({ t: 'leave', id: q.id }); }
  for (const p of players.values()) {
    if (p.inRound) { p.x = p.lx; p.y = p.ly; }
    p.role = 0; p.inRound = false; p.ready = !!p.ai; p.dx = p.dy = 0; p.hist = [];
    resetCombat(p);
    if (p.ai && p.aiRand) { p.cls = randClass(p.cls); resetCombat(p); }
  }
  broadcast({ t: 'tp' });
  if (draw) { sysChat('⏱ Time is up! Draw.'); broadcast({ t: 'winner', name: 'Draw', draw: 1 }); }
  else if (teamWin) { const bm = gameMode === 'boss'; sysChat('🏆 ' + (bm ? (teamWin === 1 ? 'The Boss wins!' : 'The Players win!') : TEAM_NAME[teamWin] + ' Team wins!')); broadcast({ t: 'winner', name: bm ? (teamWin === 1 ? '보스' : '플레이어 팀') : TEAM_NAME[teamWin] + ' Team' }); tw.forEach(q => awardGold(q, WIN_GOLD)); }
  else if (tied && tied.length) { const names = tied.join(', '); sysChat('⏱ Time is up! 2nd place: ' + names); broadcast({ t: 'winner', name: names, second: true }); }
  else if (winner) { sysChat('🏆 1st place: ' + winner.name); broadcast({ t: 'winner', name: winner.name }); }
  else sysChat('Round ended with no winner.');
  if (gw) awardGold(gw, WIN_GOLD);
  if (!draw) { const ws = new Set(tw); if (gw) ws.add(gw); ws.forEach(addWin); if (ws.size) sendWinsAll(); }
}
// ---- wins ----
let winsData = {}, winTop = [], winSave = Promise.resolve();
function calcWinTop() { winTop = Object.values(winsData).filter(e => e.w > 0).sort((a, b) => b.w - a.w || String(a.n).localeCompare(String(b.n))).slice(0, 10).map(e => ({ n: e.n, w: e.w })); }
function sendWins(p) {
  if (!p.ws) return;
  const mine = p.user && winsData[p.user] ? winsData[p.user] : null;
  send(p.ws, { t: 'wins', top: winTop, my: mine ? mine.w : 0, mi: mine ? winTop.findIndex(e => e.n === mine.n && e.w === mine.w) : -1 });
}
function sendWinsAll() { for (const p of players.values()) if (p.ws && p.joined) sendWins(p); }
function addWin(p) {
  if (!p.user || p.obs) return;
  const e = winsData[p.user] || (winsData[p.user] = { n: p.name, w: 0 });
  e.w++; e.n = p.name;
  calcWinTop();
  const json = JSON.stringify(e);
  winSave = winSave.then(() => db.set('winu:' + p.user, json)).catch(err => console.error('wins save failed:', err.message));
}
// ---- gold ----
const WIN_GOLD = 5, KILL_GOLD = 5;
async function awardGold(p, n) {
  if (p.guest) { p.gold = (p.gold || 0) + n; send(p.ws, { t: 'gold', g: p.gold, d: n }); return; }
  try {
    p.gold = (p.gold || 0) + n; send(p.ws, { t: 'gold', g: p.gold, d: n });
    const v = Number(await db.incrby('gold:' + p.user, n));
    if (Number.isFinite(v) && p.user) { p.gold = v; send(p.ws, { t: 'gold', g: v }); }
  } catch (e) { console.error('gold award failed:', e.message); }
}

// ---- shop / skins ----
const SKINS = { LightKnight: { cls: 'Knight', name: '라이트 나이트 스킨', price: 200 }, LightArcher: { cls: 'Archer', name: '라이트 아처 스킨', price: 200 }, ChessTower: { cls: 'Tower', name: '체스 타워 스킨', price: 150 } };
const SKIN_ORDER = Object.keys(SKINS);
let shopPrices = {};
const priceOf = id => Number.isInteger(shopPrices[id]) ? shopPrices[id] : SKINS[id].price;
const shopList = () => SKIN_ORDER.map(id => ({ id, cls: SKINS[id].cls, name: SKINS[id].name, price: priceOf(id) }));
const skinOf = p => { const id = p.eqs && p.eqs[p.cls]; return id && SKINS[id] && SKINS[id].cls === p.cls && p.skins && p.skins.includes(id) ? id : 0; };
const sendSinfo = p => send(p.ws, { t: 'sinfo', own: p.skins || [], eqs: p.eqs || {} });
const sendShop = ws => send(ws, { t: 'shop', items: shopList() });
async function loadSkins(id) {
  try {
    const raw = await db.get('skins:' + id); let own = raw ? JSON.parse(raw) : [];
    if (!Array.isArray(own)) own = [];
    own = own.filter(s => SKINS[s]);
    const e = await db.get('eqskin:' + id); let eqs = e ? JSON.parse(e) : {};
    if (!eqs || typeof eqs !== 'object' || Array.isArray(eqs)) eqs = {};
    for (const c of Object.keys(eqs)) if (!SKINS[eqs[c]] || SKINS[eqs[c]].cls !== c || !own.includes(eqs[c])) delete eqs[c];
    return { own, eqs, err: false };
  } catch (e) { console.error('skins load failed:', e.message); return { own: [], eqs: {}, err: true }; }
}
async function equipSkin(p, id) {
  const now = Date.now();
  if ((!p.user && !p.guest) || p.obs || p.skinsErr || now - (p.lastSkEq || 0) < 300) return sendSinfo(p);
  if (typeof id !== 'string' || !SKINS[id] || !p.skins.includes(id)) return sendSinfo(p);
  p.lastSkEq = now;
  const c = SKINS[id].cls;
  if (p.eqs[c] === id) delete p.eqs[c]; else p.eqs[c] = id;
  if (!p.guest) await db.set('eqskin:' + p.user, JSON.stringify(p.eqs));
  sendSinfo(p);
}
async function buySkin(p, id, expect) {
  const reply = (ok, msg) => send(p.ws, { t: 'buy', ok, msg, id });
  if ((!p.user && !p.guest) || p.obs) return;
  if (p.buying) return reply(0, '처리 중입니다. 잠시만 기다려 주세요.');
  if (typeof id !== 'string' || !SKINS[id]) return reply(0, '존재하지 않는 상품입니다.');
  if (p.skinsErr) return reply(0, '일시적인 오류입니다. 다시 로그인해 주세요.');
  if (p.skins.includes(id)) return reply(0, '이미 보유한 스킨입니다.');
  const price = priceOf(id);
  if (expect !== price) { sendShop(p.ws); return reply(0, '가격이 변경되었습니다. 다시 확인해 주세요.'); }
  p.buying = true; let charged = false;
  if (p.guest) {
    if ((p.gold || 0) < price) { p.buying = false; return reply(0, '골드가 부족합니다.'); }
    p.gold -= price; p.skins = p.skins.concat(id); p.buying = false;
    send(p.ws, { t: 'gold', g: p.gold }); sendSinfo(p);
    return reply(1, SKINS[id].name + ' 구매 완료!');
  }
  try {
    const v = Number(await db.incrby('gold:' + p.user, -price));
    if (!Number.isFinite(v)) throw new Error('bad balance');
    if (v < 0) {
      const back = Number(await db.incrby('gold:' + p.user, price));
      if (Number.isFinite(back)) { p.gold = back; send(p.ws, { t: 'gold', g: back }); }
      return reply(0, '골드가 부족합니다.');
    }
    charged = true;
    const own = p.skins.concat(id);
    await db.set('skins:' + p.user, JSON.stringify(own));
    p.skins = own; p.gold = v;
    send(p.ws, { t: 'gold', g: v }); sendSinfo(p);
    reply(1, SKINS[id].name + ' 구매 완료!');
  } catch (e) {
    console.error('buy failed:', e.message);
    if (charged) { try { const back = Number(await db.incrby('gold:' + p.user, price)); if (Number.isFinite(back)) { p.gold = back; send(p.ws, { t: 'gold', g: back }); } } catch (e2) { console.error('refund failed:', e2.message); } }
    reply(0, '구매 중 오류가 발생했습니다.');
  } finally { p.buying = false; }
}
function setShopPrice(p, m) {
  const id = String(m.id), n = Number(m.price), say = (ok, msg) => send(p.ws, { t: 'shopmsg', ok, msg });
  if (!SKINS[id] || !Number.isInteger(n) || n < 0 || n > 10000000) return say(0, '가격이 올바르지 않습니다. (0 ~ 10,000,000 정수)');
  shopPrices[id] = n;
  db.set('shopprice', JSON.stringify(shopPrices)).catch(e => console.error('shopprice save failed:', e.message));
  for (const q of players.values()) if (q.joined && !q.obs) sendShop(q.ws);
  say(1, SKINS[id].name + ' 가격을 ' + n.toLocaleString() + ' 골드로 변경했습니다.');
}
// ---- class unlock ----
const CLS_PRICE = { PlumBlossom: 100 };
const clsFree = p => p.user === ADMIN_ID || p.obs;
const clsOk = (p, c) => !CLS_PRICE[c] || clsFree(p) || (p.clsOwn || []).includes(c);
const sendCinfo = p => send(p.ws, { t: 'cinfo', own: p.clsOwn || [], price: CLS_PRICE, free: clsFree(p) ? 1 : 0 });
async function loadCls(id) {
  try {
    const raw = await db.get('cls:' + id); let own = raw ? JSON.parse(raw) : [];
    if (!Array.isArray(own)) own = [];
    return { own: own.filter(c => CLS_PRICE[c]), err: false };
  } catch (e) { console.error('cls load failed:', e.message); return { own: [], err: true }; }
}
async function buyClass(p, cls, expect) {
  const reply = (ok, msg) => send(p.ws, { t: 'cbuy', ok, msg, cls });
  if ((!p.user && !p.guest) || p.obs) return;
  if (p.buying) return reply(0, '처리 중입니다. 잠시만 기다려 주세요.');
  if (typeof cls !== 'string' || !CLS_PRICE[cls]) return reply(0, '존재하지 않는 상품입니다.');
  if (p.clsErr) return reply(0, '일시적인 오류입니다. 다시 로그인해 주세요.');
  if (clsOk(p, cls)) { sendCinfo(p); return reply(0, '이미 해금한 클래스입니다.'); }
  const price = CLS_PRICE[cls];
  if (expect !== price) { sendCinfo(p); return reply(0, '가격이 변경되었습니다. 다시 확인해 주세요.'); }
  const nm = (cls === 'PlumBlossom' ? '매화검' : cls);
  p.buying = true; let charged = false;
  if (p.guest) {
    if ((p.gold || 0) < price) { p.buying = false; return reply(0, '골드가 부족합니다.'); }
    p.gold -= price; p.clsOwn = (p.clsOwn || []).concat(cls); p.buying = false;
    send(p.ws, { t: 'gold', g: p.gold }); sendCinfo(p);
    return reply(1, nm + ' 클래스 해금 완료!');
  }
  try {
    const v = Number(await db.incrby('gold:' + p.user, -price));
    if (!Number.isFinite(v)) throw new Error('bad balance');
    if (v < 0) {
      const back = Number(await db.incrby('gold:' + p.user, price));
      if (Number.isFinite(back)) { p.gold = back; send(p.ws, { t: 'gold', g: back }); }
      return reply(0, '골드가 부족합니다.');
    }
    charged = true;
    const own = (p.clsOwn || []).concat(cls);
    await db.set('cls:' + p.user, JSON.stringify(own));
    p.clsOwn = own; p.gold = v;
    send(p.ws, { t: 'gold', g: v }); sendCinfo(p);
    reply(1, nm + ' 클래스 해금 완료!');
  } catch (e) {
    console.error('class buy failed:', e.message);
    if (charged) { try { const back = Number(await db.incrby('gold:' + p.user, price)); if (Number.isFinite(back)) { p.gold = back; send(p.ws, { t: 'gold', g: back }); } } catch (e2) { console.error('refund failed:', e2.message); } }
    reply(0, '구매 중 오류가 발생했습니다.');
  } finally { p.buying = false; }
}
// ---- combat ----
const RAD = Math.PI / 180;
const BASE = { hp: 1000, dmg: 150, reduce: 0, atkCd: 600 };
const CLASS_STATS = {
  Knight: { hp: 1200, dmg: 150, reduce: 0.2, atkCd: 700 },
  Archer: { hp: 1000, dmg: 180, reduce: 0, atkCd: 800 },
  Shielder: { hp: 1600, dmg: 80, reduce: 0, atkCd: 800 },
  Assassin: { hp: 1000, dmg: 135, reduce: 0, atkCd: 600 },
  Gumiho: { hp: 1100, dmg: 120, reduce: 0, atkCd: 700 },
  Gambler: { hp: 1000, dmg: 180, reduce: 0, atkCd: 600 },
  SwordMaster: { hp: 1200, dmg: 140, reduce: 0, atkCd: 400 },
  Tower: { hp: 2200, dmg: 100, reduce: 0, atkCd: 2000 },
  Gamer: { hp: 1000, dmg: 150, reduce: 0, atkCd: 700 },
  Celestial: { hp: 1500, dmg: 100, reduce: 0, atkCd: 800 },
  Reaper: { hp: 1200, dmg: 50, reduce: 0, atkCd: 700 },
  Berserker: { hp: 1200, dmg: 170, reduce: 0, atkCd: 900 },
  PlumBlossom: { hp: 1000, dmg: 90, reduce: 0, atkCd: 800 }
};
const statsBase = p => p.cls === 'PlumBlossom' ? { hp: Math.round(1000 * pbMul(p)), dmg: 90 * pbMul(p), reduce: 0, atkCd: 800 } : p.cls === 'Financier' ? { hp: 1000, dmg: p.fDmg || 90, reduce: 0, atkCd: 900 } : p.cls === 'Lucifer' ? { hp: lForm(p).hp, dmg: lForm(p).dmg, reduce: 0, atkCd: p.lf === 'd' && Date.now() < p.libUntil ? LUC.lib.atkCd : lForm(p).atkCd } : p.cls === 'Berserker' && !axeHeld(p) ? Object.assign({}, CLASS_STATS.Berserker, { dmg: 50 }) : CLASS_STATS[p.cls] || BASE;
const statsOf = p => { const s = statsBase(p); return p.pw && p.pw !== 1 ? Object.assign({}, s, { atkCd: s.atkCd / p.pw }) : s; };
const RADPX = 112.5;
let MAP = 1254, MAPH = 1254;
const ARROW = { speed: 800, range: 5 * RADPX, radius: 28 };
const ATKR = 0.5 * RADPX;
const ARCHER = {
  charge: { maxMs: 2000, min: 0.5, max: 1.5 },
  Q: { cd: 11000, arrows: 7, step: 10 * RAD, dmg: 115, invis: 1500 },
  E: { cd: 15000, dur: 4000, chargeMul: 0 },
  R: { cd: 25000, dmg: 380, stun: 1000, scale: 8, radius: 90 }
};
const ATK = { range: 1 * RADPX, span: 100 * RAD };
const SM = {
  atk: { need: 4, needAwk: 2, auraDmg: 180, kb: 1 * RADPX, kbMs: 250 },
  Q: { cd: 12000, dmg: 100, pct: 0.15, spd: 1500, range: 6 * RADPX, radius: 1.5 * RADPX },
  E: { cd: 0, cdAwk: 0, mult: 0.7, multAwk: 1.0, dash: 2 * RADPX, dashMs: 200, dashDir: 1 },
  R: { cd: 25000, dur: 10000 }
};
const KNIGHT = {
  Q: { cd: 8000, range: 2 * RADPX, span: 120 * RAD, dmg: 250, stun: 1000 },
  E: { cd: 12000, dur: 3000, reduce: 0.4, speed: 1.15 },
  R: { cd: 25000, swords: 8, ring: 195, radius: 1 * RADPX, cRadius: 2.5 * RADPX, dmg: 120, cdmg: 220, slow: 0.7, slowMs: 2000 }
};

const SHIELDER = {
  span: 90 * RAD, block: 0.9,
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
  fire: { chance: 1.0, max: 5, pick: 55, lift: 25 },
  eff: { dmg: 120, ms: 2000, radius: 2 * RADPX },
  Q: { cd: 10000 },
  E: { cd: 12000, pullMs: 500, dmg: 55, rad: 0.6 * RADPX },
  R: { cd: 25000, radius: 2.5 * RADPX, ms: 2500, speed: 0.7, stop: 45 }
};
const BURN = { tick: 35, tickMs: 1000 };
const LUC = {
  base: { hp: 1300, dmg: 150, atkCd: 900, range: 4 * RADPX, spd: 900, radius: ATKR },
  angel: { hp: 1300, dmg: 130, atkCd: 800, range: 4 * RADPX, spd: 900, radius: ATKR },
  devil: { hp: 1300, dmg: 180, atkCd: 1000, range: 4 * RADPX, spd: 900, radius: ATKR },
  G: { cd: 30000, atkCut: 1000, skillCut: 1500, afterCd: 5000, shotMul: 0.5 },
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
  range: 4 * RADPX, spd: 1100, radius: 24, chambers: 6, reloadMs: 3000,
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

const HIST_MS = 700, TOL = 90, MAX_LAG = 300, VIEW_DELAY = 50;
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
  for (let d = 0; d < MAP * 2; d += 12) {
    const tx = x + Math.cos(a) * (d + 28), ty = y + Math.sin(a) * (d + 28) * 0.8 - 30;
    const cs = [[0, 1], [L, 1], [0, -1], [L, -1]].map(([l, sd]) => [tx - ux * l + nx * sd * half, ty - uy * l + ny * sd * half]);
    if (cs.every(c => c[0] < 0) || cs.every(c => c[0] > MAP) || cs.every(c => c[1] < 0) || cs.every(c => c[1] > MAPH)) return d;
  }
  return MAP * 2;
}
function endArrow(ar, t) { arrows.delete(ar.id); broadcast(t && ar.kd === 'smq' ? { t: 'arrowEnd', id: ar.id, ex: t.x, ey: t.y } : { t: 'arrowEnd', id: ar.id }); }
function moveArrow(ar, step, time) {
  const nx = ar.x + Math.cos(ar.a) * step, ngy = ar.gy + Math.sin(ar.a) * step;
  const found = [];
  if (ar.fake) { ar.x = nx; ar.gy = ngy; ar.left -= step; return []; }
  const arOw = players.get(ar.owner), arRoot = arOw ? rootOf(arOw) : ar.owner;
  const chk = t => {
    if (t.id === ar.owner || t.owner === ar.owner || !(t.unit || t.joined) || t.role !== 1 || ar.hitIds.has(t.id) || sameTeam(arOw, t) || rootOf(t) === arRoot) return;
    const tp = posAt(t, time);
    if (segDist(tp.x, tp.y / 0.8, ar.x, ar.gy, nx, ngy) > ar.radius + (t.hr || 0)) return;
    found.push({ t, d: Math.hypot(tp.x - ar.x, tp.y / 0.8 - ar.gy) });
  };
  if (phase === 'round') { for (const t of players.values()) chk(t); for (const t of units.values()) chk(t); }
  else if (arOw && arOw.joined) for (const t of dummies) chk(t);
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
  const arO = players.get(ar.owner);
  const type = arO && arO.cls === 'PlumBlossom' && arO.pbStage >= 5 ? 'magic' : ar.type || (ar.orb ? 'magic' : 'phys');
  if (type === 'phys' && t.cls === 'Shielder' && now < t.hornUntil && shieldBlocks(t, { dir: inDir })) { deflectArrow(ar, t); return true; }
  if (t.cls === 'PlumBlossom' && now < (t.pbBlockUntil || 0) && pbTryBlock(t, { dir: inDir }, now)) { ar.left = 0; return false; }
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
    orb: !!spec.orb, eff: !!spec.eff, boom: spec.boom || 0, pierce: !!spec.pierce, noArena: !!spec.noArena, sc: spec.sc || 1, stun: spec.stun || 0, hpPct: spec.hpPct || 0, fake: !!spec.fake, hitIds: new Set(), left: spec.range || ARROW.range };
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
  if (ended && !deflected) { broadcast(spec.kind === 'smq' && pending[0] ? { t: 'arrowEnd', id, ex: pending[0].x, ey: pending[0].y } : { t: 'arrowEnd', id }); orbLand(ar, pending[0], now); } else arrows.set(id, ar);
  if (pending.length) checkRoundEnd();
  return id;
}
function stepArrows(dt, now) {
  let any = false;
  for (const ar of arrows.values()) {
    const stp = Math.min(ar.spd * dt, ar.left);
    if (pbWalls.length && !ar.fake && pbArrowWall(ar, ar.x + Math.cos(ar.a) * stp, ar.gy + Math.sin(ar.a) * stp, now)) { endArrow(ar); continue; }
    if (sanctBlocked(ar.owner, ar.x, ar.gy, ar.x + Math.cos(ar.a) * stp, ar.gy + Math.sin(ar.a) * stp, now)) { endArrow(ar); continue; }
    const hits = moveArrow(ar, stp, now);
    let deflected = false;
    for (const t of hits) { any = true; if (arrowHit(ar, t, now)) { deflected = true; break; } }
    if (deflected) continue;
    if (!ar.pierce && hits.length) { endArrow(ar, hits[0]); orbLand(ar, hits[0], now); continue; }
    const ex = (ar.x - CX) / RX, ey = (ar.gy * 0.8 - CY) / RY;
    if (ar.left <= 0 || (!ar.noArena && ndist(ex, ey) > (mapId === 2 ? 1 : 1.0724))) { endArrow(ar); orbLand(ar, null, now); }
  }
  if (any) checkRoundEnd();
}

function resetCombat(p) {
  p.axes = p.cls === 'Berserker' ? [{ s: 0, x: 0, y: 0, a: 0, d: 0 }] : []; p.bRUntil = 0;
  p.pw = 1; p.bm = 0;
  p.pbD = p.pbA = p.pbStage = 0; p.pbCd = {}; p.pbCmd = null; p.pbCh = null; p.pbResume = null; p.pbBonus = false; p.pbBn = 0; p.pbRe = {}; p.pbFly = null; p.pbBlockUntil = p.pbSlowUntil = 0; p.pbSlowMul = 1; p.pbKey = ''; p.pbSw = null; pbClean(p.id);
  p.lf = ''; p.lPend = p.lUsed = false; p.beam = p.pure = p.sanct = null; p.libUntil = p.dmUntil = 0; p.dmList = [];
  p.mh = p.hp = statsOf(p).hp;
  p.atkReady = p.cdQ = p.cdE = p.cdR = 0;
  p.stunUntil = p.guardUntil = p.slowUntil = 0;
  p.chargeStart = p.hasteUntil = p.invisUntil = 0;
  p.tauntUntil = p.tauntBy = p.kbUntil = p.hornUntil = 0; p.dash = null;
  p.markUntil = p.asUntil = p.asBonus = 0;
  p.fires = []; p.qNext = false; p.eNext = 0; p.lastBy = 0; p.charmUntil = p.charmBy = p.burnUntil = p.burnNext = 0;
  p.fDmg = 90; p.fMul = 1; p.finNext = Date.now() + 5000; p.insUntil = p.depUntil = 0; p.insAcc = 0; p.stkNext = 0; p.buyDealt = 0; p.buyHp0 = 0;
  if (p.buy) send(p.ws, { t: 'stk', id: 0 }); p.buy = 0;
  p.hr = p.cls === 'Tower' ? TOWER.hr : 0; p.towerRUntil = 0; p.mercNext = Date.now() + TOWER.merc.ms;
  for (const u of units.values()) if (u.owner === p.id) units.delete(u.id);
  p.smN = 0; p.smAura = false; p.smAwkUntil = 0; p.smLast = null; p.smSaved = false; p.bleedUntil = 0; p.bleedNext = 0; p.bleedBy = 0;
  p.ch = null; p.chi = 0; p.reloadUntil = 0; p.myTurn = false; p.gbUntil = p.gbPlusUntil = p.fastUntil = 0;
  p.dim = p.nextBonus = 0; p.celKey = ''; for (const arr of [planets, galaxies]) for (let i = arr.length - 1; i >= 0; i--) if (arr[i].owner === p.id) arr.splice(i, 1);
  p.gCopy = []; p.gSlots = 1; p.gBig = false; p.gLast = null; p.gNext = 0; p.gCheatUntil = p.gtUntil = 0; p.gCdPend = 0; p.gtint = ''; p.gInvis = p.gPierce = false; send(p.ws, { t: 'gc', l: [], s: 1, ch: 0 });
  p.souls = []; send(p.ws, { t: 'reap', s: [] });
  for (const k of ['Q', 'E', 'R']) send(p.ws, { t: 'cd', k, ms: 0 });
  if (p.cls === 'Gambler') loadRevolver(p); else send(p.ws, { t: 'rv', n: 0 });
  if (p.cls === 'Lucifer' && phase === 'round') { p.cdR = Date.now() + LUC.G.cd; send(p.ws, { t: 'cd', k: 'R', ms: LUC.G.cd }); }
}
function killPlayer(p) {
  if (p.skel) { players.delete(p.id); broadcast({ t: 'leave', id: p.id }); return; }
  const was = p.role === 1, k = was && p.lastBy && Date.now() - p.lastByT < 10000 ? players.get(p.lastBy) : null;
  if (was && phase === 'round' && p.cls) dropSoul(p.x, p.y, p.cls, 0, 1);
  p.hp = 0; p.role = 2; p.dx = p.dy = 0; p.moving = false; p.deathOrder = ++deathCounter;
  if (was) broadcast({ t: 'kill', k: k ? k.id : 0, kn: k ? k.name : '', kc: k ? k.cls : '', v: p.id, vn: p.name, vc: p.cls });
  if (was && k && phase === 'round') { const kr = players.get(rootOf(k)); if (kr && kr !== p && !p.ai && !kr.ai && !kr.skel && !kr.obs && (kr.user || kr.guest) && !sameTeam(kr, p)) awardGold(kr, KILL_GOLD); }
}
const bRage = p => p.cls === 'Berserker' && p.role === 1 && p.hp > 0 && p.hp <= p.mh * 0.5;
const berserkInc = (a, src, now) => a.cls !== 'Berserker' ? 0 : (bRage(a) ? 0.85 : 0) + (now < (a.bRUntil || 0) ? 0.3 : 0);
const axeHeld = p => !p.axes || !p.axes.length || p.axes.some(a => a.s === 0);
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
  if (pbWalls.length && src && src.x !== undefined && pbMeleeWall(t, amount, src, now)) return;
  if (t.cls === 'PlumBlossom' && now < (t.pbBlockUntil || 0) && pbTryBlock(t, src, now)) return;
  const atk0 = src && (src.by || src.kill);
  let incA = 0;
  if (atk0 && !(src && src.fixed)) { if (atk0.pw && atk0.pw !== 1) incA += atk0.pw - 1; incA += berserkInc(atk0, src, now); }
  const amount0 = amount; amount = amount0 * (1 + incA);
  let type = (src && src.type) || (src && src.by && (src.by.cls === 'Assassin' || src.by.gPierce) ? 'pierce' : 'phys');
  if (atk0 && atk0.cls === 'PlumBlossom' && atk0.pbStage >= 5 && !(src && src.fixed)) type = 'magic';
  const pierce = type === 'pierce', magic = type === 'magic';
  if (!pierce && now < (t.invulnUntil || 0)) return;
  let cut = 0, blocked = false;
  if (!pierce && !magic) {
    cut = statsOf(t).reduce;
    if (now < t.guardUntil) cut += KNIGHT.E.reduce;
    blocked = shieldBlocks(t, src);
    if (blocked) cut += SHIELDER.block;
    else if (t.cls === 'Shielder' && now < t.hornUntil) cut += SHIELDER.R.reduce;
    if (now < t.dmUntil) cut = Math.max(0, cut - LUC.mark.defCut);
  }
  let incT = 0;
  if (now < t.markUntil) incT += ASSASSIN.Q.mark;
  if (now < t.dmUntil) { const mo = players.get(t.dmBy); incT += mo && now < mo.libUntil ? LUC.mark.ampLib : LUC.mark.amp; }
  let d = (src && src.fixed) ? Math.round(amount0) : (blocked && now < t.hornUntil) ? 0 : Math.max(1, Math.round(amount0 * (1 + incA + incT) * (1 - Math.min(cut, 0.95))));
  if (t.dummy) { dummyHit(t, d, now); broadcast({ t: 'hit', id: t.id, dmg: d, bl: blocked ? 1 : 0 }); return; }
  t.hp -= d;
  if (t.cls === 'PlumBlossom' && t.pbCh && d > 0 && t.pbCh.t !== 7) pbStop(t, now, false);
  if (t.cls === 'Celestial' && t.role === 1 && d > 0) { t.dim = Math.min(CEL.cap, (t.dim || 0) + d * CEL.store); if (t.hp > 0) t.hp = Math.min(t.mh, t.hp + d * CEL.heal); }
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
const soulOrbs = new Map(); let soulSeq = 0;
function dropSoul(x, y, cls, owner, pw) {
  if (phase !== 'round' || !cls) return;
  if (soulOrbs.size >= 40) soulOrbs.delete(soulOrbs.keys().next().value);
  const c = clampArena({ x, y });
  soulOrbs.set(++soulSeq, { id: soulSeq, x: c.x, y: c.y, cls, o: owner, pw });
}
const units = new Map(); let unitSeq = 0; const balls = [], planets = [], galaxies = [];
const rootOf = t => { const o = t.unit ? players.get(t.owner) : t; return o ? (o.skel || o.id) : t.owner; };
const targetsOf = p => {
  const r = [];
  if (phase !== 'round') { if (p.joined && !p.obs) for (const d of dummies) r.push(d); return r; }
  const rp = rootOf(p);
  for (const t of players.values()) if (t !== p && t.joined && t.role === 1 && !sameTeam(p, t) && rootOf(t) !== rp) r.push(t);
  for (const t of units.values()) if (t.owner !== p.id && !sameTeam(p, t) && rootOf(t) !== rp) r.push(t);
  return r;
};
function inConeAt(ox, oy, aim, tx, ty, range, span, ext = 0) {
  const dx = tx - ox, dy = (ty - oy) / 0.8, d = Math.hypot(dx, dy);
  if (d > range + 10 + ext) return false;
  if (d < 10) return true;
  let diff = Math.abs(Math.atan2(dy, dx) - aim);
  if (diff > Math.PI) diff = 2 * Math.PI - diff;
  return diff <= span / 2;
}
const canAct = (p, now) => p.joined && p.role !== 2 && now >= p.stunUntil && now >= p.charmUntil && now >= (p.reloadUntil || 0);

const chargeMax = (p, now) => p.cls === 'Reaper' ? REAPER.chargeMs : Math.max(1, ARCHER.charge.maxMs * (now < p.hasteUntil ? ARCHER.E.chargeMul : 1));
function archerAttack(p, m, now) {
  const st = statsOf(p), o = originOf(p, m), lag = lagOf(m), C = ARCHER.charge;
  let f = 1;
  if (!p.chargeStart) return;
  const em = chargeMax(p, now), ch = Math.min(Math.max(now - p.chargeStart, 1), em);
  f = C.min + (C.max - C.min) * ch / em;
  p.chargeStart = 0;
  if (now < p.atkReady - 60) return;
  p.atkReady = now + st.atkCd;
  spawnArrow(p, o, lag, now, { a: p.aim, dmg: Math.round(st.dmg * f), spd: ARROW.speed * f, radius: ATKR, kind: 'atk' });
}
function doAttack(p, m) {
  const now = Date.now();
  if (!canAct(p, now)) return;
  if (p.cls === 'Archer') return archerAttack(p, m, now);
  if (p.cls === 'Reaper') return reaperAttack(p, m, now);
  if (p.cls === 'PlumBlossom') return plumAttack(p, m, now);
  if (p.cls === 'Gumiho') return gumihoAttack(p, m, now);
  if (p.cls === 'Lucifer') return luciferAttack(p, m, now);
  if (p.cls === 'Gambler') return gamblerAttack(p, m, now);
  if (p.cls === 'SwordMaster') return swordmasterAttack(p, m, now);
  if (p.cls === 'Gamer') return gamerAttack(p, m, now);
  if (p.cls === 'Celestial') return celestialAttack(p, m, now);
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
    spawnArrow(p, { x: o.x - Math.sin(p.aim) * off, y: o.y + Math.cos(p.aim) * off * 0.8 }, lag, now, { a: p.aim, dmg: TOWER.R.dmg, spd: ARROW.speed, range: TOWER.R.range, radius: ATKR, kind: 'tarr' });
  }
  checkRoundEnd();
}
const predCfg = () => ({
  Celestial: { Q: { cd: CEL.Q.cd, r: CEL.Q.r, fall: CEL.Q.delay }, E: { cd: CEL.E.cd, r: 1.1 * RADPX }, R: { cd: CEL.R.cd, r: CEL.R.r, fall: CEL.R.delay, ms: CEL.R.ms } },
  Knight: { Q: { cd: KNIGHT.Q.cd, span: KNIGHT.Q.span, r: KNIGHT.Q.range } },
  Shielder: { Q: { cd: SHIELDER.Q.cd, r: SHIELDER.Q.radius } },
  Archer: { Q: { cd: ARCHER.Q.cd, n: ARCHER.Q.arrows, step: ARCHER.Q.step, spd: ARROW.speed, range: ARROW.range } }
});
function doSkill(p, k, m) {
  const q = m && Number.isInteger(m.q) && m.q > 0 && m.q < 1e9 ? m.q : 0, n0 = outN, prev = curSk;
  curSk = q ? { p: p.id, q } : null;
  try { runSkill(p, k, m); } finally { curSk = prev; }
  if (q) send(p.ws, { t: 'ack', q, ok: outN !== n0 ? 1 : 0 });
}
function runSkill(p, k, m) {
  const now = Date.now();
  if (!['Q', 'E', 'R'].includes(k) || !canAct(p, now)) return;
  if (now < p['cd' + k]) return;
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
  else if (p.cls === 'Celestial') celestialSkill(p, k, m, now);
  else if (p.cls === 'Reaper') reaperSkill(p, k, m, now);
  else if (p.cls === 'Berserker') berserkerSkill(p, k, m, now);
  else if (p.cls === 'PlumBlossom') plumSkill(p, k, m, now);
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
const clampArena = (pt, from, air) => {
  const nx = (pt.x - CX) / RX, ny = (pt.y - CY) / RY, d = ndist(nx, ny);
  let r = d > 0.97 ? { x: CX + nx / d * 0.97 * RX, y: CY + ny / d * 0.97 * RY } : { x: pt.x, y: pt.y };
  if (!air && solidMap()) r = from ? slideTo(from.x, from.y, r.x, r.y) : snapWalk(r.x, r.y);
  return r;
};
let fireSeq = 0;
function spawnFoxfire(g, pos) {
  const c = clampArena(pos);
  g.fires.push({ id: ++fireSeq, x: c.x, y: c.y });
  while (g.fires.length > GUMIHO.fire.max) g.fires.shift();
}
function orbLand(ar, hitT, now) {
  if (!ar.orb || !PRACT()) return;
  const g = players.get(ar.owner);
  if (!g || g.cls !== 'Gumiho' || !inPlay(g)) return;
  if (ar.boom) {
    const at = hitT ? { x: hitT.x, y: hitT.y } : { x: ar.x, y: ar.gy * 0.8 }, rad = ar.boom * GUMIHO.E.rad;
    broadcast({ t: 'fx', type: 'ring', x: at.x, y: at.y, r: rad, c: '#7fe9ff', dur: 700 });
    for (const t of targetsOf(g)) if (t !== hitT && Math.hypot(t.x - at.x, (t.y - at.y) / 0.8) <= rad) dmgTo(t, ar.dmg, now, { x: at.x, y: at.y, kill: g, type: 'magic' });
    checkRoundEnd();
    if (!PRACT()) return;
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
  spawnArrow(p, o, lag, now, { a: p.aim, dmg: st.dmg + n * GUMIHO.E.dmg, boom: n, spd: GUMIHO.atk.speed, range: GUMIHO.atk.range, radius: ATKR, kind: 'orb', orb: true, eff });
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
    const nx = (tx - CX) / RX, ny = (ty - CY) / RY, d = ndist(nx, ny);
    if (d > 1) { tx = CX + nx / d * RX; ty = CY + ny / d * RY; }
    if (solidMap()) { const q = slideTo(o.x, o.y, tx, ty); tx = q.x; ty = q.y; }
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
    const inside = d => { const px = gx + Math.cos(a) * d, py = (gy + Math.sin(a) * d) * 0.8; return ndist((px - CX) / RX, (py - CY) / RY) <= 1 && walkAt(px, py); };
    let len = S.dist;
    if (solidMap()) { let l = 0; while (l + 4 <= S.dist && inside(l + 4)) l += 4; len = l; } else while (len > 0 && !inside(len)) len -= 5;
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
    broadcast({ t: 'fx', type: 'swords', by: p.id, x: o.x, y: o.y, r: S.ring, ar: S.radius, cr: S.cRadius, n: S.swords, dur: 900 });
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
  if (mapId === 2) {
    const px = x - CX, py = gy * 0.8 - CY, ax = Math.cos(a), ay = Math.sin(a) * 0.8; let t = Infinity;
    if (ax > 1e-9) t = Math.min(t, (RX - px) / ax); else if (ax < -1e-9) t = Math.min(t, (-RX - px) / ax);
    if (ay > 1e-9) t = Math.min(t, (RY - py) / ay); else if (ay < -1e-9) t = Math.min(t, (-RY - py) / ay);
    return Math.max(0, t);
  }
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
    spawnArrow(p, { x: p.x, y: p.y }, 0, now, { a, dmg: Math.round(S.dmg * LUC.G.shotMul), spd: S.spd, range: S.range, radius: S.radius, kind, type: 'magic', luc, sc: S.sc });
  }
}
function lucHit(ar, t, now) {
  const p = players.get(ar.owner);
  if (p && p.cls === 'Gamer' && inPlay(p)) { if (ar.luc === 'E') applyBurn(t, p, LUC.E.burnMs, now); return; }
  if (!p || p.cls !== 'Lucifer' || !inPlay(p)) return;
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
  spawnArrow(p, o, lag, now, { a: p.aim, dmg: st.dmg, spd: F.spd, range: F.range, radius: F.radius, kind: p.lf === 'a' ? 'lsa' : p.lf === 'd' ? 'lsd' : 'lbase', type: p.lf === 'd' ? 'phys' : 'magic', luc: 'atk' });
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
    if (!own || !inPlay(own) || !PRACT()) { endBomb(b); continue; }
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
  for (let d = 0; d < MAP * 2; d += 12) {
    const px = x + Math.cos(a) * d, py = y + Math.sin(a) * d * 0.8;
    if (px < 0 || px > MAP || py < 0 || py > MAPH) return d;
  }
  return MAP * 2;
}
function stepSanct(now) {
  for (const o of players.values()) {
    const S = o.sanct;
    if (!S) continue;
    if (now >= S.until || !inPlay(o)) { o.sanct = null; continue; }
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
    if (!inPlay(p)) p.beam = null;
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
    if (!inPlay(p)) p.pure = null;
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
  passive: { ms: 5000, mul: 1.04, hpMul: 1.03 },
  Q: { cd: 500, cost: 100, pick: 48 },
  E: { cd: 15000, min: 100, cost: 100, ms: 2000 },
  R: { cd: 25000, ms: 10000, drain: 70, hpMul: 1.2, heal: 1200, atkMul: 1.15 }
};
const stockPL = (f, t) => (f.buyDealt + (t.hp - f.buyHp0)) / 30;
function stockClear(p) { if (p.buy) send(p.ws, { t: 'stk', id: 0 }); p.buy = 0; }
function stepIns(p, now) {
  if (p.insUntil && now >= p.insUntil) {
    const a = Math.round(p.insAcc); p.insUntil = 0; p.insAcc = 0;
    heal(p, a); fxTxt(p.x, p.y - 30, '🛡️ +' + a, '#9dffb0');
  }
}
function stepFinancier(p, now) {
  for (let i = 0; i < 4 && now >= p.finNext; i++) { p.finNext += FIN.passive.ms; p.mh *= FIN.passive.hpMul; p.hp *= FIN.passive.hpMul; p.fMul *= FIN.passive.mul; p.fDmg = 90 * p.fMul; }
  stepIns(p, now);
  if (p.depUntil) {
    while (p.depNext <= p.depUntil && now >= p.depNext) { const h0 = p.hp; p.hp = Math.max(1, p.hp - FIN.R.drain); if (p.insUntil) p.insAcc += h0 - p.hp; p.depNext += 1000; }
    if (now >= p.depUntil) {
      p.depUntil = 0; p.mh *= FIN.R.hpMul; heal(p, FIN.R.heal); p.fMul += FIN.R.atkMul - 1; p.fDmg = 90 * p.fMul;
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
      cd(FIN.Q.cd); heal(p, gain); p.fMul = Math.max(0.1, p.fMul + pl / 100); p.fDmg = 90 * p.fMul; stockClear(p);
      fxTxt(p.x, p.y - 30, '📈 ' + (pl >= 0 ? '+' : '') + pl.toFixed(1) + '% · +' + Math.round(gain) + ' HP', pl >= 0 ? '#9dffb0' : '#ff8a8a');
    } else {
      const cx = Number(m && m.cx), cy = Number(m && m.cy);
      if (!Number.isFinite(cx) || !Number.isFinite(cy) || p.hp <= FIN.Q.cost) return;
      let best = null, bd = 1e9;
      for (const t of players.values()) {
        if (t === p || !t.joined || t.role !== 1 || sameTeam(p, t) || rootOf(t) === rootOf(p)) continue;
        const d = Math.hypot(t.x - cx, t.y - 24 - cy);
        if (d <= FIN.Q.pick + (t.hr || 0) * 1.4 && d < bd) { bd = d; best = t; }
      }
      if (!best) return;
      cd(FIN.Q.cd); p.hp -= FIN.Q.cost; if (p.insUntil) p.insAcc += FIN.Q.cost; p.buy = best.id; p.buyDealt = 0; p.buyHp0 = best.hp; p.stkNext = 0;
      fxTxt(p.x, p.y - 30, '-' + FIN.Q.cost, '#ff8a8a');
    }
  } else if (k === 'E') {
    if (p.hp <= FIN.E.min) return;
    cd(FIN.E.cd); p.hp -= FIN.E.cost; p.insUntil = now + FIN.E.ms; p.insAcc = FIN.E.cost;
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
  const c = clampArena({ x: p.x + Math.cos(a) * r, y: p.y + Math.sin(a) * r * 0.8 }, { x: p.x, y: p.y });
  const u = { id: 100000 + (++unitSeq), unit: true, ut: type, cls: type === 'i' ? 'UnitInf' : 'UnitArc', owner: p.id, name: '', x: c.x, y: c.y, hp: D.hp, mh: D.hp, role: 1, joined: true, hist: [],
    aim: 0, face: 1, moving: false, atkReady: now + 400, stunUntil: 0, slowUntil: 0, kbUntil: 0, kbx: 0, kby: 0, tauntUntil: 0, tauntBy: 0, tgt: 0, ws: null, hr: 0 };
  units.set(u.id, u);
  broadcast({ t: 'fx', type: 'ring', x: u.x, y: u.y, r: 0.6 * RADPX, c: '#ffe08a', dur: 400 });
}
const gdist = (a, b) => Math.hypot(a.x - b.x, (a.y - b.y) / 0.8);
function stepUnits(dt, now) {
  for (const u of units.values()) {
    const own = players.get(u.owner);
    if (!PRACT() || !own || !inPlay(own)) { units.delete(u.id); continue; }
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
          if (d > D.range + (tgt.hr || 0) - 12) { const q = steer(u, tgt, ux, uy, now); dx = q.x; dy = q.y; }
          else if (now >= u.atkReady) {
            u.atkReady = now + D.atkCd;
            broadcast({ t: 'fx', type: 'cone', by: u.id, x: u.x, y: u.y, a, span: ATK.span, r: D.range, c: 'rgba(255,255,255,.5)', dur: 220 });
            dmgTo(tgt, D.dmg, now, { x: u.x, y: u.y, by: own, basic: true });
            checkRoundEnd();
          }
        } else {
          if (d > D.range * 0.92) { const q = steer(u, tgt, ux, uy, now); dx = q.x; dy = q.y; }
          else if (d < D.keep) { dx = -ux; dy = -uy; }
          if (d <= D.range && now >= u.atkReady) {
            u.atkReady = now + D.atkCd;
            spawnArrow(own, { x: u.x, y: u.y }, 0, now, { a, dmg: D.dmg, spd: ARROW.speed, range: D.range, radius: ATKR, kind: 'tarr' });
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
      const sx0 = u.x, sy0 = u.y; u.x += u.kbx * dt; u.y += u.kby * dt * 0.8;
      const nx = (u.x - CX) / RX, ny = (u.y - CY) / RY, d = ndist(nx, ny);
      if (d > 1) { u.x = CX + nx / d * RX; u.y = CY + ny / d * RY; }
      if (solidMap()) { const q = slideTo(sx0, sy0, u.x, u.y); u.x = q.x; u.y = q.y; }
    }
    const l = Math.hypot(dx, dy);
    if (l > 0.01) {
      dx /= l; dy /= l;
      const spd = D.speed * mul * (now < u.slowUntil ? KNIGHT.R.slow : 1);
      const sx0 = u.x, sy0 = u.y; u.x += dx * spd * dt; u.y += dy * spd * dt * 0.8;
      const nx = (u.x - CX) / RX, ny = (u.y - CY) / RY, d = ndist(nx, ny);
      if (d > 0.97) { u.x = CX + nx / d * 0.97 * RX; u.y = CY + ny / d * 0.97 * RY; }
      if (solidMap()) { const q = slideTo(sx0, sy0, u.x, u.y); u.x = q.x; u.y = q.y; }
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
    if (!own || !PRACT()) continue;
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
    const c = clampArena({ x: tx, y: ty }, null, true), ms = Math.max(350, Math.round(Math.hypot(c.x - o.x, (c.y - o.y) / 0.8) / T.Q.speed * 1000));
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
function smCastQ(p, o, lag, now, mult, viaE) {
  const Q = SM.Q, spec = { a: p.aim, dmg: Math.round(Q.dmg * mult), hpPct: Q.pct * mult, spd: Q.spd, range: Q.range, radius: Q.radius, pierce: false, kind: 'smq', type: 'magic' };
  Object.assign(spec, { noArena: true, range: offMapRange(o.x, o.y, p.aim, 1) });
  if (viaE) spec.pierce = true;
  spawnArrow(p, o, lag, now, spec);
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
    if (L.k === 'Q') smCastQ(p, o2, 0, now, mult, true);
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
  spawnArrow(p, o, lag, now, { a: p.aim, dmg: gamblerDmg(p, now), spd: GAMBLER.spd, range: GAMBLER.range, radius: ATKR, kind: 'gbullet', type: 'phys' });
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
    if (!PRACT()) return;
    cd(G.E.cd);
    if (p.myTurn) return rouletteShot(p, true, now);
    const live = fireChamber(p, now);
    if (live) { fxTxt(p.x, p.y, '💥 실탄!', '#ff6b6b'); dmgTo(p, G.E.self, now, { type: 'pierce' }); }
    else { fxTxt(p.x, p.y, '🍀 공포탄! 실탄 ' + G.E.buffDmg, '#9dffb0'); p.gbUntil = now + G.E.buffMs; }
  } else {
    if (!PRACT()) return;
    cd(G.R.cd);
    p.cdE = 0; send(p.ws, { t: 'cd', k: 'E', ms: 0 });
    p.myTurn = true;
    broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: RADPX, c: '#ff4b4b', dur: 700 });
    fxTxt(p.x, p.y, '🎲 내 차례', '#ff8a8a');
  }
  checkRoundEnd();
}
// ---- Celestial ----
const CEL = {
  cap: 300, store: 0.7, heal: 0.1,
  Q: { cd: 7000, r: 2 * RADPX, delay: 700, dmg: 400, back: 0.2 },
  E: { cd: 1000 },
  R: { cd: 25000, delay: 0, r: 3 * RADPX, ms: 4000, tickMs: 250, tick: 10, pull: 0.55, burstR: RADPX, burst: 300 }
};
function celestialAttack(p, m, now) {
  if (now < p.atkReady) return;
  const st = statsOf(p), o = originOf(p, m), lag = lagOf(m), dmg = st.dmg + (p.nextBonus || 0);
  p.nextBonus = 0;
  p.atkReady = now + st.atkCd / atkSpeed(p, now);
  broadcast({ t: 'fx', type: 'cone', by: p.id, x: o.x, y: o.y, a: p.aim, span: ATK.span, r: ATK.range, c: 'rgba(255,255,255,.6)', dur: 220 });
  for (const t of targetsOf(p)) {
    const tp = posAt(t, now - lag);
    if (inConeAt(o.x, o.y, p.aim, tp.x, tp.y, ATK.range, ATK.span, t.hr || 0)) dmgTo(t, dmg, now, { x: o.x, y: o.y, by: p, basic: true, type: 'magic' });
  }
  checkRoundEnd();
}
function celestialSkill(p, k, m, now) {
  const o = originOf(p, m), S = CEL[k];
  if (k === 'E') {
    if (!(p.dim > 0)) return;
    const n = Math.round(p.dim);
    p.cdE = now + S.cd; send(p.ws, { t: 'cd', k, ms: S.cd });
    p.nextBonus = (p.nextBonus || 0) + n; p.dim = 0;
    broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 1.1 * RADPX, c: '#ffffff', dur: 450 });
    fxTxt(p.x, p.y - 40, '⚪ +' + n, '#ffffff');
    return;
  }
  p['cd' + k] = now + S.cd; send(p.ws, { t: 'cd', k, ms: S.cd });
  if (k === 'Q') {
    planets.push({ owner: p.id, x: o.x, y: o.y, at: now + S.delay, tint: curTint, bonus: p.nextBonus || 0 }); p.nextBonus = 0;
    broadcast({ t: 'fx', type: 'planet', x: o.x, y: o.y, r: S.r, fall: S.delay, dur: S.delay + 260 });
  } else {
    galaxies.push({ owner: p.id, x: o.x, y: o.y, start: now + S.delay, until: now + S.delay + S.ms, next: now + S.delay + S.tickMs, tint: curTint, bonus: p.nextBonus || 0 }); p.nextBonus = 0;
    broadcast({ t: 'fx', type: 'galaxy', x: o.x, y: o.y, r: S.r, fall: S.delay, dur: S.delay + S.ms });
  }
}
function stepCelestial(dt, now) {
  let any = false;
  for (let i = planets.length - 1; i >= 0; i--) {
    const b = planets[i];
    if (now < b.at) continue;
    planets.splice(i, 1);
    curTint = b.tint || null;
    broadcast({ t: 'fx', type: 'ring', x: b.x, y: b.y, r: CEL.Q.r, c: '#b69cff', dur: 400 });
    curTint = null;
    const own = players.get(b.owner);
    if (!own || !inPlay(own) || !PRACT()) continue;
    let total = 0;
    for (const t of targetsOf(own)) {
      if (Math.hypot(t.x - b.x, (t.y - b.y) / 0.8) > CEL.Q.r + (t.hr || 0)) continue;
      const before = t.hp;
      dmgTo(t, CEL.Q.dmg + (b.bonus || 0), now, { x: b.x, y: b.y, by: own, type: 'phys' });
      total += Math.max(0, Math.min(before, before - t.hp));
    }
    own.dim = Math.min(CEL.cap, (own.dim || 0) + total * CEL.Q.back);
    any = true;
  }
  for (let i = galaxies.length - 1; i >= 0; i--) {
    const g = galaxies[i], own = players.get(g.owner), R = CEL.R;
    if (!own || !inPlay(own) || !PRACT()) { galaxies.splice(i, 1); continue; }
    if (now < g.start) continue;
    const live = targetsOf(own).filter(t => Math.hypot(t.x - g.x, (t.y - g.y) / 0.8) <= R.r + (t.hr || 0));
    for (const t of live) {
      const dx = g.x - t.x, dy = (g.y - t.y) / 0.8, d = Math.hypot(dx, dy);
      if (d < 1) continue;
      const st = Math.min(d, SPEED * R.pull * dt), c = clampArena({ x: t.x + dx / d * st, y: t.y + dy / d * st * 0.8 }, { x: t.x, y: t.y });
      t.x = c.x; t.y = c.y;
    }
    while (g.next <= g.until && now >= g.next) {
      g.next += R.tickMs;
      for (const t of live) { dmgTo(t, R.tick, now, { x: g.x, y: g.y, kill: own, type: 'pierce' }); any = true; }
    }
    if (now >= g.until) {
      galaxies.splice(i, 1);
      curTint = g.tint || null;
      broadcast({ t: 'fx', type: 'ring', x: g.x, y: g.y, r: R.burstR, c: '#ffffff', dur: 450 });
      curTint = null;
      for (const t of targetsOf(own)) if (Math.hypot(t.x - g.x, (t.y - g.y) / 0.8) <= R.burstR + (t.hr || 0)) { dmgTo(t, R.burst + (g.bonus || 0), now, { x: g.x, y: g.y, kill: own, type: 'pierce' }); any = true; }
    }
  }
  for (const p of players.values()) {
    if (p.cls !== 'Celestial' && p.cls !== 'Gamer') continue;
    const key = Math.round(p.dim || 0) + '|' + (p.nextBonus || 0);
    if (key !== p.celKey) { p.celKey = key; send(p.ws, { t: 'cel', d: Math.round(p.dim || 0), b: p.nextBonus || 0 }); }
  }
  if (any) checkRoundEnd();
}
// ---- Gamer ----
const GAMER = {
  atk: { range: 4 * RADPX, melee: 170 },
  Q: { cd: 8000 },
  E: { cd: 15000, potion: 250, windMs: 4000, wind: 0.5 },
  R: { cd: 25000, dur: 4000 }
};
const GFN = { Knight: knightSkill, Archer: archerSkill, Shielder: shielderSkill, Assassin: assassinSkill, Lucifer: luciferSkill, Celestial: celestialSkill, SwordMaster: swordmasterSkill, Tower: towerSkill, Financier: financierSkill };
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
  { cls: 'Financier', k: 'E', n: '보험' },
  { cls: 'Celestial', k: 'Q', n: '행성 폭발' },
  { cls: 'Berserker', k: 'Q', n: '도끼' }, { cls: 'Berserker', k: 'E', n: '대지 강타' }
];
const GCOPY_BAN = new Set(['Celestial:E', 'Reaper:E']);
function randTint() {
  const h = Math.random() * 360, s = 0.85, l = 0.55, a = s * Math.min(l, 1 - l);
  const f = n => { const k = (n + h / 30) % 12; return Math.round(255 * (l - a * Math.max(-1, Math.min(k - 3, 9 - k, 1)))).toString(16).padStart(2, '0'); };
  return '#' + f(0) + f(8) + f(4);
}
const sendGc = (p, now) => send(p.ws, { t: 'gc', l: (p.gCopy || []).map(e => e.n), s: p.gSlots || 1, ch: Math.max(0, (p.gCheatUntil || 0) - (now || Date.now())) });
function gamerAttack(p, m, now) {
  if (now < p.atkReady) return;
  const st = statsOf(p), o = originOf(p, m), lag = lagOf(m), bonus = p.nextBonus || 0;
  p.nextBonus = 0;
  p.atkReady = now + st.atkCd / atkSpeed(p, now);
  breakStealth(p);
  const ranged = p.gNext === 1;
  p.gNext = ranged ? 0 : 1;
  const base = ranged ? st.dmg : GAMER.atk.melee;
  p.gLast = { ranged, dmg: base + bonus };
  gamerStrike(p, o, lag, now, ranged, base + bonus, 'atk');
}
function gamerStrike(p, o, lag, now, ranged, dmg, kind) {
  if (ranged) {
    spawnArrow(p, o, lag, now, { a: p.aim, dmg, spd: ARROW.speed, range: GAMER.atk.range, radius: ATKR, kind: 'gr', type: 'magic' });
    return;
  }
  broadcast({ t: 'fx', type: 'gslash', by: p.id, x: o.x, y: o.y, a: p.aim, span: ATK.span, r: ATK.range, dur: 240 });
  for (const t of targetsOf(p)) {
    const tp = posAt(t, now - lag);
    if (inConeAt(o.x, o.y, p.aim, tp.x, tp.y, ATK.range, ATK.span, t.hr || 0)) dmgTo(t, dmg, now, { x: o.x, y: o.y, by: p, basic: true, type: 'phys' });
  }
  checkRoundEnd();
}
function castCopied(p, e, m, now) {
  const keep = { Q: p.cdQ, E: p.cdE, R: p.cdR }, lf0 = p.lf, tint = randTint();
  p['cd' + e.k] = 0; p.gPierce = e.cls === 'Assassin'; p.lf = e.lf || ''; curTint = tint;
  let fired;
  try {
    if (e.cls === 'SwordMaster' && e.k === 'E') {
      fired = !!p.gLast;
      if (fired) {
        const L = p.gLast, o2 = L.ranged ? originOf(p, m) : { x: p.x, y: p.y };
        broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 0.7 * RADPX, c: '#8fe3ff', dur: 450 });
        gamerStrike(p, o2, 0, now, L.ranged, Math.round(L.dmg * SM.E.mult), 'atk');
      } else fxTxt(p.x, p.y, '직전 공격 없음', '#cfcfcf');
    } else if (e.cls === 'Berserker') {
      fired = true;
      if (e.k === 'Q') spawnArrow(p, originOf(p, m), lagOf(m), now, { a: p.aim, dmg: BERS.Q.dmg, spd: BERS.Q.spd, range: BERS.Q.range, radius: BERS.Q.hit, pierce: true, kind: 'axe', type: 'phys' });
      else berserkSlam(p, { x: p.x, y: p.y }, now);
    } else { GFN[e.cls](p, e.k, m, now); fired = p['cd' + e.k] > 0; }
  } finally { curTint = null; }
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
      let used = 0;
      for (const e of list) if (!castCopied(p, e, m, now)) p.gCopy.push(e); else used++;
      if (used) {
        if (p.gBig) { p.gSlots = 1; p.gBig = false; }
        const ms = now < p.gCheatUntil ? 0 : G.Q.cd;
        p.cdQ = now + ms; send(p.ws, { t: 'cd', k: 'Q', ms });
      }
      sendGc(p, now);
      checkRoundEnd();
      return;
    }
    const pool = GCOPY.filter(e => !GCOPY_BAN.has(e.cls + ':' + e.k));
    const got = [];
    for (let i = 0, n = Math.min(p.gSlots, pool.length); i < n; i++) got.push(pool.splice(Math.floor(Math.random() * pool.length), 1)[0]);
    p.gCopy = got; p.gBig = p.gSlots > 1;
    p.cdQ = 0; send(p.ws, { t: 'cd', k: 'Q', ms: 0 });
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
    broadcast({ t: 'fx', type: 'gacha', x: p.x, y: p.y, dur: 1100 });
    broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 1.2 * RADPX, c: '#9dffb0', dur: 600 });
    fxTxt(p.x, p.y - 40, msg.join(' · '), '#9dffb0');
  } else {
    p.cdR = now + G.R.dur + G.R.cd; p.gCdPend = 1; send(p.ws, { t: 'cd', k: 'R', ms: G.R.dur });
    p.gCheatUntil = now + G.R.dur; p.cdQ = 0; send(p.ws, { t: 'cd', k: 'Q', ms: 0 });
    sendGc(p, now);
    broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 1.5 * RADPX, c: '#ff6bd5', dur: 700 });
    fxTxt(p.x, p.y - 40, '💻 치트', '#ff9be8');
  }
}
function stepGamer(now) {
  for (const p of players.values()) if (p.gCdPend && now >= p.gCheatUntil) {
    p.gCdPend = 0;
    if (p.cls === 'Gamer') { send(p.ws, { t: 'cd', k: 'R', ms: Math.max(0, p.cdR - now) }); sendGc(p, now); }
  }
}
function checkTimeout(now) {
  if (phase !== 'round' || now - roundStart < ROUND_MS) return;
  if (gameMode === 'boss') return endRound(null, null, 1);
  if (gameMode === 'team') {
    const sum = { 1: 0, 2: 0 };
    for (const p of players.values()) if (p.role === 1 && p.team) sum[p.team] += p.hp;
    return endRound(null, null, sum[1] > sum[2] ? 1 : sum[2] > sum[1] ? 2 : 0, sum[1] === sum[2]);
  }
  endRound(null, [...players.values()].filter(p => p.role === 1 && !p.skel).map(p => p.name));
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
setInterval(() => { const n = Date.now(); for (const [k, e] of mem) if (e.exp && e.exp < n) mem.delete(k); }, 60000).unref();
const memGet = k => { const e = mem.get(k); if (!e) return null; if (e.exp && e.exp < Date.now()) { mem.delete(k); return null; } return e; };
const db = (UP_URL && UP_TOKEN) ? {
  get: k => upstash('GET', KEY + k),
  set: (k, v) => upstash('SET', KEY + k, v),
  setnx: async (k, v) => (await upstash('SET', KEY + k, v, 'NX')) === 'OK',
  setex: (k, sec, v) => upstash('SET', KEY + k, v, 'EX', sec),
  del: k => upstash('DEL', KEY + k),
  incr: k => upstash('INCR', KEY + k),
  incrby: (k, n) => upstash('INCRBY', KEY + k, String(n)),
  expire: (k, sec) => upstash('EXPIRE', KEY + k, sec),
  mget: ks => ks.length ? upstash('MGET', ...ks.map(k => KEY + k)) : Promise.resolve([]),
  keys: async prefix => { let cur = '0'; const out = []; do { const r = await upstash('SCAN', cur, 'MATCH', KEY + prefix + '*', 'COUNT', '200'); cur = String(r[0]); for (const k of r[1]) out.push(k.slice(KEY.length)); } while (cur !== '0' && out.length < 5000); return out; }
} : {
  get: async k => { const e = memGet(k); return e ? e.v : null; },
  set: async (k, v) => { mem.set(k, { v }); },
  setnx: async (k, v) => { if (memGet(k)) return false; mem.set(k, { v }); return true; },
  setex: async (k, sec, v) => { mem.set(k, { v, exp: Date.now() + sec * 1000 }); },
  del: async k => { mem.delete(k); },
  incrby: async (k, n) => { const e = memGet(k), v = (e ? Number(e.v) : 0) + n; mem.set(k, { v: String(v), exp: e && e.exp }); return v; },
  incr: async k => { const e = memGet(k), n = (e ? Number(e.v) : 0) + 1; mem.set(k, { v: String(n), exp: e && e.exp }); return n; },
  expire: async (k, sec) => { const e = memGet(k); if (e) e.exp = Date.now() + sec * 1000; },
  mget: async ks => ks.map(k => { const e = memGet(k); return e ? e.v : null; }),
  keys: async prefix => [...mem.keys()].filter(k => k.startsWith(prefix) && memGet(k))
};
(async () => { try { const r = await db.get('wins'); const o = r ? JSON.parse(r) : {}; for (const id of Object.keys(o)) if (o[id] && Number.isInteger(o[id].w) && o[id].w > 0) winsData[id] = { n: String(o[id].n || id).slice(0, 24), w: o[id].w }; calcWinTop(); } catch (e) { console.error('wins load failed:', e.message); }
  try {
    const ks = await db.keys('winu:');
    for (let i = 0; i < ks.length; i += 200) {
      const part = ks.slice(i, i + 200), vs = await db.mget(part);
      part.forEach((k, n) => { try { const o = JSON.parse(vs[n]); if (o && Number.isInteger(o.w) && o.w > 0) winsData[k.slice(5)] = { n: String(o.n || k.slice(5)).slice(0, 24), w: o.w }; } catch (e) {} });
    }
    calcWinTop();
  } catch (e) { console.error('wins (per-user) load failed:', e.message); }
})();
(async () => {
  try { const r = await db.get('mapcfg'), o = r ? JSON.parse(r) : null; if (o) { if (Number.isFinite(o.rt) && o.rt >= 10000 && o.rt <= 3600000) ROUND_MS = o.rt; if ([1, 1.5, 2].includes(o.scale) && o.scale !== mapScale) setScale(o.scale); if (ARENAS[o.id] && o.id !== mapId) setMap(o.id); } } catch (e) { console.error('mapcfg load failed:', e.message); }
})();
(async () => { try { const r = await db.get('shopprice'); const o = r ? JSON.parse(r) : {}; for (const id of Object.keys(o)) if (SKINS[id] && Number.isInteger(o[id]) && o[id] >= 0) shopPrices[id] = o[id]; } catch (e) { console.error('shopprice load failed:', e.message); } })();
console.log((UP_URL && UP_TOKEN) ? 'Accounts: Upstash Redis' : 'WARNING: UPSTASH_REDIS_REST_URL / UPSTASH_REDIS_REST_TOKEN not set - accounts live in memory and are LOST on restart');
if (!(UP_URL && UP_TOKEN) && process.env.RENDER && process.env.ALLOW_MEMORY_DB !== '1') { console.error('FATAL: no database configured on Render (set ALLOW_MEMORY_DB=1 to override).'); process.exit(1); }

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
const adminGoldQ = (p, m) => { const run = admLock.then(() => adminGold(p, m)); admLock = run.catch(() => {}); return run; };
async function adminGold(p, m) {
  const reply = (ok, msg, extra) => send(p.ws, Object.assign({ t: 'gadmin', ok, msg }, extra));
  if (m.t === 'glist') {
    const ids = (await db.keys('user:')).map(k => k.slice(5)).filter(id => id && id !== OBS_ID).sort().slice(0, 300);
    const us = await db.mget(ids.map(i => 'user:' + i)), gs = await db.mget(ids.map(i => 'gold:' + i));
    const list = ids.map((id, i) => { let nick = id; try { nick = JSON.parse(us[i]).nick || id; } catch {} return { id, nick, gold: Math.max(0, parseInt(gs[i], 10) || 0) }; });
    return reply(1, '', { list });
  }
  const target = normId(m.target);
  if (!target) return reply(0, '대상 아이디가 올바르지 않습니다.');
  const raw = await db.get('user:' + target);
  if (!raw) return reply(0, '존재하지 않는 아이디입니다.');
  const rec = JSON.parse(raw), n = Number(m.amount);
  if (!Number.isInteger(n) || n < 0 || n > 1000000000) return reply(0, '금액은 0 ~ 1,000,000,000 사이의 정수여야 합니다.');
  let v, msg;
  if (m.t === 'gset') { await db.set('gold:' + target, String(n)); v = n; msg = rec.nick + '님의 골드를 ' + n.toLocaleString() + '(으)로 설정했습니다.'; }
  else { v = Number(await db.incrby('gold:' + target, n)); msg = rec.nick + '님에게 ' + n.toLocaleString() + ' 골드를 지급했습니다.'; }
  if (!Number.isFinite(v)) return reply(0, '서버 오류가 발생했습니다.');
  for (const q of players.values()) if (q.user === target) { const d = v - (q.gold || 0); q.gold = v; send(q.ws, { t: 'gold', g: v, d: d > 0 ? d : 0 }); }
  reply(1, msg, { row: { id: target, nick: rec.nick, gold: v } });
}
async function loginOk(p, rec, token) {
  kickOld(rec.id, p);
  p.user = rec.id; p.name = rec.nick;
  if (rec.id === OBS_ID) {
    p.obs = true; p.titles = []; p.eq = null; p.gold = 0; p.skins = []; p.eqs = {};
    send(p.ws, { t: 'auth', ok: 1, name: rec.nick, token, admin: 0, obs: 1 });
    const all = {};
    for (const q of players.values()) if (q.joined) { const tt = titleOf(q); if (tt) all[q.id] = tt; }
    return send(p.ws, { t: 'ttls', m: all });
  }
  if (!p.joined && joinedList().filter(q => !q.skel).length >= MAX_PLAYERS) { send(p.ws, { t: 'full' }); try { p.ws.close(); } catch (e) {} return; }
  const ti = await loadTitles(rec.id);
  p.titles = ti.list; p.eq = ti.eq;
  try { p.gold = Math.max(0, parseInt(await db.get('gold:' + rec.id), 10) || 0); } catch (e) { p.gold = 0; }
  if (winsData[rec.id] && winsData[rec.id].n !== rec.nick) { winsData[rec.id].n = rec.nick; calcWinTop(); }
  if (!p.joined) { p.joined = true; if (phase === 'round') p.role = 2; }
  send(p.ws, { t: 'auth', ok: 1, name: rec.nick, token, admin: rec.id === ADMIN_ID ? 1 : 0 });
  const sk = await loadSkins(rec.id); p.skins = sk.own; p.eqs = sk.eqs; p.skinsErr = sk.err;
  const cl = await loadCls(rec.id); p.clsOwn = cl.own; p.clsErr = cl.err;
  sendTinfo(p); send(p.ws, { t: 'gold', g: p.gold }); sendSinfo(p); sendCinfo(p); sendShop(p.ws); sendWins(p);
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
async function guestLogin(p, m) {
  const nick = clean(m.name, 14), lc = nick.toLowerCase();
  if (nick.length < 2) return authFail(p, '닉네임은 2~14자로 입력해 주세요.');
  if (['system', 'admin', 'server'].includes(lc)) return authFail(p, '사용할 수 없는 닉네임입니다.');
  let taken = false;
  try { taken = !!(await db.get('nick:' + lc)); } catch (e) { return authFail(p, '서버 오류가 발생했습니다. 잠시 후 다시 시도해 주세요.'); }
  if (taken) return authFail(p, '이미 가입된 닉네임입니다.');
  for (const q of players.values()) if (q !== p && q.joined && !q.skel && String(q.name).toLowerCase() === lc) return authFail(p, '이미 사용 중인 닉네임입니다.');
  if (p.user || p.guest || p.joined) return;
  if (joinedList().filter(q => !q.skel).length >= MAX_PLAYERS) { send(p.ws, { t: 'full' }); try { p.ws.close(); } catch (e) {} return; }
  p.guest = true; p.user = null; p.name = nick;
  p.titles = []; p.eq = null; p.gold = 0; p.skins = []; p.eqs = {}; p.skinsErr = false; p.clsOwn = []; p.clsErr = false;
  p.joined = true; if (phase === 'round') p.role = 2;
  send(p.ws, { t: 'auth', ok: 1, name: nick, token: '', admin: 0, guest: 1 });
  sendTinfo(p); send(p.ws, { t: 'gold', g: 0 }); sendSinfo(p); sendCinfo(p); sendShop(p.ws); sendWins(p);
  const all = {};
  for (const q of players.values()) if (q.joined && q !== p) { const tt = titleOf(q); if (tt) all[q.id] = tt; }
  send(p.ws, { t: 'ttls', m: all });
}
async function handleAuth(p, m, ip) {
  if (p.user || p.guest || p.authBusy) return;
  p.authBusy = true;
  try {
    if (!rateOk('a:' + ip, 40, 60000)) return authFail(p, '시도가 너무 많습니다. 잠시 후 다시 시도해 주세요.');
    if (m.t === 'guest') {
      if (!rateOk('g:' + ip, 30, 3600 * 1000)) return authFail(p, '입장 시도가 너무 많습니다. 나중에 다시 시도해 주세요.');
      return await guestLogin(p, m);
    }
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

    const fk = 'fail:' + id, ipk = fk + ':' + sha(ip).slice(0, 12);
    if ((Number(await db.get(ipk)) || 0) >= LOCK_FAILS || (Number(await db.get(fk)) || 0) >= LOCK_FAILS * 5) return authFail(p, '로그인 시도가 너무 많습니다. 10분 후 다시 시도해 주세요.');
    const raw = await db.get('user:' + id), rec = raw && JSON.parse(raw);
    const h = await scryptHex(pw, rec ? rec.salt : DUMMY_SALT);
    if (!rec || !safeEq(h, rec.hash)) {
      for (const k of [ipk, fk]) if (await db.incr(k) === 1) await db.expire(k, LOCK_SEC);
      return authFail(p, '아이디 또는 비밀번호가 올바르지 않습니다.');
    }
    await db.del(ipk); await db.del(fk);
    return await loginOk(p, rec, await newSession(id));
  } finally { p.authBusy = false; }
}

// ---- player factory ----
function mkPlayer(id, ws) {
  const a = Math.random() * Math.PI * 2, r = Math.random() * 0.5;
  return { id, ws, name: 'Player' + id, hue: Math.floor(Math.random() * 360),
    ...ringPos(a, r), face: 1, dx: 0, dy: 0, lastChat: 0, alive: true,
    joined: false, cls: '', ready: false, role: 0, inRound: false, lx: 0, ly: 0, deathOrder: 0,
    hp: 1000, mh: 1000, atkReady: 0, cdQ: 0, cdE: 0, cdR: 0, stunUntil: 0, guardUntil: 0, slowUntil: 0, chargeStart: 0, hasteUntil: 0, invisUntil: 0, tauntUntil: 0, tauntBy: 0, kbUntil: 0, hornUntil: 0, dash: null, markUntil: 0, asUntil: 0, asBonus: 0, fires: [], qNext: false, pull: null, charmUntil: 0, charmBy: 0, burnUntil: 0, burnNext: 0, titles: [], eq: null, lastEquip: 0, aim: 0, hist: [] };
}
// ---- Berserker ----
const BERS = {
  Q: { cd: 5000, range: 4 * RADPX, spd: 900, hit: 45, dmg: 250, pick: 0.6 * RADPX },
  E: { cd: 15000, r: 1.5 * RADPX, dmg: 100, stun: 1000, cut: 1000 },
  R: { cd: 25000, ms: 10000 }
};
function berserkSlam(p, c, now) {
  broadcast({ t: 'fx', type: 'disc', x: c.x, y: c.y, r: BERS.E.r, c: 'rgba(255,120,50,.35)', s: '#ff9a5a', dur: 450 });
  for (const t of targetsOf(p)) {
    if (Math.hypot(t.x - c.x, (t.y - c.y) / 0.8) > BERS.E.r + (t.hr || 0)) continue;
    dmgTo(t, BERS.E.dmg, now, { x: c.x, y: c.y, by: p, type: 'phys' });
    if (t.role === 1 && !t.unit) t.stunUntil = Math.max(t.stunUntil || 0, now + BERS.E.stun);
  }
}
function berserkerSkill(p, k, m, now) {
  const cd = ms => { p['cd' + k] = now + ms; send(p.ws, { t: 'cd', k, ms }); };
  if (!p.axes || !p.axes.length) return;
  if (k === 'Q') {
    const ax = p.axes.find(a => a.s === 0);
    if (!ax) {
      const out = p.axes.filter(a => a.s !== 0); if (!out.length) return;
      for (const a of out) { if (a.s === 1) broadcast({ t: 'arrowEnd', id: a.vid }); a.s = 0; p.cdE = Math.max(now, p.cdE - BERS.E.cut); fxTxt(p.x, p.y - 30, '🪓 회수', '#ffb27a'); }
      send(p.ws, { t: 'cd', k: 'E', ms: Math.max(0, p.cdE - now) }); cd(0); return;
    }
    ax.s = 1; ax.x = p.x; ax.y = p.y; ax.a = p.aim; ax.d = 0; ax.hit = new Set(); ax.vid = ++arrowSeq;
    broadcast({ t: 'arrow', id: ax.vid, by: p.id, x: p.x, y: p.y, a: p.aim, spd: BERS.Q.spd, range: BERS.Q.range, adv: 0, sc: 1, kd: 'axe', bm: 0 });
    cd(now < p.bRUntil && p.axes.some(a => a.s === 0) ? 0 : BERS.Q.cd);
  } else if (k === 'E') {
    cd(BERS.E.cd);
    for (const ax of p.axes) {
      const c = ax.s === 0 ? { x: p.x, y: p.y } : { x: ax.x, y: ax.y };
      berserkSlam(p, c, now);
    }
    checkRoundEnd();
  } else {
    cd(BERS.R.cd); p.bRUntil = now + BERS.R.ms;
    if (p.axes.length < 2) p.axes.push({ s: 0, x: 0, y: 0, a: 0, d: 0 });
    p.cdQ = 0; send(p.ws, { t: 'cd', k: 'Q', ms: 0 });
    broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 1.3 * RADPX, c: '#ff5a3a', dur: 600 });
  }
}
// ---- bleeding (public status effect) ----
const BLEED = { dmg: 50, ms: 1000 };
function applyBleed(t, ms, now, src) {
  if (!t || t.unit || t.role !== 1 || phase !== 'round') return;
  if (!(t.bleedUntil > now)) t.bleedNext = now + BLEED.ms;
  t.bleedUntil = Math.max(t.bleedUntil || 0, now + ms); t.bleedBy = src ? src.id : 0;
}
function stepBleed(p, now) {
  if (!p.bleedUntil) return;
  if (p.role !== 1 || phase !== 'round') { p.bleedUntil = 0; return; }
  while (p.bleedUntil && p.bleedNext <= p.bleedUntil && now >= p.bleedNext) {
    p.bleedNext += BLEED.ms;
    dmgTo(p, BLEED.dmg, now, { kill: players.get(p.bleedBy) || null, type: 'pierce', fixed: true });
    if (p.role !== 1) { p.bleedUntil = 0; return; }
  }
  if (p.bleedUntil && now >= p.bleedUntil) p.bleedUntil = 0;
}
// ---- buff duration bars ----
const BUFFS = ['hasteUntil', 'invisUntil', 'hornUntil', 'guardUntil', 'libUntil', 'insUntil', 'depUntil', 'towerRUntil', 'smAwkUntil', 'gbUntil', 'gbPlusUntil', 'fastUntil', 'asUntil', 'gCheatUntil', 'bRUntil', 'bleedUntil'];
function buffsOf(p, now) {
  if (p.role !== 1 || phase !== 'round') return 0;
  const bt = p._bt || (p._bt = {}); let out = null;
  for (let i = 0; i < BUFFS.length; i++) {
    const f = BUFFS[i], u = p[f] || 0, rem = u - now;
    if (rem <= 0 || rem > 60000) { if (bt[f]) delete bt[f]; continue; }
    let b = bt[f]; if (!b || b.u !== u) b = bt[f] = { u, t: rem };
    (out || (out = [])).push([Math.round(rem), Math.round(b.t), i]);
  }
  return out || 0;
}
function stepBerserker(dt, now) {
  for (const p of players.values()) {
    if (p.cls !== 'Berserker' || !p.axes) continue;
    if (p.bRUntil && now >= p.bRUntil) { p.bRUntil = 0; if (p.axes.length > 1) { const keep = p.axes.find(a => a.s === 0) || p.axes.find(a => a.s === 2) || p.axes[0]; for (const a of p.axes) if (a !== keep && a.s === 1) broadcast({ t: 'arrowEnd', id: a.vid }); p.axes = [keep]; } }
    if (!inPlay(p) || !PRACT()) continue;
    let any = false;
    for (const a of p.axes) {
      if (a.s === 1) {
        const step = Math.min(BERS.Q.spd * dt, BERS.Q.range - a.d);
        const nx = a.x + Math.cos(a.a) * step, ny = a.y + Math.sin(a.a) * step * 0.8, ex = (nx - CX) / RX, ey = (ny - CY) / RY;
        let land = false, hitNow = false;
        if (ndist(ex, ey) > 1) land = true; else { a.x = nx; a.y = ny; a.d += step; if (a.d >= BERS.Q.range - 0.01) land = true; }
        for (const t of targetsOf(p)) {
          if (a.hit.has(t.id) || Math.hypot(t.x - a.x, (t.y - a.y) / 0.8) > BERS.Q.hit + (t.hr || 0)) continue;
          a.hit.add(t.id); any = true; hitNow = true;
          dmgTo(t, BERS.Q.dmg, now, { dir: a.a + Math.PI, kill: p, type: 'phys' });
        }
        if (hitNow) land = true;
        if (land) { a.s = 2; broadcast({ t: 'arrowEnd', id: a.vid }); }
      } else if (a.s === 2 && Math.hypot(p.x - a.x, (p.y - a.y) / 0.8) <= BERS.Q.pick) {
        a.s = 0; p.cdE = Math.max(now, p.cdE - BERS.E.cut); send(p.ws, { t: 'cd', k: 'E', ms: Math.max(0, p.cdE - now) });
        p.cdQ = 0; send(p.ws, { t: 'cd', k: 'Q', ms: 0 });
        fxTxt(p.x, p.y - 30, '🪓 회수', '#ffb27a');
      }
    }
    if (any) checkRoundEnd();
  }
}
// ---- Plum Blossom ----
const PB = {
  g0: 0.02, max: [50, 100, 200, 400, 800, 1600], cost: [0, 2.5, 5, 10, 20, 40, 40], cmd: 300, slack: 100, menu: 3000,
  hw: 0.3 * RADPX, blk: { ms: 500, r: 1.1 * RADPX, span: 150 * RAD }, spd: 1200,
  cd: { E4: 4000, E1: 4000, E2: 4000, E3: 4000, S1: 4000, S2: 4000, S3: 4000, R1: 4000, R2: 4000, R3: 4000 },
  names: ['삼류', '이류', '일류', '절정', '초절정', '화경', '현경']
};
PB.mul = (() => { let m = 1; return [0, 1, 2, 3, 4, 5, 6].map(i => (m *= 1 + PB.g0 * Math.pow(2, i))); })();
const pbMul = p => PB.mul[p.pbStage | 0];
const PB_Q = [null,
  { iv: 500, en: 3 },
  { iv: 500, en: 4.5, hp: 40 },
  { iv: 1000, en: 12 },
  { iv: 1000, en: 22.5, as: 0.1, frac: 0.5 },
  { iv: 2000, en: 75 },
  { iv: 1000, en: 45, as: 0.2, frac: 0.75 },
  { iv: 1000, en: 45, heal: 0.05, healEvery: 2, mobile: true }
];
const pbWalls = [], pbZones = [], pbTimers = []; let pbSeq = 0;
const pbLater = (p, ms, fn) => pbTimers.push({ at: Date.now() + ms, owner: p.id, fn });
function pbClean(id) {
  for (const arr of [pbZones, pbTimers]) for (let i = arr.length - 1; i >= 0; i--) if (arr[i].owner === id) arr.splice(i, 1);
  for (let i = pbWalls.length - 1; i >= 0; i--) if (pbWalls[i].owner === id) { broadcast({ t: 'pbend', id: pbWalls[i].id }); pbWalls.splice(i, 1); }
}
function pbGain(p, n) {
  p.pbD += n; p.pbA += n;
  let up = false;
  while (p.pbStage < 6 && p.pbD > PB.max[p.pbStage]) {
    p.pbStage++; up = true;
    const f = 1 + PB.g0 * Math.pow(2, p.pbStage);
    p.mh = Math.round(p.mh * f); p.hp = Math.min(p.mh, p.hp * f);
  }
  if (up) {
    p.pbA = p.pbD;
    broadcast({ t: 'fx', type: 'pbburst', x: p.x, y: p.y, r: 1.6 * RADPX, dur: 900 });
    fxTxt(p.x, p.y - 50, '✨ ' + PB.names[p.pbStage], '#F4AABB');
  }
}
function pbStart(p, n, now) {
  if (n < 1 || n > p.pbStage + 1) return;
  p.pbResume = null;
  p.pbCh = { t: n, t0: now, next: now + PB_Q[n].iv };
  broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 0.8 * RADPX, c: '#F4AABB', dur: 500 });
}
function pbStop(p, now, byAtk) {
  const ch = p.pbCh; if (!ch) return;
  p.pbCh = null;
  const T = PB_Q[ch.t];
  if (T.as) { const dur = (now - ch.t0) * T.frac; if (dur > 200) { p.asUntil = now + dur; p.asBonus = T.as; } }
  if (ch.t === 7 && byAtk) p.pbResume = { at: now + 1000 };
}
function pbTryBlock(t, src, now) {
  if (!src || now >= (t.pbBlockUntil || 0)) return false;
  let dir = src.dir;
  if (dir === undefined) {
    if (src.x === undefined) return false;
    const dx = src.x - t.x, dy = (src.y - t.y) / 0.8;
    if (Math.hypot(dx, dy) > PB.blk.r) return false;
    dir = Math.atan2(dy, dx);
  }
  if (Math.abs(Math.atan2(Math.sin(dir - t.aim), Math.cos(dir - t.aim))) > PB.blk.span / 2) return false;
  t.pbBlockUntil = 0;
  broadcast({ t: 'hit', id: t.id, dmg: 0, bl: 2 });
  broadcast({ t: 'fx', type: 'pbburst', x: t.x, y: t.y, r: 0.9 * RADPX, dur: 500 });
  fxTxt(t.x, t.y - 50, '막기!', '#F4AABB');
  return true;
}
function segsNear(ax, ay, bx, by, cx, cy, dx, dy, tol) {
  const o = (px, py, qx, qy, rx, ry) => Math.sign((qx - px) * (ry - py) - (qy - py) * (rx - px));
  if (o(ax, ay, bx, by, cx, cy) !== o(ax, ay, bx, by, dx, dy) && o(cx, cy, dx, dy, ax, ay) !== o(cx, cy, dx, dy, bx, by)) return true;
  return segDist(ax, ay, cx, cy, dx, dy) <= tol || segDist(bx, by, cx, cy, dx, dy) <= tol || segDist(cx, cy, ax, ay, bx, by) <= tol || segDist(dx, dy, ax, ay, bx, by) <= tol;
}
function pbWallHit(w, x0, gy0, x1, gy1) {
  if (w.kind === 'seg') return segsNear(x0, gy0, x1, gy1, w.x1, w.gy1, w.x2, w.gy2, 10);
  return (Math.hypot(x0 - w.x, gy0 - w.gy) <= w.r) !== (Math.hypot(x1 - w.x, gy1 - w.gy) <= w.r);
}
function pbWallBreak(w) { const i = pbWalls.indexOf(w); if (i >= 0) pbWalls.splice(i, 1); broadcast({ t: 'pbend', id: w.id }); }
function pbAbsorb(attId, x0, gy0, x1, gy1, amt, type, now) {
  const a = players.get(attId);
  for (const w of pbWalls) {
    if (w.owner === attId || now >= w.until) continue;
    const wo = players.get(w.owner); if (a && wo && sameTeam(a, wo)) continue;
    if (!pbWallHit(w, x0, gy0, x1, gy1)) continue;
    w.hp -= type === 'pierce' ? amt * 2 : amt;
    if (w.hp < 0) pbWallBreak(w);
    return true;
  }
  return false;
}
function pbArrowWall(ar, nx, ngy, now) { return ar.dmg > 0 && pbAbsorb(ar.owner, ar.x, ar.gy, nx, ngy, ar.dmg, ar.type, now); }
function pbMeleeWall(t, amount, src, now) {
  const att = src.by || src.kill; if (!att) return false;
  const type = src.type || (att.cls === 'Assassin' || att.gPierce ? 'pierce' : 'phys');
  return pbAbsorb(att.id, src.x, src.y / 0.8, t.x, t.y / 0.8, amount, type, now);
}
const pbPos = p => p.pbSw ? { x: p.pbSw.x, y: p.pbSw.g * 0.8 } : { x: p.x, y: p.y };
const pbOrigin = (p, m) => p.pbSw ? pbPos(p) : originOf(p, m);
function pbTargetPt(m, p) {
  let cx = Number(m && m.cx), cy = Number(m && m.cy) + 30;
  if (!Number.isFinite(cx) || !Number.isFinite(cy)) { cx = p.x + Math.cos(p.aim) * 3 * RADPX; cy = p.y + Math.sin(p.aim) * 3 * RADPX * 0.8; }
  return { x: cx, gy: cy / 0.8 };
}
function pbThrust(p, o, lag, now, len, mult, bleedMs) {
  const a = p.aim, gx = o.x, gy = o.y / 0.8, ex = gx + Math.cos(a) * len, ey = gy + Math.sin(a) * len, hits = [], dmg = Math.round(statsOf(p).dmg * mult);
  broadcast({ t: 'fx', type: 'pbline', x: o.x, y: o.y, a, len, w: PB.hw * 2, dur: 380 });
  for (const t of targetsOf(p)) {
    const tp = posAt(t, now - lag);
    if (segDist(tp.x, tp.y / 0.8, gx, gy, ex, ey) > PB.hw + (t.hr || 0)) continue;
    dmgTo(t, dmg, now, { x: o.x, y: o.y, by: p, type: 'pierce' });
    if (bleedMs) applyBleed(t, bleedMs, now, p);
    hits.push(t);
  }
  checkRoundEnd();
  return hits;
}
function plumAttack(p, m, now) {
  if (now < p.atkReady || p.pbSw) return;
  pbStop(p, now, true);
  const st = statsOf(p), o = originOf(p, m), lag = lagOf(m);
  p.atkReady = now + st.atkCd / atkSpeed(p, now);
  let mult = 1; if (p.pbBonus) { mult = 1.2; p.pbBonus = false; }
  const dmg = Math.round(st.dmg * mult);
  broadcast({ t: 'fx', type: 'smslash', by: p.id, x: o.x, y: o.y, a: p.aim, span: ATK.span, r: ATK.range, aura: 0, echo: 0, pb: 1, dur: 280 });
  let hit = false;
  for (const t of targetsOf(p)) {
    const tp = posAt(t, now - lag);
    if (inConeAt(o.x, o.y, p.aim, tp.x, tp.y, ATK.range, ATK.span, t.hr || 0)) { dmgTo(t, dmg, now, { x: o.x, y: o.y, by: p, basic: true, type: 'phys' }); hit = true; }
  }
  if (hit) pbGain(p, 5 * Math.pow(2, p.pbStage));
  checkRoundEnd();
}
function plumSkill(p, k, m, now) {
  if (!inPlay(p)) return;
  if (k === 'E') {
    if (p.pbRe.e2 && now < p.pbRe.e2.until) return pbReuseE2(p, m, now);
  }
  if (k === 'R' && p.pbRe.r2 && now < p.pbRe.r2.until) return pbReuseR2(p, m, now);
  if (k === 'R' && pbRedirect(p, m, now)) return;
  if (k === 'Q' && p.pbSw) { p.pbSw = null; p.pbCmd = null; broadcast({ t: 'fx', type: 'pbburst', x: p.x, y: p.y, r: 1.2 * RADPX, dur: 600 }); return; }
  if (k === 'Q' && p.pbCh) { pbStop(p, now, false); p.pbCmd = null; return; }
  const win = m && m.mob ? 1500 : PB.cmd + PB.slack;
  p.pbCmd = { k, sp: false, win, until: now + (k === 'Q' ? PB.menu : win) };
}
function plumKey(p, m) {
  const now = Date.now(), c = p.pbCmd;
  if (p.cls !== 'PlumBlossom' || !c || now > c.until || !inPlay(p) || !canAct(p, now)) return;
  if (m.sp) { if (c.k === 'E' && !c.sp && p.pbStage >= 1) { c.sp = true; c.until = now + (c.win || PB.cmd + PB.slack); } return; }
  const n = Number(m.n) | 0;
  if (n < 1 || n > 7 || (c.k !== 'Q' && n > (c.k === 'E' && !c.sp ? 4 : 3)) || (c.k === 'Q' && n > p.pbStage + 1)) return;
  p.pbCmd = null;
  if (c.k === 'Q') pbStart(p, n, now);
  else pbCast(p, (c.k === 'R' ? 'R' : c.sp ? 'S' : 'E') + n, m, now);
}
function pbCast(p, id, m, now) {
  const need = id === 'E4' ? 6 : id[0] === 'E' ? 0 : id[0] === 'S' ? 1 : 2;
  if (p.pbStage < need || (id === 'E4' && p.pbSw)) return false;
  if (now < (p.pbCd[id] || 0)) { fxTxt(p.x, p.y - 40, '쿨타임', '#cfcfcf'); return false; }
  const c = PB.cost[p.pbStage];
  if (p.pbA < c) { fxTxt(p.x, p.y - 40, '내공 부족', '#9fd0ff'); return false; }
  p.pbA -= c; p.pbCd[id] = now + PB.cd[id];
  const o = pbOrigin(p, m), lag = p.pbSw ? 0 : lagOf(m), base = statsOf(p).dmg, mast = p.pbStage >= 3, ult = p.pbStage >= 4;
  const slashAt = (ms, fn) => pbLater(p, ms, fn);
  if (id === 'E4') {
    pbStop(p, now, false);
    p.pbSw = { x: p.x, g: p.y / 0.8, vx: 0, vg: 0, cx: p.x + Math.cos(p.aim) * 3 * RADPX, cg: p.y / 0.8 + Math.sin(p.aim) * 3 * RADPX, hit: {} };
    broadcast({ t: 'fx', type: 'pbburst', x: p.x, y: p.y, r: 1.4 * RADPX, dur: 700 });
  } else if (id === 'E1') {
    broadcast({ t: 'fx', type: 'ring', x: o.x, y: o.y, r: 0.5 * RADPX, c: '#F4AABB', dur: 300 });
    slashAt(100, () => {
      const t0 = Date.now(), a = p.aim, L = 1.5 * RADPX, pp = pbPos(p), gx = pp.x, gy = pp.y / 0.8, ex = gx + Math.cos(a) * L, ey = gy + Math.sin(a) * L;
      broadcast({ t: 'fx', type: 'pbline', x: pp.x, y: pp.y, a, len: L, w: PB.hw * 2, dur: 380, down: 1 });
      for (const t of targetsOf(p)) {
        if (segDist(t.x, t.y / 0.8, gx, gy, ex, ey) > PB.hw + (t.hr || 0)) continue;
        dmgTo(t, Math.round(base), t0, { x: pp.x, y: pp.y, by: p, type: 'phys' });
        if (t.role === 1) t.stunUntil = Math.max(t.stunUntil || 0, t0 + 100);
      }
      checkRoundEnd();
    });
  } else if (id === 'E2') {
    pbThrust(p, o, lag, now, 1 * RADPX, 0.9, 2000);
  } else if (id === 'E3') {
    p.pbBlockUntil = now + PB.blk.ms;
    broadcast({ t: 'fx', type: 'pbfan', ow: p.id, x: o.x, y: o.y, a: p.aim, span: PB.blk.span, r: PB.blk.r, dur: PB.blk.ms });
  } else if (id === 'S1') {
    broadcast({ t: 'fx', type: 'ring', x: o.x, y: o.y, r: 0.5 * RADPX, c: '#F4AABB', dur: 300 });
    slashAt(100, () => spawnArrow(p, pbPos(p), 0, Date.now(), { a: p.aim, dmg: Math.round(base), spd: PB.spd, range: 5 * RADPX, radius: 0.45 * RADPX, kind: 'pbq', type: 'magic' }));
  } else if (id === 'S2') {
    pbZone(p, o, 3 * RADPX, 6 * RADPX, 1500, 0.6, now);
    p.pbRe.e2 = { until: now + 2000 };
  } else if (id === 'S3') {
    const a = p.aim, cx = o.x + Math.cos(a) * 0.9 * RADPX, cgy = o.y / 0.8 + Math.sin(a) * 0.9 * RADPX, h = RADPX, nx = -Math.sin(a) * h, ny = Math.cos(a) * h, wid = ++pbSeq;
    pbWalls.push({ id: wid, owner: p.id, kind: 'seg', x1: cx - nx, gy1: cgy - ny, x2: cx + nx, gy2: cgy + ny, hp: 1000, until: now + 1000 });
    broadcast({ t: 'fx', type: 'pbwall', id: wid, x1: cx - nx, y1: (cgy - ny) * 0.8, x2: cx + nx, y2: (cgy + ny) * 0.8, dur: 1000 });
  } else if (id === 'R1') {
    pbFlurry(p, now, mast, base, ult);
  } else if (id === 'R2') {
    pbZone(p, o, 4 * RADPX, 6 * RADPX, 2000, 0.8, now, true);
    p.pbRe.r2 = { until: now + 2000, left: 2, mast };
    if (ult) for (let i = 1; i <= 8; i++) slashAt(i * 250, () => {
      const pp = pbPos(p), best = pbRandFoe(p, pp, 5 * RADPX);
      if (!best) return;
      const ang = Math.atan2((best.y - pp.y) / 0.8, best.x - pp.x), keep = p.aim; p.aim = ang;
      pbThrust(p, pp, 0, Date.now(), 5 * RADPX, 1.2, 3000);
      p.aim = keep;
    });
    else if (mast) for (const d of [500, 1000]) slashAt(d, () => {
      const pp = pbPos(p), best = pbRandFoe(p, pp, 5 * RADPX);
      if (best) broadcast({ t: 'fx', type: 'pbline', x: pp.x, y: pp.y, a: Math.atan2((best.y - pp.y) / 0.8, best.x - pp.x), len: 5 * RADPX, w: PB.hw * 2, dur: 360, fake: 1 });
    });
  } else if (id === 'R3') {
    const wid = ++pbSeq, hp = 2000 + (mast ? 1000 : 0) + (ult ? 2000 : 0), br = (ult ? 2 : 1) * RADPX;
    pbWalls.push({ id: wid, owner: p.id, kind: 'circ', x: o.x, gy: o.y / 0.8, r: br, hp, until: now + 4000, follow: mast });
    broadcast({ t: 'fx', type: 'pbbarrier', id: wid, ow: p.id, x: o.x, y: o.y, r: br, follow: mast ? 1 : 0, dur: 4000 });
  }
  return true;
}
function pbZone(p, o, w, len, ms, mul, now, fog) {
  const id = ++pbSeq;
  pbZones.push({ id, owner: p.id, gx: o.x, gy: o.y / 0.8, a: p.aim, c: Math.cos(p.aim), s: Math.sin(p.aim), len, w, mul, fog: !!fog, until: now + ms });
  broadcast({ t: 'fx', type: 'pbzone', x: o.x, y: o.y, a: p.aim, len, w, dur: ms });
}
const pbFogZones = () => { const now = Date.now(); return pbZones.filter(z => z.fog && now < z.until); };
function pbInZ(z, x, y, tol) {
  const dx = x - z.gx, dy = y / 0.8 - z.gy, u = dx * z.c + dy * z.s, v = -dx * z.s + dy * z.c;
  return u >= -tol && u <= z.len + tol && Math.abs(v) <= z.w / 2 + tol;
}
function pbBlind(q, now, fz) {
  if (!q.joined || q.role !== 1 || q.obs || phase !== 'round') return null;
  const r = [];
  for (const z of fz) {
    const own = players.get(z.owner); if (!own || own === q || own.role !== 1 || sameTeam(own, q) || rootOf(q) === rootOf(own)) continue;
    if (pbInZ(z, q.x, q.y, 0)) r.push(z);
  }
  return r;
}
function pbEvVisible(e, bz) {
  let x, y;
  if (typeof e.x === 'number' && typeof e.y === 'number') { x = e.x; y = e.y; }
  else if (typeof e.x1 === 'number') { x = e.x1; y = e.y1; }
  else if (e.t === 'hit') { const t = players.get(e.id) || units.get(e.id); if (!t) return true; x = t.x; y = t.y; }
  else if (e.t === 'arrowEnd' && typeof e.ex === 'number') { x = e.ex; y = e.ey; }
  else return true;
  return bz.some(z => pbInZ(z, x, y, 40));
}
function pbRandFoe(p, pp, range) {
  const c = targetsOf(p).filter(t => t.role === 1 && Date.now() >= (t.invisUntil || 0) && Math.hypot(t.x - pp.x, (t.y - pp.y) / 0.8) <= range + (t.hr || 0));
  return c.length ? c[Math.floor(Math.random() * c.length)] : null;
}
function pbFlurry(p, now, mast, base, ult) {
  const spd = PB.spd * (ult ? 1.3 : mast ? 1.2 : 1), nDir = ult ? 16 : 8, fly = p.pbFly = { ids: new Set(), end: now + 600 + 250, redir: null, done: false, mast };
  const fire = (a, dmg, fake, track) => {
    if (!inPlay(p)) return;
    const id = spawnArrow(p, pbPos(p), 0, Date.now(), { a, dmg, spd, range: 6 * RADPX, radius: 0.4 * RADPX, kind: 'pbq', type: 'magic', fake });
    if (track && id) fly.ids.add(id);
  };
  for (let i = 0; i < 8; i++) pbLater(p, i * 200, () => fire(p.aim, Math.round(base * 0.8), false, false));
  for (let r = 0; r < 3; r++) pbLater(p, r * 300, () => {
    for (let i = 0; i < nDir; i++) {
      const pp = pbPos(p);
      let a = Math.random() * Math.PI * 2;
      if (fly.redir) a = Math.atan2(fly.redir.gy - pp.y / 0.8, fly.redir.x - pp.x) + (Math.random() - 0.5) * 0.5;
      fire(a, Math.round(base * 0.4), false, true);
      if (mast) fire(fly.redir ? a + (Math.random() - 0.5) * 0.3 : Math.random() * Math.PI * 2, Math.round(base * 0.5), false, true);
    }
  });
}
function pbRedirect(p, m, now) {
  const fly = p.pbFly;
  if (!fly || !fly.mast || fly.done || now > fly.end) return false;
  if (p.pbA < PB.cost[p.pbStage]) { fxTxt(p.x, p.y - 40, '내공 부족', '#9fd0ff'); return true; }
  p.pbA -= PB.cost[p.pbStage]; fly.done = true;
  const tg = pbTargetPt(m, p); fly.redir = tg;
  for (const id of fly.ids) {
    const ar = arrows.get(id); if (!ar) continue;
    const x = ar.x, y = ar.gy * 0.8, a = Math.atan2(tg.gy - ar.gy, tg.x - ar.x), dmg = ar.dmg, fake = ar.fake;
    endArrow(ar);
    spawnArrow(p, { x, y }, 0, now, { a, dmg, spd: ar.spd, range: 6 * RADPX, radius: ar.radius, kind: 'pbq', type: 'magic', fake });
  }
  return true;
}
function pbReuseE2(p, m, now) {
  if (p.pbA < PB.cost[p.pbStage]) return void fxTxt(p.x, p.y - 40, '내공 부족', '#9fd0ff');
  p.pbA -= PB.cost[p.pbStage]; p.pbRe.e2 = null;
  pbThrust(p, pbOrigin(p, m), p.pbSw ? 0 : lagOf(m), now, 3 * RADPX, 1.0, 2000);
}
function pbReuseR2(p, m, now) {
  const R = p.pbRe.r2;
  if (p.pbA < PB.cost[p.pbStage]) return void fxTxt(p.x, p.y - 40, '내공 부족', '#9fd0ff');
  p.pbA -= PB.cost[p.pbStage]; R.left--;
  const o = pbOrigin(p, m), hits = pbThrust(p, o, p.pbSw ? 0 : lagOf(m), now, (4 + (R.mast ? 1 : 0)) * RADPX, 1.2, 3000);
  if (R.left > 0) return;
  p.pbRe.r2 = null; pbStop(p, now, false);
  let dest, a = p.aim;
  if (hits.length) {
    let t = hits[0], bd = Infinity;
    for (const h of hits) { const dd = Math.hypot(h.x - o.x, (h.y - o.y) / 0.8); if (dd < bd) { bd = dd; t = h; } }
    dest = { x: t.x + Math.cos(a) * 0.9 * RADPX, y: t.y + Math.sin(a) * 0.9 * RADPX * 0.8 };
  } else dest = { x: o.x + Math.cos(a) * 4 * RADPX, y: o.y + Math.sin(a) * 4 * RADPX * 0.8 };
  dest = clampArena(dest, { x: o.x, y: o.y });
  broadcast({ t: 'fx', type: 'dash', x: p.x, y: p.y, x2: dest.x, y2: dest.y, c: 'rgba(244,170,187,.7)', dur: 380 });
  if (p.pbSw) { p.pbSw.x = dest.x; p.pbSw.g = dest.y / 0.8; p.pbSw.vx = p.pbSw.vg = 0; }
  else { p.x = dest.x; p.y = dest.y; send(p.ws, { t: 'warp', x: dest.x, y: dest.y }); }
  broadcast({ t: 'fx', type: 'pbburst', x: dest.x, y: dest.y, r: 1.1 * RADPX, dur: 600 });
}
function plumBot(p, foe, now) {
  if (p.pbRe.e2 && now < p.pbRe.e2.until) return pbReuseE2(p, {}, now);
  if (p.pbRe.r2 && now < p.pbRe.r2.until) return pbReuseR2(p, {}, now);
  const ids = ['E1', 'E2', 'E3', 'S1', 'S2', 'S3', 'R1', 'R2', 'R3'].filter(i => now >= (p.pbCd[i] || 0) && p.pbStage >= (i[0] === 'E' ? 0 : i[0] === 'S' ? 1 : 2) && p.pbA >= PB.cost[p.pbStage]);
  if (ids.length) pbCast(p, ids[Math.floor(Math.random() * ids.length)], { cx: foe.x, cy: foe.y - 24 }, now);
}
function pbSend(p, now) {
  const cmd = p.pbCmd && now < p.pbCmd.until ? p.pbCmd : null;
  const key = [p.pbD, p.pbA, p.pbStage, p.pbCh ? p.pbCh.t : 0, cmd ? cmd.k + (cmd.sp ? 's' : '') + cmd.until : '', p.pbBonus ? 1 : 0, Object.values(p.pbCd).join(','), p.pbRe.e2 ? p.pbRe.e2.until : 0, p.pbRe.r2 ? p.pbRe.r2.until + ':' + p.pbRe.r2.left : 0, p.pbFly && p.pbFly.mast && !p.pbFly.done ? p.pbFly.end : 0].join('|');
  if (key === p.pbKey) return;
  p.pbKey = key;
  const cds = {}; for (const k in p.pbCd) { const r = p.pbCd[k] - now; if (r > 0) cds[k] = Math.round(r); }
  const re = { e: p.pbRe.e2 && now < p.pbRe.e2.until ? Math.round(p.pbRe.e2.until - now) : 0, r: p.pbRe.r2 && now < p.pbRe.r2.until ? Math.round(p.pbRe.r2.until - now) : 0, rl: p.pbRe.r2 ? p.pbRe.r2.left : 0, f: p.pbFly && p.pbFly.mast && !p.pbFly.done && now < p.pbFly.end ? Math.round(p.pbFly.end - now) : 0 };
  send(p.ws, { t: 'pb', d: p.pbD, a: p.pbA, s: p.pbStage, ch: p.pbCh ? p.pbCh.t : 0, cmd: cmd ? cmd.k + (cmd.sp ? 's' : '') : '', cm: cmd ? Math.round(cmd.until - now) : 0, cds, re, bn: p.pbBonus ? 1 : 0 });
}
const PB_SW = { vmax: 1500, hitR: 0.5 * RADPX, dmg: 300, rehit: 300 };
function pbSwordStep(p, dt, now) {
  const S = p.pbSw, ex = S.cx - S.x, eg = S.cg - S.g, d = Math.hypot(ex, eg), k = Math.min(1, dt * 6);
  const want = d > 1 ? Math.min(PB_SW.vmax, d * 7) : 0;
  S.vx += ((d > 1 ? ex / d * want : 0) - S.vx) * k; S.vg += ((d > 1 ? eg / d * want : 0) - S.vg) * k;
  const sp0 = Math.hypot(S.vx, S.vg);
  S.x += S.vx * dt; S.g += S.vg * dt;
  const nx = (S.x - CX) / RX, ny = (S.g * 0.8 - CY) / RY, nd = ndist(nx, ny);
  if (nd > 1) { S.x = CX + nx / nd * RX; S.g = (CY + ny / nd * RY) / 0.8; S.vx = S.vg = 0; }
  const dmg = Math.round(PB_SW.dmg * Math.min(1, sp0 / PB_SW.vmax));
  if (dmg < 1) return;
  for (const t of targetsOf(p)) {
    if ((S.hit[t.id] || 0) > now) continue;
    if (Math.hypot(t.x - S.x, t.y / 0.8 - S.g) > PB_SW.hitR + (t.hr || 0) + 24) continue;
    S.hit[t.id] = now + PB_SW.rehit;
    dmgTo(t, dmg, now, { x: S.x, y: S.g * 0.8, by: p, type: 'magic', fixed: true });
    S.vx = S.vg = 0;
    broadcast({ t: 'fx', type: 'pbburst', x: S.x, y: S.g * 0.8, r: 0.7 * RADPX, dur: 450 });
    checkRoundEnd();
    break;
  }
}
function stepPlum(dt, now) {
  for (let i = pbTimers.length - 1; i >= 0; i--) {
    const T = pbTimers[i]; if (now < T.at) continue;
    pbTimers.splice(i, 1);
    const o = players.get(T.owner);
    if (o && inPlay(o)) { try { T.fn(); } catch (e) { console.error('pb timer:', e.message); } }
  }
  for (let i = pbZones.length - 1; i >= 0; i--) {
    const z = pbZones[i], own = players.get(z.owner);
    if (now >= z.until || !own || !inPlay(own)) { pbZones.splice(i, 1); continue; }
    const c = Math.cos(z.a), s = Math.sin(z.a);
    for (const t of targetsOf(own)) {
      const dx = t.x - z.gx, dy = t.y / 0.8 - z.gy, u = dx * c + dy * s, v = -dx * s + dy * c;
      if (u < 0 || u > z.len || Math.abs(v) > z.w / 2) continue;
      t.pbSlowMul = now < (t.pbSlowUntil || 0) ? Math.min(t.pbSlowMul, z.mul) : z.mul; t.pbSlowUntil = now + 120;
    }
  }
  for (let i = pbWalls.length - 1; i >= 0; i--) {
    const w = pbWalls[i], own = players.get(w.owner);
    if (now >= w.until || !own || !inPlay(own)) { pbWalls.splice(i, 1); continue; }
    if (w.follow) {
      const fp = pbPos(own), dx = fp.x - w.x, dy = fp.y / 0.8 - w.gy, d = Math.hypot(dx, dy), st = Math.min(d, 450 * dt);
      if (d > 0.01) { w.x += dx / d * st; w.gy += dy / d * st; }
    }
    if (w.kind === 'circ') for (const q of players.values()) {
      if (q.id === w.owner || !inPlay(q)) continue;
      const dx = q.x - w.x, dy = q.y / 0.8 - w.gy, d = Math.hypot(dx, dy);
      if (d >= w.r) continue;
      const ux = d > 0.01 ? dx / d : 1, uy = d > 0.01 ? dy / d : 0;
      q.x = w.x + ux * (w.r + 1); q.y = (w.gy + uy * (w.r + 1)) * 0.8;
      if (solidMap()) { const c2 = snapWalk(q.x, q.y); q.x = c2.x; q.y = c2.y; }
    }
  }
  for (const p of players.values()) {
    if (p.cls !== 'PlumBlossom') continue;
    if (!inPlay(p)) { p.pbCh = null; p.pbResume = null; p.pbCmd = null; p.pbRe = {}; p.pbFly = null; p.pbBlockUntil = 0; p.pbSw = null; continue; }
    if (p.pbSw) pbSwordStep(p, dt, now);
    if (p.pbCmd && now > p.pbCmd.until) p.pbCmd = null;
    const ch = p.pbCh;
    if (ch) {
      const T = PB_Q[ch.t];
      if (!T.mobile && (p.moving || p.dash || now < p.kbUntil)) pbStop(p, now, false);
      else {
        while (now >= ch.next) {
          ch.next += T.iv;
          if (T.en) pbGain(p, T.en);
          if (T.hp) heal(p, T.hp);
          ch.n = (ch.n || 0) + 1;
          if (T.heal && ch.n % (T.healEvery || 1) === 0) heal(p, (p.mh - p.hp) * T.heal);
        }
        if (ch.t === 7) { p.pbBn += dt * 1000; if (p.pbBn >= 5000) { p.pbBn -= 5000; p.pbBonus = true; } }
      }
    } else if (p.pbResume && now >= p.pbResume.at && canAct(p, now)) pbStart(p, 7, now);
    pbSend(p, now);
  }
}

// ---- Reaper ----
const REAPER = { chargeMs: 1500, rMax: 1.5 * RADPX, rMin: 0.2, dmg: [50, 270], soul: [0.05, 0.30], maxSouls: 5, collect: 0.7 * RADPX, atkPw: 0.7, R: { cd: 25000 } };
const sendReap = p => send(p.ws, { t: 'reap', s: (p.souls || []).map(x => x.c), q: (p.souls || []).map(x => x.pw >= 1 ? 1 : 0) });
function stepSouls() {
  if (!soulOrbs.size || phase !== 'round') return;
  for (const p of players.values()) {
    if (p.cls !== 'Reaper' || p.skel || !p.joined || p.role !== 1) continue;
    for (const s of soulOrbs.values()) {
      if (p.souls.length >= REAPER.maxSouls) break;
      if (s.o && s.o !== p.id) continue;
      if (Math.hypot(s.x - p.x, (s.y - p.y) / 0.8) > REAPER.collect) continue;
      soulOrbs.delete(s.id); p.souls.push({ c: s.cls, pw: s.pw }); sendReap(p);
    }
  }
}
function reaperAttack(p, m, now) {
  if (!p.chargeStart) return;
  const ch = Math.min(Math.max(now - p.chargeStart, 1), REAPER.chargeMs), f = ch / REAPER.chargeMs;
  p.chargeStart = 0;
  if (now < p.atkReady - 60) return;
  p.atkReady = now + statsOf(p).atkCd;
  const lag = lagOf(m), r = REAPER.rMax * (REAPER.rMin + (1 - REAPER.rMin) * f);
  const dmg = Math.round(REAPER.dmg[0] + (REAPER.dmg[1] - REAPER.dmg[0]) * f), chance = REAPER.soul[0] + (REAPER.soul[1] - REAPER.soul[0]) * f;
  broadcast({ t: 'fx', type: 'disc', by: p.id, x: p.x, y: p.y, r, rm: REAPER.rMax, c: 'rgba(140,140,140,.38)', s: '#d8d8d8', dur: 350 });
  for (const t of targetsOf(p)) {
    const tp = posAt(t, now - lag);
    if (Math.hypot(tp.x - p.x, (tp.y - p.y) / 0.8) > r + (t.hr || 0)) continue;
    dmgTo(t, dmg, now, { x: p.x, y: p.y, by: p, basic: true });
    if (!t.unit && !t.skel && t.cls && t.role === 1 && Math.random() < chance) dropSoul(t.x, t.y, t.cls, p.id, REAPER.atkPw);
  }
  checkRoundEnd();
}
function summonSkeleton(p, cls, now, big, hp, pw) {
  const id = nextId++, sk = mkPlayer(id, null);
  let ex = (p.x + Math.cos(p.aim) * 70 - CX) / RX, ey = (p.y + Math.sin(p.aim) * 70 * 0.8 - CY) / RY; const dd = ndist(ex, ey);
  if (dd > 0.95) { ex *= 0.95 / dd; ey *= 0.95 / dd; }
  Object.assign(sk, { x: CX + ex * RX, y: CY + ey * RY, skel: p.id, name: '해골', cls, hue: p.hue, joined: true, role: 1, inRound: false, team: p.team || 0, titles: [], eq: null, skins: [], eqs: {}, gold: 0 });
  if (solidMap()) { const q = snapWalk(sk.x, sk.y); sk.x = q.x; sk.y = q.y; }
  sk.lx = sk.x; sk.ly = sk.y;
  resetCombat(sk);
  sk.pw = pw;
  if (big) { sk.sz = 1.5; sk.mh = sk.hp = Math.round(hp); sk.hr = 18; sk.noR = true; }
  else { sk.sz = 1; sk.mh = sk.hp = Math.round(sk.hp * pw); sk.hr = 0; sk.noR = true; }
  sk.atkReady = now + 600;
  players.set(id, sk);
  return sk;
}
function reaperSkill(p, k, m, now) {
  if (k === 'Q') return;
  if (!(p.souls || []).length) { if (!p.skel && !p.ai) fxTxt(p.x, p.y, '영혼 없음', '#cfcfcf'); return; }
  if (k === 'E') {
    const s = p.souls.pop(); sendReap(p);
    summonSkeleton(p, s.c, now, false, 0, s.pw);
    broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 0.8 * RADPX, c: '#b69cff', dur: 500 });
  } else {
    const list = p.souls.slice(); p.souls = []; sendReap(p);
    p.cdR = now + REAPER.R.cd; send(p.ws, { t: 'cd', k: 'R', ms: REAPER.R.cd });
    const hp = list.reduce((a, s) => a + statsBase({ cls: s.c, lf: '' }).hp * s.pw, 0), pw = list.reduce((a, s) => a + s.pw, 0) / list.length;
    summonSkeleton(p, list[list.length - 1].c, now, true, hp, pw);
    broadcast({ t: 'fx', type: 'ring', x: p.x, y: p.y, r: 1.6 * RADPX, c: '#8a5cff', dur: 800 });
  }
}
// ---- AI players ----
const CLASS_LIST = ['Knight', 'Archer', 'Shielder', 'Assassin', 'Gumiho', 'Lucifer', 'Gambler', 'SwordMaster', 'Tower', 'Financier', 'Gamer', 'Celestial', 'Reaper', 'Berserker', 'PlumBlossom'];
const BOT_RANGE = { Knight: 95, Archer: 520, Shielder: 95, Assassin: 90, Gumiho: 340, Lucifer: 340, Gambler: 420, SwordMaster: 95, Tower: 100, Financier: 95, Gamer: 95, Celestial: 95, Reaper: 130, Berserker: 95, PlumBlossom: 95 };
const nextBotNo = () => { const used = new Set([...players.values()].filter(q => q.ai).map(q => q.name)); let n = 1; while (used.has('AI ' + n)) n++; return n; };
const randClass = cur => { const l = CLASS_LIST.filter(c => c !== cur); return l[Math.floor(Math.random() * l.length)]; };
function addBot(cls, iq) {
  if (players.size >= MAX_PLAYERS) return null;
  const id = nextId++, p = mkPlayer(id, null);
  p.ai = true; p.iq = Number.isInteger(iq) && iq >= 0 && iq <= 10 ? iq : 5; p.aiRand = cls === 'random'; p.name = 'AI ' + nextBotNo(); p.user = null; p.joined = true; p.ready = true; p.gold = 0; p.skins = []; p.eqs = {};
  p.cls = p.aiRand ? randClass('') : cls; resetCombat(p);
  players.set(id, p); return p;
}
function removeBot(q) {
  if (bossId === q.id) bossId = 0;
  players.delete(q.id); broadcast({ t: 'leave', id: q.id });
  if (phase === 'lobby') checkReady(); else if (phase === 'round') checkRoundEnd();
}
const iqOf = p => p.skel ? 5 : Number.isInteger(p.iq) ? p.iq : 5;
function velOf(t, now) {
  const h = t.hist; if (!h || h.length < 2) return { x: 0, y: 0 };
  let a = h[0]; for (const e of h) if (e.t >= now - 250) { a = e; break; }
  const dt = (now - a.t) / 1000; return dt < 0.05 ? { x: 0, y: 0 } : { x: (t.x - a.x) / dt, y: (t.y - a.y) / dt };
}
function botTick(now) {
  if (phase !== 'round') return;
  for (const p of players.values()) {
    if (!p.ai && !p.skel) continue;
    if (p.role !== 1) { p.dx = p.dy = 0; continue; }
    if (now < (p.botT || 0)) continue;
    const iq = iqOf(p);
    p.botT = now + Math.round(380 - iq * 32);
    let foe = null, fs = Infinity, fd = Infinity;
    for (const t of targetsOf(p)) {
      if (now < (t.invisUntil || 0)) continue;
      const d = Math.hypot(t.x - p.x, (t.y - p.y) / 0.8), sc = d - (iq >= 7 && t.mh ? (1 - t.hp / t.mh) * 150 : 0);
      if (sc < fs) { fs = sc; fd = d; foe = t; }
    }
    if (!foe) { p.dx = p.dy = 0; continue; }
    const vx = foe.x - p.x, vy = (foe.y - p.y) / 0.8, d = fd || 1, R = BOT_RANGE[p.cls] || 95;
    let mx = 0, my = 0;
    if (iq > 0) {
      if (d > R * 0.85) { const q = steer(p, foe, vx / d, vy / d, now); mx = q.x; my = q.y; }
      else if (R > 200 && iq >= 3 && d < R * 0.45) { mx = -vx / d; my = -vy / d; }
      else if (iq >= 4) { if (now > (p.botSg || 0)) { p.botSg = now + 900 + Math.random() * 900; p.botDir = Math.random() < 0.5 ? -1 : 1; } mx = -vy / d * (p.botDir || 1); my = vx / d * (p.botDir || 1); }
      if (iq >= 7) for (const ar of arrows.values()) {
        const ow = players.get(ar.owner);
        if (!ow || rootOf(ow) === rootOf(p) || sameTeam(p, ow)) continue;
        const ex = p.x - ar.x, ey = p.y / 0.8 - ar.gy, c = Math.cos(ar.a), sn = Math.sin(ar.a), al = ex * c + ey * sn, pp = -ex * sn + ey * c;
        if (al > 0 && al < 380 && Math.abs(pp) < 70) { const sg = pp >= 0 ? 1 : -1; mx = -sn * sg; my = c * sg; break; }
      }
    }
    p.dx = Math.abs(mx) > 0.38 ? Math.sign(mx) : 0; p.dy = Math.abs(my) > 0.38 ? Math.sign(my) : 0;
    let ax = vx, ay = vy;
    if (iq >= 6) { const v = velOf(foe, now), lt = Math.min(0.35, d / 800) * (iq - 5) / 5; ax += v.x * lt; ay += v.y / 0.8 * lt; }
    setAim(p, Math.atan2(ay, ax) + (Math.random() - 0.5) * (10 - iq) * 0.05);
    if (iq > 0 && d <= R) {
      if (p.cls === 'Archer' || p.cls === 'Reaper') {
        if (!p.chargeStart) { if (now >= p.atkReady - 60 && canAct(p, now)) { p.chargeStart = now; p.botCh = 300 + iq * 150 + Math.random() * 300; } }
        else if (now - p.chargeStart >= p.botCh) doAttack(p, {});
      } else doAttack(p, {});
    }
    if (iq > 0 && now >= (p.botSk || 0)) {
      p.botSk = now + 3600 - iq * 300 + Math.random() * (2400 - iq * 180);
      if (Math.random() < 0.35 + iq * 0.065) {
        if (p.cls === 'PlumBlossom') plumBot(p, foe, now); else {
        const ks = ['Q', 'E', 'R'].filter(k => now >= p['cd' + k] && !(k === 'R' && (p.noR || p.skel)) && !(k === 'Q' && p.cls === 'Reaper'));
        if (ks.length && d <= Math.max(R * 1.6, 260)) doSkill(p, ks[Math.floor(Math.random() * ks.length)], { cx: foe.x, cy: foe.y - 24 });
        }
      }
    }
  }
}
wss.on('connection', (ws, req) => {
  const ip = clientIp(req), ipN = ipConns.get(ip) || 0;
  if (players.size >= MAX_SOCKETS || ipN >= MAX_PER_IP) { send(ws, { t: 'full' }); return ws.close(); }
  ipConns.set(ip, ipN + 1);
  const id = nextId++;
  const p = mkPlayer(id, ws);
  players.set(id, p);
  const authTimer = setTimeout(() => { if (!(p.user || p.guest)) { try { ws.close(); } catch (e) {} } }, AUTH_TIMEOUT);
  pruneChat();
  send(ws, { t: 'hello', v: PROTO, id, map: mapId, scale: mapScale, rt: ROUND_MS, mode: gameMode, arena: { CX, CY, RX, RY }, pred: predCfg() });
  send(ws, { t: 'history', log: chatLog.map(c => ({ name: c.name, text: c.text, sys: c.sys ? 1 : 0, age: Date.now() - c.ts })) });

  ws.on('pong', () => { p.alive = true; p.missed = 0; if (p.pingAt) { const r = Date.now() - p.pingAt; p.rtt = p.rtt ? p.rtt * 0.7 + r * 0.3 : r; } });
  ws.on('message', raw => {
    const tn = Date.now();
    p.tok = Math.min(RATE_BURST, (p.tok === undefined ? RATE_BURST : p.tok) + (tn - (p.tokT || tn)) / 1000 * RATE_PER_S); p.tokT = tn;
    if (p.tok < 1) { if ((p.flood = (p.flood || 0) + 1) > 400) { try { ws.close(); } catch (e) {} } return; }
    p.tok -= 1; if (p.tok > RATE_BURST / 2) p.flood = 0;
    let m; try { m = JSON.parse(raw); } catch { return; }
    if (!m || typeof m !== 'object') return;
    if (m.rt !== undefined) m.rt = Math.min(Math.max(0, Number(m.rt) || 0), (p.rtt || 80) + 40);
    for (const k of ['x', 'y', 'cx', 'cy']) if (m[k] !== undefined) { const v = Number(m[k]); m[k] = Number.isFinite(v) ? Math.max(-300, Math.min(MAP + 300, v)) : undefined; }
    if (m.t === 'signup' || m.t === 'login' || m.t === 'resume' || m.t === 'guest') {
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
      if ((phase === 'lobby' || p.role === 2 || p.obs) && CLASS_LIST.includes(m.cls)) {
        if (!clsOk(p, m.cls)) { send(ws, { t: 'cbuy', ok: 0, msg: '잠긴 클래스입니다. 클래스 선택창에서 해금해 주세요.', cls: m.cls }); sendCinfo(p); }
        else { p.cls = m.cls; resetCombat(p); }
      }
    } else if (m.t === 'mode') {
      if (p.user === ADMIN_ID && phase === 'lobby' && (m.m === 'ffa' || m.m === 'team' || m.m === 'boss') && m.m !== gameMode) {
        if (gameMode === 'boss' || m.m === 'boss') for (const q of players.values()) q.team = 0;
        bossId = 0; gameMode = m.m; broadcast({ t: 'mode', m: gameMode }); sysChat(p.name + ' changed the game mode to ' + (gameMode === 'team' ? 'Team' : gameMode === 'boss' ? 'Boss Battle' : 'Free-for-All') + '.');
      }
    } else if (m.t === 'team') {
      const q = players.get(Number(m.id));
      if (p.user === ADMIN_ID && gameMode === 'team' && phase === 'lobby' && q && q.joined && !q.obs && [0, 1, 2].includes(m.team)) { q.team = m.team; sysChat(q.name + (q.team ? ' joined the ' + TEAM_NAME[q.team] + ' team.' : ' left their team.')); }
    } else if (m.t === 'bleed') {
      const q = players.get(Number(m.id));
      if (p.user === ADMIN_ID && phase === 'round' && q && q.joined && q.role === 1) applyBleed(q, 5000, Date.now(), null);
    } else if (m.t === 'boss') {
      const q = players.get(Number(m.id));
      if (p.user === ADMIN_ID && gameMode === 'boss' && phase === 'lobby' && q && q.joined && !q.obs && !q.skel) { bossId = bossId === q.id ? 0 : q.id; sysChat(bossId ? q.name + ' is the Boss.' : 'Boss designation cleared.'); }
    } else if (m.t === 'aiadd') {
      if (p.user === ADMIN_ID && phase === 'lobby' && (m.cls === 'random' || CLASS_LIST.includes(m.cls))) { const b = addBot(m.cls, m.iq); if (b) { sysChat(p.name + ' added ' + b.name + '.'); checkReady(); } }
    } else if (m.t === 'aiset') {
      const q = players.get(Number(m.id));
      if (p.user === ADMIN_ID && phase === 'lobby' && q && q.ai) {
        if (Number.isInteger(m.iq) && m.iq >= 0 && m.iq <= 10) q.iq = m.iq;
        if (m.cls === 'random' || CLASS_LIST.includes(m.cls)) {
          const same = m.cls === 'random' ? q.aiRand : (!q.aiRand && q.cls === m.cls);
          if (!same) { q.aiRand = m.cls === 'random'; q.cls = q.aiRand ? randClass(q.cls) : m.cls; resetCombat(q); }
        }
      }
    } else if (m.t === 'aidel') {
      const q = players.get(Number(m.id));
      if (p.user === ADMIN_ID && q && q.ai) { sysChat(q.name + ' was removed.'); removeBot(q); }
    } else if (m.t === 'kick') {
      const q = players.get(Number(m.id));
      if (p.user === ADMIN_ID && q && q.ai) { sysChat(q.name + ' was removed.'); removeBot(q); }
      else if (p.user === ADMIN_ID && q && q !== p && q.joined && !q.skel) { sysChat(q.name + ' was kicked.'); send(q.ws, { t: 'kicked' }); try { q.ws.close(); } catch (e) {} }
    } else if (m.t === 'map') {
      if (p.user === ADMIN_ID && phase === 'lobby' && Number.isInteger(m.id) && ARENAS[m.id] && m.id !== mapId) { setMap(m.id); sysChat(p.name + ' changed the map.'); }
    } else if (m.t === 'mapscale') {
      const sc = Number(m.s);
      if (p.user === ADMIN_ID && phase === 'lobby' && [1, 1.5, 2].includes(sc) && sc !== mapScale) { setScale(sc); sysChat(p.name + ' set the map size to ' + sc + 'x.'); }
    } else if (m.t === 'roundtime') {
      const mn = Math.floor(Number(m.min)), sc = Math.floor(Number(m.sec));
      if (p.user === ADMIN_ID && phase === 'lobby' && Number.isFinite(mn) && Number.isFinite(sc) && mn >= 0 && mn <= 60 && sc >= 0 && sc <= 59) {
        const ms = (mn * 60 + sc) * 1000;
        if (ms >= 10000 && ms <= 3600000) { ROUND_MS = ms; saveMapCfg(); broadcast({ t: 'rtime', ms }); sysChat(p.name + ' set the game time to ' + mn + 'm ' + sc + 's.'); }
        else send(ws, { t: 'rtime', ms: ROUND_MS, err: 1 });
      } else send(ws, { t: 'rtime', ms: ROUND_MS, err: 1 });
    } else if (m.t === 'aiclear') {
      if (p.user === ADMIN_ID) { const bs = [...players.values()].filter(q => q.ai); if (bs.length) { for (const q of bs) removeBot(q); sysChat(p.name + ' removed all AI players.'); } }
    } else if (m.t === 'pbc') {
      const S = p.pbSw, x = Number(m.x), y = Number(m.y);
      if (S && Number.isFinite(x) && Number.isFinite(y)) { S.cx = x; S.cg = (y + 30) / 0.8; }
    } else if (m.t === 'tequip') {
      equipTitle(p, m.id === null ? null : m.id).catch(e => console.error('equip:', e.message));
    } else if (m.t === 'buy') {
      buySkin(p, m.id, m.price).catch(e => { console.error('buy:', e.message); send(ws, { t: 'buy', ok: 0, msg: '구매 중 오류가 발생했습니다.' }); });
    } else if (m.t === 'cbuy') {
      buyClass(p, m.cls, m.price).catch(e => { console.error('cbuy:', e.message); send(ws, { t: 'cbuy', ok: 0, msg: '구매 중 오류가 발생했습니다.' }); });
    } else if (m.t === 'skequip') {
      equipSkin(p, m.id).catch(e => console.error('skequip:', e.message));
    } else if (m.t === 'shopprice') {
      if (p.user === ADMIN_ID) setShopPrice(p, m);
    } else if (m.t === 'glist' || m.t === 'gset' || m.t === 'gadd') {
      if (p.user === ADMIN_ID) adminGoldQ(p, m).catch(e => { console.error('admin gold:', e.message); send(ws, { t: 'gadmin', ok: 0, msg: '서버 오류가 발생했습니다.' }); });
    } else if (m.t === 'tgrant' || m.t === 'tlist' || m.t === 'trevoke') {
      if (p.user === ADMIN_ID) adminTitle(p, m).catch(e => { console.error('admin title:', e.message); send(ws, { t: 'tadmin', ok: 0, msg: '서버 오류가 발생했습니다.' }); });
    } else if (m.t === 'charge') {
      const now = Date.now();
      if ((p.cls === 'Archer' || p.cls === 'Reaper') && canAct(p, now) && now >= p.atkReady - 60) p.chargeStart = now;
    } else if (m.t === 'ccancel') {
      p.chargeStart = 0;
    } else if (m.t === 'atk') {
      if (m.a !== undefined) setAim(p, Number(m.a));
      doAttack(p, m);
    } else if (m.t === 'skill') {
      if (m.a !== undefined) setAim(p, Number(m.a));
      doSkill(p, String(m.k), m);
    } else if (m.t === 'pbk') {
      if (m.a !== undefined) setAim(p, Number(m.a));
      plumKey(p, m);
    } else if (m.t === 'ready') {
      if (phase !== 'lobby' || joinedList().length < 2) return;
      p.ready = !p.ready; checkReady();
    }
  });
  ws.on('close', () => {
    clearTimeout(authTimer);
    const ic = (ipConns.get(ip) || 1) - 1; if (ic <= 0) ipConns.delete(ip); else ipConns.set(ip, ic);
    if (bossId === id) bossId = 0;
    players.delete(id); broadcast({ t: 'leave', id });
    if (phase === 'lobby') checkReady(); else if (phase === 'round') checkRoundEnd();
  });
  ws.on('error', () => {});
});

let last = Date.now(), lastAiChk = 0;
const tickStat = { n: 0, sum: 0, max: 0, slowAt: 0, errAt: 0 };
function tickErr(e) { const t = Date.now(); if (t - tickStat.errAt > 5000) { tickStat.errAt = t; console.error('tick error:', (e && e.stack) || e); } }
function autoClearAi() {
  let humans = 0; const bots = [];
  for (const q of players.values()) { if (q.ai) bots.push(q); else if ((q.user || q.guest) && !q.obs && !q.skel && q.ws && q.ws.readyState === 1) humans++; }
  if (!humans && bots.length) { for (const q of bots) removeBot(q); console.log('No human players left: removed ' + bots.length + ' AI player(s).'); }
}
const SLIM_KEYS = ['m', 'r', 'ai', 'ar', 'skl', 'so', 'su', 'gd', 'sl', 'hs', 'iv', 'hn', 'ta', 'kb', 'ds', 'mk', 'as', 'cm', 'bn', 'qn', 'lb', 'dm', 'cg', 'rl', 'mt', 'gb', 'fs', 'sa', 'smn', 'smx', 'sk', 'tr', 'ins', 'dp', 'gm', 'sn', 'iq', 'bs', 'bm', 'rg', 'ax', 'bu', 'bd'];
setInterval(() => {
  const now = Date.now(), dt = Math.min((now - last) / 1000, 0.1); last = now;
  let needEnd = false;
  try {
  if (now - lastAiChk > 2000) { lastAiChk = now; autoClearAi(); }
  botTick(now);
  for (const p of players.values()) {
    if (!p.joined) continue;
    let { dx, dy } = p;
    if (p.role === 2 || now < p.stunUntil || now < p.charmUntil) { dx = dy = 0; p.chargeStart = 0; }
    if (p.dash) {
      const D = p.dash;
      if (!inPlay(p)) p.dash = null;
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
    if (p.bleedUntil) stepBleed(p, now);
    if (now < p.kbUntil && inPlay(p)) {
      const sx0 = p.x, sy0 = p.y; p.x += p.kbx * dt; p.y += p.kby * dt * 0.8;
      const nx = (p.x - CX) / RX, ny = (p.y - CY) / RY, d = ndist(nx, ny);
      if (d > 1) { p.x = CX + nx / d * RX; p.y = CY + ny / d * RY; }
      if (solidMap()) { const q = slideTo(sx0, sy0, p.x, p.y); p.x = q.x; p.y = q.y; }
    }
    if (dx || dy) {
      const l = Math.hypot(dx, dy); dx /= l; dy /= l;
      const spd = SPEED * (now < p.guardUntil ? KNIGHT.E.speed : 1) * (now < p.slowUntil ? KNIGHT.R.slow : 1) * tauntMul * (now < p.hornUntil ? SHIELDER.R.speed : 1) * ((p.cls === 'Assassin' || (p.cls === 'Gamer' && p.gInvis)) && now < p.invisUntil ? ASSASSIN.E.speed : 1) * (now < (p.pbSlowUntil || 0) ? p.pbSlowMul : 1) * (now < p.libUntil ? LUC.lib.speed : 1) * (now < p.fastUntil ? GAMBLER.R.fast : 1) * (p.bm || 1);
      const sx0 = p.x, sy0 = p.y; p.x += dx * spd * dt; p.y += dy * spd * dt * 0.8;
      const nx = (p.x - CX) / RX, ny = (p.y - CY) / RY, d = ndist(nx, ny);
      if (d > 1) { p.x = CX + nx / d * RX; p.y = CY + ny / d * RY; }
      if (solidMap()) { const q = slideTo(sx0, sy0, p.x, p.y); p.x = q.x; p.y = q.y; }
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
  stepUnits(dt, now); stepBalls(now); stepCelestial(dt, now); stepGamer(now); stepSouls(); stepBerserker(dt, now); stepPlum(dt, now); placeDummies();
  } catch (e) { tickErr(e); }
  try {
  const list = [], hidden = [];
  for (const p of players.values()) {
    if (!p.joined) continue;
    const iv = now < p.invisUntil;
    if (iv && !p.wasIv) { p.hideX = p.x; p.hideY = p.y; }
    p.wasIv = iv;
    const e = { id: p.id, name: p.name, hue: p.hue, x: Math.round(p.x * 10) / 10, y: Math.round(p.y * 10) / 10,
      f: p.face, a: Math.round(p.aim * 100) / 100, m: p.moving ? 1 : 0, c: p.cls, r: p.ready ? 1 : 0, o: p.role, tm: p.team || 0, ai: p.ai ? 1 : 0, ar: p.aiRand ? 1 : 0, skl: p.skel ? 1 : 0, so: p.skel || 0, sz: p.sz || 1,
      hp: Math.max(0, Math.round(p.hp)), mh: Math.round(p.mh), su: Math.max(0, p.stunUntil - now), gd: now < p.guardUntil ? 1 : 0, sl: now < p.slowUntil ? 1 : 0,
      hs: now < p.hasteUntil ? 1 : 0, iv: iv ? 1 : 0, hn: now < p.hornUntil ? 1 : 0, ta: p.role === 1 && now < p.tauntUntil ? 1 : 0, kb: now < p.kbUntil ? 1 : 0, ds: p.dash ? 1 : 0,
      mk: now < p.markUntil ? 1 : 0, as: now < p.asUntil ? p.asBonus : 0, cm: p.role === 1 && now < p.charmUntil ? 1 : 0, bn: p.role === 1 && now < p.burnUntil ? 1 : 0, qn: (p.qNext || p.eNext) ? 1 : 0, lf: p.lf || '', lb: now < p.libUntil ? 1 : 0, dm: p.role === 1 && now < p.dmUntil ? 1 : 0,
      cg: p.chargeStart ? Math.max(1, Math.round(Math.min(now - p.chargeStart, chargeMax(p, now)) / chargeMax(p, now) * ARCHER.charge.maxMs)) : 0,
      rl: p.reloadUntil && now < p.reloadUntil ? 1 : 0, mt: p.myTurn ? 1 : 0, gb: now < p.gbUntil || now < p.gbPlusUntil ? 1 : 0, fs: now < p.fastUntil ? 1 : 0, sa: p.smAura ? 1 : 0, smn: p.cls === 'SwordMaster' ? p.smN | 0 : 0, smx: p.cls === 'SwordMaster' ? smNeed(p, now) : 0, sk: now < p.smAwkUntil ? 1 : 0, tr: now < p.towerRUntil ? 1 : 0, ins: now < p.insUntil ? 1 : 0, dp: now < p.depUntil ? 1 : 0, gm: p.gNext | 0, sn: skinOf(p), gt: now < p.gtUntil ? p.gtint : '', iq: p.ai ? iqOf(p) : 0, bs: p.id === bossId ? 1 : 0, bm: p.bm || 0, rg: bRage(p) ? 1 : 0, ax: p.cls === 'Berserker' && p.axes && p.role === 1 ? p.axes.map(a => [a.s, Math.round(a.x), Math.round(a.y)]) : 0, bu: buffsOf(p, now), bd: now < (p.bleedUntil || 0) ? 1 : 0 };
    for (const k of SLIM_KEYS) if (e[k] === 0) delete e[k];
    if (p.cls === 'PlumBlossom') { e.pbs = p.pbStage + 1; if (p.pbCh) e.pbc = p.pbCh.t; if (now < (p.pbBlockUntil || 0)) e.pbk = 1; if (p.pbSw) e.psw = [Math.round(p.pbSw.x), Math.round(p.pbSw.g * 0.8), Math.round(Math.hypot(p.pbSw.vx, p.pbSw.vg)), +Math.atan2(p.pbSw.vg * 0.8, p.pbSw.vx).toFixed(2)]; }
    if (p.role === 1 && now < (p.pbSlowUntil || 0)) e.pz = p.pbSlowMul;
    list.push(e);
    hidden.push(iv ? Object.assign({}, e, { x: Math.round(p.hideX * 10) / 10, y: Math.round(p.hideY * 10) / 10, a: 0, m: 0, cg: 0, bu: 0, bd: 0 }) : e);
  }
  for (const u of units.values()) {
    const e = { id: u.id, name: '', hue: 0, x: Math.round(u.x * 10) / 10, y: Math.round(u.y * 10) / 10, f: u.face, a: Math.round(u.aim * 100) / 100, m: u.moving ? 1 : 0, c: u.cls, ut: u.ut, ow: u.owner, sn: players.has(u.owner) ? skinOf(players.get(u.owner)) : 0, r: 0, o: 1,
      hp: Math.max(0, Math.round(u.hp)), mh: u.mh, su: Math.max(0, u.stunUntil - now), sl: now < u.slowUntil ? 1 : 0, kb: now < u.kbUntil ? 1 : 0 };
    list.push(e); hidden.push(e);
  }
  const ff = [];
  for (const p of players.values()) if (p.joined) for (const f of p.fires) ff.push({ id: f.id, o: p.id, x: Math.round(f.x), y: Math.round(f.y) });
  const sb = [...soulOrbs.values()].map(s => ({ id: s.id, x: Math.round(s.x), y: Math.round(s.y), c: s.cls, o: s.o }));
  const head = { t: 'state', ph: phase, left: phase === 'round' ? Math.max(0, ROUND_MS - (now - roundStart)) : 0, ff, sb };
  if (phase !== 'round') head.dmy = dummies.map(d => { const live = now - d.lastT < 3000; return [d.id, Math.round(d.x), Math.round(d.y), live ? d.sum : 0, d.last, live ? 1 : 0]; });
  const fz = pbFogZones();
  if (!fz.length && !list.some(e => e.iv)) { const msg = JSON.stringify(Object.assign(head, { p: list })); for (const q of players.values()) if (q.ws && (q.user || q.guest)) sendState(q.ws, msg); return; }
  const common = JSON.stringify(Object.assign({}, head, { p: hidden }));
  for (const q of players.values()) {
    if (!q.ws || q.ws.readyState !== 1 || !(q.user || q.guest)) continue;
    const self = q.joined && now < q.invisUntil, bz = fz.length ? pbBlind(q, now, fz) : null;
    if (bz && bz.length) {
      const inZ = (x, y) => bz.some(z => pbInZ(z, x, y, 30));
      let pl = self ? hidden.map((e, i) => list[i].id === q.id ? list[i] : e) : hidden;
      pl = pl.filter(e => (e.id === q.id && !e.ut) || e.ow === q.id || e.so === q.id || inZ(e.x, e.y));
      sendState(q.ws, JSON.stringify(Object.assign({}, head, { p: pl, ff: ff.filter(f => f.o === q.id || inZ(f.x, f.y)), sb: sb.filter(b => inZ(b.x, b.y)), fg: bz.map(z => [Math.round(z.gx), Math.round(z.gy * 0.8), +z.a.toFixed(3), z.len, z.w]) })));
    } else if (self) sendState(q.ws, JSON.stringify(Object.assign({}, head, { p: hidden.map((e, i) => list[i].id === q.id ? list[i] : e) })));
    else sendState(q.ws, common);
  }
  } catch (e) { tickErr(e); }
  finally {
    const ms = Date.now() - now; tickStat.n++; tickStat.sum += ms; if (ms > tickStat.max) tickStat.max = ms;
    if (ms > 40 && now - tickStat.slowAt > 10000) { tickStat.slowAt = now; console.warn('slow tick: ' + ms + 'ms'); }
  }
}, 1000 / TICK);
setInterval(() => {
  const h = [...players.values()].filter(q => (q.user || q.guest) && !q.ai && !q.skel).length, a = [...players.values()].filter(q => q.ai).length;
  console.log('stats: humans=' + h + ' ai=' + a + ' phase=' + phase + ' ticks=' + tickStat.n + ' avgTick=' + (tickStat.n ? (tickStat.sum / tickStat.n).toFixed(2) : 0) + 'ms maxTick=' + tickStat.max + 'ms sockets=' + players.size);
  tickStat.n = tickStat.sum = tickStat.max = 0;
}, 5 * 60 * 1000).unref();

setInterval(() => {
  const now = Date.now();
  for (const p of players.values()) {
    if (!p.ws) continue;
    if ((p.missed = (p.missed || 0) + 1) > 5) { p.ws.terminate(); continue; }
    p.pingAt = now; try { p.ws.ping(); } catch (e) {}
  }
}, 5000);

process.on('uncaughtException', e => console.error('uncaughtException:', (e && e.stack) || e));
process.on('unhandledRejection', e => console.error('unhandledRejection:', (e && e.stack) || e));
let shuttingDown = false;
async function shutdown(sig) {
  if (shuttingDown) return; shuttingDown = true; console.log(sig + ': shutting down');
  setTimeout(() => process.exit(0), 5000).unref();
  try { for (const p of players.values()) { try { if (p.ws) p.ws.close(1001); } catch (e) {} } await winSave; server.close(); } catch (e) { console.error('shutdown:', e.message); }
  process.exit(0);
}
process.on('SIGTERM', () => shutdown('SIGTERM')); process.on('SIGINT', () => shutdown('SIGINT'));
server.listen(PORT, () => console.log('Geolgani PvP running on port ' + PORT));
