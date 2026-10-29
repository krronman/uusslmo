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
const GRACE = 5000, SHRINK = 40000;        // round: 5s full arena, then a 40s shrinking safe zone
const chatLog = [];                        // {name,text,ts,sys}
let phase = 'lobby', roundStart = 0, deathCounter = 0;

const joinedList = () => [...players.values()].filter(p => p.joined);
const zoneScale = el => el < GRACE ? 1 : Math.max(0, 1 - (el - GRACE) / SHRINK);

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
  phase = 'round'; roundStart = Date.now();
  parts.forEach((p, i) => {
    const a = -Math.PI / 2 + i * 2 * Math.PI / parts.length;   // evenly spaced on the outer edge
    p.lx = p.x; p.ly = p.y;
    p.x = CX + Math.cos(a) * RX * 0.92; p.y = CY + Math.sin(a) * RY * 0.92;
    p.dx = p.dy = 0; p.role = 1; p.inRound = true; p.ready = false; p.deathOrder = 0;
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
function endRound(winner) {
  phase = 'lobby';
  for (const p of players.values()) {
    if (p.inRound) { p.x = p.lx; p.y = p.ly; }      // back to where they were in the lobby
    p.role = 0; p.inRound = false; p.ready = false; p.dx = p.dy = 0;
  }
  broadcast({ t: 'tp' });
  if (winner) { sysChat('🏆 1st place: ' + winner.name); broadcast({ t: 'winner', name: winner.name }); }
  else sysChat('Round ended with no winner.');
}

// ================= connections =================
wss.on('connection', ws => {
  if (players.size >= MAX_PLAYERS) { send(ws, { t: 'full' }); return ws.close(); }
  const id = nextId++;
  const a = Math.random() * Math.PI * 2, r = Math.random() * 0.5;
  const p = { id, ws, name: 'Player' + id, hue: Math.floor(Math.random() * 360),
    x: CX + Math.cos(a) * RX * r, y: CY + Math.sin(a) * RY * r, face: 1, dx: 0, dy: 0, lastChat: 0, alive: true,
    joined: false, cls: '', ready: false, role: 0, inRound: false, lx: 0, ly: 0, deathOrder: 0 };
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
    if (!p.joined) return;
    if (m.t === 'input') {
      p.dx = Math.sign(Number(m.dx) || 0); p.dy = Math.sign(Number(m.dy) || 0);
    } else if (m.t === 'chat') {
      const now = Date.now(), text = clean(m.text, 60);
      if (text && now - p.lastChat > 800) { p.lastChat = now; addChat({ id, name: p.name, text }); }
    } else if (m.t === 'class') {
      if (['Knight', 'Archer', 'Shielder', 'Assassin'].includes(m.cls)) p.cls = m.cls;
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
  const z = phase === 'round' ? zoneScale(now - roundStart) : 1;
  const dying = [];
  for (const p of players.values()) {
    if (!p.joined) continue;
    let { dx, dy } = p;
    if (p.role === 2) dx = dy = 0;
    if (dx || dy) {
      const l = Math.hypot(dx, dy); dx /= l; dy /= l;
      p.x += dx * SPEED * dt; p.y += dy * SPEED * dt * 0.8;
      if (dx) p.face = dx > 0 ? 1 : -1;
      const nx = (p.x - CX) / RX, ny = (p.y - CY) / RY, d = Math.hypot(nx, ny);
      if (d > 1) { p.x = CX + nx / d * RX; p.y = CY + ny / d * RY; }
    }
    p.moving = !!(dx || dy);
    if (phase === 'round' && p.role === 1) {
      const out = z <= 0 || Math.hypot((p.x - CX) / (RX * z), (p.y - CY) / (RY * z)) > 1;
      if (out) dying.push({ p, d: Math.hypot((p.x - CX) / RX, (p.y - CY) / RY) });
    }
  }
  if (dying.length) {                       // farthest from the center dies first
    dying.sort((a, b) => b.d - a.d);
    for (const { p } of dying) { p.role = 2; p.dx = p.dy = 0; p.moving = false; p.deathOrder = ++deathCounter; }
    checkRoundEnd();
  }
  const list = [];
  for (const p of players.values()) {
    if (!p.joined) continue;
    list.push({ id: p.id, name: p.name, hue: p.hue, x: Math.round(p.x * 10) / 10, y: Math.round(p.y * 10) / 10,
      f: p.face, m: p.moving ? 1 : 0, c: p.cls, r: p.ready ? 1 : 0, o: p.role });
  }
  broadcast({ t: 'state', ph: phase, z: phase === 'round' ? z : 1, p: list });
}, 1000 / TICK);

// Drop dead connections
setInterval(() => {
  for (const p of players.values()) {
    if (!p.alive) { p.ws.terminate(); continue; }
    p.alive = false; p.ws.ping();
  }
}, 30000);

server.listen(PORT, () => console.log('Sky Colosseum running on port ' + PORT));
