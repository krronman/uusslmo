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

wss.on('connection', ws => {
  if (players.size >= MAX_PLAYERS) { send(ws, { t: 'full' }); return ws.close(); }
  const id = nextId++;
  const a = Math.random() * Math.PI * 2, r = Math.random() * 0.5;
  const p = { id, ws, name: 'Player' + id, hue: Math.floor(Math.random() * 360),
    x: CX + Math.cos(a) * RX * r, y: CY + Math.sin(a) * RY * r, face: 1, dx: 0, dy: 0, lastChat: 0, alive: true, joined: false, cls: '', ready: false };
  players.set(id, p);
  send(ws, { t: 'hello', id, arena: { CX, CY, RX, RY } });

  ws.on('pong', () => { p.alive = true; });
  ws.on('message', raw => {
    let m; try { m = JSON.parse(raw); } catch { return; }
    if (m.t === 'join') { p.name = clean(m.name, 14) || p.name; p.joined = true; return; }
    if (!p.joined) return;
    if (m.t === 'input') {
      p.dx = Math.sign(Number(m.dx) || 0); p.dy = Math.sign(Number(m.dy) || 0);
    } else if (m.t === 'chat') {
      const now = Date.now(), text = clean(m.text, 60);
      if (text && now - p.lastChat > 800) { p.lastChat = now; broadcast({ t: 'chat', id, text }); }
    } else if (m.t === 'class') {
      if (['Knight', 'Archer', 'Shielder', 'Assassin'].includes(m.cls)) p.cls = m.cls;
    } else if (m.t === 'ready') {
      p.ready = !p.ready; checkReady();
    }
  });
  ws.on('close', () => { players.delete(id); broadcast({ t: 'leave', id }); checkReady(); });
  ws.on('error', () => {});
});
function checkReady() {
  const list = [...players.values()].filter(p => p.joined);
  if (!list.length || !list.every(p => p.ready)) return;
  list.forEach((p, i) => {
    const a = -Math.PI / 2 + i * 2 * Math.PI / list.length;
    p.x = CX + Math.cos(a) * RX * 0.92;
    p.y = CY + Math.sin(a) * RY * 0.92;
    p.dx = p.dy = 0; p.ready = false;
  });
  broadcast({ t: 'arrange' });
}

// Authoritative simulation
let last = Date.now();
setInterval(() => {
  const now = Date.now(), dt = Math.min((now - last) / 1000, 0.1); last = now;
  const list = [];
  for (const p of players.values()) {
    if (!p.joined) continue;
    let { dx, dy } = p;
    const moving = !!(dx || dy);
    if (moving) {
      const l = Math.hypot(dx, dy); dx /= l; dy /= l;
      p.x += dx * SPEED * dt; p.y += dy * SPEED * dt * 0.8;
      if (dx) p.face = dx > 0 ? 1 : -1;
      const nx = (p.x - CX) / RX, ny = (p.y - CY) / RY, d = Math.hypot(nx, ny);
      if (d > 1) { p.x = CX + nx / d * RX; p.y = CY + ny / d * RY; }
    }
    list.push({ id: p.id, name: p.name, hue: p.hue, x: Math.round(p.x * 10) / 10, y: Math.round(p.y * 10) / 10, f: p.face, m: moving ? 1 : 0, c: p.cls, r: p.ready ? 1 : 0 });
  }
  broadcast({ t: 'state', p: list });
}, 1000 / TICK);

// Drop dead connections
setInterval(() => {
  for (const p of players.values()) {
    if (!p.alive) { p.ws.terminate(); continue; }
    p.alive = false; p.ws.ping();
  }
}, 30000);

server.listen(PORT, () => console.log('Sky Colosseum running on port ' + PORT));
