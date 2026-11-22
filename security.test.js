process.env.AUTH_TIMEOUT_MS = '1500';
const { D, port, mk, tx, sleep, ok, done, get, WebSocket } = require('./harness');
(async () => {
  // static server
  let r = await get('/', { 'Accept-Encoding': 'gzip' });
  ok(r.status === 200 && r.headers['content-encoding'] === 'gzip' && r.headers.etag, 'static: gzip + etag');
  ok(r.headers['x-content-type-options'] === 'nosniff' && /default-src/.test(r.headers['content-security-policy'] || ''), 'static: security headers');
  const r2 = await get('/', { 'If-None-Match': r.headers.etag });
  ok(r2.status === 304, 'static: 304 on matching etag');
  const r3 = await get('/..%2fserver.js'); ok(r3.status === 403, 'static: traversal blocked (' + r3.status + ')');
  const r4 = await get('/..%2fpublic-evil%2fx'); ok(r4.status === 403 || r4.status === 404, 'static: sibling-prefix blocked');
  // XFF: rightmost hop is used
  const x = await mk(null, null, { 'X-Forwarded-For': '6.6.6.6, 7.7.7.7' });
  ok(D.ipConns.has('7.7.7.7') && !D.ipConns.has('6.6.6.6'), 'ip: uses the proxy-appended (rightmost) address');
  x.ws.close();
  // per-IP connection cap
  const socks = []; for (let i = 0; i < 9; i++) socks.push(await mk(null, null, { 'X-Forwarded-For': '8.8.8.8' }));
  ok(socks.slice(0, 8).every(c => !c.raw.some(m => m.t === 'full')) && socks[8].raw.some(m => m.t === 'full'), 'per-IP cap rejects the 9th socket');
  socks.forEach(c => c.ws.close()); await sleep(200);
  // auth timeout
  const idle = await mk(null, null, { 'X-Forwarded-For': '5.5.5.5' }); await sleep(2200);
  ok(idle.closed, 'unauthenticated socket closed after timeout');
  // flood control
  const fl = await mk('flooder1', 'pw123456', { 'X-Forwarded-For': '4.4.4.4' }); const before = fl.m.filter(m => m.t === 'pong').length;
  for (let i = 0; i < 1200; i++) { try { tx(fl, { t: 'ping', c: i }); } catch (e) {} }
  await sleep(600); const pongs = fl.m.filter(m => m.t === 'pong').length - before;
  ok(pongs < 500 && fl.closed, 'flood limited (' + pongs + ' of 1200 answered, closed=' + fl.closed + ')');
  // per-IP login lock, other IP unaffected
  const vic = await mk('victimx1', 'rightpass1', { 'X-Forwarded-For': '3.3.3.3' });
  const bad = async ip => { const c = await mk(null, null, { 'X-Forwarded-For': ip }); tx(c, { t: 'login', id: 'victimx1', pw: 'wrongpass' }); await sleep(450); const m = c.m.filter(m => m.t === 'auth' && !m.ok).pop(); c.ws.close(); return m && m.err; };
  let last; for (let i = 0; i < 9; i++) last = await bad('2.2.2.2');
  ok(/너무 많/.test(last || ''), 'login locked for the attacking IP');
  const other = await bad('2.2.2.3'); ok(other && !/너무 많/.test(other), 'other IP not locked out');
  vic.ws.close(); await sleep(200);
  // events are batched
  const a = await mk('batcha1', 'pw123456', { 'X-Forwarded-For': '1.1.1.1' }), b = await mk('batchb1', 'pw123456', { 'X-Forwarded-For': '1.1.1.2' });
  tx(a, { t: 'class', cls: 'PlumBlossom' }); tx(b, { t: 'class', cls: 'Knight' }); await sleep(200); tx(a, { t: 'ready' }); tx(b, { t: 'ready' }); await sleep(3000);
  const P = D.players.get(a.id); P.pbStage = 4; P.pbD = P.pbA = 700; a.raw.length = 0;
  tx(a, { t: 'skill', k: 'R', a: 0 }); await sleep(40); tx(a, { t: 'pbk', n: 1 }); await sleep(900);
  ok(a.raw.some(m => m.t === 'ev' && m.l.length > 3) && a.m.filter(m => m.t === 'arrow').length > 20, 'projectile events arrive batched');
  // kill gold: AI victim gives none, human victim gives 5
  const Vh = D.players.get(b.id); P.gold = 0; P.guest = true; P.user = null; D.getPhase();
  Vh.hp = 1; Vh.lastBy = P.id; Vh.lastByT = Date.now(); D.dmgTo(Vh, 50, Date.now(), { by: P, basic: true }); await sleep(150);
  ok(P.gold === 5, 'human kill awards 5 gold');
  const bot = D.addBot('Knight', 3); bot.role = 1; bot.hp = 1; bot.lastBy = P.id; bot.lastByT = Date.now(); P.gold = 0; D.dmgTo(bot, 50, Date.now(), { by: P, basic: true }); await sleep(150);
  ok(P.gold === 0, 'killing an AI awards no gold');
  // AI auto-clear when no human players remain
  a.ws.close(); b.ws.close(); await sleep(300);
  D.addBot('Knight', 3); D.addBot('Archer', 3); await sleep(2600);
  ok([...D.players.values()].filter(p => p.ai).length === 0, 'AI auto-removed when no humans are connected');
  done();
})();
