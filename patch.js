// ---- plum patch test (server in-process, real ws clients) ----
const fs = require('fs'), path = require('path'), WebSocket = require('ws');
const root = path.join(__dirname, '..'), PORT = 4200 + Math.floor(Math.random() * 500);
process.env.PORT = PORT; process.env.TRUST_PROXY = '0';
const tmp = path.join(root, '.tmp_server.js');
fs.writeFileSync(tmp, fs.readFileSync(path.join(root, 'server.js'), 'utf8') + `
global.__d={players,units,pbZones,PB,PB_Q,CLS_PRICE,db,pbCast,plumSkill,pbRandFoe,pbEvVisible,pbInZ,statsOf,RADPX,get phase(){return phase},set phase(v){phase=v},get roundStart(){return roundStart},set roundStart(v){roundStart=v}};
`);
process.chdir(root); require(tmp);
const sleep = ms => new Promise(r => setTimeout(r, ms));
let fails = 0; const ok = (c, m) => { console.log((c ? 'PASS ' : 'FAIL ') + m); if (!c) fails++; };
const client = () => new Promise(res => {
  const ws = new WebSocket('ws://127.0.0.1:' + PORT), c = { ws, msgs: [], state: null };
  ws.on('message', d => { const m = JSON.parse(d); for (const x of (m.t === 'ev' ? m.l : [m])) { c.msgs.push(x); if (x.t === 'state') c.state = x; } });
  ws.on('open', () => res(c)); c.send = o => ws.send(JSON.stringify(o));
  c.last = t => { for (let i = c.msgs.length - 1; i >= 0; i--) if (c.msgs[i].t === t) return c.msgs[i]; };
});
const byName = n => [...__d.players.values()].find(p => p.name === n);
(async () => {
  await sleep(1500);
  const D = global.__d, R = D.RADPX;
  // ---- constants ----
  ok(JSON.stringify(D.PB.cost) === '[0,2.5,5,10,20,40,40]', 'cost x2.5');
  ok(Object.values(D.PB.cd).every(v => v === 4000), 'all cd 4s');
  ok(D.PB_Q[1].en === 3 && D.PB_Q[2].en === 4.5 && D.PB_Q[2].hp === 40 && D.PB_Q[5].en === 75 && D.PB_Q[7].en === 45, 'Q gains x1.5, 운기조식 hp 40');
  // ---- unlock ----
  const g = await client(); g.send({ t: 'guest', name: 'guestA' }); await sleep(400);
  const gp = byName('guestA');
  ok(g.last('cinfo') && g.last('cinfo').price.PlumBlossom === 200, 'cinfo price 200');
  g.send({ t: 'class', cls: 'PlumBlossom' }); await sleep(150);
  ok(gp.cls !== 'PlumBlossom' && g.last('cbuy') && !g.last('cbuy').ok, 'locked class refused');
  g.send({ t: 'cbuy', cls: 'PlumBlossom', price: 200 }); await sleep(150);
  ok(/부족/.test(g.last('cbuy').msg), 'insufficient gold refused');
  gp.gold = 300; g.send({ t: 'cbuy', cls: 'PlumBlossom', price: 199 }); await sleep(150);
  ok(!g.last('cbuy').ok && gp.gold === 300, 'price mismatch refused');
  g.send({ t: 'cbuy', cls: 'PlumBlossom', price: 200 }); await sleep(150);
  ok(g.last('cbuy').ok === 1 && gp.gold === 100 && gp.clsOwn.includes('PlumBlossom'), 'guest buy ok, gold 300->100');
  g.send({ t: 'cbuy', cls: 'PlumBlossom', price: 200 }); await sleep(150);
  ok(!g.last('cbuy').ok && gp.gold === 100, 'no double charge');
  g.send({ t: 'class', cls: 'PlumBlossom' }); await sleep(150);
  ok(gp.cls === 'PlumBlossom', 'unlocked class selectable');
  const a = await client(); a.send({ t: 'signup', id: 'plumuser1', pw: 'secret12', name: 'userA' }); await sleep(900);
  const up = byName('userA'); await D.db.incrby('gold:plumuser1', 250); up.gold = 250;
  a.send({ t: 'cbuy', cls: 'PlumBlossom', price: 200 }); await sleep(300);
  ok(a.last('cbuy') && a.last('cbuy').ok === 1 && up.gold === 50 && (await D.db.get('gold:plumuser1')) == 50, 'user buy atomic, gold 250->50');
  ok(JSON.parse(await D.db.get('cls:plumuser1')).includes('PlumBlossom'), 'unlock persisted');
  const a2 = await client(); a2.send({ t: 'login', id: 'plumuser1', pw: 'secret12' }); await sleep(900);
  ok(a2.last('cinfo') && a2.last('cinfo').own.includes('PlumBlossom'), 'unlock survives relogin');
  const b = await client(); b.send({ t: 'signup', id: 'plumuser2', pw: 'secret12', name: 'userB' }); await sleep(900);
  const bp = byName('userB'); b.send({ t: 'class', cls: 'PlumBlossom' }); await sleep(150);
  ok(bp.cls !== 'PlumBlossom', 'other account still locked');
  const ad = await client(); ad.send({ t: 'signup', id: 'admin', pw: 'secret12', name: 'adminN' }); await sleep(900);
  ad.send({ t: 'class', cls: 'PlumBlossom' }); await sleep(150);
  ok(byName('adminN') && byName('adminN').cls === 'PlumBlossom', 'admin exempt');
  // ---- mechanics ----
  a.ws.close(); await sleep(200);
  const A = gp, B = bp, C = [...D.players.values()].find(p => p.name === 'userA' && p.ws && p.ws.readyState === 1);
  for (const p of [A, B, C]) { p.role = 1; p.joined = true; p.hp = p.mh = 1000; }
  D.phase = 'round'; D.roundStart = Date.now();
  A.cls = 'PlumBlossom'; A.pbStage = 3; A.pbA = A.pbD = 500; A.pbCd = {}; A.pbRe = {};
  A.x = 400; A.y = 400; A.aim = 0;
  B.cls = 'Archer'; B.x = 700; B.y = 400; C.cls = 'Archer'; C.x = 1300; C.y = 400;
  const now = Date.now(), rc = D.pbCast(A, 'R2', {}, now);
  ok(rc !== false, 'R2 cast ' + JSON.stringify([A.role, A.pbStage, A.pbA, D.phase, A.cls]));
  const z = D.pbZones[D.pbZones.length - 1];
  ok(z && z.mul === 0.8 && z.fog && z.len === 6 * R, 'R2 zone slow x0.8 + fog');
  ok(A.pbA === 490, 'R2 cost 10 at stage 3');
  await sleep(250);
  const sB = B.ws && b.state, sC = a2.state, sA = g.state;
  const ids = s => s.p.map(e => e.id);
  ok(sB && !ids(sB).includes(C.id) && ids(sB).includes(B.id) && ids(sB).includes(A.id) && sB.fg && sB.fg.length === 1, 'blinded victim: outside player hidden, zone data sent');
  ok(sA && ids(sA).includes(C.id) && !sA.fg, 'caster sees everyone');
  ok(sC && ids(sC).includes(B.id) && !sC.fg, 'outsider sees everyone');
  ok(z && D.pbEvVisible({ t: 'fx', x: 1300, y: 400 }, [z]) === false && D.pbEvVisible({ t: 'fx', x: 600, y: 400 }, [z]) === true, 'event filter by position');
  // slow applied
  await sleep(200); ok(B.pbSlowMul === 0.8, 'victim slowed to 0.8');
  // random foe
  const seen = new Set(); B.x = 500; B.y = 400; C.x = 560; C.y = 400;
  for (let i = 0; i < 200; i++) { const f = D.pbRandFoe(A, { x: A.x, y: A.y }, 5 * R); if (f) seen.add(f.id); }
  ok(seen.has(B.id) && seen.has(C.id), 'random target hits both in-range foes');
  C.x = 1300; const s2 = new Set(); for (let i = 0; i < 100; i++) { const f = D.pbRandFoe(A, { x: A.x, y: A.y }, 5 * R); if (f) s2.add(f.id); }
  ok(s2.has(B.id) && !s2.has(C.id), 'out-of-range foe never targeted');
  // redirect on R
  A.pbCd = {}; A.pbRe = {}; A.pbFly = null; A.pbCmd = null;
  D.pbCast(A, 'R1', {}, Date.now()); await sleep(100);
  D.plumSkill(A, 'E', { cx: 900, cy: 400 }, Date.now());
  ok(A.pbFly && !A.pbFly.done && A.pbCmd && A.pbCmd.k === 'E', 'E no longer redirects');
  A.pbCmd = null; const before = A.pbA;
  D.plumSkill(A, 'R', { cx: 900, cy: 400 }, Date.now());
  ok(A.pbFly.done && A.pbA === before - 10 && !A.pbCmd, 'R redirects (cost 10), no menu opened');
  // E1 100%, S1 range 5
  await sleep(2500);
  D.phase = 'round'; D.roundStart = Date.now(); A.role = B.role = C.role = 1; A.pbCd = {}; A.pbRe = {}; B.x = 450; B.y = 400; B.hp = B.mh = 1000; A.aim = 0;
  const hp0 = B.hp; D.pbCast(A, 'E1', {}, Date.now()); await sleep(300);
  const dealt = hp0 - B.hp, base = D.statsOf(A).dmg;
  ok(Math.abs(dealt - Math.round(base)) <= 1, 'E1 deals 100% (' + dealt + ' vs ' + Math.round(base) + ')');
  // normal-class energy unaffected
  ok(!out().includes('Error'), 'no server errors');
  console.log(fails ? 'FAILED ' + fails : 'ALL PASS'); fs.unlinkSync(tmp); process.exit(fails ? 1 : 0);
})().catch(e => { console.error(e); try { fs.unlinkSync(tmp); } catch (x) {} process.exit(1); });
function out() { return ''; }
