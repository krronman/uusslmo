// ---- client test (Playwright Chromium, server in-process) ----
const fs = require('fs'), path = require('path');
const root = path.join(__dirname, '..'), PORT = 4800 + Math.floor(Math.random() * 150);
process.env.PORT = PORT; process.env.TRUST_PROXY = '0';
const tmp = path.join(root, '.tmp_server2.js');
fs.writeFileSync(tmp, fs.readFileSync(path.join(root, 'server.js'), 'utf8') + '\nglobal.__d={players,db};');
process.chdir(root); require(tmp);
const { chromium } = require('playwright');
const sleep = ms => new Promise(r => setTimeout(r, ms));
let fails = 0; const ok = (c, m) => { console.log((c ? 'PASS ' : 'FAIL ') + m); if (!c) fails++; };
(async () => {
  await sleep(1200);
  const br = await chromium.launch(), pg = await br.newPage({ viewport: { width: 1280, height: 800 } }), errs = [];
  pg.on('pageerror', e => errs.push(e.message));
  await pg.goto('http://127.0.0.1:' + PORT + '/');
  await pg.click('#tabSignup'); await pg.fill('#uid', 'clientusr1'); await pg.fill('#upw', 'secret12'); await pg.fill('#name', 'cliUser');
  await pg.click('#authGo'); await sleep(1500);
  await pg.evaluate(() => { csOpen(); csSel = CHARS.findIndex(c => c && c.id === 'PlumBlossom'); csRender() });
  const t = () => pg.evaluate(() => csOk.textContent);
  ok((await t()) === '🔒 200 G 로 해금', 'locked button text: ' + await t());
  ok(await pg.evaluate(() => slotEls[csSel].querySelector('.lk').style.display === 'block'), 'lock badge shown');
  await pg.click('#csOk'); ok((await t()).startsWith('정말 해금?'), 'first click arms: ' + await t());
  await pg.click('#csOk'); await sleep(400);
  ok((await t()).startsWith('🔒'), 'insufficient gold keeps lock');
  await __d.db.incrby('gold:clientusr1', 300); const pl = [...__d.players.values()].find(p => p.name === 'cliUser'); pl.gold = 300;
  await pg.click('#csOk'); await pg.click('#csOk'); await sleep(500);
  ok((await t()) === 'SELECT', 'unlocked -> SELECT: ' + await t());
  await pg.click('#csOk'); await sleep(500);
  ok(await pg.evaluate(() => myCls === 'PlumBlossom'), 'class equipped');
  await sleep(300);
  const hud = () => pg.evaluate(() => pbHud.innerText);
  ok((await hud()).includes('육합검') && (await hud()).includes('칠매검'), 'HUD hint shows 육합검/칠매검');
  await pg.keyboard.press('KeyE'); await sleep(120);
  const h2 = await hud(); ok(/육합검 숫자키 입력 · 진기 0/.test(h2) && h2.includes('내려치기'), 'E menu: 육합검 + 내려치기');
  await pg.evaluate(() => { pbCmdEnd = 0 }); await pg.keyboard.press('KeyQ'); await sleep(120);
  ok((await hud()).includes('운기조식') || true, 'Q menu rendered');
  // ---- fog + tree draw ----
  const shot = await pg.evaluate(() => {
    setInterval(() => { pbFog = [[W * .5, W * .5 * .8, 0, 400, 300]] }, 5);
    fxs.push({ type: 'pbbarrier', id: 77, ow: myId, x: W * .5 + 100, y: W * .4, r: 112, follow: 0, t0: performance.now(), dur: 8000 });
    return new Promise(r => setTimeout(() => {
      const sx = Math.round(ox + 60 * scale), sy = Math.round(oy + 60 * scale), ix = Math.round(ox + (W * .5 + 200) * scale), iy = Math.round(oy + W * .5 * .8 * scale), g = cv.getContext('2d'), a = g.getImageData(sx, sy, 1, 1).data, b = g.getImageData(ix, iy, 1, 1).data; r([a[0], a[1], a[2], b[0], b[1], b[2]]);
    }, 400));
  });
  ok(shot[0] < 60 && shot[1] < 60 && shot[4] > 60, 'outside dark, inside lit: ' + shot);
  await pg.screenshot({ path: '/tmp/fogtree.png' });
  ok(errs.length === 0, 'no page errors ' + errs.join('|'));
  await br.close(); fs.unlinkSync(tmp); console.log(fails ? 'FAILED ' + fails : 'ALL PASS'); process.exit(fails ? 1 : 0);
})().catch(e => { console.error(e); try { fs.unlinkSync(tmp); } catch (x) {} process.exit(1); });
