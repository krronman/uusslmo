const fs = require('fs'), path = require('path'), http = require('http');
const WebSocket = require('ws');
const port = 9000 + Math.floor(Math.random() * 900);
process.env.PORT = port; process.env.TRUST_PROXY = '1';
const root = path.join(__dirname, '..'), tmp = path.join(root, '.server.test.js');
const EXPOSE = `\nglobal.__d={players,arrows,pbWalls,pbZones,PB,statsOf,CX:()=>CX,CY:()=>CY,RADPX,getPhase:()=>phase,dmgTo,spawnArrow,pbStop,pbGain,ms:()=>mapScale,MAPv:()=>MAP,units,getArena:()=>({CX,CY,RX,RY}),ipConns,db,winsData,tickStat,autoClearAi,addBot,removeBot};\n`;
fs.writeFileSync(tmp, fs.readFileSync(path.join(root, 'server.js'), 'utf8') + EXPOSE);
process.on('exit', () => { try { fs.unlinkSync(tmp); } catch (e) {} });
require(tmp);
const D = global.__d, sleep = ms => new Promise(r => setTimeout(r, ms));
function mk(name, pw, headers) {
  return new Promise(res => {
    const ws = new WebSocket('ws://localhost:' + port, { headers: headers || {} }), c = { ws, id: 0, m: [], raw: [], closed: false };
    ws.on('message', r => { const m = JSON.parse(r); c.raw.push(m); if (m.t === 'ev') for (const x of m.l) c.m.push(x); else c.m.push(m); if (m.t === 'hello') c.id = m.id; });
    ws.on('close', () => { c.closed = true; });
    ws.on('open', () => { if (!name) return setTimeout(() => res(c), 150); ws.send(JSON.stringify({ t: 'signup', id: name, pw: pw || 'pw123456', name })); setTimeout(() => res(c), 350); });
  });
}
const tx = (c, o) => c.ws.send(JSON.stringify(o));
const fail = [];
const ok = (c, m) => { if (!c) { fail.push(m); console.log('FAIL', m); } else console.log('ok', m); };
const done = () => { console.log(fail.length ? 'FAILED: ' + fail.join('; ') : 'ALL OK'); process.exit(fail.length ? 1 : 0); };
function get(p, headers) {
  return new Promise((res, rej) => http.get({ port, path: p, headers: headers || {} }, r => { const ch = []; r.on('data', d => ch.push(d)); r.on('end', () => res({ status: r.statusCode, headers: r.headers, body: Buffer.concat(ch) })); }).on('error', rej));
}
module.exports = { D, port, mk, tx, sleep, ok, done, get, WebSocket, fail };
