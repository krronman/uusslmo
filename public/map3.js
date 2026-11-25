// Map 3 (Maehwa plaza) server test. Run: NODE_PATH=/opt/npm-tools/node_modules node tests/map3.js  (needs ../server_t.js = server.js + global.__d export)
process.env.PORT=0;process.env.ALLOW_MEMORY_DB='1';
require('../server_t.js');const d=global.__d;d.setMap(2);
for(const sc of [1,1.5,2]){
 d.setScale(sc);
 const inR=(x,y)=>x>=264*sc&&x<1272*sc&&y>=250*sc&&y<812*sc;
 let mism=0;for(let i=0;i<50000;i++){const x=Math.random()*1536*sc,y=Math.random()*1024*sc;if(d.walkAt(x,y)&&!inR(x,y))mism++}
 let viol=0;for(let t=0;t<200;t++){let p=d.snapWalk((300+Math.random()*900)*sc,(300+Math.random()*450)*sc);for(let s=0;s<300;s++){const a=Math.random()*6.283,q=d.slideTo(p.x,p.y,p.x+Math.cos(a)*14,p.y+Math.sin(a)*14);if(!d.walkAt(q.x,q.y))viol++;p=q}}
 let thr=0;for(let t=0;t<2000;t++){const p=d.snapWalk(Math.random()*1536*sc,Math.random()*1024*sc),a=Math.random()*6.283,q=d.slideTo(p.x,p.y,p.x+Math.cos(a)*200,p.y+Math.sin(a)*200);if(!d.walkAt(q.x,q.y))thr++}
 let ring=true;for(let i=0;i<24;i++){const q=d.ringPos(i/24*6.283,.92);if(!d.walkAt(q.x,q.y))ring=false}
 console.log('scale',sc,'walkable outside plaza:',mism,'walk viol',viol,'dash viol',thr,'ring ok',ring);
}
d.setScale(1);
d.placeDummies();console.log('dummies walkable',d.dummies.every(x=>d.walkAt(x.x,x.y)),d.dummies.map(x=>[Math.round(x.x),Math.round(x.y)]).join(' '));
for(const id of [0,1,2,1]){d.setMap(id);}
console.log('maps switch ok; map1 walkAt anywhere:',(d.setMap(1),d.walkAt(5,5)));
process.exit(0);
