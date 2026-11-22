// Usage: node tests/run.js   (needs the "ws" package; set NODE_PATH if it is not installed locally)
const { spawnSync } = require('child_process'), fs = require('fs'), path = require('path');
let bad = 0;
for (const f of fs.readdirSync(__dirname).filter(f => f.endsWith('.test.js')).sort()) {
  const r = spawnSync(process.execPath, [path.join(__dirname, f)], { encoding: 'utf8', timeout: 120000 });
  const out = (r.stdout || '') + (r.stderr || ''), failed = r.status !== 0 || /\bFAIL\b/.test(out);
  console.log((failed ? 'FAIL ' : 'PASS ') + f);
  if (failed) { bad++; console.log(out.split('\n').filter(l => /FAIL|Error|error/.test(l)).join('\n')); }
}
console.log(bad ? bad + ' test file(s) failed' : 'all tests passed'); process.exit(bad ? 1 : 0);
