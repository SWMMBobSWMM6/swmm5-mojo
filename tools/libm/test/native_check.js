// native_check.js - how often V8's own Math.* differs from glibc on the test vectors (node native_check.js vectors.bin).
// Written by Claude (Anthropic).
const fs = require('fs');
const buf = fs.readFileSync(process.argv[2]); const dv = new DataView(buf.buffer, buf.byteOffset, buf.byteLength);
const F = { exp: Math.exp, log: Math.log, log10: Math.log10, pow: Math.pow, sin: Math.sin, cos: Math.cos, tan: Math.tan, asin: Math.asin, acos: Math.acos, atan: Math.atan };
const f = new Float64Array(1), u = new BigUint64Array(f.buffer); const b = x => { f[0] = x; return u[0]; };
let p = 0;
while (p < buf.length) {
  let e = p; while (buf[e] !== 0) e++; const name = buf.toString('latin1', p, e); p = e + 1;
  const n = dv.getUint32(p, true); p += 4; const na = name === 'pow' ? 2 : name === 'fma' ? 3 : 1;
  const fn = F[name]; if (!fn) { p += n * 8 * (na + 1); continue; }
  let bad = 0, cnt = 0;
  for (let i = 0; i < n; i++) { const a = dv.getFloat64(p, true), y = na > 1 ? dv.getFloat64(p + 8, true) : 0, w = dv.getFloat64(p + 8 * na, true); p += 8 * (na + 1);
    const g = na === 1 ? fn(a) : fn(a, y); if (g !== g && w !== w) { cnt++; continue; } cnt++; if (b(g) !== b(w)) bad++; }
  console.log(`V8 Math.${name.padEnd(6)} ${bad} of ${cnt} differ from glibc (${(100 * bad / cnt).toFixed(2)}%)`);
}
