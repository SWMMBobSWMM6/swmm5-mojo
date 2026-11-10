// powtime.js - what the TypeScript pow fast path saves: time pow (fast path) and pow_exact (the full GIMPLE
// translation, whose 64-bit steps are BigInt) on the same arguments, after a warm-up, in one Node process.
//   node tools/libm/test/powtime.js [N]        (after `npm run build` in ts/)
// Arguments: bases log-uniform in [1e-3, 1e3], exponents uniform in [-3, 3], from a fixed seed.
// Written by Claude (Anthropic); see AI-USE.md.
'use strict';
const path = require('path');
const M = require(path.join(__dirname, '../../../ts/dist/glibm.js'));
const N = +(process.argv[2] || 2000000);
let s = 1729 >>> 0;
const rnd = () => { s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0; return s / 4294967296; };
const xs = new Float64Array(N), ys = new Float64Array(N);
for (let i = 0; i < N; i++) { xs[i] = Math.pow(10, -3 + 6 * rnd()); ys[i] = -3 + 6 * rnd(); }
function run(f) { let acc = 0; for (let i = 0; i < N; i++) acc += f(xs[i], ys[i]); return acc; }
for (let k = 0; k < 2; k++) { run(M.pow); run(M.pow_exact); }              // warm-up
const out = {};
for (const [name, f] of [['pow (fast path)', M.pow], ['pow_exact (full translation)', M.pow_exact], ['Math.pow (V8)', Math.pow]]) {
  const t = process.hrtime.bigint(); const acc = run(f); const dt = Number(process.hrtime.bigint() - t) / 1e9;
  out[name] = dt; console.log(name.padEnd(30), (dt / N * 1e9).toFixed(1).padStart(7), 'ns/call', ' checksum', acc);
}
console.log('full translation / fast path:', (out['pow_exact (full translation)'] / out['pow (fast path)']).toFixed(1),
            'times;  fast path / V8 Math.pow:', (out['pow (fast path)'] / out['Math.pow (V8)']).toFixed(1), 'times;  N =', N,
            '; node', process.version);
