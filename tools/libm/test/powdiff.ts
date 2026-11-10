// powdiff.ts - differential test of the TypeScript pow fast path against pow_exact (the full translation of
// glibc's pow), on random arguments concentrated where the fast path runs and around its boundaries.
// node dist/powdiff.js [millions]. Written by Claude (Anthropic).
import * as M from "./glibm";
const F = new Float64Array(1), U = new Uint32Array(F.buffer);
let seed = 0x9e3779b9;
function rnd(): number { seed ^= seed << 13; seed ^= seed >>> 17; seed ^= seed << 5; return (seed >>> 0) / 4294967296; }
function bits(): number { U[0] = (rnd() * 4294967296) >>> 0; U[1] = (rnd() * 4294967296) >>> 0; return F[0]; }
function logu(e0: number, e1: number): number { return Math.pow(2, e0 + rnd() * (e1 - e0)) * (1 + rnd()); }
const n = (Number(process.argv[2]) || 20) * 1e6;
let bad = 0, nanSign = 0;
const B = new Float64Array(1), BU = new BigUint64Array(B.buffer);
const b = (x: number) => { B[0] = x; return BU[0]; };
for (let i = 0; i < n; i++) {
  const k = i % 8;
  let x: number, y: number;
  if (k === 0) { x = logu(-1022, 1023); y = (rnd() - 0.5) * 20; }
  else if (k === 1) { x = 1 + (rnd() - 0.5) * 2 ** -(rnd() * 52); y = (rnd() - 0.5) * 2 ** (rnd() * 70 - 65); }
  else if (k === 2) { x = rnd() * 10; y = [5 / 3, 0.5, 1.5, 2 / 3, 2, 3, 0.25, 1.33333][i % 8]; }
  else if (k === 3) { x = logu(-1022, 1023); y = Math.round((rnd() - 0.5) * 4000) / 7; }
  else if (k === 4) { x = Math.abs(bits()); y = bits(); }
  else if (k === 5) { x = logu(-30, 30); y = (rnd() - 0.5) * 2 ** (rnd() * 130 - 66); }
  else if (k === 6) { x = 0.5 + rnd() * 1.5; y = (rnd() - 0.5) * 2000; }
  else { x = logu(-1074, -1000); y = (rnd() - 0.5) * 3; }
  const a = M.pow(x, y), e = M.pow_exact(x, y);
  if (a !== a && e !== e) { if ((b(a) >> 63n) !== (b(e) >> 63n)) nanSign++; continue; }
  if (b(a) !== b(e)) { if (bad++ < 5) console.log(`pow(${x}, ${y}) = ${a}, pow_exact ${e}`); }
}
console.log(`pow vs pow_exact: ${bad} of ${n} differ, ${nanSign} NaN sign`);
