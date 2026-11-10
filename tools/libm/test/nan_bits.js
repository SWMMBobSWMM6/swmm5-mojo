// nan_bits.js - what bit pattern does V8 give a NaN, and does it keep it?
//   node tools/libm/test/nan_bits.js
// On x86-64, 0/0 computed by the processor is the "default NaN" 0xfff8000000000000 (sign bit set), which glibc
// prints as "-nan". This prints the bits V8 produces for 0/0 computed at run time, after the value passes
// through a plain array, an object field and a Float64Array, and for the literal NaN.
// Written by Claude (Anthropic); see AI-USE.md.
'use strict';
const dv = new DataView(new ArrayBuffer(8));
const bits = (x) => { dv.setFloat64(0, x); return dv.getBigUint64(0).toString(16).padStart(16, '0'); };
function div(a, b) { return a / b; }            // called with run-time arguments, so not constant-folded
let zero = Number(process.argv.length > 99 ? 1 : 0);
const q = div(zero, zero);
const arr = [1.5, q]; const obj = { f: 0.5 }; obj.f = q; const ta = new Float64Array(1); ta[0] = q;
const rows = [
  ['0/0 at run time', q],
  ['  through a plain array', arr[1]],
  ['  through an object field', obj.f],
  ['  through a Float64Array', ta[0]],
  ['  negated', -q],
  ['literal NaN', NaN],
  ['Number.NaN', Number.NaN],
];
for (const [what, x] of rows) console.log(what.padEnd(28), bits(x));
console.log('node', process.version, process.arch);
