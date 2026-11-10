// check.ts - compare the TypeScript glibc ports (and the exact fma) bit for bit with system-libm vectors.
import * as fs from "fs";
import * as M from "./glibm";
import * as R from "./glibm_rt";
const buf = fs.readFileSync(process.argv[2]);
const only = process.argv[3] ? process.argv[3].split(",") : null;
const dv = new DataView(buf.buffer, buf.byteOffset, buf.byteLength);
const fns: Record<string, (...a: number[]) => number> = { ...(M as any), fma: R.fma };
const f = new Float64Array(1), u = new BigUint64Array(f.buffer);
const bits = (x: number) => { f[0] = x; return u[0]; };
let p = 0;
while (p < buf.length) {
  let e = p; while (buf[e] !== 0) e++;
  const name = buf.toString("latin1", p, e); p = e + 1;
  const n = dv.getUint32(p, true); p += 4;
  const na = name === "pow" ? 2 : name === "fma" ? 3 : 1;
  const fn = fns[name];
  if (!fn || (only && !only.includes(name))) { p += n * 8 * (na + 1); continue; }
  let bad = 0, shown = 0, nanSign = 0; const t0 = Date.now();
  for (let i = 0; i < n; i++) {
    const a = dv.getFloat64(p, true), b = na > 1 ? dv.getFloat64(p + 8, true) : 0, c = na > 2 ? dv.getFloat64(p + 16, true) : 0;
    const want = dv.getFloat64(p + 8 * na, true);
    p += 8 * (na + 1);
    const got = na === 1 ? fn(a) : na === 2 ? fn(a, b) : fn(a, b, c);
    if (Number.isNaN(got) && Number.isNaN(want)) { if ((bits(got) >> 63n) !== (bits(want) >> 63n)) nanSign++; continue; }
    if (bits(got) !== bits(want)) {
      bad++;
      if (shown++ < 4) console.log(`  ${name}(${[a, b, c].slice(0, na).join(", ")}) = ${got}, libm ${want}`);
    }
  }
  console.log(`${name.padEnd(6)} ${bad} of ${n} differ, ${nanSign} NaN sign   (${((Date.now() - t0) / n * 1e3).toFixed(3)} us/call)`);
}
