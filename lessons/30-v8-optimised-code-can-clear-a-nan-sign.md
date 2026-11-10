V8's optimised code can clear a NaN's sign bit: `strtod("-nan")` returned through a JavaScript array came back as `nan` once the function was hot.

lessons/10 established that V8 keeps the bits of a NaN the hardware computes, "through a plain array" included
(gate/results/js_nan_bits.txt), and the TypeScript runtime relied on it: its `scanDouble` returns `[value, end]`, and
for "-nan" the value is x86's default NaN, 0xfff8000000000000, which glibc prints as "-nan". The runtime check of the
JavaScript port (js/test/run_crtcheck.sh, the 1,394,252 glibc cases) passed on that code. A direct test did not:

    glibc strtod("-nan") = fff8000000000000; node v22.23.4
    ts/dist/crt.js   fff8000000000000 fff8000000000000 fff8000000000000 7ff8000000000000
    js/swmm5/crt.js  fff8000000000000 fff8000000000000 fff8000000000000 fff8000000000000   (after the fix)

The first three columns are cold calls; the fourth comes after 100,000 calls with "1.5", when V8's optimising
compiler has taken over `strtod` and `scanDouble`, and it hands back the canonical NaN with the sign bit clear
(js/test/nan_paths.js, js/results/nan_paths.txt). A three-line imitation of the same pattern kept the bits, so the
behaviour depends on what the optimiser does with the particular function, not on the language. The JavaScript
runtime now leaves the value in a `Float64Array` slot and returns only the end position; the test above is the
check. Run against the TypeScript runtime, the glibc cases found 964 differences in all (`%lu` of negative longs,
hexadecimal floats, NaN payloads, a saturating `%d`, and these NaN signs; js/results/crtcheck_ts_runtime.txt); the
corpus reaches none of them.

What to carry forward: in a JIT-compiled language a bit pattern that survives a cold test can be normalised by the
optimised code. Test the special values after warming the code up, and pass doubles whose bits matter through
storage that is defined to keep them (a typed array), not through containers the engine is free to re-represent.
