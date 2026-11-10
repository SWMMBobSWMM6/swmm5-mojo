EPA's own results depend on which CPU runs it: glibc picks FMA versions of its math functions when the processor has FMA and AVX2.

glibc 2.39 on x86-64 ships two builds of its double-precision exp, log, pow, sin, cos, tan, asin, acos and
atan, and picks one when the program starts (an "ifunc"): a version compiled with `-mfma -mavx2` on
processors that have fused multiply-add, and a generic one otherwise. The two round differently in the last
bit for some arguments. Running EPA 5.2.4 with `GLIBC_TUNABLES=glibc.cpu.hwcaps=-AVX2,-FMA,-FMA4` (the generic
versions, as an older CPU would get) changes the .out or .rpt of 43 of the 480 gate models
(gate/ctl_libm_generic.txt). So "byte-identical to EPA" means "to EPA on this kind of CPU".

Consequences for the ports:

- C, C++, Fortran, C#, Python and Rust call the system libm, so they inherit the same choice and should agree
  with EPA on any machine, as long as both run on the same machine (expected from how ifuncs work; only EPA
  itself was run on the generic routines).
- JavaScript (V8) and Java bring their own math functions, which differ from glibc in the last bit (measured:
  V8's Math.pow on 9.1% of the test arguments, Java's Math.pow on 0.08%, Java's StrictMath.pow, a port of
  fdlibm, on 8.7%; gate/results/libm_native.txt). The TypeScript and Java ports therefore carry their own copy
  of glibc's routines: tools/libm translates GCC's optimized GIMPLE for the FMA builds into TypeScript and
  Java, keeping every fused multiply-add where GCC placed one. They match the FMA build bit for bit (22
  million test vectors, tools/libm/test), and so match EPA on FMA hardware -- but they would NOT follow EPA
  onto a non-FMA CPU.
- The census (tools/libm/census.c) says which functions matter: pow is called 1.24 billion times across the
  corpus, sin and cos 136 million each, exp 14 million, log 3 million; atan and sqrt never reach libm (sqrt is
  an instruction).
- Was carrying glibc necessary? Built with their own Math instead, the TypeScript engine differed from EPA on
  6 of the 40 control models and the Java engine on 1, and on 38 of all 480 (gate/run_ts_native_control.sh,
  gate/run_java_native_control.sh). A rare per-call difference still reaches the report: one model's
  continuity error moved from -0.170% to -0.185%, and a control rule fired 76 seconds late.
