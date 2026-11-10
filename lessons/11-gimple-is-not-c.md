GCC's GIMPLE is not C: `(_Bool) x` keeps the low bit of x, and an "iftmp" name begins with "if".

tools/libm/gim2x.py translates GCC's optimized GIMPLE dumps of glibc's math routines. Two bugs in the
translator made pow wrong while exp and log were already bit-exact:

1. GCC folds the source's test of one bit, `iy & (1ULL << k)` (e_pow.c:264, checkint), into
   `(_Bool) (iy >> k)` (gate/results/checkint_evidence.txt). In GIMPLE a conversion to a one-bit
   boolean type truncates; it is not C's `!= 0`. Translating it as `!= 0` made pow(-x, even integer)
   negative. The fix: integer -> bool is `(x & 1) != 0`.
2. The declaration collector skipped statements that `startswith('if')` to avoid `if (...)`, which also
   skipped every assignment to GCC's temporaries `iftmp.N_M`. JavaScript then threw "viftmp_0_88 is not
   defined" on pow's special cases. The fix: skip `if (`, not `if`.

Both showed up because the checker compares against the system libm on millions of arguments, including
census samples from the real models and edge cases (negative bases, huge and subnormal arguments). The
second failed loudly; a spot check of positive bases would have missed the first.
