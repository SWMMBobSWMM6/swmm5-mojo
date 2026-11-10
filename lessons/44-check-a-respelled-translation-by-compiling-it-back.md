A translation re-spelled in another syntax can be checked by compiling it back to the first one's syntax tree; that check, and the Hy runtime's math check, found what the gate had not.

The Hy port reuses the Python back end's translation: `tools/c2x/emit_hy.py` runs `emit_py.py` in memory, parses the
Python it would have written with Python's `ast` module and writes each node as a Hy form. Hy compiles to Python's
syntax tree, so the claim "the Hy engine is the same program as the Python text" can be tested directly:
`emit_hy.py --check` compiles the written Hy with Hy's compiler and compares the trees statement by statement. The
first comparison found 177 of 3,529 statements different, and none of them was a translation error. Hy keeps the
value of every `if` in a temporary (`_hy_anon_N = ...` in each branch), writes an `if` whose branches are single
expressions as a conditional expression, and turns `cond`'s last branch into `if True:`; a normaliser that knows
those three habits brought the count to 0. The check is cheap (15 s) and it is what makes the claim more than a
reading of the code. Two Hy facts it also pinned down: Hy's reader takes the symbols `NaN` and `Infinity` for numbers,
and a name in call position that is a Hy core macro is that macro, which SWMM's own function `match` is (renamed
`match__h`).

The math check found something else. `math.floor` returns a Python integer, and an integer has no -0.0. The Python
port's runtime (`py/swmm5/crt.py`) computes C's floor as `float(math.floor(x))` and ceil the same way, so
`_floor(-0.0)`, `_ceil(-0.0)` and `_ceil(-0.5)` all give +0.0 where C gives -0.0. The Hy runtime started as the same
code and `hy/test/run_libm_tests.sh` (the exact-functions vectors of `mkexact.c`) stopped it at once; it now keeps
zeros and whole numbers as they are and returns -0.0 for a ceiling in (-1, 0). The Python port passed every model it
ran (465), so no gate model reaches those arguments in a way that changes an output; the defect is latent there and
left for its owner. Two more CPython facts from the same check: this CPython binary imports `exp`, `log` and `pow`
at their old GLIBC_2.2.5 versions (glibc's SVID wrappers, which differ from EPA's GLIBC_2.29 ones only for error
cases), and the `math` module raises or answers by itself for NaN, infinite and out-of-domain arguments; the Hy
runtime sends exactly those to glibc through `ctypes`, which binds each symbol's default version, EPA's.

What to take from it: when a port is another port's translation in different clothes, prove the clothes changed
nothing by round-tripping through the shared intermediate form; and give each runtime its own exact checks even when
it was copied from one that passed, because the gate tests a runtime only through the arguments the corpus happens
to give it (lessons/25).
