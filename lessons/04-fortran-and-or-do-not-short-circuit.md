Fortran's .and. and .or. may evaluate both operands, so C's `p != NULL && p->x` must become nested IFs.

gfortran evaluates both sides of `.and.` whenever it likes (a test at -O0 segfaulted on a null pointer
guarded exactly the way SWMM guards them). emit_f90.py keeps an operand pair as `.and.`/`.or.` only when
the right side provably cannot fault or change anything: literals, variables, '.' member access, arithmetic
without integer division by a non-constant, and the pure math functions. Anything else (an array element,
a '->', a call, an assignment) is evaluated into a logical temporary inside an IF on the left side. The
same rule covers ?: (merge() evaluates both arms).
