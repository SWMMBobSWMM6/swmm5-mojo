PHP keeps C's statements and changes its data: arrays and strings are values, `/` on two ints may give an int or a float, a zero divisor throws, and `-$x` is a multiplication.

PHP has C's `if`, `while`, `do`, `for`, `switch` with fall-through, `break` and `continue`, so the PHP back end
(tools/c2x/emit_php.py) could keep EPA's control flow almost word for word, which no earlier interpreted port could
(Python and Ruby have no `switch` with fall-through, Kotlin no C `for`). Only `continue` inside a `switch` changes:
PHP counts a switch as a loop, so it becomes `continue 2`. The differences are all in the data:

- **Arrays are values.** `$a = $b` and passing `$b` to a function copy the array (lazily, on the first write), where
  C copies a pointer. A translation that maps `double*` to a PHP array works until a function fills an array it was
  given, as gwater.c's `getDxDt(t, x, dxdt)` fills `dxdt[]` for the ODE solver: it would fill a private copy, and the
  solver would never see the derivatives. Every C array is therefore an
  object (`Arr`, whose property `a` is the PHP array), so a handle is shared as a pointer is; `$Node->a[$j]->depth`.
  A PHP array held in an object property ran about as fast under the JIT as a plain global array, and
  `SplFixedArray`, which is an object too, four times slower. Strings are values as well, so `char*` is a `CPtr`
  over a shared buffer object, not a PHP string.
- **Pointers to numbers became references.** PHP can pass any lvalue by reference (`&$x`, an object property, an
  array element), so a C pointer parameter that is only dereferenced is a by-reference parameter, as `ref` is in the
  C# port, and the boxes the Python and Ruby ports allocate for `&local` are not needed. `sscanf`'s targets are an
  array of references, `[&$year, &$month, $token]`.
- **Integers and doubles.** `6 / 2` is the int 3 and `7 / 2` the float 3.5; C's integer `/` is `\intdiv`, and every
  int-to-double conversion is written out, or a double variable would sometimes hold an int (and `0 * -1` is the int
  0, where C's `0.0 * -1.0` is -0.0).
- **A zero divisor throws.** `1.0 / 0.0` raises DivisionByZeroError in PHP 8; C gives infinity, and 0.0 / 0.0 gives
  x86's NaN with the sign bit set, which EPA prints as "-nan". Divisions that are not by a nonzero constant are
  `($b == 0.0 ? \fdiv($a, $b) : $a / $b)`.
- **`-$x` is `$x * -1`.** PHP compiles unary minus as a multiplication, which leaves a NaN's sign bit alone; C's
  negation flips it. The engine negates doubles with a runtime function that flips the bit.
- **`global`.** Each function binds the globals it uses with `global $Name;`, a hash lookup per name per call. The
  first engine bound them all at the top of each function, and `xsect_getAofY`, called several times per conduit per
  step, bound 26 cross-section tables to use one. The back end now binds each global in the innermost block that holds
  all its uses (never inside a loop): `case 1: global $A_Circ, $N_A_Circ; return ...`.

What to carry forward: a language that looks like C invites a translation that looks like C, and the statements can
be; the values cannot. List, for each C type, what assignment and argument passing do to it in the target language
before choosing its representation.
