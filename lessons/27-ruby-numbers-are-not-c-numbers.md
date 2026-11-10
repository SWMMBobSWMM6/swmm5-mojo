Ruby is not Python with different keywords: 0 is true, `/` floors, 1 / 2 is 0, 0.0 / 0.0 is a NaN with the wrong sign, and Math raises where C returns NaN.

The Ruby back end (tools/c2x/emit_ruby.py) started from the Python back end, because the two languages face the
same problems (integers without a width, no pointers, a slow interpreter). Most of what the Python back end
could leave implicit had to be written out for Ruby:

- **Truth.** In Ruby only `nil` and `false` are false; 0 and 0.0 are true. Every C condition on a number becomes
  `(x != 0)` or `(x != 0.0)`, `!x` becomes `!(x != 0)`, and a comparison used as a number becomes
  `(c ? 1 : 0)` (Python's True is the integer 1; Ruby's `true` is not a number at all).
- **Integers and doubles.** Ruby never turns an Integer into a Float by itself, and Integer `/` floors:
  `1 / 2` is 0 and `-7 / 2` is -4. Python's `/` always divides as floats, so the Python back end could leave
  clang's int-to-double conversions out; the Ruby back end writes each one (`n.to_f`, literals as `2.0`), uses
  `idiv` (truncating) for C's integer `/` and `Integer#remainder` for `%`.
- **0.0 / 0.0.** MRI's Float#/ returns `nan("")` when both operands are zero, a NaN with the sign bit clear,
  which glibc prints as "nan". x86 returns its default NaN, sign bit set, printed "-nan", and that is what
  EPA's reports show. A division whose divisor is not a nonzero constant is written
  `(b == 0.0 ? fdiv0(a, b) : a / b)`. The other NaNs of Ruby's arithmetic come from the hardware and have C's sign.
- **math.h.** MRI's Math functions call the same glibc routines EPA calls (libruby imports `exp@GLIBC_2.29`,
  `log@GLIBC_2.29`, `pow@GLIBC_2.29`, `sin@GLIBC_2.2.5`, ..., the versions EPA imports), but around them it adds
  its own rules: `Math.sqrt`, `log`, `log10`, `asin` and `acos` raise Math::DomainError where C returns a NaN;
  `Math.sqrt(-0.0)` is +0.0 (C: -0.0); `Float#**` returns a Complex for a negative base and a non-integral
  exponent; `Float#floor` returns an Integer. Small wrappers in `ruby/swmm5/crt.rb` return C's answers in those
  cases and call Math otherwise; `ruby/test/run_libm_tests.sh` checks them against the system libm on 17.3 million
  arguments, NaN signs and payloads included: none differ (`ruby/results/libm_tests.txt`).
- **(float)x.** `[x].pack('f')` is not C's cast either: MRI's `VALUE_to_float` (pack.c) turns every NaN into +NaN
  and sends anything above FLT_MAX to infinity, where C rounds values just above FLT_MAX down to FLT_MAX. The
  runtime's `f32` was written around that from the start, but the binary writer still packed REAL4 arrays with
  `pack('e*')`, the same conversion. The medium discovery run (rb_3) passed 107 of 108 models; the 108th,
  Hydraulics/Allow_Ponding_Low_CE.inp, the model that prints "-nan" in its report (lessons/10), had an identical report
  and 86,995 differing bytes in its `.out`: EPA's -nan (0xffc00000) written as 0x7fc00000. NaNs are now written
  from their bits, as `cvtsd2ss` stores them.
- **Names.** Ruby decides what a name is from its first letter: a capital makes a constant, so C locals such as
  `Re` become `_Re`, and SWMM's lower-case enum values (`s_TITLE`, `r_RULE`) become constants `K_s_TITLE`.
  Fields called `end`, `next` or `name`, and a C function called `hash`, get a trailing `_` so they cannot
  shadow Ruby's keywords or Object's methods. Constants are looked up lexically, so the record classes nested in
  the engine module could not see the runtime's `CPtr` through the module's `include` (the first run stopped with
  `uninitialized constant SWMM5::TFile::CPtr`); the module now names the runtime classes itself.
- **switch.** Ruby's `case` compares with `===` one `when` after another unless every label is a literal, in
  which case it jumps through a hash; case labels are written as integer literals (clang evaluates the enum
  names), and a `case` is used only where no C case falls through.

What to carry forward: when two languages look alike, list their differences from C one by one, not their
differences from each other. A translator built for one of them carries silent assumptions (Python's `/`,
Python's integer True) that the other does not honour, and the only symptom may be a wrong last digit.
