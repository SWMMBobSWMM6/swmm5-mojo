Ruby's Kernel#format is not correctly rounded: it printed 36.15 as "36.2" where glibc prints "36.1", in 11,553 of 1,082,106 test cases.

The Ruby port's first runtime let MRI's `format` write the digits of `%f`, `%e` and `%g` and only spelled out the
cases where Ruby and C obviously differ (Ruby writes "NaN" and "Inf", glibc "nan", "-nan" and "inf"). The first
discovery gate (rb_1) failed 27 of 305 models, every one in the last digit of a report value:

    glibc:  5                    JUNCTION        1.23         11.056       50.944
    Ruby:   5                    JUNCTION        1.22         11.056       50.944

The runtime check (`ruby/test/run_crtcheck.sh`, the same 1,394,252 glibc cases the other runtimes replay) found
the cause at once: `printf %f: 1082106 cases, 11553 differ`, for example 0x4042133333333333, which is
36.149999999999998578..., printed with `%.1f`: glibc "36.1", Ruby "36.2". glibc prints the exact value of the
binary number, so it rounds down; MRI's formatter (BSD vfprintf with David Gay's dtoa, built into the
interpreter) rounds up, as if the number were the decimal 36.15, although `format('%.20f', 36.15)` shows the exact
digits 36.14999999999999857891. Python's `'%.1f' % 36.15` gives "36.1", as glibc does. The `.out` files of all
27 models were already identical; only the report text was wrong.

The fix was to stop using `format` for floating conversions. `crt.rb` (`fmt_float`) writes x = m * 2**e with
Ruby's big integers and rounds m * 2**e * 10**p to the nearest integer, ties to even, which is what glibc does
in the default rounding mode; `%e` finds the decimal exponent by exact comparison with a power of ten, and `%g`
follows C99's rule for choosing between the two. After the change the check gives 1 difference in 1,394,252, the
same one the Zig and Pascal runtimes leave (`%#g` of 999999.5: glibc writes "1.e+06", a glibc quirk in a
format EPA never uses), and the 27 models passed (rb_2).

What to carry forward: a language's printf is not C's printf even when it accepts the same format strings.
Python's `%` operator happens to be correctly rounded, Ruby's is not, and nothing in the documentation of either
says so. Test the digits, not the syntax, against the C library, before the gate.
