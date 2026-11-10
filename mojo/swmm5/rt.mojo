# rt.mojo - the C runtime of the Mojo port of EPA SWMM 5.2.4 (imported by the generated engine as `rt`).
#
# It reproduces the glibc 2.39 / x86-64 behaviour SWMM's output depends on, in Mojo:
#   * printf/snprintf with glibc's exact decimal rounding: the binary value is expanded exactly with big
#     integers and rounded half to even, as glibc does in its default rounding mode;
#   * strtod/atof/atoi/sscanf with glibc's syntax (decimal, hexadecimal, inf, nan(...)), correctly rounded:
#     Clinger's fast path when it is exact, otherwise the nearest double found by exact big-integer
#     comparison; sscanf's %f into a float rounds once, as strtof does;
#   * stdio files over open/pread/pwrite/write/lseek/close (C's position, end-of-file flag and buffering);
#   * strings, memory (zero-filled blocks with a size header), time;
#   * x86-64 integer behaviour: (int)x of a double is cvttsd2si (NaN or out of range -> INT_MIN), division
#     truncates, shift counts are masked;
#   * libm: exp, log, log10, pow, sin, cos, tan, asin, acos and atan are glibc's own functions, which EPA
#     itself calls, reached through external_call from wrappers the compiler may not inline (so LLVM can
#     neither fold a call with constant arguments nor rewrite one); fabs, sqrt, floor and ceil are exact
#     instructions.
# Mojo 1.2 has no global variables, so the runtime's state (standard output, strtok's position, ...) lives
# in an RT record that the engine's globals point to.
# Only the C library's low-level I/O (open, pread, pwrite, write, lseek, close, unlink, getcwd, time,
# getpid) and its allocator (calloc, free) are called from libc.
# Written by Claude (Anthropic) for Robert Dickinson; see ../README.md.

from std.ffi import external_call
from std.memory import bitcast
from std.collections import List
from std.sys import size_of

comptime P = Pointer[_, MutUntrackedOrigin]
comptime VP = Pointer[NoneType, MutUntrackedOrigin]


# ================================================================ pointers

@always_inline
def null[T: AnyType]() -> P[T]:
    return P[T](unsafe_from_address=Int(0))


@always_inline
def addr[T: AnyType](ref x: T) -> P[T]:
    """the address of x as an untracked C pointer (x must live in memory that stays put: the heap, the
    globals record, or a stack slot made with stack_allocation)"""
    return P[T](unsafe_from_address=Int(Pointer(to=x)))


@always_inline
def isnull[T: AnyType](p: P[T]) -> Bool:
    return Int(p) == 0


@always_inline
def s(lit: StaticString) -> P[Int8]:
    """a C string literal (ASCII text: the compiler stores it with a terminating NUL)"""
    return P[Int8](unsafe_from_address=Int(lit.unsafe_ptr()))


@always_inline
def pdiff[T: AnyType](p: P[T], q: P[T], size: Int) -> Int64:
    return Int64((Int(p) - Int(q)) // size)


# ================================================================ integers

@always_inline
def d2i32(x: Float64) -> Int32:
    """(int)x as x86-64 converts it (cvttsd2si): NaN or out of range gives INT_MIN"""
    if not (x > -2147483649.0 and x < 2147483648.0):
        return Int32(-2147483648)
    return Int32(x)


@always_inline
def d2i64(x: Float64) -> Int64:
    if not (x >= -9223372036854775808.0 and x < 9223372036854775808.0):
        return Int64(-9223372036854775807) - 1
    return Int64(x)


@always_inline
def d2u32(x: Float64) -> UInt32:
    return UInt32(d2i64(x))


@always_inline
def d2u64(x: Float64) -> UInt64:
    if x < 9223372036854775808.0:
        return UInt64(d2i64(x))
    return UInt64(d2i64(x - 9223372036854775808.0)) ^ UInt64(0x8000000000000000)


@always_inline
def d2u16(x: Float64) -> UInt16:
    return UInt16(d2i32(x))


@always_inline
def d2i16(x: Float64) -> Int16:
    return Int16(d2i32(x))


@always_inline
def d2i8(x: Float64) -> Int8:
    return Int8(d2i32(x))


@always_inline
def d2u8(x: Float64) -> UInt8:
    return UInt8(d2i32(x))


@always_inline
def idiv32(a: Int32, b: Int32) -> Int32:
    """C's a / b: truncates toward zero (Mojo's // floors)"""
    var q = a // b
    if (a % b != 0) and ((a < 0) != (b < 0)):
        q += 1
    return q


@always_inline
def irem32(a: Int32, b: Int32) -> Int32:
    return a - b * idiv32(a, b)


@always_inline
def idiv64(a: Int64, b: Int64) -> Int64:
    var q = a // b
    if (a % b != 0) and ((a < 0) != (b < 0)):
        q += 1
    return q


@always_inline
def irem64(a: Int64, b: Int64) -> Int64:
    return a - b * idiv64(a, b)


@always_inline
def shl32(a: Int32, n: Int32) -> Int32:
    return a << (n & 31)


@always_inline
def shr32(a: Int32, n: Int32) -> Int32:
    return a >> (n & 31)


@always_inline
def shl64(a: Int64, n: Int32) -> Int64:
    return a << Int64(n & 63)


@always_inline
def shr64(a: Int64, n: Int32) -> Int64:
    return a >> Int64(n & 63)


@always_inline
def shlu32(a: UInt32, n: Int32) -> UInt32:
    return a << UInt32(n & 31)


@always_inline
def shru32(a: UInt32, n: Int32) -> UInt32:
    return a >> UInt32(n & 31)


@always_inline
def shlu64(a: UInt64, n: Int32) -> UInt64:
    return a << UInt64(n & 63)


@always_inline
def shru64(a: UInt64, n: Int32) -> UInt64:
    return a >> UInt64(n & 63)


# ---------------------------------------------------------------- C expressions with side effects as values

@always_inline
def set[T: Copyable & Deinitable](mut dst: T, v: T) -> T:
    """C's (dst = v) used as a value"""
    dst = v.copy()
    return v.copy()


@always_inline
def postinc[dt: DType](mut x: Scalar[dt]) -> Scalar[dt]:
    var old = x
    x += 1
    return old


@always_inline
def postdec[dt: DType](mut x: Scalar[dt]) -> Scalar[dt]:
    var old = x
    x -= 1
    return old


@always_inline
def preinc[dt: DType](mut x: Scalar[dt]) -> Scalar[dt]:
    x += 1
    return x


@always_inline
def predec[dt: DType](mut x: Scalar[dt]) -> Scalar[dt]:
    x -= 1
    return x


@always_inline
def postdecp[T: AnyType](mut p: P[T]) -> P[T]:
    var old = p
    p = p.unsafe_offset(-1)
    return old


@always_inline
def predecp[T: AnyType](mut p: P[T]) -> P[T]:
    p = p.unsafe_offset(-1)
    return p


@always_inline
def postinc32(mut x: Int32) -> Int32:
    var old = x
    x += 1
    return old


@always_inline
def postdec32(mut x: Int32) -> Int32:
    var old = x
    x -= 1
    return old


@always_inline
def preinc32(mut x: Int32) -> Int32:
    x += 1
    return x


@always_inline
def predec32(mut x: Int32) -> Int32:
    x -= 1
    return x


@always_inline
def postinc64(mut x: Int64) -> Int64:
    var old = x
    x += 1
    return old


@always_inline
def preinc64(mut x: Int64) -> Int64:
    x += 1
    return x


@always_inline
def postincp[T: AnyType](mut p: P[T]) -> P[T]:
    var old = p
    p = p.unsafe_offset(1)
    return old


@always_inline
def preincp[T: AnyType](mut p: P[T]) -> P[T]:
    p = p.unsafe_offset(1)
    return p


# ================================================================ floating point

@always_inline
def nan64() -> Float64:
    return bitcast[DType.float64](UInt64(0x7FF8000000000000))


@always_inline
def inf64() -> Float64:
    return bitcast[DType.float64](UInt64(0x7FF0000000000000))


@always_inline
def bits64(x: Float64) -> UInt64:
    return bitcast[DType.uint64](x)


@always_inline
def f64bits(u: UInt64) -> Float64:
    return bitcast[DType.float64](u)


@always_inline
def f32b(u: UInt32) -> Float32:
    return bitcast[DType.float32](u)


@always_inline
def signbit(x: Float64) -> Bool:
    return (bits64(x) >> 63) != 0


@always_inline
def fabs(x: Float64) -> Float64:
    return f64bits(bits64(x) & UInt64(0x7FFFFFFFFFFFFFFF))


# ---------------------------------------------------------------- libm: glibc's own functions, as EPA calls them

@no_inline
def exp(x: Float64) -> Float64:
    return external_call["exp", Float64](x)


@no_inline
def log(x: Float64) -> Float64:
    return external_call["log", Float64](x)


@no_inline
def log10(x: Float64) -> Float64:
    return external_call["log10", Float64](x)


@no_inline
def pow(x: Float64, y: Float64) -> Float64:
    return external_call["pow", Float64](x, y)


@no_inline
def sin(x: Float64) -> Float64:
    return external_call["sin", Float64](x)


@no_inline
def cos(x: Float64) -> Float64:
    return external_call["cos", Float64](x)


@no_inline
def tan(x: Float64) -> Float64:
    return external_call["tan", Float64](x)


@no_inline
def asin(x: Float64) -> Float64:
    return external_call["asin", Float64](x)


@no_inline
def acos(x: Float64) -> Float64:
    return external_call["acos", Float64](x)


@no_inline
def atan(x: Float64) -> Float64:
    return external_call["atan", Float64](x)


# ================================================================ memory
# Every block is zero-filled (EPA reads nothing it has not written, except the matrix of lessons/02 defect 5,
# which this makes zero) and carries its size in a 16-byte header, for realloc.

def _raw_alloc(n0: UInt64) -> VP:
    var n = n0 if n0 > 0 else UInt64(1)        # calloc(0) still gives a unique block, as glibc's does
    var b = external_call["calloc", VP](Int(n + 16), Int(1))
    if isnull(b):
        return b
    b.unsafe_bitcast[UInt64]()[] = n
    return VP(unsafe_from_address=Int(b) + 16)


def malloc(n: UInt64) -> VP:
    return _raw_alloc(n)


def calloc(n: UInt64, size: UInt64) -> VP:
    return _raw_alloc(n * size)


def free(p: VP):
    if not isnull(p):
        external_call["free", NoneType](VP(unsafe_from_address=Int(p) - 16))


def realloc(p: VP, n: UInt64) -> VP:
    var q = _raw_alloc(n)
    if isnull(q) or isnull(p):
        return q
    var have = P[UInt64](unsafe_from_address=Int(p) - 16)[]
    var m = have if have < n else n
    var d = q.unsafe_bitcast[UInt8]()
    var s0 = p.unsafe_bitcast[UInt8]()
    for k in range(Int(m)):
        d[unsafe_offset=k] = s0[unsafe_offset=k]
    free(p)
    return q


def memset(p: VP, c: Int32, n: UInt64) -> VP:
    var b = p.unsafe_bitcast[UInt8]()
    var v = UInt8(c)
    for k in range(Int(n)):
        b[unsafe_offset=k] = v
    return p


def init_chars(d: P[Int8], src: P[Int8], n: Int):
    """char d[N] = "...": the literal's n characters (the rest of d is already zero)"""
    for k in range(n):
        d[unsafe_offset=k] = src[unsafe_offset=k]


def bad_function_pointer(f: Int32):
    _die("call through an unknown function pointer\n")


def zero_bytes(p: VP, n: Int):
    var b = p.unsafe_bitcast[UInt8]()
    for k in range(n):
        b[unsafe_offset=k] = 0


# ================================================================ strings

def strlen(p: P[Int8]) -> UInt64:
    var n = 0
    while p[unsafe_offset=n] != 0:
        n += 1
    return UInt64(n)


@always_inline
def slen(p: P[Int8]) -> Int:
    var n = 0
    while p[unsafe_offset=n] != 0:
        n += 1
    return n


def strcpy(d: P[Int8], src: P[Int8]) -> P[Int8]:
    var n = slen(src) + 1
    for i in range(n):
        d[unsafe_offset=i] = src[unsafe_offset=i]
    return d


def strcat(d: P[Int8], src: P[Int8]) -> P[Int8]:
    _ = strcpy(d.unsafe_offset(slen(d)), src)
    return d


def strcmp(a: P[Int8], b: P[Int8]) -> Int32:
    var i = 0
    while True:
        var x = Int32(UInt8(a[unsafe_offset=i]))
        var y = Int32(UInt8(b[unsafe_offset=i]))
        if x != y:
            return x - y
        if x == 0:
            return 0
        i += 1


def strchr(p: P[Int8], c: Int32) -> P[Int8]:
    var ch = Int8(c)
    var i = 0
    while True:
        if p[unsafe_offset=i] == ch:
            return p.unsafe_offset(i)
        if p[unsafe_offset=i] == 0:
            return null[Int8]()
        i += 1


def strrchr(p: P[Int8], c: Int32) -> P[Int8]:
    var ch = Int8(c)
    var n = slen(p)
    if ch == 0:
        return p.unsafe_offset(n)
    var i = n
    while i > 0:
        i -= 1
        if p[unsafe_offset=i] == ch:
            return p.unsafe_offset(i)
    return null[Int8]()


def strstr(h: P[Int8], n: P[Int8]) -> P[Int8]:
    var hl = slen(h)
    var nl = slen(n)
    var i = 0
    while i + nl <= hl:
        var k = 0
        while k < nl and h[unsafe_offset=i + k] == n[unsafe_offset=k]:
            k += 1
        if k == nl:
            return h.unsafe_offset(i)
        i += 1
    return null[Int8]()


def strcspn(p: P[Int8], rej: P[Int8]) -> UInt64:
    var n = slen(p)
    var m = slen(rej)
    for i in range(n):
        for k in range(m):
            if p[unsafe_offset=i] == rej[unsafe_offset=k]:
                return UInt64(i)
    return UInt64(n)


def _in_set(c: Int8, set0: P[Int8]) -> Bool:
    var k = 0
    while set0[unsafe_offset=k] != 0:
        if set0[unsafe_offset=k] == c:
            return True
        k += 1
    return False


def strtok(rt: P[RT], p: P[Int8], delim: P[Int8]) -> P[Int8]:
    if not isnull(p):
        rt[].tok_next = p
    var b = rt[].tok_next
    if isnull(b):
        return b
    var i = 0
    while b[unsafe_offset=i] != 0 and _in_set(b[unsafe_offset=i], delim):
        i += 1
    if b[unsafe_offset=i] == 0:
        rt[].tok_next = null[Int8]()
        return null[Int8]()
    var start = i
    while b[unsafe_offset=i] != 0 and not _in_set(b[unsafe_offset=i], delim):
        i += 1
    if b[unsafe_offset=i] != 0:
        b[unsafe_offset=i] = 0
        rt[].tok_next = b.unsafe_offset(i + 1)
    else:
        rt[].tok_next = null[Int8]()
    return b.unsafe_offset(start)


def toupper(c: Int32) -> Int32:
    if c >= 97 and c <= 122:
        return c - 32
    return c


@always_inline
def _space(c: Int) -> Bool:
    return c == 32 or (c >= 9 and c <= 13)


@always_inline
def _low(c: Int) -> Int:
    return c | 0x20 if (c >= 65 and c <= 90) else c


@always_inline
def _digit(c: Int) -> Bool:
    return c >= 48 and c <= 57


@always_inline
def _hexval(c: Int) -> Int:
    if c >= 48 and c <= 57:
        return c - 48
    var l = _low(c)
    if l >= 97 and l <= 102:
        return l - 87
    return -1


def atoi(p: P[Int8]) -> Int32:
    """(int)strtol(p, NULL, 10): the low 32 bits of a long that saturates on overflow"""
    var i = 0
    while p[unsafe_offset=i] != 0 and _space(Int(p[unsafe_offset=i])):
        i += 1
    var neg = False
    if p[unsafe_offset=i] == 43 or p[unsafe_offset=i] == 45:
        neg = p[unsafe_offset=i] == 45
        i += 1
    var v: Int64 = 0
    var over = False
    while _digit(Int(p[unsafe_offset=i])):
        var d = Int64(p[unsafe_offset=i]) - 48
        if v > (Int64(9223372036854775807) - d) // 10:
            over = True
        else:
            v = v * 10 + d
        i += 1
    if over:
        v = (Int64(-9223372036854775807) - 1) if neg else Int64(9223372036854775807)
    elif neg:
        v = -v
    return Int32(v)


# ================================================================ big integers (little-endian 32-bit limbs)

struct Big(Copyable, Movable):
    var w: List[UInt32]

    def __init__(out self):
        self.w = List[UInt32]()

    def __init__(out self, v: UInt64):
        self.w = List[UInt32]()
        self.w.append(UInt32(v & 0xFFFFFFFF))
        self.w.append(UInt32(v >> 32))
        self.trim()

    def trim(mut self):
        while len(self.w) > 0 and self.w[len(self.w) - 1] == 0:
            _ = self.w.pop()

    def is_zero(self) -> Bool:
        return len(self.w) == 0

    def mul_small(mut self, m: UInt32):
        var carry: UInt64 = 0
        for k in range(len(self.w)):
            var t = UInt64(self.w[k]) * UInt64(m) + carry
            self.w[k] = UInt32(t & 0xFFFFFFFF)
            carry = t >> 32
        if carry != 0:
            self.w.append(UInt32(carry))

    def add_small(mut self, a: UInt32):
        var carry = UInt64(a)
        var k = 0
        while carry != 0:
            if k == len(self.w):
                self.w.append(0)
            var t = UInt64(self.w[k]) + carry
            self.w[k] = UInt32(t & 0xFFFFFFFF)
            carry = t >> 32
            k += 1

    def mul_pow10(mut self, n: Int):
        var r = n
        while r >= 9:
            self.mul_small(1000000000)
            r -= 9
        var f: UInt32 = 1
        while r > 0:
            f *= 10
            r -= 1
        self.mul_small(f)

    def mul_pow5(mut self, n: Int):
        var r = n
        while r >= 13:
            self.mul_small(1220703125)
            r -= 13
        var f: UInt32 = 1
        while r > 0:
            f *= 5
            r -= 1
        self.mul_small(f)

    def shl(mut self, k: Int):
        if len(self.w) == 0 or k == 0:
            return
        var ws = k // 32
        var bs = k % 32
        var n = len(self.w)
        var out = List[UInt32]()
        for _ in range(n + ws + 1):
            out.append(0)
        for i in range(n):
            var v = UInt64(self.w[i]) << UInt64(bs)
            out[i + ws] = out[i + ws] | UInt32(v & 0xFFFFFFFF)
            out[i + ws + 1] = out[i + ws + 1] | UInt32(v >> 32)
        self.w = out^
        self.trim()

    def div_billion(mut self) -> UInt32:
        """divide by 10^9, returning the remainder"""
        var r: UInt64 = 0
        var i = len(self.w)
        while i > 0:
            i -= 1
            var t = (r << 32) | UInt64(self.w[i])
            self.w[i] = UInt32(t // 1000000000)
            r = t % 1000000000
        self.trim()
        return UInt32(r)

    def to_dec(mut self, mut dst: List[UInt8]):
        """the decimal digits (most significant first) appended to dst; nothing for zero"""
        var tmp = List[UInt8]()
        while len(self.w) > 0:
            var r = self.div_billion()
            for _ in range(9):
                tmp.append(UInt8(48 + r % 10))
                r //= 10
        var t = len(tmp)
        while t > 0 and tmp[t - 1] == 48:
            t -= 1
        var k = t
        while k > 0:
            k -= 1
            dst.append(tmp[k])

    def cmp(self, other: Big) -> Int:
        var a = len(self.w)
        var b = len(other.w)
        if a != b:
            return 1 if a > b else -1
        var i = a
        while i > 0:
            i -= 1
            if self.w[i] != other.w[i]:
                return 1 if self.w[i] > other.w[i] else -1
        return 0


# ================================================================ strtod

struct Scan(Copyable, Movable):
    var v: Float64
    var end: Int          # -1: no number
    var dec: Bool         # a decimal number: digits and exponent below are set
    var digits: List[UInt8]
    var exp10: Int
    var neg: Bool
    var hexf: Bool        # a hexadecimal number: mant and exp2 below
    var hmant: UInt64
    var hexp: Int
    var hsticky: Bool

    def __init__(out self):
        self.v = 0.0
        self.end = -1
        self.dec = False
        self.digits = List[UInt8]()
        self.exp10 = 0
        self.neg = False
        self.hexf = False
        self.hmant = 0
        self.hexp = 0
        self.hsticky = False


@always_inline
def _g(b: P[Int8], k: Int, lim: Int) -> Int:
    if k >= lim:
        return 0
    return Int(b[unsafe_offset=k])


def _scan(b: P[Int8], maxw: Int, skip_space: Bool, mut sc: Scan):
    """glibc's strtod syntax at b (at most maxw characters when maxw >= 0, after leading space when
    skip_space): sets sc.end (-1: no number) and either sc.v or the parsed digits"""
    var i = 0
    if skip_space:
        while b[unsafe_offset=i] != 0 and _space(Int(b[unsafe_offset=i])):
            i += 1
    var lim = i + maxw if maxw >= 0 else Int(0x7FFFFFFFFFFFFFFF)
    var neg = False
    if _g(b, i, lim) == 43 or _g(b, i, lim) == 45:
        neg = _g(b, i, lim) == 45
        i += 1
    sc.neg = neg
    if _low(_g(b, i, lim)) == 105 and _low(_g(b, i + 1, lim)) == 110 and _low(_g(b, i + 2, lim)) == 102:
        i += 3
        if (_low(_g(b, i, lim)) == 105 and _low(_g(b, i + 1, lim)) == 110 and _low(_g(b, i + 2, lim)) == 105
                and _low(_g(b, i + 3, lim)) == 116 and _low(_g(b, i + 4, lim)) == 121):
            i += 5
        sc.v = -inf64() if neg else inf64()
        sc.end = i
        return
    if _low(_g(b, i, lim)) == 110 and _low(_g(b, i + 1, lim)) == 97 and _low(_g(b, i + 2, lim)) == 110:
        i += 3
        var v = nan64()
        if _g(b, i, lim) == 40:
            var k = i + 1
            while True:
                var c = _g(b, k, lim)
                if _digit(c) or (c >= 65 and c <= 90) or (c >= 97 and c <= 122) or c == 95:
                    k += 1
                    continue
                break
            if _g(b, k, lim) == 41:
                # glibc reads the n-char-sequence with strtoull(seq, 0) and keeps it as the payload
                var pl: UInt64 = 0
                if _parse_payload(b, i + 1, k, pl):
                    v = f64bits(UInt64(0x7FF8000000000000) | (pl & ((UInt64(1) << 51) - 1)))
                i = k + 1
        sc.v = -v if neg else v
        sc.end = i
        return
    if _g(b, i, lim) == 48 and _low(_g(b, i + 1, lim)) == 120:       # hexadecimal (C99), as glibc reads it
        var j = i + 2
        var nh = 0
        var m: UInt64 = 0
        var e2 = 0
        var sticky = False
        var seen = False
        while _hexval(_g(b, j, lim)) >= 0:
            var d = UInt64(_hexval(_g(b, j, lim)))
            if d != 0:
                seen = True
            if m < (UInt64(1) << 56):
                m = m * 16 + d
            else:
                e2 += 4
                if d != 0:
                    sticky = True
            j += 1
            nh += 1
        if _g(b, j, lim) == 46:
            j += 1
            while _hexval(_g(b, j, lim)) >= 0:
                var d = UInt64(_hexval(_g(b, j, lim)))
                if m < (UInt64(1) << 56):
                    m = m * 16 + d
                    e2 -= 4
                elif d != 0:
                    sticky = True
                j += 1
                nh += 1
        if nh > 0:
            if _low(_g(b, j, lim)) == 112:
                var e = j + 1
                var eneg = False
                if _g(b, e, lim) == 43 or _g(b, e, lim) == 45:
                    eneg = _g(b, e, lim) == 45
                    e += 1
                if _digit(_g(b, e, lim)):
                    var ev = 0
                    while _digit(_g(b, e, lim)):
                        if ev < 100000:
                            ev = ev * 10 + _g(b, e, lim) - 48
                        e += 1
                    e2 += -ev if eneg else ev
                    j = e
            sc.hexf = True
            sc.hmant = m
            sc.hexp = e2
            sc.hsticky = sticky
            sc.end = j
            _ = seen
            return
        # "0x" with no hex digit: the number 0, ending before the x (falls through to the decimal reader)
    var nd = 0
    var exp10 = 0
    var started = False
    while _digit(_g(b, i, lim)):
        var c = _g(b, i, lim)
        if c != 48 or started:
            started = True
            sc.digits.append(UInt8(c - 48))
        i += 1
        nd += 1
    if _g(b, i, lim) == 46:
        i += 1
        while _digit(_g(b, i, lim)):
            var c = _g(b, i, lim)
            if c != 48 or started:
                started = True
                sc.digits.append(UInt8(c - 48))
            exp10 -= 1
            i += 1
            nd += 1
    if nd == 0:
        sc.end = -1
        return
    if _low(_g(b, i, lim)) == 101:
        var k = i + 1
        var eneg = False
        if _g(b, k, lim) == 43 or _g(b, k, lim) == 45:
            eneg = _g(b, k, lim) == 45
            k += 1
        if _digit(_g(b, k, lim)):
            var ev = 0
            while _digit(_g(b, k, lim)):
                if ev < 100000:
                    ev = ev * 10 + _g(b, k, lim) - 48
                k += 1
            exp10 += -ev if eneg else ev
            i = k
    sc.dec = True
    sc.exp10 = exp10
    sc.end = i


def _parse_payload(b: P[Int8], start: Int, end: Int, mut res: UInt64) -> Bool:
    """strtoull(seq, &e, 0) must consume the whole sequence b[start:end]"""
    var n = end - start
    if n == 0:
        return False
    var i = start
    var base: UInt64 = 10
    if n >= 2 and b[unsafe_offset=i] == 48 and _low(Int(b[unsafe_offset=i + 1])) == 120:
        base = 16
        i += 2
    elif b[unsafe_offset=i] == 48:
        base = 8
    if i >= end:
        return False
    var v: UInt64 = 0
    var over = False
    while i < end:
        var c = _low(Int(b[unsafe_offset=i]))
        var d: UInt64 = 99
        if _digit(c):
            d = UInt64(c - 48)
        elif c >= 97 and c <= 122:
            d = UInt64(c - 87)
        if d >= base:
            return False
        var nv = v * base + d
        if (nv - d) // base != v:
            over = True
        v = nv
        i += 1
    res = UInt64(0xFFFFFFFFFFFFFFFF) if over else v
    return True


def _pow10_exact(n: Int) -> Float64:
    var r: Float64 = 1.0
    for _ in range(n):
        r *= 10.0
    return r


def _round_big(mut num: Big, den: Big, bits: Int, emin: Int, emax: Int, mut e2: Int) -> Float64:
    """num/den * 2^e2 (positive) rounded to the nearest float with `bits` significant bits, ties to even;
    emin: the exponent of the smallest subnormal's unit; emax: the largest finite value's exponent (+1)"""
    # scale so that the quotient has bits+2 or more significant bits, then remember the remainder as sticky
    # (done by comparison, with no division: find q bit by bit from the top)
    # 1. find the binary length of num/den: shift until 2^(bits+1) <= num/den < 2^(bits+2)
    var nb = len(num.w) * 32
    var db = len(den.w) * 32
    var sh = (bits + 1) - (nb - db)
    var n2 = num.copy()
    var d2 = den.copy()
    if sh > 0:
        n2.shl(sh)
    elif sh < 0:
        d2.shl(-sh)
    e2 -= sh
    # adjust so that d2 * 2^(bits+1) <= n2 < d2 * 2^(bits+2)
    var lo = d2.copy()
    lo.shl(bits + 1)
    while n2.cmp(lo) < 0:
        n2.shl(1)
        e2 -= 1
    var hi = lo.copy()
    hi.shl(1)
    while n2.cmp(hi) >= 0:
        d2.shl(1)
        lo.shl(1)
        hi.shl(1)
        e2 += 1
    # now the quotient q = floor(n2/d2) has bits+2 significant bits; extract it by long division on bits
    var q: UInt64 = 0
    var rem = n2.copy()
    var dd = d2.copy()
    dd.shl(bits + 1)
    for _ in range(bits + 2):
        q = q << 1
        if rem.cmp(dd) >= 0:
            _sub(rem, dd)
            q |= 1
        _shr1(dd)
    var sticky = not rem.is_zero()
    # q has bits+2 bits; value = (q + frac) * 2^e2, exponent of q's lowest bit is e2
    # subnormal: the lowest kept bit may not be below emin
    var drop = 2
    if e2 + drop < emin:
        drop = emin - e2
    if drop > 62:
        return 0.0
    var keep = q >> UInt64(drop)
    var rbit = (q >> UInt64(drop - 1)) & 1
    var low_bits = q & ((UInt64(1) << UInt64(drop - 1)) - 1)
    if low_bits != 0:
        sticky = True
    if rbit == 1 and (sticky or (keep & 1) == 1):
        keep += 1
    var e = e2 + drop
    # keep * 2^e
    if keep == 0:
        return 0.0
    if keep >= (UInt64(1) << UInt64(bits)):
        keep >>= 1
        e += 1
    if e + bits > emax:
        return inf64()
    return Float64(keep) * _pow2(e)


def _pow2(e: Int) -> Float64:
    """2^e exactly (for the exponents a double or a float can hold, subnormals included)"""
    if e >= -1022 and e <= 1023:
        return f64bits(UInt64(e + 1023) << 52)
    if e < -1022:
        return f64bits(UInt64(1) << UInt64(e + 1074)) if e >= -1074 else 0.0
    return inf64()


def _sub(mut a: Big, b: Big):
    """a -= b (a >= b)"""
    var borrow: Int64 = 0
    for k in range(len(a.w)):
        var t = Int64(a.w[k]) - borrow - (Int64(b.w[k]) if k < len(b.w) else 0)
        if t < 0:
            t += Int64(1) << 32
            borrow = 1
        else:
            borrow = 0
        a.w[k] = UInt32(t)
    a.trim()


def _shr1(mut a: Big):
    var carry: UInt32 = 0
    var i = len(a.w)
    while i > 0:
        i -= 1
        var v = a.w[i]
        a.w[i] = (v >> 1) | (carry << 31)
        carry = v & 1
    a.trim()


def _decimal_value(sc: Scan, single: Bool) -> Float64:
    """the correctly rounded double (or float, when single) of the decimal number in sc"""
    var nd = len(sc.digits)
    var r: Float64 = 0.0
    if nd == 0:
        r = 0.0
    else:
        # Clinger's fast path: an exact integer below 2^53 times or over an exact power of ten
        var fast = False
        if not single and nd <= 15 and sc.exp10 >= -22 and sc.exp10 <= 22:
            var m: UInt64 = 0
            for k in range(nd):
                m = m * 10 + UInt64(sc.digits[k])
            var mf = Float64(m)
            if sc.exp10 >= 0:
                r = mf * _pow10_exact(sc.exp10)
            else:
                r = mf / _pow10_exact(-sc.exp10)
            fast = True
        if not fast:
            var e10 = sc.exp10
            if e10 + nd > 400:
                r = inf64() if not single else inf64()
            elif e10 + nd < -400:
                r = 0.0
            else:
                var num = Big(0)
                for k in range(nd):
                    num.mul_small(10)
                    num.add_small(UInt32(sc.digits[k]))
                var den = Big(1)
                if e10 >= 0:
                    num.mul_pow10(e10)
                else:
                    den.mul_pow10(-e10)
                var e2 = 0
                if single:
                    r = _round_big(num, den, 24, -149, 128, e2)
                else:
                    r = _round_big(num, den, 53, -1074, 1024, e2)
    return -r if sc.neg else r


def _hex_value(sc: Scan, single: Bool) -> Float64:
    var m = sc.hmant
    if m == 0:
        return -0.0 if sc.neg else 0.0
    var num = Big(m)
    if sc.hsticky:
        # the digits beyond those kept: a value strictly between m and m+1 (times 2^hexp)
        num.shl(1)
        num.add_small(1)
        var e2 = sc.hexp - 1
        var r = _round_big(num, Big(1), 24 if single else 53, -149 if single else -1074, 128 if single else 1024, e2)
        return -r if sc.neg else r
    var e2 = sc.hexp
    var r = _round_big(num, Big(1), 24 if single else 53, -149 if single else -1074, 128 if single else 1024, e2)
    return -r if sc.neg else r


def _scan_value(sc: Scan, single: Bool) -> Float64:
    if sc.dec:
        return _decimal_value(sc, single)
    if sc.hexf:
        return _hex_value(sc, single)
    return sc.v


def strtod(p: P[Int8], end: P[P[Int8]]) -> Float64:
    var sc = Scan()
    _scan(p, -1, True, sc)
    if not isnull(end):
        end[] = p if sc.end < 0 else p.unsafe_offset(sc.end)
    if sc.end < 0:
        return 0.0
    return _scan_value(sc, False)


def atof(p: P[Int8]) -> Float64:
    return strtod(p, null[P[Int8]]())


# ================================================================ printf and sscanf arguments

struct Arg(Copyable, Movable):
    """one variadic argument: kind 1 int (C int), 2 long, 3 unsigned int, 4 unsigned long, 5 double, 6 char*;
    as a sscanf target: 11 int*, 12 long*, 13 unsigned*, 15 double*, 16 float*, 17 char* (a buffer)"""
    var kind: Int
    var i: Int64
    var d: Float64
    var a: Int

    def __init__(out self, kind: Int, i: Int64, d: Float64, a: Int):
        self.kind = kind
        self.i = i
        self.d = d
        self.a = a


@always_inline
def ai(v: Int32) -> Arg:
    return Arg(1, Int64(v), 0.0, 0)


@always_inline
def al(v: Int64) -> Arg:
    return Arg(2, v, 0.0, 0)


@always_inline
def au(v: UInt32) -> Arg:
    return Arg(3, Int64(v), 0.0, 0)


@always_inline
def aul(v: UInt64) -> Arg:
    return Arg(4, Int64(v), 0.0, 0)


@always_inline
def ad(v: Float64) -> Arg:
    return Arg(5, 0, v, 0)


@always_inline
def astr(p: P[Int8]) -> Arg:
    return Arg(6, 0, 0.0, Int(p))


@always_inline
def tpi(p: P[Int32]) -> Arg:
    return Arg(11, 0, 0.0, Int(p))


@always_inline
def tpl(p: P[Int64]) -> Arg:
    return Arg(12, 0, 0.0, Int(p))


@always_inline
def tpu(p: P[UInt32]) -> Arg:
    return Arg(13, 0, 0.0, Int(p))


@always_inline
def tpd(p: P[Float64]) -> Arg:
    return Arg(15, 0, 0.0, Int(p))


@always_inline
def tpf(p: P[Float32]) -> Arg:
    return Arg(16, 0, 0.0, Int(p))


@always_inline
def tps(p: P[Int8]) -> Arg:
    return Arg(17, 0, 0.0, Int(p))


def _arg_long(a: Arg) -> Int64:
    if a.kind == 5:
        return d2i64(a.d)
    if a.kind == 6:
        return Int64(a.a)
    return a.i


def _arg_double(a: Arg) -> Float64:
    if a.kind == 5:
        return a.d
    if a.kind == 4:
        return Float64(UInt64(a.i))
    if a.kind == 6:
        return 0.0
    return Float64(a.i)


# ================================================================ sscanf

def sscanf(str0: P[Int8], fmt: P[Int8], *args: Arg) -> Int32:
    var b = str0
    var f = fmt
    var i = 0
    var k = 0
    var ai0 = 0
    var count: Int32 = 0
    var any_input = False
    var nf = slen(f)
    while k < nf:
        var fc = Int(f[unsafe_offset=k])
        if _space(fc):
            while k < nf and _space(Int(f[unsafe_offset=k])):
                k += 1
            while b[unsafe_offset=i] != 0 and _space(Int(b[unsafe_offset=i])):
                i += 1
            continue
        if fc != 37:
            if b[unsafe_offset=i] == 0:
                return count if (any_input or count > 0) else Int32(-1)
            if Int(b[unsafe_offset=i]) != fc:
                return count
            i += 1
            k += 1
            continue
        k += 1
        if f[unsafe_offset=k] == 37:
            while b[unsafe_offset=i] != 0 and _space(Int(b[unsafe_offset=i])):
                i += 1
            if b[unsafe_offset=i] != 37:
                return count
            i += 1
            k += 1
            continue
        var suppress = False
        if f[unsafe_offset=k] == 42:
            suppress = True
            k += 1
        var width = 0
        while k < nf and _digit(Int(f[unsafe_offset=k])):
            width = width * 10 + Int(f[unsafe_offset=k]) - 48
            k += 1
        while k < nf and (f[unsafe_offset=k] == 108 or f[unsafe_offset=k] == 104 or f[unsafe_offset=k] == 76):
            k += 1
        var conv = Int(f[unsafe_offset=k])
        k += 1
        if conv != 99 and conv != 91 and conv != 110:
            while b[unsafe_offset=i] != 0 and _space(Int(b[unsafe_offset=i])):
                i += 1
        if b[unsafe_offset=i] == 0 and conv != 110:
            return Int32(-1) if (count == 0 and not any_input) else count
        if conv == 100 or conv == 105 or conv == 117:
            var j = i
            var lim = i + width if width != 0 else Int(0x7FFFFFFFFFFFFFFF)
            var neg = False
            if j < lim and (b[unsafe_offset=j] == 43 or b[unsafe_offset=j] == 45):
                neg = b[unsafe_offset=j] == 45
                j += 1
            var ds = j
            var v: Int64 = 0
            var over = False
            while j < lim and _digit(Int(b[unsafe_offset=j])):
                var d = Int64(b[unsafe_offset=j]) - 48
                if v > (Int64(9223372036854775807) - d) // 10:
                    over = True
                else:
                    v = v * 10 + d
                j += 1
            if j == ds:
                return count
            i = j
            any_input = True
            if over:
                v = (Int64(-9223372036854775807) - 1) if neg else Int64(9223372036854775807)
            elif neg:
                v = -v
            if not suppress:
                var a = args[ai0].copy()
                if a.kind == 11:
                    P[Int32](unsafe_from_address=a.a)[] = Int32(v)
                elif a.kind == 12:
                    P[Int64](unsafe_from_address=a.a)[] = v
                elif a.kind == 13:
                    P[UInt32](unsafe_from_address=a.a)[] = UInt32(v)
                ai0 += 1
                count += 1
        elif conv == 102 or conv == 101 or conv == 103:
            var sc = Scan()
            _scan(b.unsafe_offset(i), width if width != 0 else -1, False, sc)
            if sc.end < 0:
                return count
            i += sc.end
            any_input = True
            if not suppress:
                var a = args[ai0].copy()
                if a.kind == 15:
                    P[Float64](unsafe_from_address=a.a)[] = _scan_value(sc, False)
                elif a.kind == 16:
                    P[Float32](unsafe_from_address=a.a)[] = Float32(_scan_value(sc, True))
                ai0 += 1
                count += 1
        elif conv == 115:
            var j = i
            var w = width if width != 0 else Int(0x7FFFFFFFFFFFFFFF)
            var m = 0
            while b[unsafe_offset=j] != 0 and not _space(Int(b[unsafe_offset=j])) and m < w:
                j += 1
                m += 1
            if not suppress:
                var d = P[Int8](unsafe_from_address=args[ai0].a)
                ai0 += 1
                for q in range(m):
                    d[unsafe_offset=q] = b[unsafe_offset=i + q]
                d[unsafe_offset=m] = 0
                count += 1
            i = j
            any_input = True
        elif conv == 99:
            var cnt = width if width != 0 else 1
            if b[unsafe_offset=i] == 0:
                return Int32(-1) if (count == 0 and not any_input) else count
            var d = null[Int8]()
            if not suppress:
                d = P[Int8](unsafe_from_address=args[ai0].a)
                ai0 += 1
            var t = 0
            while t < cnt and b[unsafe_offset=i] != 0:
                if not suppress:
                    d[unsafe_offset=t] = b[unsafe_offset=i]
                i += 1
                t += 1
            any_input = True
            if not suppress:
                count += 1
        else:
            return count
    return count


# ================================================================ printf

struct Digits(Copyable, Movable):
    """the exact decimal expansion of a positive finite double: d[0:n] with the point after d[0:p]"""
    var d: List[UInt8]
    var p: Int

    def __init__(out self):
        self.d = List[UInt8]()
        self.p = 0


def _exact_digits(v: Float64, mut dg: Digits):
    var bits = bits64(v)
    var ex = Int((bits >> 52) & 0x7FF)
    var m = bits & ((UInt64(1) << 52) - 1)
    var e: Int
    if ex == 0:
        e = -1074
    else:
        e = ex - 1075
        m |= UInt64(1) << 52
    if e >= 0:
        var b = Big(m)
        b.shl(e)
        b.to_dec(dg.d)
        dg.p = len(dg.d)
        if dg.p == 0:
            dg.d.append(48)
            dg.p = 1
        return
    var k = -e
    var ip: UInt64 = m >> UInt64(k) if k < 64 else 0
    var fp: UInt64 = m & ((UInt64(1) << UInt64(k)) - 1) if k < 64 else m
    var ib = Big(ip)
    ib.to_dec(dg.d)
    if len(dg.d) == 0:
        dg.d.append(48)
    var ilen = len(dg.d)
    dg.p = ilen
    # fraction: fp / 2^k = fp * 5^k / 10^k: k digits
    var b = Big(fp)
    b.mul_pow5(k)
    var fd = List[UInt8]()
    b.to_dec(fd)
    var lead = k - len(fd)
    for _ in range(lead):
        dg.d.append(48)
    for q in range(len(fd)):
        dg.d.append(fd[q])
    var t = len(dg.d)
    while t > ilen and dg.d[t - 1] == 48:
        _ = dg.d.pop()
        t -= 1


def _round_digits(mut d: List[UInt8], keep: Int) -> Bool:
    """round d to its first keep digits, half to even on the exact value; d is then exactly keep long;
    True if the carry ran off the front (all nines: the caller prepends a 1)"""
    var n = len(d)
    if keep >= n:
        while len(d) < keep:
            d.append(48)
        return False
    var nxt = d[keep]
    var up = False
    if nxt > 53:
        up = True
    elif nxt == 53:
        var rest = False
        for k in range(keep + 1, n):
            if d[k] != 48:
                rest = True
                break
        if rest:
            up = True
        else:
            up = keep > 0 and (Int(d[keep - 1]) - 48) % 2 == 1
    while len(d) > keep:
        _ = d.pop()
    if not up:
        return False
    var k = keep
    while k > 0:
        k -= 1
        if d[k] == 57:
            d[k] = 48
        else:
            d[k] = d[k] + 1
            return False
    return True


def _fixed(mut o: List[UInt8], a: Float64, prec: Int, alt: Bool):
    """%.{prec}f of a positive finite value"""
    var dg = Digits()
    _exact_digits(a, dg)
    var keep = dg.p + prec
    var p = dg.p
    var w = dg.d.copy()
    if _round_digits(w, keep):
        w.insert(0, 49)
        p += 1
        keep += 1
    for k in range(p):
        o.append(w[k])
    if prec > 0 or alt:
        o.append(46)
    for k in range(p, keep):
        o.append(w[k])


def _exp_raw(a: Float64, sig: Int, mut res: List[UInt8]) -> Int:
    """the digits of a positive finite value rounded to sig significant digits, and its decimal exponent"""
    var dg = Digits()
    _exact_digits(a, dg)
    var f = 0
    while f < len(dg.d) and dg.d[f] == 48:
        f += 1
    var x = dg.p - 1 - f
    var w = List[UInt8]()
    for k in range(f, len(dg.d)):
        w.append(dg.d[k])
    if _round_digits(w, sig):
        res.append(49)
        for _ in range(1, sig):
            res.append(48)
        x += 1
    else:
        for k in range(sig):
            res.append(w[k])
    return x


def _expf(mut o: List[UInt8], a: Float64, prec: Int, alt: Bool, upper: Bool):
    var d = List[UInt8]()
    var x = 0
    if a == 0:
        for _ in range(prec + 1):
            d.append(48)
    else:
        x = _exp_raw(a, prec + 1, d)
    o.append(d[0])
    if prec > 0:
        o.append(46)
        for k in range(1, prec + 1):
            o.append(d[k])
    elif alt:
        o.append(46)
    o.append(UInt8(69) if upper else UInt8(101))
    if x < 0:
        o.append(45)
        x = -x
    else:
        o.append(43)
    if x < 10:
        o.append(48)
    var tmp = List[UInt8]()
    if x == 0:
        tmp.append(48)
    while x > 0:
        tmp.append(UInt8(48 + x % 10))
        x //= 10
    var k = len(tmp)
    while k > 0:
        k -= 1
        o.append(tmp[k])


def _float(mut o: List[UInt8], a: Float64, conv: Int, prec: Int, alt: Bool):
    var lc = conv | 0x20
    if lc == 102:
        _fixed(o, a, prec, alt)
        return
    if lc == 101:
        _expf(o, a, prec, alt, conv == 69)
        return
    var pp = 1 if prec == 0 else prec
    var xx = 0
    if a != 0:
        var d = List[UInt8]()
        xx = _exp_raw(a, pp, d)
    var sub = List[UInt8]()
    if pp > xx and xx >= -4:
        _fixed(sub, a, pp - 1 - xx, alt)
    else:
        _expf(sub, a, pp - 1, alt, conv == 71)
    if alt:
        for k in range(len(sub)):
            o.append(sub[k])
        return
    var ep = len(sub)
    for k in range(len(sub)):
        if sub[k] == 101 or sub[k] == 69:
            ep = k
            break
    var has_point = False
    for k in range(ep):
        if sub[k] == 46:
            has_point = True
    var e = ep
    if has_point:
        while e > 0 and sub[e - 1] == 48:
            e -= 1
        if e > 0 and sub[e - 1] == 46:
            e -= 1
    for k in range(e):
        o.append(sub[k])
    for k in range(ep, len(sub)):
        o.append(sub[k])


def _int_body(mut o: List[UInt8], uval: UInt64, base: UInt64, upper: Bool, prec: Int):
    var tmp = List[UInt8]()
    var u = uval
    while u != 0:
        var dgt = Int(u % base)
        tmp.append(UInt8(48 + dgt) if dgt < 10 else UInt8((55 if upper else 87) + dgt))
        u //= base
    if prec < 0:
        if len(tmp) == 0:
            tmp.append(48)
    else:
        while len(tmp) < prec:
            tmp.append(48)
    var k = len(tmp)
    while k > 0:
        k -= 1
        o.append(tmp[k])


def format(mut o: List[UInt8], fmt: P[Int8], args: VariadicList[Arg, ...]):
    var k = 0
    var ai0 = 0
    var f = fmt
    while f[unsafe_offset=k] != 0:
        if f[unsafe_offset=k] != 37:
            o.append(UInt8(f[unsafe_offset=k]))
            k += 1
            continue
        k += 1
        if f[unsafe_offset=k] == 37:
            o.append(37)
            k += 1
            continue
        var left = False
        var plus = False
        var space = False
        var alt = False
        var zero = False
        while True:
            var c = Int(f[unsafe_offset=k])
            if c == 45:
                left = True
            elif c == 43:
                plus = True
            elif c == 32:
                space = True
            elif c == 35:
                alt = True
            elif c == 48:
                zero = True
            else:
                break
            k += 1
        var width = 0
        var prec = -1
        if f[unsafe_offset=k] == 42:
            var w = _arg_long(args[ai0])
            ai0 += 1
            if w < 0:
                left = True
                width = Int(-w)
            else:
                width = Int(w)
            k += 1
        else:
            while _digit(Int(f[unsafe_offset=k])):
                width = width * 10 + Int(f[unsafe_offset=k]) - 48
                k += 1
        if f[unsafe_offset=k] == 46:
            k += 1
            prec = 0
            if f[unsafe_offset=k] == 42:
                var pv = _arg_long(args[ai0])
                ai0 += 1
                prec = -1 if pv < 0 else Int(pv)
                k += 1
            else:
                while _digit(Int(f[unsafe_offset=k])):
                    prec = prec * 10 + Int(f[unsafe_offset=k]) - 48
                    k += 1
        var lng = False
        while True:
            var c = Int(f[unsafe_offset=k])
            if c == 108 or c == 76 or c == 122 or c == 106 or c == 116 or c == 113:
                lng = True
            elif c != 104:
                break
            k += 1
        var conv = Int(f[unsafe_offset=k])
        k += 1
        var sign = 0
        var body = List[UInt8]()
        var numeric = True
        if conv == 100 or conv == 105:
            var v = _arg_long(args[ai0])
            if args[ai0].kind == 1 or not lng:
                v = Int64(Int32(v))
            ai0 += 1
            if v < 0:
                sign = 45
            elif plus:
                sign = 43
            elif space:
                sign = 32
            var u = UInt64(0) - UInt64(v) if v < 0 else UInt64(v)
            _int_body(body, u, 10, False, prec)
            if prec >= 0:
                zero = False
        elif conv == 117 or conv == 120 or conv == 88 or conv == 111:
            var a = args[ai0].copy()
            ai0 += 1
            var u = UInt64(_arg_long(a))
            if a.kind == 1 or a.kind == 3 or not lng:
                u &= 0xFFFFFFFF
            var base: UInt64 = UInt64(10) if conv == 117 else (UInt64(8) if conv == 111 else UInt64(16))
            _int_body(body, u, base, conv == 88, prec)
            if prec >= 0:
                zero = False
        elif conv == 99:
            numeric = False
            var v = _arg_long(args[ai0])
            ai0 += 1
            body.append(UInt8(v & 255))
        elif conv == 115:
            numeric = False
            var pa = args[ai0].a
            ai0 += 1
            if pa == 0:
                for c in "(null)".as_bytes():
                    body.append(c)
            else:
                var p = P[Int8](unsafe_from_address=pa)
                var n = slen(p)
                if prec >= 0 and n > prec:
                    n = prec
                for q in range(n):
                    body.append(UInt8(p[unsafe_offset=q]))
        elif conv == 102 or conv == 70 or conv == 101 or conv == 69 or conv == 103 or conv == 71:
            var v = _arg_double(args[ai0])
            ai0 += 1
            var pr = 6 if prec < 0 else prec
            if signbit(v):
                sign = 45
            elif plus:
                sign = 43
            elif space:
                sign = 32
            var upper = conv == 70 or conv == 69 or conv == 71
            if v != v:
                for c in ("NAN" if upper else "nan").as_bytes():
                    body.append(c)
                zero = False
            elif fabs(v) == inf64():
                for c in ("INF" if upper else "inf").as_bytes():
                    body.append(c)
                zero = False
            else:
                _float(body, fabs(v), conv, pr, alt)
        else:
            numeric = False
        var n = (1 if sign != 0 else 0) + len(body)
        if n >= width:
            if sign != 0:
                o.append(UInt8(sign))
            o.extend(body^)
        elif left:
            if sign != 0:
                o.append(UInt8(sign))
            o.extend(body^)
            for _ in range(width - n):
                o.append(32)
        elif zero and numeric:
            if sign != 0:
                o.append(UInt8(sign))
            for _ in range(width - n):
                o.append(48)
            o.extend(body^)
        else:
            for _ in range(width - n):
                o.append(32)
            if sign != 0:
                o.append(UInt8(sign))
            o.extend(body^)


def fprintf(f: P[FILE], fmt: P[Int8], *args: Arg) -> Int32:
    var o = List[UInt8]()
    format(o, fmt, args)
    if isnull(f):
        return -1
    _fwrite_bytes(f, o)
    return Int32(len(o))


def snprintf(d: P[Int8], n: UInt64, fmt: P[Int8], *args: Arg) -> Int32:
    var o = List[UInt8]()
    format(o, fmt, args)
    if n > 0:
        var m = len(o) if UInt64(len(o)) < n - 1 else Int(n - 1)
        for k in range(m):
            d[unsafe_offset=k] = Int8(o[k])
        d[unsafe_offset=m] = 0
    return Int32(len(o))


# ================================================================ stdio

comptime BUFSZ = 65536

struct FILE(Movable):
    var fd: Int32
    var std: Int32
    var eof: Int32
    var append: Int32
    var pos: Int64
    var wpos: Int64
    var wlen: Int64
    var rstart: Int64
    var rlen: Int64
    var wbuf: P[UInt8]
    var rbuf: P[UInt8]

    def __init__(out self, fd: Int32, std: Int32):
        self.fd = fd
        self.std = std
        self.eof = 0
        self.append = 0
        self.pos = 0
        self.wpos = 0
        self.wlen = 0
        self.rstart = 0
        self.rlen = 0
        self.wbuf = null[UInt8]()
        self.rbuf = null[UInt8]()


struct RT(Movable):
    """the runtime's state (Mojo 1.2 has no global variables), and the stack the engine keeps the C locals
    whose address is taken in (stk, sp, cap: see salloc)"""
    var stdout: P[FILE]
    var tok_next: P[Int8]
    var rnd: UInt64
    var ctime_buf: P[Int8]
    var stk: P[UInt8]
    var sp: Int
    var cap: Int

    def __init__(out self):
        self.stdout = null[FILE]()
        self.tok_next = null[Int8]()
        self.rnd = 0
        self.ctime_buf = null[Int8]()
        self.stk = null[UInt8]()
        self.sp = 0
        self.cap = 0


def rt_init() -> P[RT]:
    var r = calloc(1, UInt64(size_of[RT]())).unsafe_bitcast[RT]()
    r[].stdout = calloc(1, UInt64(size_of[FILE]())).unsafe_bitcast[FILE]()
    r[].stdout[].fd = 1
    r[].stdout[].std = 1
    r[].tok_next = null[Int8]()
    r[].rnd = 0
    r[].ctime_buf = calloc(1, 64).unsafe_bitcast[Int8]()
    r[].cap = 1 << 26
    r[].stk = calloc(1, UInt64(r[].cap)).unsafe_bitcast[UInt8]()
    r[].sp = 0
    return r


@always_inline
def salloc[T: AnyType](r: P[RT], n: Int) -> P[T]:
    """n zeroed objects of type T for a C local whose address is taken, on the engine's own stack. They are
    not in a Mojo stack slot because Mojo 1.2 marks a call `tail` (LLVM: the callee touches none of the
    caller's stack) even when the slot's address, as an untracked pointer, is passed to it, and LLVM then
    reads the slot as if the callee had not written it. The function gives the space back on return."""
    var size = (n * size_of[T]() + 15) & ~15
    var p = r[].stk.unsafe_offset(r[].sp)
    r[].sp += size
    if r[].sp > r[].cap:
        _die("the engine's stack is full\n")
    for k in range(size):
        p[unsafe_offset=k] = 0
    return p.unsafe_bitcast[T]()


def _die(msg: StaticString):
    _ = external_call["write", Int](Int32(2), VP(unsafe_from_address=Int(msg.unsafe_ptr())), Int(msg.byte_length()))
    external_call["exit", NoneType](Int32(3))


def _write_all(f: P[FILE], b: P[UInt8], n: Int, at: Int64):
    var done = 0
    while done < n:
        var r: Int
        var src = VP(unsafe_from_address=Int(b) + done)
        if f[].std != 0:
            r = external_call["write", Int](f[].fd, src, n - done)
        else:
            r = external_call["pwrite", Int](f[].fd, src, n - done, Int(at) + done)
        if r <= 0:
            _die("write error\n")
        done += r


def _flush_w(f: P[FILE]):
    if f[].wlen == 0:
        return
    _write_all(f, f[].wbuf, Int(f[].wlen), f[].wpos)
    f[].wlen = 0


def _fsize(f: P[FILE]) -> Int64:
    _flush_w(f)
    return Int64(external_call["lseek", Int](f[].fd, Int(0), Int32(2)))


def _fwrite_raw(f: P[FILE], src: P[UInt8], n0: Int):
    var n = Int64(n0)
    f[].rlen = 0
    if isnull(f[].wbuf):
        f[].wbuf = calloc(1, BUFSZ).unsafe_bitcast[UInt8]()
    if f[].append != 0 and f[].std == 0:
        _flush_w(f)
        f[].pos = _fsize(f)
    if f[].wlen > 0 and f[].pos != f[].wpos + f[].wlen:
        _flush_w(f)
    if f[].wlen == 0:
        f[].wpos = f[].pos
    if f[].wlen + n > BUFSZ:
        _flush_w(f)
        if n > BUFSZ:
            _write_all(f, src, n0, f[].pos)
            f[].pos += n
            return
        f[].wpos = f[].pos
    var w = f[].wbuf.unsafe_offset(Int(f[].wlen))
    for k in range(n0):
        w[unsafe_offset=k] = src[unsafe_offset=k]
    f[].wlen += n
    f[].pos += n


def _fwrite_bytes(f: P[FILE], o: List[UInt8]):
    if len(o) == 0:
        return
    var p = P[UInt8](unsafe_from_address=Int(o.unsafe_ptr()))
    _fwrite_raw(f, p, len(o))


def _read_bytes(f: P[FILE], dst: P[UInt8], n: Int) -> Int:
    _flush_w(f)
    var got = 0
    while got < n:
        if f[].rlen > 0 and f[].pos >= f[].rstart and f[].pos < f[].rstart + f[].rlen:
            var a = Int(f[].pos - f[].rstart)
            var m = n - got
            if m > Int(f[].rlen) - a:
                m = Int(f[].rlen) - a
            for k in range(m):
                dst[unsafe_offset=got + k] = f[].rbuf[unsafe_offset=a + k]
            got += m
            f[].pos += Int64(m)
            continue
        if isnull(f[].rbuf):
            f[].rbuf = calloc(1, BUFSZ).unsafe_bitcast[UInt8]()
        f[].rstart = f[].pos
        var r = external_call["pread", Int](f[].fd, f[].rbuf.unsafe_bitcast[NoneType](), Int(BUFSZ), Int(f[].pos))
        f[].rlen = Int64(r) if r > 0 else 0
        if r <= 0:
            break
    return got


@always_inline
def _getc(f: P[FILE]) -> Int:
    if f[].wlen == 0 and f[].rlen > 0 and f[].pos >= f[].rstart and f[].pos < f[].rstart + f[].rlen:
        var c = Int(f[].rbuf[unsafe_offset=Int(f[].pos - f[].rstart)])
        f[].pos += 1
        return c
    var t = calloc(1, 1).unsafe_bitcast[UInt8]()
    var c = -1
    if _read_bytes(f, t, 1) == 1:
        c = Int(t[])
    free(t.unsafe_bitcast[NoneType]())
    return c


def fopen(name: P[Int8], mode: P[Int8]) -> P[FILE]:
    var m0 = 0
    var plus = False
    var k = 0
    var ml = 0
    while mode[unsafe_offset=k] != 0 and ml < 8:
        var c = Int(mode[unsafe_offset=k])
        if c != 98 and c != 116:
            if ml == 0:
                m0 = c
            elif ml == 1 and c == 43:
                plus = True
            ml += 1
        k += 1
    if ml == 0:
        return null[FILE]()
    var flags: Int32 = 0
    if m0 == 114:
        flags = Int32(2) if plus else Int32(0)
    elif m0 == 119:
        flags = (Int32(2) if plus else Int32(1)) | 0o100 | 0o1000
    elif m0 == 97:
        flags = (Int32(2) if plus else Int32(1)) | 0o100 | 0o2000
    else:
        return null[FILE]()
    var fd = external_call["open", Int32](name.unsafe_bitcast[NoneType](), flags, UInt32(0o666))
    if fd < 0:
        return null[FILE]()
    var f = calloc(1, UInt64(size_of[FILE]())).unsafe_bitcast[FILE]()
    f[].fd = fd
    if m0 == 97:
        f[].append = 1
        f[].pos = Int64(external_call["lseek", Int](fd, Int(0), Int32(2)))
    return f


def fclose(f: P[FILE]) -> Int32:
    if isnull(f):
        return -1
    _flush_w(f)
    if f[].std != 0:
        return 0
    var r = external_call["close", Int32](f[].fd)
    if not isnull(f[].wbuf):
        free(f[].wbuf.unsafe_bitcast[NoneType]())
    if not isnull(f[].rbuf):
        free(f[].rbuf.unsafe_bitcast[NoneType]())
    free(f.unsafe_bitcast[NoneType]())
    return Int32(0) if r == 0 else Int32(-1)


def fflush(f: P[FILE]) -> Int32:
    if not isnull(f):
        _flush_w(f)
    return 0


def feof(f: P[FILE]) -> Int32:
    return Int32(1) if f[].eof != 0 else Int32(0)


def rewind(f: P[FILE]):
    _flush_w(f)
    f[].pos = 0
    f[].eof = 0


def fseek(f: P[FILE], off: Int64, whence: Int32) -> Int32:
    _flush_w(f)
    var p = off
    if whence == 1:
        p = f[].pos + off
    elif whence == 2:
        p = _fsize(f) + off
    if p < 0:
        return -1
    f[].pos = p
    f[].eof = 0
    return 0


def ftell(f: P[FILE]) -> Int64:
    return f[].pos


def fgets(b: P[Int8], n: Int32, f: P[FILE]) -> P[Int8]:
    var m = 0
    while Int64(m) < Int64(n) - 1:
        var c = _getc(f)
        if c < 0:
            f[].eof = 1
            break
        b[unsafe_offset=m] = Int8(c)
        m += 1
        if c == 10:
            break
    if m == 0:
        return null[Int8]()
    b[unsafe_offset=m] = 0
    return b


def fread(p: VP, size: UInt64, n: UInt64, f: P[FILE]) -> UInt64:
    """the bytes go straight into the caller's memory, as C's do (a short read fills part of an item)"""
    var total = Int(size * n)
    if total == 0:
        return 0
    var got = _read_bytes(f, p.unsafe_bitcast[UInt8](), total)
    if got < total:
        f[].eof = 1
    return UInt64(got) // size


def fwrite(p: VP, size: UInt64, n: UInt64, f: P[FILE]) -> UInt64:
    var total = Int(size * n)
    if total == 0:
        return 0
    _fwrite_raw(f, p.unsafe_bitcast[UInt8](), total)
    return n


def remove(name: P[Int8]) -> Int32:
    return Int32(0) if external_call["unlink", Int32](name.unsafe_bitcast[NoneType]()) == 0 else Int32(-1)


def mkstemp(rt: P[RT], tmpl: P[Int8]) -> Int32:
    """six random characters, created exclusively (the descriptor is left open, as EPA leaves it)"""
    var chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789".as_bytes()
    if rt[].rnd == 0:
        var t = external_call["time", Int](Int(0))
        var pid = external_call["getpid", Int32]()
        rt[].rnd = ((UInt64(t) << 20) ^ UInt64(pid)) | 1
    var n = slen(tmpl)
    if n < 6:
        return -1
    for _ in range(1000):
        for i in range(n - 6, n):
            var r = rt[].rnd
            r ^= r << 13
            r ^= r >> 7
            r ^= r << 17
            rt[].rnd = r
            tmpl[unsafe_offset=i] = Int8(chars[Int(r % 62)])
        var fd = external_call["open", Int32](tmpl.unsafe_bitcast[NoneType](), Int32(0o2 | 0o100 | 0o200), UInt32(0o600))
        if fd >= 0:
            return fd
    return -1


def realpath(path: P[Int8], resolved: P[Int8]) -> P[Int8]:
    """the current directory joined to a relative path, with "." and ".." removed"""
    var src = List[UInt8]()
    var pl = slen(path)
    if pl == 0 or path[] != 47:
        var buf = calloc(1, 8192).unsafe_bitcast[Int8]()
        var r = external_call["getcwd", VP](buf.unsafe_bitcast[NoneType](), Int(8192))
        if isnull(r):
            free(buf.unsafe_bitcast[NoneType]())
            return null[Int8]()
        for q in range(slen(buf)):
            src.append(UInt8(buf[unsafe_offset=q]))
        free(buf.unsafe_bitcast[NoneType]())
    src.append(47)
    for q in range(pl):
        src.append(UInt8(path[unsafe_offset=q]))
    var res = List[UInt8]()
    var i = 0
    var n = len(src)
    while i <= n:
        var j = i
        while j < n and src[j] != 47:
            j += 1
        var cl = j - i
        if cl == 0 or (cl == 1 and src[i] == 46):
            pass
        elif cl == 2 and src[i] == 46 and src[i + 1] == 46:
            while len(res) > 0 and res[len(res) - 1] != 47:
                _ = res.pop()
            if len(res) > 0:
                _ = res.pop()
        else:
            res.append(47)
            for q in range(i, j):
                res.append(src[q])
        i = j + 1
    if len(res) == 0:
        res.append(47)
    for q in range(len(res)):
        resolved[unsafe_offset=q] = Int8(res[q])
    resolved[unsafe_offset=len(res)] = 0
    return resolved


# ================================================================ time

def time(t: P[Int64]) -> Int64:
    var v = Int64(external_call["time", Int](Int(0)))
    if not isnull(t):
        t[] = v
    return v


def difftime(a: Int64, b: Int64) -> Float64:
    return Float64(a) - Float64(b)


def ctime(rt: P[RT], t: P[Int64]) -> P[Int8]:
    """ctime: "Www Mmm dd hh:mm:ss yyyy\\n" (UTC; only the report's clock lines use it)"""
    var secs = Int(t[]) if t[] > 0 else 0
    var days = secs // 86400
    var ds = secs % 86400
    var wd = (days + 4) % 7
    # civil date from days since 1970-01-01 (Howard Hinnant's algorithm)
    var z = days + 719468
    var era = z // 146097
    var doe = z - era * 146097
    var yoe = (doe - doe // 1460 + doe // 36524 - doe // 146096) // 365
    var y = yoe + era * 400
    var doy = doe - (365 * yoe + yoe // 4 - yoe // 100)
    var mp = (5 * doy + 2) // 153
    var d = doy - (153 * mp + 2) // 5 + 1
    var m = mp + 3 if mp < 10 else mp - 9
    if m <= 2:
        y += 1
    var wn = "SunMonTueWedThuFriSat".as_bytes()
    var mn = "JanFebMarAprMayJunJulAugSepOctNovDec".as_bytes()
    var o = List[UInt8]()
    for k in range(3):
        o.append(wn[wd * 3 + k])
    o.append(32)
    for k in range(3):
        o.append(mn[(m - 1) * 3 + k])
    o.append(32)
    o.append(UInt8(32 if d < 10 else 48 + d // 10))
    o.append(UInt8(48 + d % 10))
    o.append(32)
    var hh = ds // 3600
    var mi = (ds % 3600) // 60
    var ss = ds % 60
    for v in [hh, mi, ss]:
        o.append(UInt8(48 + v // 10))
        o.append(UInt8(48 + v % 10))
        o.append(58)
    _ = o.pop()
    o.append(32)
    var yy = y
    var ys = List[UInt8]()
    while yy > 0:
        ys.append(UInt8(48 + yy % 10))
        yy //= 10
    var k = len(ys)
    while k > 0:
        k -= 1
        o.append(ys[k])
    o.append(10)
    for q in range(len(o)):
        rt[].ctime_buf[unsafe_offset=q] = Int8(o[q])
    rt[].ctime_buf[unsafe_offset=len(o)] = 0
    return rt[].ctime_buf


def conout(rt: P[RT], x: StaticString):
    """write a Mojo string to standard output at once (for the command-line runner)"""
    var o = List[UInt8]()
    for c in x.as_bytes():
        o.append(c)
    _fwrite_bytes(rt[].stdout, o)
    _flush_w(rt[].stdout)


def conout_bytes(rt: P[RT], o: List[UInt8]):
    _fwrite_bytes(rt[].stdout, o)
    _flush_w(rt[].stdout)
