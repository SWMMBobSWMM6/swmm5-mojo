# crtcheck.mojo - compare the Mojo runtime's printf, strtod and sscanf (swmm5/rt.mojo) with the system glibc's
# results written by tools/crt/test/mkfmt.c (lines KIND \t FORMAT \t ARG \t RESULT, hex-encoded).
#   mojo/test/run_crtcheck.sh  (builds mkfmt and this program, runs both, prints the summary)
# Written by Claude (Anthropic) for Robert Dickinson; see ../README.md.
from std.sys import argv
from std.collections import List
from swmm5.rt import *
from swmm5.rt import _hexval


def unhex(p: P[Int8], start: Int, end: Int, dst: P[Int8]) -> Int:
    var n = 0
    var i = start
    while i + 1 < end:
        dst[unsafe_offset=n] = Int8((_hexval(Int(p[unsafe_offset=i])) << 4) | _hexval(Int(p[unsafe_offset=i + 1])))
        n += 1
        i += 2
    dst[unsafe_offset=n] = 0
    return n


def hexu(p: P[Int8], start: Int, end: Int) -> UInt64:
    var v: UInt64 = 0
    for i in range(start, end):
        v = v * 16 + UInt64(_hexval(Int(p[unsafe_offset=i])))
    return v


def tohex(mut o: List[UInt8], p: P[Int8]):
    var d = "0123456789abcdef".as_bytes()
    var i = 0
    while p[unsafe_offset=i] != 0:
        var c = Int(UInt8(p[unsafe_offset=i]))
        o.append(d[c >> 4])
        o.append(d[c & 15])
        i += 1


def hex64(mut o: List[UInt8], v: UInt64):
    var d = "0123456789abcdef".as_bytes()
    var k = 60
    while k >= 0:
        o.append(d[Int((v >> UInt64(k)) & 15)])
        k -= 4


def dec(mut o: List[UInt8], v0: Int64):
    var v = v0
    if v < 0:
        o.append(45)
        v = -v
    var t = List[UInt8]()
    if v == 0:
        t.append(48)
    while v > 0:
        t.append(UInt8(48 + Int(v % 10)))
        v //= 10
    var k = len(t)
    while k > 0:
        k -= 1
        o.append(t[k])


def main():
    var rt = rt_init()
    var args = argv()
    var path = calloc(1, 4096).unsafe_bitcast[Int8]()
    var a1 = args[1].as_bytes()
    for k in range(len(a1)):
        path[unsafe_offset=k] = Int8(a1[k])
    var f = fopen(path, s("r"))
    var line = calloc(1, 8192).unsafe_bitcast[Int8]()
    var fmt = calloc(1, 256).unsafe_bitcast[Int8]()
    var arg = calloc(1, 4096).unsafe_bitcast[Int8]()
    var out = calloc(1, 4096).unsafe_bitcast[Int8]()
    var total = List[Int]()
    var bad = List[Int]()
    for _ in range(6):
        total.append(0)
        bad.append(0)
    var shown = 0
    while not isnull(fgets(line, 8192, f)):
        var n = slen(line)
        if n > 0 and line[unsafe_offset=n - 1] == 10:
            n -= 1
            line[unsafe_offset=n] = 0
        if n == 0:
            continue
        # fields: KIND \t FORMAT \t ARG \t RESULT
        var t1 = 0
        while line[unsafe_offset=t1] != 9:
            t1 += 1
        var t2 = t1 + 1
        while line[unsafe_offset=t2] != 9:
            t2 += 1
        var t3 = t2 + 1
        while line[unsafe_offset=t3] != 9:
            t3 += 1
        var kind = Int(line[])
        for q in range(t1 + 1, t2):
            fmt[unsafe_offset=q - t1 - 1] = line[unsafe_offset=q]
        fmt[unsafe_offset=t2 - t1 - 1] = 0
        var got = List[UInt8]()
        var k = -1
        if kind == 102:       # f
            k = 0
            var x = f64bits(hexu(line, t2 + 1, t3))
            if strcmp(fmt, s("%*.*f")) == 0:
                _ = snprintf(out, 4096, fmt, ai(9), ai(3), ad(x))
            else:
                _ = snprintf(out, 4096, fmt, ad(x))
            tohex(got, out)
        elif kind == 105:     # i
            k = 1
            _ = snprintf(out, 4096, fmt, ai(Int32(UInt32(hexu(line, t2 + 1, t3)))))
            tohex(got, out)
        elif kind == 108:     # l
            k = 2
            _ = snprintf(out, 4096, fmt, al(Int64(hexu(line, t2 + 1, t3))))
            tohex(got, out)
        elif kind == 115:     # s
            k = 3
            _ = unhex(line, t2 + 1, t3, arg)
            _ = snprintf(out, 4096, fmt, astr(arg))
            tohex(got, out)
        elif kind == 100:     # d: strtod
            k = 4
            _ = unhex(line, t2 + 1, t3, arg)
            var e = calloc(1, 8).unsafe_bitcast[P[Int8]]()
            var v = strtod(arg, e)
            hex64(got, bits64(v))
            got.append(58)
            dec(got, Int64(Int(e[]) - Int(arg)))
        elif kind == 110:     # n: sscanf
            k = 5
            _ = unhex(line, t2 + 1, t3, arg)
            var i1 = calloc(1, 8).unsafe_bitcast[Int32]()
            var d1 = calloc(1, 8).unsafe_bitcast[Float64]()
            var b = calloc(1, 64).unsafe_bitcast[Int8]()
            i1[] = -77
            d1[] = -77.0
            b[] = 63
            var nn = sscanf(arg, s("%d %lf %s"), tpi(i1), tpd(d1), tps(b))
            dec(got, Int64(nn))
            got.append(58)
            dec(got, Int64(i1[]))
            got.append(58)
            hex64(got, bits64(d1[]))
            got.append(58)
            tohex(got, b)
        else:
            continue
        total[k] += 1
        var want = line.unsafe_offset(t3 + 1)
        var same = slen(want) == len(got)
        if same:
            for q in range(len(got)):
                if UInt8(want[unsafe_offset=q]) != got[q]:
                    same = False
                    break
        if not same:
            bad[k] += 1
            if shown < 25:
                shown += 1
                var o = List[UInt8]()
                for c in "  ".as_bytes():
                    o.append(c)
                var q = 0
                while line[unsafe_offset=q] != 0:
                    o.append(UInt8(line[unsafe_offset=q]))
                    q += 1
                for c in "  mojo=".as_bytes():
                    o.append(c)
                o.extend(got^)
                o.append(10)
                conout_bytes(rt, o)
    var names = ["printf %f", "printf %d", "printf %ld", "printf %s", "strtod", "sscanf"]
    var allbad = 0
    var all = 0
    for k in range(6):
        print(names[k], ":", total[k], "cases,", bad[k], "differ")
        allbad += bad[k]
        all += total[k]
    print(allbad, "of", all, "cases differ")
