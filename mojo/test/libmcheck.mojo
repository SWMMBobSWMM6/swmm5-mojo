# libmcheck.mojo - check the math the Mojo engine computes against the system libm (the library EPA calls), bit
# for bit, NaN signs and payloads included. Reads vector files in the format of tools/libm/test/mkvectors.c
# (name\0, n:u32, then n x (args..., result) as raw little-endian doubles; for d2i and d2l the result holds the
# integer's 64 bits) and evaluates each function the way the generated engine does: rt.exp ... rt.atan (glibc
# through external_call), Mojo's sqrt, floor and ceil, rt.fabs, negation, Float32(x), rt.d2i32 and rt.d2i64.
#   mojo/test/run_libm_tests.sh
# Written by Claude (Anthropic) for Robert Dickinson; see ../README.md.
from std.sys import argv
from std.math import sqrt, floor, ceil
from swmm5 import rt
from swmm5.rt import P


@no_inline
def call1(name: String, x: Float64) -> UInt64:
    if name == "exp":
        return rt.bits64(rt.exp(x))
    if name == "log":
        return rt.bits64(rt.log(x))
    if name == "log10":
        return rt.bits64(rt.log10(x))
    if name == "sin":
        return rt.bits64(rt.sin(x))
    if name == "cos":
        return rt.bits64(rt.cos(x))
    if name == "tan":
        return rt.bits64(rt.tan(x))
    if name == "asin":
        return rt.bits64(rt.asin(x))
    if name == "acos":
        return rt.bits64(rt.acos(x))
    if name == "atan":
        return rt.bits64(rt.atan(x))
    if name == "sqrt":
        return rt.bits64(sqrt(x))
    if name == "floor":
        return rt.bits64(floor(x))
    if name == "ceil":
        return rt.bits64(ceil(x))
    if name == "fabs":
        return rt.bits64(rt.fabs(x))
    if name == "neg":
        return rt.bits64(-x)
    if name == "f32":
        return rt.bits64(Float64(Float32(x)))
    if name == "d2i":
        return UInt64(Int64(rt.d2i32(x)))
    if name == "d2l":
        return UInt64(rt.d2i64(x))
    return 0x7FF0DEAD


def main():
    var args = argv()
    var path = rt.calloc(1, 4096).unsafe_bitcast[Int8]()
    var a1 = args[1].as_bytes()
    for k in range(len(a1)):
        path[unsafe_offset=k] = Int8(a1[k])
    var f = rt.fopen(path, rt.s("rb"))
    _ = rt.fseek(f, 0, 2)
    var size = Int(rt.ftell(f))
    rt.rewind(f)
    var data = rt.calloc(UInt64(size + 8), 1).unsafe_bitcast[UInt8]()
    _ = rt.fread(data.unsafe_bitcast[NoneType](), 1, UInt64(size), f)
    var pos = 0
    var total = 0
    var bad = 0
    while pos < size:
        var z = pos
        while data[unsafe_offset=z] != 0:
            z += 1
        var name = String()
        for q in range(pos, z):
            name += chr(Int(data[unsafe_offset=q]))
        var n = Int(data.unsafe_offset(z + 1).unsafe_bitcast[UInt32]()[])
        pos = z + 5
        var nargs = 2 if name == "pow" else (3 if name == "fma" else 1)
        var k = nargs + 1
        var vals = data.unsafe_offset(pos).unsafe_bitcast[UInt64]()
        pos += n * k * 8
        if name == "fma":
            print(name, ":", n, "vectors, not used by the Mojo port (skipped)")
            continue
        var nb = 0
        var nn = 0
        var shown = 0
        for j in range(n):
            var x = rt.f64bits(vals[unsafe_offset=j * k])
            var want = vals[unsafe_offset=j * k + k - 1]
            var got: UInt64
            if name == "pow":
                got = rt.bits64(rt.pow(x, rt.f64bits(vals[unsafe_offset=j * k + 1])))
            else:
                got = call1(name, x)
            if name == "d2i":
                want = UInt64(Int64(Int32(want & 0xFFFFFFFF)))
            if got == want:
                continue
            nb += 1
            var gw = rt.f64bits(got)
            var ww = rt.f64bits(want)
            if gw != gw and ww != ww:
                nn += 1
            if shown < 5:
                shown += 1
                print("  ", name, "(", hex(vals[unsafe_offset=j * k]), ") libm", hex(want), "mojo", hex(got))
        print(name, ":", n, "vectors,", nb, "differ (", nn, "of them only in a NaN's sign or payload)")
        total += n
        bad += nb
    print(bad, "of", total, "differ")
