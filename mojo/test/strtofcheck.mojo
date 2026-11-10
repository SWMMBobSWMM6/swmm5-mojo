# strtofcheck.mojo - compare the Mojo runtime's sscanf %f into a C float with glibc's, on the cases of mkstrtof.c
# (lines TEXT \t BITS). Written by Claude (Anthropic) for Robert Dickinson; see ../README.md.
from std.sys import argv
from swmm5 import rt
from swmm5.rt import P, _hexval


def main():
    var R = rt.rt_init()
    var args = argv()
    var path = rt.calloc(1, 4096).unsafe_bitcast[Int8]()
    var a1 = args[1].as_bytes()
    for k in range(len(a1)):
        path[unsafe_offset=k] = Int8(a1[k])
    var f = rt.fopen(path, rt.s("r"))
    var line = rt.calloc(1, 512).unsafe_bitcast[Int8]()
    var v = rt.calloc(1, 8).unsafe_bitcast[Float32]()
    var total = 0
    var bad = 0
    while not rt.isnull(rt.fgets(line, 512, f)):
        var t = 0
        while line[unsafe_offset=t] != 9:
            t += 1
        line[unsafe_offset=t] = 0
        var want: UInt32 = 0
        for q in range(t + 1, t + 9):
            want = want * 16 + UInt32(_hexval(Int(line[unsafe_offset=q])))
        v[] = -77.0
        _ = rt.sscanf(line, rt.s("%f"), rt.tpf(v))
        var got = rt.bitcast[DType.uint32](v[])
        total += 1
        if got != want:
            bad += 1
            if bad <= 10:
                _ = rt.fprintf(R[].stdout, rt.s("  %s  glibc=%08x  mojo=%08x\n"), rt.astr(line), rt.au(want), rt.au(got))
    _ = rt.fflush(R[].stdout)
    print("sscanf %f into a float:", total, "cases,", bad, "differ")
