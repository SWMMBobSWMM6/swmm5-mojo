# main.mojo - command-line runner for the Mojo port of EPA SWMM 5.2.4: the same arguments, console messages and
# exit status (always 0) as EPA's run/main.c.   runswmm <input file> <report file> [output file]
# Written by Claude (Anthropic) for Robert Dickinson; see ../README.md.
from std.sys import argv
from std.collections import List
from swmm5 import rt
from swmm5.rt import P
from swmm5.engine import Globals, new_globals, swmm_getVersion, swmm_run, swmm_getError, swmm_getWarnings


def cstr(s: StringSlice) -> P[Int8]:
    """a NUL-terminated copy of a command-line argument"""
    var b = s.as_bytes()
    var p = rt.calloc(UInt64(len(b) + 1), 1).unsafe_bitcast[Int8]()
    for k in range(len(b)):
        p[unsafe_offset=k] = Int8(b[k])
    return p


def same(s: StringSlice, t: StaticString) -> Bool:
    return s == t


def main():
    var G = new_globals()
    var R = G[].R_
    var args = argv()
    var version = swmm_getVersion(G)
    var vMajor = version // 10000
    var vMinor = (version - 10000 * vMajor) // 1000
    var vRelease = version - 10000 * vMajor - 1000 * vMinor
    var start = rt.time(rt.null[Int64]())
    var buf = rt.calloc(512, 1).unsafe_bitcast[Int8]()
    if len(args) == 1:
        rt.conout(R, "\nNot Enough Arguments (See Help --help)\n\n")
    elif len(args) == 2:
        var a = args[1]
        if same(a, "--help") or same(a, "-h"):
            rt.conout(R, "\n\nSTORMWATER MANAGEMENT MODEL (SWMM) HELP\n\nCOMMANDS:\n\t--help (-h)       SWMM Help\n"
                      + "\t--version (-v)    Build Version\n\nRUNNING A SIMULATION:\n"
                      + "\t runswmm <input file> <report file> <optional output file>\n\n")
        elif same(a, "--version") or same(a, "-v"):
            _ = rt.snprintf(buf, 512, rt.s("\n%d.%d.%0d\n\n"), rt.ai(vMajor), rt.ai(vMinor), rt.ai(vRelease))
            _ = rt.fprintf(R[].stdout, rt.s("%s"), rt.astr(buf))
        else:
            rt.conout(R, "\nUnknown Argument (See Help --help)\n\n")
    else:
        var inp = cstr(args[1])
        var rpt = cstr(args[2])
        var out = cstr(args[3]) if len(args) > 3 else cstr("")
        _ = rt.fprintf(R[].stdout, rt.s("\n... EPA SWMM %d.%d (Build %d.%d.%0d)\n"), rt.ai(vMajor), rt.ai(vMinor),
                       rt.ai(vMajor), rt.ai(vMinor), rt.ai(vRelease))
        _ = rt.fflush(R[].stdout)
        _ = swmm_run(G, inp, rpt, out)
        var runTime = rt.difftime(rt.time(rt.null[Int64]()), start)
        _ = rt.fprintf(R[].stdout, rt.s("\n\n... EPA SWMM completed in %.2f seconds."), rt.ad(runTime))
        var errMsg = rt.calloc(128, 1).unsafe_bitcast[Int8]()
        if swmm_getError(G, errMsg, 127) > 0:
            _ = rt.fprintf(R[].stdout, rt.s(" There are errors.\n"))
        elif swmm_getWarnings(G) > 0:
            _ = rt.fprintf(R[].stdout, rt.s(" There are warnings.\n"))
        else:
            _ = rt.fprintf(R[].stdout, rt.s("\n"))
    _ = rt.fflush(R[].stdout)
