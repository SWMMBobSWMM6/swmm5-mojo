EPA SWMM 5.2.4 defects the ports exposed: the ports copy EPA's defined behaviour, and do the safe thing where EPA's is undefined.

1. inlet.c, PlacementTypeWords has no NULL sentinel: `{"AUTOMATIC", "ON_GRADE", "ON_SAG"}`.
   findmatch() walks past the end of the array (undefined behaviour). In EPA's gcc build the next word in
   memory is zero, so an unknown placement keyword returns -1. The ports append the missing NULL, which
   reproduces EPA byte for byte on Hydraulics/inlet_capture_test.inp (without it, C# threw
   IndexOutOfRangeException in its first gate run: gate/csharp_run1.txt). The Python back end was written later and missed the fix: its first
   gate run failed that one model with IndexError until the same NULL was appended there too. A fix
   that lives in one back end is a fix the next back end has to rediscover; it belongs in the front end.
2. gage.c:251 overflows int when a time series has one point (dxMin = BIG):
   `gageInterval = (int)(floor(Tseries[k].dxMin*SECperDAY + 0.5));`
   x86-64 gives INT_MIN (no WARNING 09); Rust and Java saturate to INT_MAX (WARNING 09 appears); wasm
   saturates with the non-trapping conversion instructions and traps with the plain ones (toolchain choice).
   The ports use x86 semantics (R.D2I / D2I) so they match the Linux reference.
3. swmm5.c:1593 realpath() into a 260-byte InpDir; glibc _FORTIFY_SOURCE aborts every run opened by a
   relative path. The reference is built with _FORTIFY_SOURCE=0; the ports resolve the path with the
   host library into a buffer with no fixed size, so a path over 259 bytes, which would overflow EPA's
   InpDir, cannot be reproduced. No gate model has one.
4. output.c:523-525 writes 8-byte off_t positions with sizeof(INT4): fwrite copies the first four bytes,
   which on little-endian x86 are the low half, so the value is right. The three positions are ftell()
   values taken before any results are written (output.c:208, 230, 397), so they stay small however big
   the file grows. Only a big-endian machine would be wrong (it would write the high half, zero). The ports
   write the low four bytes (R.fwriteN1). (An earlier version of this note said files over 2 GB would
   wrap; that was wrong, a reviewer caught it.)
5. project.c:421, project_createMatrix() zeroes only an eighth of the matrix it allocates:
   `size_t size = (size_t)nrows * (size_t)ncols;` (line 401) and `memset(a[0], 0, size);` (line 421)
   size counts doubles but memset counts bytes, so 7 of every 8 bytes stay as malloc left them.
   Only USE INFLOWS (reading a routing interface file) creates these matrices, and none of the 480 gate
   models does that, so the gate says nothing about this path. Reading uninitialised memory is not
   behaviour a port can copy, so the ports zero the whole matrix (C#, Python and Fortran overrides).
