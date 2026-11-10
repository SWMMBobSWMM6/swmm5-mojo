Gate a checked build as well as the fast one: the Zig port passed 480 of 480 while its calloc(0) returned a pointer past the end of its block.

Zig's ReleaseFast build has no run-time checks; ReleaseSafe traps on an out-of-bounds index, integer overflow,
a lossy cast or a misaligned pointer. The fast build passed the gate (zig_3: 480 of 480). The checked build,
gated the same way, passed 3 (gate/zig_safe_1_run.txt); the other 477 stopped at once:

    panic: index out of bounds: index 1, len 1
    zig/src/rt.zig: return @ptrCast(&mem[1]);      in rawAlloc
    zig/src/swmm5.zig: Gage = ... R.calloc(Nobjects[0], 1848) ...   in createObjects

EPA allocates every object array, including empty ones: `calloc(0, sizeof(TGage))` for a model with no rain
gages. The runtime's allocator puts a 16-byte size header in front of each block and returns the address after
it; for a zero-byte request the block was the header alone, so the returned address was one past the end. The
fast build never dereferenced it, so every output was right. glibc's calloc(0) returns a unique, valid block;
the runtime now does the same by allocating one byte. After the fix the checked build passed 480 of 480 with no
trap (zig_safe_2), and the fast build was gated again (zig_4, zig_5).

What to carry forward: a byte-identical gate shows the outputs are right, not that the program is. Where the
language offers a checked mode (Zig's ReleaseSafe, Rust's debug build, gcc's -fsanitize=address,undefined for
the C reference), run the whole gate in it once. It costs one more run and it reports undefined behaviour the
outputs cannot.
