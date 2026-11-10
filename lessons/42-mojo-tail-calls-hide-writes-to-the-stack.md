Mojo 1.2 marks a call `tail` even when it passes the caller's stack slot as an untracked pointer, and LLVM then reads the slot as if the callee had not written it.

The first model the Mojo engine ran, Hydraulics/swmm5_shapes.inp, stopped on its options with seven errors of the form

    ERROR 213: invalid date/time 00:15:00 at line 25 of [OPTION] section:

for every time EPA reads. The C (datetime.c, `datetime_strToTime`) first tries the text as decimal hours:

    char *endptr;
    *t = strtod(s, &endptr);
    if ( *endptr == 0 ) { *t /= 24.0; return 1; }

and the translation was faithful: `endptr` was a stack slot from Mojo's `stack_allocation`, held as
`Pointer[P[Int8], MutUntrackedOrigin]` (the engine's one pointer type, `P`), passed to the runtime's `strtod`, which
stored the end position through it. Yet `*endptr` read 0 after the call, so "00:15:00" was taken as 0 hours and the
time-of-day parse never ran. A ten-line test showed the same with any callee; its unoptimised LLVM IR:

    %2 = alloca ptr, i64 1, align 8
    tail call void @"t14::wr(...)"(ptr %2, ptr %3)
    %4 = load ptr, ptr %2, align 8

`tail` tells LLVM that the callee does not access the caller's allocas. Mojo tracks where a pointer may point through
its origin; a pointer with `MutUntrackedOrigin` carries none, so Mojo concludes that no stack slot escapes and marks
the call. LLVM is then entitled to forward the load past the call, and it read the slot's old contents.

The engine now keeps every C local whose address is taken, every local array and every local struct on a stack of its
own: a 64 MB block of heap memory in the runtime, from which `rt.salloc` hands out zeroed space at function entry and
to which each return gives it back (`G[].R_[].sp = __sp` before every `return`). Heap memory is outside the `tail`
promise. With that change the model matched EPA byte for byte, then the 40-model development sample, then all 480 gate
models (mojo_1, and mojo_v from a clean checkout).

What to take from it: in a language that reasons about where pointers point, an "unsafe" or "untracked" pointer may
switch that reasoning off for the program around it, not only for the pointer: here it made the compiler more
confident, not less. When a translation needs C's pointers into the stack, give them memory the compiler does not
own (the heap), or read the generated IR of one call before trusting the rest.
