A printf runtime may cache a parsed format only for a string that cannot change; EPA formats with a buffer it rewrites.

The Lua port's printf parses each C format into pieces (text and conversions) before formatting, which is slow in
Lua, so the first version kept the parse in a table keyed by the format argument (a char pointer object, `CPtr`):

    local function format(fmt, ...)
      local pieces = fcache[fmt]
      if pieces == nil then pieces = parse(fmt); fcache[fmt] = pieces end

On Hydraulics/inlet_capture_test.inp the report then said `ERROR 211: invalid number 0.0 at line 93 of [INLET_USAGE]
section` where EPA says `ERROR 205: invalid keyword 0.0 ...`, on four lines in a row.

EPA's error reporting writes the message's format into one global buffer, `Msg` (globals.h: `Msg[MAXMSG+1]`), and
formats with it (report.c, `report_writeErrorMsg`):

    fprintf(Frpt.file, error_getMsg(code, Msg), s);

`error_getMsg` copies the text of error `code` into `Msg` and returns `Msg`. The pointer is the same on every call;
the characters are not. The cache was keyed on the pointer, so every message after the first was printed with the
first message's text: "invalid number %s" stayed in the cache after `Msg` had been rewritten to "invalid keyword %s".

The fix (`lua/swmm5/rt.lua`): `R.lit`, which builds the objects for the C program's string literals, marks them
constant, and only a marked format at offset 0 is cached; any other format is parsed every time. C string literals
cannot be written to, so their parse cannot go stale.

What to take from it: a cache keyed on a pointer caches the pointer, not the text. Key it on the content, or cache only
what the language guarantees is immutable. The two kinds of check cover each other (lessons/25 is the other half): the
replay of glibc's printf cases (`lua/test/run_crtcheck.sh`) formats with fixed formats and cannot see this, and only a
model that formats through a rewritten buffer, run in development before the gate, showed it.
