#!/usr/bin/env python3
# Print, one per line, the files a deck's [FILES] section names for SAVE (resolved against the
# deck's folder, as upstream's PathResolver does), so gate/ctxgate.sh can back them up before
# a harness opens them for writing and restore them after: a start() truncates them (SAVE
# RDII, SAVE RUNOFF, SAVE OUTFLOWS), and another deck may USE the same file. Also the per-unit
# LID report files [LID_USAGE] names (its ninth field, '*' for none), which the runoff step
# creates and writes.
import os, shlex, sys
deck = sys.argv[1]
d = os.path.dirname(os.path.abspath(deck))
sec = None
try:
    lines = open(deck, 'rb').read().decode('latin-1').splitlines()
except OSError:
    sys.exit(0)
for ln in lines:
    s = ln.split(';', 1)[0].strip()
    if not s:
        continue
    if s.startswith('['):
        sec = s.upper()
        continue
    if sec not in ('[FILES]', '[LID_USAGE]'):
        continue
    try:
        t = shlex.split(s, posix=True)
    except ValueError:
        t = s.split()
    if sec == '[LID_USAGE]':
        if len(t) >= 9 and t[8] != '*':
            p = t[8].replace('\\', '/')  # upstream's PathResolver turns '\' into '/'
            print(p if os.path.isabs(p) else os.path.join(d, p))
        continue
    if len(t) >= 3 and t[0].upper() == 'SAVE':
        p = t[2]
        print(p if os.path.isabs(p) else os.path.join(d, p))
