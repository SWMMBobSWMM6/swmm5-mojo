#!/bin/bash
# runswmm_saves.sh - the Mojo engine (bin/runswmm, built by build.sh) for gate/gate.py, which runs
# `ENGINE model.inp report.rpt output.out` in the model's folder. The files the deck SAVEs to ([FILES], listed
# by savefiles.py from the swmm6-rust repository, called read-only) are backed up first and restored after, so
# a SAVE in the corpus never changes a file another deck USEs. The exit status is the engine's.
# savefiles.py also lists [LID_USAGE] report files, with '\' turned into '/' as OpenSWMM 6 does; EPA 5.2.4 (and
# this port) opens the name as written, so a Windows path such as C:\Users\x\lid.txt becomes one file called
# 'C:\Users\x\lid.txt' in the deck's folder. Both spellings are backed up and restored.
# A deck with nothing to back up runs the engine with exec, so that gate.py's timeout, which kills its own child,
# kills the engine and does not leave it running as an orphan.
# SWMM_BIN overrides the engine; SAVEFILES the lister; TMPDIR where the backups go.
# (Copied from ruby/runswmm_saves.sh for the Mojo port by Claude (Anthropic) for Robert Dickinson; see README.md.)
H=$(cd "$(dirname "$0")" && pwd)
BIN=${SWMM_BIN:-$H/bin/runswmm}
SAVEFILES=${SAVEFILES:-$H/../gate/savefiles.py}
d="$PWD/$1"
dir=$(dirname "$d")
B=$(mktemp -d "${TMPDIR:-/tmp}/swmmsave.XXXXXX"); python3 "$SAVEFILES" "$d" > "$B/listed.txt" 2>/dev/null
while IFS= read -r f; do
  printf '%s\n' "$f"
  rel=${f#"$dir/"}
  if [ "$rel" != "$f" ] && [ "${rel//\//\\}" != "$rel" ]; then printf '%s\n' "$dir/${rel//\//\\}"; fi
done < "$B/listed.txt" > "$B/saves.txt"
if [ ! -s "$B/saves.txt" ]; then rm -rf "$B"; exec "$BIN" "$@"; fi
k=0; while IFS= read -r f; do k=$((k+1)); [ -f "$f" ] && cp -p "$f" "$B/$k"; done < "$B/saves.txt"
"$BIN" "$@"; rc=$?
k=0; while IFS= read -r f; do k=$((k+1)); if [ -f "$B/$k" ]; then cp -p "$B/$k" "$f"; else rm -f "$f"; fi; done < "$B/saves.txt"
rm -rf "$B"; exit $rc
