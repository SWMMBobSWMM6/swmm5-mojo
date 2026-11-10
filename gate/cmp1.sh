#!/bin/bash
# cmp1.sh <engine-cmd> <model-id> : run one model, report IDENT / RPTDIFF / OUTDIFF / CRASH
cd "$(dirname "$0")/.."
eng="$1"; id="$2"; p=$(grep "^$id"$'\t' gate/models_all.tsv | cut -f2-)
[[ "$p" = /* ]] || p="${SWMM_CORPUS:-$(pwd)/../1729-SWMM5-Models-2030}/$p"
o=${TMPDIR:-/tmp}/swmm_cmp1/$id; rm -rf $o; mkdir -p $o
gate/run_one.sh "$eng" "$p" "$o" >/dev/null 2>&1
r=gate/ref_outputs/$id
a=$(grep -vE 'Analysis begun|Analysis ended|Total elapsed time' $r/r.rpt 2>/dev/null | md5sum)
b=$(grep -vE 'Analysis begun|Analysis ended|Total elapsed time' $o/r.rpt 2>/dev/null | md5sum)
ro=same; [ -f $r/r.out ] && { cmp -s $r/r.out $o/r.out || ro=diff; }
st=IDENT; [ "$a" != "$b" ] && st=RPTDIFF; [ $ro = diff ] && st="$st+OUTDIFF"
grep -q 'Unhandled exception' $o/stderr.txt $o/stdout.txt 2>/dev/null && st=CRASH
echo "$st $id $(cat $o/sec)s $(basename "$p")"
