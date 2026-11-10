#!/usr/bin/env python3
"""Byte gate: run an engine on the corpus models and compare with EPA 5.2.4 reference outputs.

  gate.py NAME "ENGINE COMMAND" [--ids FILE] [-j N] [--timeout S] [--prune]

PASS for a model = .out byte-identical (when EPA wrote one) and .rpt identical except the three
timestamp lines (Analysis begun / Analysis ended / Total elapsed time)."""
import argparse, concurrent.futures as cf, json, os, re, subprocess, time, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
TS = re.compile(rb'Analysis begun|Analysis ended|Total elapsed time')


def rpt_lines(p):
    try:
        return [l for l in open(p, 'rb').read().split(b'\n') if not TS.search(l)]
    except FileNotFoundError:
        return None


def run(args, mid, path):
    out = os.path.join(HERE, 'results', args.name, mid)
    os.makedirs(out, exist_ok=True)
    for f in ('r.rpt', 'r.out'):
        try: os.remove(os.path.join(out, f))
        except FileNotFoundError: pass
    t0 = time.time()
    try:
        p = subprocess.run(args.engine.split() + [os.path.basename(path), out + '/r.rpt', out + '/r.out'],
                           cwd=os.path.dirname(path), capture_output=True, timeout=args.timeout)
        rc = p.returncode; err = p.stderr.decode(errors='replace')[-2000:]
    except subprocess.TimeoutExpired:
        rc = 'timeout'; err = ''
    sec = time.time() - t0
    ref = os.path.join(HERE, 'ref_outputs', mid)
    a, b = rpt_lines(ref + '/r.rpt'), rpt_lines(out + '/r.rpt')
    st = []
    if rc == 'timeout':
        st.append('TIMEOUT')
    elif rc != 0:
        st.append('CRASH')
    if a != b:
        st.append('RPTDIFF')
    ro, eo = ref + '/r.out', out + '/r.out'
    if os.path.exists(ro) and os.path.getsize(ro) > 0:
        try:
            if open(ro, 'rb').read() != open(eo, 'rb').read():
                st.append('OUTDIFF')
        except FileNotFoundError:
            st.append('OUTDIFF')
    elif os.path.exists(eo) and os.path.getsize(eo) > 0:
        st.append('OUTDIFF')          # EPA wrote no results file; the engine must not write one either
    first = None
    if a is not None and b is not None and a != b:
        for i, (x, y) in enumerate(zip(a, b)):
            if x != y:
                first = (i, x.decode(errors='replace').strip()[:100], y.decode(errors='replace').strip()[:100]); break
        if first is None:
            first = (min(len(a), len(b)), 'len %d' % len(a), 'len %d' % len(b))
    if args.prune and not st:         # a passing model's outputs equal the reference's: keep only the verdict
        for f in ('r.rpt', 'r.out'):
            try: os.remove(os.path.join(out, f))
            except FileNotFoundError: pass
        try: os.rmdir(out)
        except OSError: pass
    return {'id': mid, 'path': path, 'status': '+'.join(st) or 'PASS', 'sec': round(sec, 3), 'rc': rc,
            'first_rpt_diff': first, 'stderr': err if st and st[0] == 'CRASH' else ''}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('name'); ap.add_argument('engine')
    ap.add_argument('--ids'); ap.add_argument('-j', type=int, default=2); ap.add_argument('--timeout', type=float, default=120)
    ap.add_argument('--prune', action='store_true', help='delete the outputs of models that pass (disk is short)')
    args = ap.parse_args()
    models = [l.rstrip('\n').split('\t', 1) for l in open(os.path.join(HERE, 'models_all.tsv'))]
    # paths may be relative to the corpus checkout (SWMM_CORPUS, default: next to this repository)
    corpus = os.environ.get('SWMM_CORPUS', os.path.join(HERE, '..', '..', '1729-SWMM5-Models-2030'))
    models = [[m, p if os.path.isabs(p) else os.path.join(corpus, p)] for m, p in models]
    if args.ids:
        keep = set(open(args.ids).read().split())
        models = [m for m in models if m[0] in keep]
    res = []
    with cf.ThreadPoolExecutor(args.j) as ex:
        for r in ex.map(lambda m: run(args, *m), models):
            res.append(r)
    res.sort(key=lambda r: r['path'])
    os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)
    json.dump(res, open(os.path.join(HERE, 'results', args.name + '.json'), 'w'), indent=1)
    from collections import Counter
    c = Counter(r['status'] for r in res)
    print('%s: %d models  %s' % (args.name, len(res), ', '.join('%s %d' % kv for kv in c.most_common())))
    for r in res:
        if r['status'] != 'PASS':
            print('  %-16s %s  %s' % (r['status'], os.path.relpath(r['path'], '/home/claude/swmmbobswmm6/1729-swmm5-models-2030'), r['first_rpt_diff'] or r['stderr'][:200].replace('\n', ' | ')))


if __name__ == '__main__':
    main()
