#!/usr/bin/env python3
"""check_gpatches.py STAGE_OUT PATCHDIR [--before P ...] -- check the g-*.patch files the way port_core applies --patch.

STAGE_OUT is a run's stage-out; port_core writes its provenance line AFTER the --patch step, so the text the patches
apply to is stage-out WITHOUT that line. The check works in a temporary tree (removed at the end):
1. copy STAGE_OUT/{A,Reusable}/*.v there without the provenance line (= the text after every patch of the run);
2. with --before (the run's own --patch files, in the run's order; STAGE_OUT already has them applied): undo them in
   reverse order (`patch -R -p0 -F0`), giving the text the run patched, then apply them forward again (`patch -p0
   -F0`) and check the tree equals step 1 byte for byte (the reverse / forward round trip is exact);
3. apply every PATCHDIR/g-*.patch in the order of ORDER (those present), each with `patch -p0 --dry-run -F0` first
   and then for real, so each later one sees the earlier ones' text; compare each patched file with
   PATCHDIR/stage-g/A/<f>.v when that file exists;
4. control: the first G patch with one context line altered must be refused by `patch -p0 --dry-run -F0`.
Exit 0 only when every step holds and the control is refused."""
import argparse
import filecmp
import os
import re
import shutil
import subprocess
import sys
import tempfile

PROV = re.compile(r'^\(\* Relocated from proofs/\S+ at [0-9a-f]{12} by port_core [0-9a-f]{12} onto \S+ \((plain|ubsan|asan|asan-ubsan)\)\. \*\)$')
ORDER = ['ACfn', 'AD1w', 'AD1m', 'AD1p', 'AD1q', 'AD1r', 'AD2f', 'AD2d', 'AD2e', 'AD1x']


def run(tree, args, text):
    r = subprocess.run(['patch', '-p0', '-F0', '--batch'] + args, input=text, cwd=tree, capture_output=True, text=True)
    return r.returncode, (r.stdout + r.stderr).strip().replace('\n', ' | ')


def copy_noprov(so, dst):
    for sub in ('A', 'Reusable'):
        d = os.path.join(so, sub)
        if not os.path.isdir(d):
            continue
        os.makedirs(os.path.join(dst, sub))
        for f in os.listdir(d):
            if f.endswith('.v'):
                lines = open(os.path.join(d, f)).read().split('\n')
                keep = [l for l in lines if not PROV.match(l)]
                if len(keep) != len(lines) - 1:
                    sys.exit(f'check_gpatches: {sub}/{f}: expected one provenance line')
                open(os.path.join(dst, sub, f), 'w').write('\n'.join(keep))


def same_tree(a, b):
    for sub in ('A', 'Reusable'):
        da, db = os.path.join(a, sub), os.path.join(b, sub)
        if not os.path.isdir(da):
            continue
        c = filecmp.dircmp(da, db)
        if c.left_only or c.right_only:
            return False
        _, mism, err = filecmp.cmpfiles(da, db, c.common_files, shallow=False)
        if mism or err:
            return False
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('stage_out')
    ap.add_argument('patchdir')
    ap.add_argument('--before', nargs='*', default=[])
    a = ap.parse_args()
    top = tempfile.mkdtemp(prefix='gpatch-')
    bad = 0
    try:
        ref, tree = os.path.join(top, 'ref'), os.path.join(top, 'tree')
        copy_noprov(a.stage_out, ref)
        shutil.copytree(ref, tree)
        if a.before:
            for p in reversed(a.before):
                rc, out = run(tree, ['-R'], open(p).read())
                bad += rc != 0
                print(f'undo {os.path.basename(p)}\trc={rc}\t{out}')
            for p in a.before:
                rc, out = run(tree, ['--dry-run'], open(p).read())
                rc2, _ = run(tree, [], open(p).read()) if rc == 0 else (rc, '')
                bad += rc != 0 or rc2 != 0
                print(f'apply {os.path.basename(p)}\trc={rc}\t{out}')
            ok = same_tree(ref, tree)
            bad += not ok
            print(f'round trip\t{"equal" if ok else "DIFFERS"}\tthe tree after undo + apply equals the stage-out text')
        first = None
        for f in ORDER:
            pf = os.path.join(a.patchdir, f'g-{f}.patch')
            if not os.path.exists(pf):
                continue
            first = first or pf
            text = open(pf).read()
            rc, out = run(tree, ['--dry-run'], text)
            rc2 = run(tree, [], text)[0] if rc == 0 else rc
            want = os.path.join(a.patchdir, 'stage-g', 'A', f + '.v')
            eq = 'n/a'
            if os.path.exists(want):
                eq = 'equal' if filecmp.cmp(os.path.join(tree, 'A', f + '.v'), want, shallow=False) else 'DIFFERS'
            bad += rc != 0 or rc2 != 0 or eq == 'DIFFERS'
            print(f'g-{f}.patch\trc={rc}\t{out}\tpatched text vs stage-g: {eq}')
        ctl = open(first).read().split('\n')
        i = next(k for k, l in enumerate(ctl) if l.startswith(' ') and k > 2)
        ctl[i] = ctl[i] + ' (* planted *)'
        rc, out = run(ref, ['--dry-run'], '\n'.join(ctl))
        print(f'control ({os.path.basename(first)}, context line {i + 1} altered)\trc={rc}\t{out}')
        sys.exit(1 if bad or rc == 0 else 0)
    finally:
        shutil.rmtree(top)


main()
