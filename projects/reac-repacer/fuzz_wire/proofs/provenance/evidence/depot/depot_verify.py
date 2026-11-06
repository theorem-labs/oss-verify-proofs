#!/usr/bin/env python3
"""depot_verify.py APPLIED_DIR KNOCK_LIB FILE... -- the gate on depot_apply.py's output: the token difference (comments
removed, module paths / record names mapped, NOTHING reduced) between each applied file and libreac/fuzz_knock's
released text must consist ONLY of the 'other, grant kept' hunks of the ruling, i.e. every residue piece must be one of
the grant-lineage differences named below; anything else fails the gate (exit 1).
  kFreeArrayOffset   grant's bound / unfolds of kFreeArrayOffset (knock: 2 ^ 31, no unfold)
  EV_MAX             grant's EV_MAX 11776 (knock 8192) and prim_committed_bound_nev (knock prim_committed_bound[_any])
  stack-class        grant's aa_stack_malloc premise pc_stack_malloc (as_code B) cid <> 0 (knock: cid = 1 \\/ cid = 2)
  Require-Import     grant's `Require Import` where knock has `Require`
  IMG-notation       grant's IMG_LO / IMG_TOP where knock writes YImgTop.IMG_LO / YImgTop.IMG_TOP
Prints every residue piece with its class and the per-file / total counts."""
import difflib, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from depot_classify import tokens  # noqa: E402


def klass(g, k):
    s = ' '.join(g) + ' | ' + ' '.join(k)
    if 'kFreeArrayOffset' in s:
        return 'kFreeArrayOffset'
    if any(x in s for x in ('EV_MAX', '11776', 'prim_committed_bound', 'wf_nev', 'NEx')):
        return 'EV_MAX'
    if 'pc_stack_malloc' in s or 'cid' in s:
        return 'stack-class'
    if g == ['Import'] and not k:
        return 'Require-Import'
    if g in (['IMG_LO'], ['IMG_TOP']) and k in (['YImgTop.IMG_LO'], ['YImgTop.IMG_TOP']):
        return 'IMG-notation'
    return None


def main():
    ad, kl = sys.argv[1:3]
    bad = 0
    tot = {}
    for f in sys.argv[3:]:
        a = tokens(open(os.path.join(ad, f)).read())
        k = tokens(open(os.path.join(kl, 'Reusable', f)).read())
        n = {}
        for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, [t for t, _ in a], [t for t, _ in k], autojunk=False).get_opcodes():
            if tag == 'equal':
                continue
            g, kk = [t for t, _ in a[i1:i2]], [t for t, _ in k[j1:j2]]
            c = klass(g, kk)
            ln = a[i1][1] if i1 < len(a) else a[-1][1]
            print('%s:%d\t%s\t%s\t->\t%s' % (f, ln, c or 'UNEXPECTED', ' '.join(g)[:150], ' '.join(kk)[:150]))
            if c is None:
                bad += 1
            n[c] = n.get(c, 0) + 1
            tot[c] = tot.get(c, 0) + 1
        print('%s: %s' % (f, ', '.join('%s %d' % (c, v) for c, v in sorted(n.items(), key=str)) or 'equal to knock'))
    print('total residue pieces: %s; UNEXPECTED %d' % (', '.join('%s %d' % (c, v) for c, v in sorted(tot.items(), key=str)), bad))
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
