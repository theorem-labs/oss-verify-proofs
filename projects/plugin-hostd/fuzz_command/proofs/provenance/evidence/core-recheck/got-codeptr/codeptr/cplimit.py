#!/usr/bin/env python3
"""cplimit.py - re-judge the literals that codeptr 12348302dfd2's stale check passes WITHOUT comparing names (its
registered limits, the registry's false-equal audit rows H12 / H13 on codeptr 12348302dfd2):

  H12  codeptr.py:428-431: when the 16 file bytes around v are equal in both images, codeptr sets both meanings to
       the bytes, so a literal that names one symbol in the donor and ANOTHER symbol here passes as 'same'.
  H13  codeptr.py:434 + stale_verdict: a donor-file literal is judged only in the SAME slot (definition, ordinal); the
       same donor number one place earlier or later in the same definition is never judged.
  (H14, --same skips the check: this run declares nothing.)

For every checked file and every literal v that is a donor address (codeptr's own old.known(v)), this script takes
the two meanings by NAME (codeptr's own Img.meaning, without the bytes override) and lists:
  H12 rows: the bytes override applied (equal 16 bytes) and the two meanings differ;
  H13 rows: v is a literal of the donor's own file, but in no common slot, and the two meanings differ.
It imports codeptr.py (the file whose sha256 starts 12348302dfd2, checked) for Img, literals and the pairing rule.

  cplimit.py --tool DIR --image PIN --names TWIN --stale-image PIN --stale-names TWIN --stale-dir DONORLIB FILE.v...
"""
import argparse, hashlib, os, sys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tool', required=True)
    ap.add_argument('--image', required=True); ap.add_argument('--names', required=True)
    ap.add_argument('--stale-image', required=True); ap.add_argument('--stale-names', required=True)
    ap.add_argument('--stale-dir', required=True)
    ap.add_argument('--min', type=lambda s: int(s, 0), default=0x10000)
    ap.add_argument('files', nargs='+')
    a = ap.parse_args()
    src = os.path.join(a.tool, 'codeptr.py')
    sha = hashlib.sha256(open(src, 'rb').read()).hexdigest()[:12]
    if sha != '12348302dfd2':
        sys.exit('cplimit: REFUSED: %s is %s, not 12348302dfd2' % (src, sha))
    sys.path.insert(0, a.tool)
    import codeptr as C
    cur = C.Img(a.image, a.names, '--names')
    old = C.Img(a.stale_image, a.stale_names, '--stale-names')
    print('file\tline\tvalue\tlimit\tdonor_meaning\tour_meaning\tbytes_equal\tslots_here\tslots_donor')
    tot = {'H12': 0, 'H13': 0, 'judged': 0}
    for f in a.files:
        alll, fslots = C.literals(f, a.min)
        side = os.path.basename(os.path.dirname(os.path.abspath(f)))
        dfile = next(p for p in (os.path.join(a.stale_dir, side, os.path.basename(f)),
                                 os.path.join(a.stale_dir, os.path.basename(f))) if os.path.exists(p))
        dl, dslots = C.literals(dfile, a.min)
        txt = open(f).read()
        for v in sorted(alll):
            if not old.known(v) or (v >= cur.hi and not cur.in_section(v)):
                continue
            tot['judged'] += 1
            mo, mc = old.meaning(v), cur.meaning(v)
            wo, wc = old.bytes_at(max(v - 8, old.lo), 16), cur.bytes_at(max(v - 8, cur.lo), 16)
            beq = wo is not None and wo == wc
            insame = bool(fslots.get(v, set()) & dslots.get(v, set()))
            lim = None
            if beq and mo != mc and insame:
                lim = 'H12'
            elif v in dl and not insame and mo != mc:
                lim = 'H13'
            if lim:
                tot[lim] += 1
                # the first line of the file that writes v (hex or decimal), for the reader
                ln = next((i + 1 for i, l in enumerate(txt.split('\n')) if ('%#x' % v) in l.lower() or
                           (' %d' % v) in l or ('(%d' % v) in l), '-')
                print('%s\t%s\t%#x\t%s\t%r\t%r\t%s\t%s\t%s' % (os.path.basename(f), ln, v, lim, mo, mc, beq,
                      sorted(fslots.get(v, set()))[:3], sorted(dslots.get(v, set()))[:3]))
    print('# cplimit: %d donor-address literals looked at; H12 (equal bytes, names differ) %d; H13 (donor literal at '
          'another slot, meanings differ) %d' % (tot['judged'], tot['H12'], tot['H13']))


if __name__ == '__main__':
    main()
