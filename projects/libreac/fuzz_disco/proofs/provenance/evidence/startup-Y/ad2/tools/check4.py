#!/usr/bin/env python3
"""check4.py -- map check 4 of the start-up map review on one AD2j/YD2j + AD1k/YD1k pair, with the donor's own
pair as the control.

Regions (`mkRegion None lo hi wlo whi [chunks]`): lo <= hi; the first chunk at lo; chunks of every kind ordered and
contiguous up to hi (a gap or a chunk-less region is allowed only where the donor's region of the same name, or the
donor region the cut pieces NAME_k come from, has one); every region inside the image's page-rounded PT_LOADs (TSEGS);
the strict PT_LOAD [vaddr, vaddr+memsz) overhang is listed. HALF-RELOCATED test: a region whose bounds moved but whose
chunk-size list equals the donor's is listed (it is a defect unless the chunks were recomputed for the new image).
AD1k restatements: every `img_rd_of_mem_ok … IMG_REGIONS R_X a n` and `CH R_X a n` must be a CImg chunk (a, n) of R_X in
the given AD2j; every `img_rd m lo hi` and `file_is_img _ lo hi` must lie inside one CImg chunk; every
`mkChunk a (CVal …)` named in AD1k must be a chunk of the AD2j.

  check4.py --ad2j AD2j.v --ad1k AD1k.v --image IMG --donor-ad2j DONOR_AD2j.v --donor-image DONOR_IMG --label NAME
exit 1 on any failure.
"""
import argparse, os, re, sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_ad2 as g  # noqa: E402


def check(regs, img, dregs, dimg, out):
    fails = []
    segs = [(va & ~0xfff, (va + ms + 0xfff) & ~0xfff) for va, fs, ms, off in img.loads]
    dby = {r['name']: r for r in dregs}
    out.append('| region | lo | hi | chunks | first chunk at lo | contiguous (gaps) | donor same region: gaps | in TSEGS | outside PT_LOAD memsz | sizes = donor\'s (bounds moved) |')
    out.append('|---|---|---|---|---|---|---|---|---|---|')
    for r in regs:
        n = r['name']
        d = dby.get(n) or dby.get(re.sub(r'_\d+$', '', n))
        ok_lohi = r['lo'] <= r['hi']
        first = (not r['chunks']) or r['chunks'][0][0] == r['lo']
        order = all(a[0] + g.clen(a[1]) <= b[0] for a, b in zip(r['chunks'], r['chunks'][1:])) and \
            all(r['lo'] <= o and o + g.clen(k) <= r['hi'] for o, k in r['chunks'])
        gaps = g.gaps_of(r)
        dgaps = g.gaps_of(d) if d else []
        dfirst = d is not None and ((not d['chunks']) or d['chunks'][0][0] == d['lo'])
        tseg = not g.complement(r['lo'], r['hi'], segs)
        ov = g.strict_overhang(r, img)
        same = d is not None and (d['lo'], d['hi']) != (r['lo'], r['hi']) and [k for o, k in d['chunks']] == [k for o, k in r['chunks']]
        if not ok_lohi:
            fails.append('%s: lo > hi' % n)
        if not order:
            fails.append('%s: chunks not ordered / overlapping / outside [lo, hi)' % n)
        if not first and not (d and not dfirst):
            fails.append('%s: first chunk not at lo, donor region is' % n)
        if gaps and not dgaps:
            fails.append('%s: gap %s, donor region %s contiguous' % (n, gaps, d['name'] if d else '(none: every donor A1/A2 region is)'))
        if not tseg:
            fails.append('%s: outside the page-rounded PT_LOADs' % n)
        f = lambda iv: ', '.join('[%#x,%#x)' % x for x in iv) or 'none'
        out.append('| %s | %#x | %#x | %d | %s | %s | %s | %s | %s | %s |' % (
            n, r['lo'], r['hi'], len(r['chunks']), 'yes' if first else 'no (no chunks)' if not r['chunks'] else 'NO',
            'yes' if not gaps else f(gaps), (f(dgaps) if d else '-'), 'yes' if tseg else 'NO', f(ov), 'yes' if same else 'no'))
    return fails


def ad1k_check(regs, ad1k, out):
    fails, rows = [], []
    by = {r['name']: r for r in regs}
    cimg = [(o, o + k[1]) for r in regs for o, k in r['chunks'] if k[0] == 'CImg']
    allch = {(o, g.show(k)) for r in regs for o, k in r['chunks']}
    for i, l in enumerate(ad1k.split('\n'), 1):
        for m in re.finditer(r'IMG_REGIONS (R_\w+) (\d+) (\d+) HM|CH (R_\w+) (\d+) (\d+)\)', l):
            name, a, n = (m.group(1), m.group(2), m.group(3)) if m.group(1) else (m.group(4), m.group(5), m.group(6))
            a, n = int(a), int(n)
            ok = name in by and (a, ('CImg', n)) in by[name]['chunks']
            rows.append((i, 'chunk %s %d %d' % (name, a, n), ok))
        for m in re.finditer(r'img_rd m (0x[0-9a-f]+|\d+) (0x[0-9a-f]+|\d+)|file_is_img _ (\d+) (\d+)\)', l):
            lo, hi = (int(m.group(1), 0), int(m.group(2), 0)) if m.group(1) else (int(m.group(3)), int(m.group(4)))
            ok = any(x <= lo and hi <= y for x, y in cimg)
            rows.append((i, 'range [%#x, %#x) inside one CImg chunk' % (lo, hi), ok))
        for m in re.finditer(r'mkChunk (\d+) \((CVal [^()]*\([^()]*\))\)', l):
            ok = (int(m.group(1)), m.group(2)) in allch
            rows.append((i, 'chunk %s (%s)' % (m.group(1), m.group(2)), ok))
    for i, what, ok in rows:
        if not ok:
            fails.append('AD1k line %d: %s: NOT in the AD2j' % (i, what))
    out.append('AD1k restatements checked: %d (%d ok)' % (len(rows), sum(1 for x in rows if x[2])))
    return fails


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    for k in ('ad2j', 'ad1k', 'image', 'donor_ad2j', 'donor_image', 'label'):
        ap.add_argument('--' + k.replace('_', '-'), required=True)
    a = ap.parse_args()
    regs = g.template_regions(open(a.ad2j).read())
    dregs = g.template_regions(open(a.donor_ad2j).read())
    out = ['### check 4: %s' % a.label, '', 'AD2j %s, AD1k %s, image %s (sha256 %s)' % (a.ad2j, a.ad1k, a.image, g.Image(a.image).sha[:16]), '']
    fails = check(regs, g.Image(a.image), dregs, g.Image(a.donor_image), out)
    out.append('')
    fails += ad1k_check(regs, open(a.ad1k).read(), out)
    out.append('')
    out += ['FAIL ' + f for f in fails] or ['VERDICT: pass (%d regions)' % len(regs)]
    print('\n'.join(out))
    sys.exit(1 if fails else 0)


if __name__ == '__main__':
    main()
