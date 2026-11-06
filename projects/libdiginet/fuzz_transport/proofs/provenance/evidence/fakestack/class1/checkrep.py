#!/usr/bin/env python3
"""checkrep.py -- check every numeral row of alreloc's per-numeral report against the two ELFs, independently of
alreloc's own rules (alreloc a5c53bb2bed4 maps .got cells by .got offset and moves model constants as addresses).

usage: checkrep.py REPORT_DIR IMG DONOR_TWIN TARGET_TWIN      (REPORT_DIR/<IMG>/Rt/*.tsv as alreloc --report writes)

Per row, by the rule alreloc names:
  FUNC entry / same-code function / symbol / OBJECT start: the old numeral's symbol + offset in the donor equals the
    new numeral's symbol + offset in the target;
  .got slot ...: the two cells hold the same symbol + offset (or the same non-address value);
  gap: refused (the rule is unsound across .got layouts; a resolve line must decide the row);
  derived image bound: old / new are the two images' page-rounded ends, or those ends / 8 (the shadow span);
  range end: end - 1 lies at the same symbol + offset on both sides;
  any rule that keeps the value (SIZES_KEEP, not an address, ...): listed when the value lies in a donor symbol, so a
    reader sees every kept numeral that could have been an address.
Rows decided by a resolve line are not re-checked here (class5cmp.py derived them from the images). Exit 1 on any
wrong row."""
import collections, glob, os, sys
from elftools.elf.elffile import ELFFile


class Elf:
    def __init__(self, p):
        e = ELFFile(open(p, 'rb'))
        self.segs = [(g['p_vaddr'], g['p_filesz'], g.data()) for g in e.iter_segments() if g['p_type'] == 'PT_LOAD']
        self.end = max(g['p_vaddr'] + g['p_memsz'] for g in e.iter_segments() if g['p_type'] == 'PT_LOAD')
        self.syms = [(s['st_value'], s['st_size'], s.name) for s in e.get_section_by_name('.symtab').iter_symbols()
                     if s['st_value'] and s.name and s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT', 'STT_TLS')]

    def q(self, a):
        for v, fz, d in self.segs:
            if v <= a and a + 8 <= v + fz:
                return int.from_bytes(d[a - v:a - v + 8], 'little')
        return None

    def at(self, a):
        ex = sorted(x[2] for x in self.syms if x[0] == a)
        if ex:
            return ex[0], 0
        c = [x for x in self.syms if x[0] <= a < x[0] + x[1]]
        if c:
            m = min(c, key=lambda x: x[1])
            return m[2], a - m[0]
        return None


def num(s):
    s = s.strip()
    return int(s, 16) if s.lower().startswith('0x') else int(s)


def main():
    rep, img, dtw, ttw = sys.argv[1:5]
    D, T = Elf(dtw), Elf(ttw)
    page = lambda x: (x + 4095) // 4096 * 4096
    dend, tend = page(D.end), page(T.end)
    rules, bad, kept = collections.Counter(), [], []
    for p in sorted(glob.glob(os.path.join(rep, img, 'Rt', '*.tsv'))):
        for line in open(p):
            f = line.rstrip('\n').split('\t')
            if line.startswith(('#', 'file:line')) or len(f) < 4:
                continue
            loc, old, new, rule = f[:4]
            r = rule.split(' (')[0]
            rules[r] += 1
            try:
                o, n = num(old), num(new)
            except ValueError:
                continue
            if r in ('FUNC entry', 'same-code function', 'symbol', 'OBJECT start'):
                if D.at(o) is None or D.at(o) != T.at(n):
                    bad.append('%s %s -> %s [%s]: %s vs %s' % (loc, old, new, r, D.at(o), T.at(n)))
                elif r == 'symbol':
                    # a value moved by its offset inside a symbol: right for an address, wrong for a model constant that
                    # happens to fall in the image (FS_FROFF 0x509000 -> theDepot + 0x376068): a reader confirms each
                    kept.append('%s %s -> %s MOVED [symbol] (%s+0x%x on both sides): confirm it is an address'
                                % ((loc, old, new) + D.at(o)))
            elif r.startswith('.got slot'):
                vo, vn = D.q(o), T.q(n)
                so, sn = (D.at(vo) if vo is not None else None), (T.at(vn) if vn is not None else None)
                if not ((so is not None and so == sn) or (so is None and vo == vn)):
                    bad.append('%s %s -> %s [%s]: holds %s vs %s' % (loc, old, new, r, hex(vo or 0), hex(vn or 0)))
            elif r == 'gap':
                bad.append('%s %s -> %s [gap]: needs a resolve line' % (loc, old, new))
            elif r == 'derived image bound':
                if (o, n) not in ((dend, tend), (dend // 8, tend // 8)):
                    bad.append('%s %s -> %s [%s]: image ends 0x%x / 0x%x' % (loc, old, new, r, dend, tend))
            elif r.startswith('range end'):
                if D.at(o - 1) is None or D.at(o - 1) != T.at(n - 1):
                    bad.append('%s %s -> %s [range end]: %s vs %s' % (loc, old, new, D.at(o - 1), T.at(n - 1)))
            elif r != 'resolve' and o == n and D.at(o) is not None:
                kept.append('%s %s kept [%s] (lies in %s+0x%x of the donor)' % ((loc, old, r) + D.at(o)))
    if not rules:
        bad.append('no report rows under %s/%s/Rt: nothing was checked' % (rep, img))
    print('image %s: rows by rule %s' % (img, dict(rules)))
    print('kept values that lie in a donor symbol (each a model constant or an instruction word, see RELOC-PLAN.md):')
    print('\n'.join('  ' + k for k in kept) or '  none')
    print('\n'.join('WRONG: ' + b for b in bad) or 'PASS: 0 wrong rows')
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
