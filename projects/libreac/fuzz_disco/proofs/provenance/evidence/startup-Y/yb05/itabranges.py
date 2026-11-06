#!/usr/bin/env python3
"""itabranges.py -- recompute a plan's `<name>_ranges : list (Z * nat)` for the new image.

RULE (default, `--rule text`): one range per EXECUTABLE SECTION of the new image, covering it whole:
(sec_lo, ceil(sec_size / 4)). So every pc the plan can reach is in the itab, whatever the map pairs. Why: the map rule
below covers only pcs the address map pairs, and knock's asan-ubsan image has 1,838 unpaired old pcs, so its range 11 stopped
at 0x7ef88 and the run halted at asan.module_ctor 0x7f448 (label 10322). mk_itab_ranges decodes whatever words
it is given and itab_sound holds for any ranges (YK0c.v:2211-2213), so coverage costs only build time (fuzz_reply.asan:
110,249 words instead of 72,545). The itab holds 4-byte instructions at lo + 4k only (mk_itab_fuel, YK0c.v:2201): the release
images have no compressed instructions (MEASURED: all 110,249 / 110,579 instructions of fuzz_reply's asan / asan-ubsan
.text are 4 bytes at 4-aligned pcs), and the tool REFUSES an image where that is false.

`--rule map` (the old rule, kept for comparison):

  itabranges.py --old OLD.elf --new NEW.elf --map map.json --plan DONOR_PLAN.v [--out-plan NEW_PLAN.v] [--name NAME] [--write]

A range (lo, n) is read by mk_itab_ranges (YK09.v:2713) through mk_itab_fuel (YK0c.v:2201): it records the decoded word at
lo, lo+4, ..., lo+4(n-1), so it covers the BYTES [lo, lo + 4n). numeral_map.py moves lo and keeps n, which under-covers when the
new code is longer: the symbolic run then stops at the first pc the itab lacks (observed on fuzz_reply: the run left
__init_ssp and halted at asan.module_ctor). Here every old range is re-derived: map each 4-byte-aligned pc of the old range
through the map's code runs, take the hull of the mapped pcs, and emit (new_lo, ceil(span / 4)). Overlapping or adjacent
new ranges are merged. The result covers every mapped pc of the old ranges, with the same instruction-word rule.
"""
import argparse, json, re, sys


def code_map(mapjson):
    m = json.load(open(mapjson))
    runs = sorted((r['old_lo'], r['old_hi'], r['delta']) for r in m['runs'] if r.get('section') == '.text')
    if not runs:
        sys.exit('itabranges: the map has no .text runs')

    def f(a):
        for lo, hi, d in runs:
            if lo <= a < hi:
                return a + d
        return None
    return f


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--old', default=None); ap.add_argument('--new', required=True); ap.add_argument('--map', default=None)
    ap.add_argument('--rule', default='text', choices=['text', 'map'])
    ap.add_argument('--plan', required=True, help='the DONOR plan: its ranges are the old ones')
    ap.add_argument('--out-plan', default=None, help='write the new definition into this plan file (default: --plan with --write)')
    ap.add_argument('--name', default=None); ap.add_argument('--write', action='store_true')
    a = ap.parse_args()
    txt = open(a.plan).read()
    name = a.name or re.search(r'Definition (\w+_ranges) : list \(Z \* nat\)', txt).group(1)
    m = re.search(r'Definition %s : list \(Z \* nat\) := \[(.*?)\]%%Z\.' % name, txt, re.S)
    if not m:
        sys.exit('itabranges: %s not found in %s' % (name, a.plan))
    rs = [(int(x, 0), int(n)) for x, n in re.findall(r'\((0x[0-9a-f]+|\d+), (\d+)%nat\)', m.group(1))]
    if a.rule == 'text':
        import os
        sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'trlen'))
        from rvdis import md
        from elftools.elf.elffile import ELFFile
        e = ELFFile(open(a.new, 'rb'))
        merged = []
        for sec in e.iter_sections():
            if not (sec['sh_flags'] & 0x4) or not sec['sh_size']:
                continue
            lo, sz = sec['sh_addr'], sec['sh_size']
            bad = [i.address for i in md.disasm(sec.data(), lo) if i.size != 4 or i.address % 4]
            if lo % 4 or bad:
                sys.exit('itabranges: REFUSED: %s of %s has compressed or misaligned instructions (%d, first %s): the itab '
                         '(4-byte words at lo + 4k) would miss them' % (sec.name, a.new, len(bad), [hex(x) for x in bad[:3]]))
            merged.append([lo, (sz + 3) // 4, sec.name])
        mapped_words = None
    else:
        merged = None
    if merged is not None:
        body = '; '.join('(%#x, %d%%nat)' % (lo, n) for lo, n, _ in merged)
        newdef = 'Definition %s : list (Z * nat) := [%s]%%Z.' % (name, body)
        print('%s (rule text): %d donor ranges (%d words) -> %d new, the executable sections whole (%d words)' % (
            name, len(rs), sum(n for _, n in rs), len(merged), sum(n for _, n, _ in merged)))
        for lo, n, src in merged:
            print('  %#x +%d words (%#x..%#x) = %s' % (lo, n, lo, lo + 4 * n, src))
        return write_out(a, txt, m, name, newdef)
    mp = code_map(a.map)
    out, unmapped = [], 0
    for lo, n in rs:
        mapped = [mp(lo + 4 * k) for k in range(n)]
        hit = [x for x in mapped if x is not None]
        unmapped += len(mapped) - len(hit)
        if not hit:
            sys.exit('itabranges: range %#x +%d maps nowhere' % (lo, n))
        nlo, nhi = min(hit), max(hit) + 4
        out.append([nlo, (nhi - nlo + 3) // 4, '%#x+%d' % (lo, n)])
    out.sort()
    merged = []
    for nlo, cnt, src in out:
        if merged and nlo <= merged[-1][0] + 4 * merged[-1][1]:
            end = max(merged[-1][0] + 4 * merged[-1][1], nlo + 4 * cnt)
            merged[-1][1] = (end - merged[-1][0] + 3) // 4
            merged[-1][2] += ',' + src
        else:
            merged.append([nlo, cnt, src])
    body = '; '.join('(%#x, %d%%nat)' % (lo, n) for lo, n, _ in merged)
    newdef = 'Definition %s : list (Z * nat) := [%s]%%Z.' % (name, body)
    print('%s: %d old ranges (%d words) -> %d new (%d words); unmapped old pcs %d' % (
        name, len(rs), sum(n for _, n in rs), len(merged), sum(n for _, n, _ in merged), unmapped))
    for lo, n, src in merged:
        print('  %#x +%d words (%#x..%#x) from old %s' % (lo, n, lo, lo + 4 * n, src))
    write_out(a, txt, m, name, newdef)


def write_out(a, txt, m, name, newdef):
    if a.out_plan:
        t2 = open(a.out_plan).read()
        m2 = re.search(r'Definition %s : list \(Z \* nat\) := \[(.*?)\]%%Z\.' % name, t2, re.S)
        if not m2:
            sys.exit('itabranges: %s not found in %s' % (name, a.out_plan))
        open(a.out_plan, 'w').write(t2[:m2.start()] + newdef + t2[m2.end():])
        print('wrote %s' % a.out_plan)
    elif a.write:
        open(a.plan, 'w').write(txt[:m.start()] + newdef + txt[m.end():])
        print('wrote %s' % a.plan)
    else:
        print(newdef)


if __name__ == '__main__':
    main()
