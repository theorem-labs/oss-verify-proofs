#!/usr/bin/env python3
"""Turn a port_addr_check predict TSV into the per-line numeral substitutions to apply.

MAPS rows carry the prediction (column `expected`).  Two classes are kept as fm wrote them:
  * GXA / donor symbol keys: the numeral is the argument of `sym` (`@sym A_img 0x22e18`), a key into
    the donor key space that disco's record (lib/CJ/RL/I/RecAsanVf{A,B}.v over IImg{A,B}) maps, not an address of this image;
  * anything the tool does not call MAPS (NON-ADDRESS: sizes, counts, masks, bounds; UNRESOLVED-SOURCE).
The first G9 tool version's numerals.py (sha256 88e6de21e497f06cd322e4e14f41d5da3adb3b99a2e6dbe13ccf872c5b2ac295) with
this docstring changed only (it named the machine path it was copied from); it reads no host path.
"""
import csv, json, re, sys, collections

def load(tsv, srcfile):
    rows = []
    with open(tsv) as fh:
        for r in csv.DictReader(fh, delimiter='\t'):
            if r['verdict'] != 'MAPS':
                continue
            if not r['expected']:
                continue
            rows.append(r)
    return rows

SYMKEY = re.compile(r'sym\s+[A-Za-z0-9_]*\s*' )

# By hand: numerals the tool keys to a symbol by accident but which are not addresses of this image.
# key: (file stem, value) -> why
KEEP = {('FMsnprintfGvsni0', '0x140000'):
        'a round bound over vsni_rodata (ro_low: r_hi <= 0x140000), not an address; the tool keys it to '
        '__sanitizer::useCounts+0xc3c0 by position only',
        }

# By hand, for disco: numerals the tool cannot key (NO-PREDICTION / UNRESOLVED), with the disco value and its source.
# key: (file stem, fm value) -> {target: (disco value, why)}.  Applied at every occurrence in the file.
_ZSH = ("end of the first Tfib_zero_shadow row (fm lib/A/AF0m.v:644 (0x10000, 0x20d00 - 0x10000)); disco "
        "lib/A/AF0m.v:1394 and lib/Reusable/YF0m.v:1471 both start (0x10000, 0x20f98 - 0x10000); "
        "boxreg's 0x20cc0 is boxreg's own row")
HAND = {('FMgxaSeamReady', '0x20d00'): {'disco-A': ('0x20f98', _ZSH), 'disco-Y': ('0x20f98', _ZSH)},
        ('FMgxaSeamShadow', '0x20d00'): {'disco-A': ('0x20f98', _ZSH), 'disco-Y': ('0x20f98', _ZSH)},
        }

def build(tsv, srctext, stem=None, target=None):
    lines = srctext.split('\n')
    subs = collections.defaultdict(list)
    kept = []
    for (st, val), per in HAND.items():
        if st != stem or target not in per:
            continue
        exp, why = per[target]
        for i, text in enumerate(lines, start=1):
            if re.search(re.escape(val) + r'\b', text) and not re.search(
                    r'sym\s+(?:[A-Za-z0-9_]+\s+)?' + re.escape(val) + r'\b', text):
                subs[i].append((val, exp))
                kept.append((i, val, exp, 'by hand: ' + why, 'hand'))
    for r in load(tsv, None):
        ln = int(r['src_line'])
        val, exp = r['src_value'], r['expected']
        if r['kind'] == 'dec':
            val, exp = str(int(val, 16)), str(int(exp, 16))
        if (stem, val) in HAND and target in HAND[(stem, val)]:
            continue
        text = lines[ln - 1]
        if re.search(r'sym\s+(?:[A-Za-z0-9_]+\s+)?' + re.escape(val) + r'\b', text):
            kept.append((ln, val, exp, r['src_res'], 'sym-key'))
            continue
        if (stem, val) in KEEP:
            kept.append((ln, val, exp, 'NON-ADDRESS by hand: ' + KEEP[(stem, val)], 'kept-by-hand'))
            continue
        if val == exp:
            kept.append((ln, val, exp, r['src_res'], 'same-value'))
            continue
        subs[ln].append((val, exp))
        kept.append((ln, val, exp, r['src_res'], 'applied'))
    # Every occurrence of a numeral the tool keyed takes the same value, including the ones it did not
    # report (comments).  This is what the base relocation did for 0x99000 / 0x5f7000 and so on.
    mapping = {}
    for ln, pairs in subs.items():
        for val, exp in pairs:
            mapping[val] = exp
    for i, text in enumerate(lines, start=1):
        for val, exp in mapping.items():
            if val in text and (val, exp) not in subs.get(i, []):
                if re.search(r'sym\s+(?:[A-Za-z0-9_]+\s+)?' + re.escape(val) + r'\b', text):
                    kept.append((i, val, exp, 'sym-key occurrence', 'sym-key'))
                    continue
                subs[i].append((val, exp))
                kept.append((i, val, exp, 'same numeral, not reported by the tool', 'propagated'))
    return subs, kept

if __name__ == '__main__':
    tsv, src, out = sys.argv[1:4]
    subs, kept = build(tsv, open(src).read())
    json.dump({str(k): v for k, v in subs.items()}, open(out, 'w'))
    for ln, val, exp, res, how in kept:
        print('%s\t%d\t%s\t%s\t%s' % (how, ln, val, exp, res.split(';')[0]))
