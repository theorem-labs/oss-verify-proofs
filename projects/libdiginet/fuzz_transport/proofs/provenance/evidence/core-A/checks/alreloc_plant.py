#!/usr/bin/env python3
"""Write the planted controls of the alreloc cross-check into a COPY of stage-out (alreloc-xcheck-control.sh),
libdiginet/fuzz_transport image-A core. Kind: measurement; it proves no function. From libdiginet/fuzz_decode's record
(alreloc_plant.py, sha256 6c4f2678caa8; internal record) plus three plants (rodata-const,
region-split, czone), one per decision group this unit added.

  alreloc_plant.py --positions OUT/out/positions.tsv --stage-out COPY --grant-elf G --grant-syms GU
                   --target-elf T --target-syms TU --plants PLANTS.tsv

Each plant replaces one numeral token of one stage-out line (same notation, hex or decimal) by a value known to be
wrong, and is listed in PLANTS.tsv: plant, file, stage-out line, token index, port_core value, planted value, why.
"""
import argparse, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from alreloc_decide import Img, TOK, val, hx  # noqa: E402


def fmt(tok, v):
    return hx(v) if tok[:2].lower() == '0x' else str(v)


def main():
    ap = argparse.ArgumentParser()
    for k in ('positions', 'stage-out', 'grant-elf', 'grant-syms', 'target-elf', 'target-syms', 'plants'):
        ap.add_argument('--' + k, required=True)
    a = ap.parse_args()
    G, D = Img(a.grant_elf, a.grant_syms), Img(a.target_elf, a.target_syms)
    glo, gsz = G.secrange('.got')
    dlo, dsz = D.secrange('.got')
    cols = open(a.positions).readline().rstrip('\n').split('\t')
    rows = [dict(zip(cols, l.split('\t'))) for l in open(a.positions).read().split('\n')[1:] if l]
    code = lambda r: not r['file'].startswith('Reusable/YA0') or True
    plants = []

    def first(pred):
        for r in rows:
            if r['out_line'] != '-' and r['port_core'] != '-' and r['donor'] != '-' and pred(r):
                return r
        return None

    # got-offset: a .got cell moved alike by both tools; plant the cell at the same .got offset (alreloc's rule `gap`)
    def got_ok(r):
        d, p = val(r['donor']), val(r['port_core'])
        return r['class'] == 'agree' and glo <= d < glo + gsz and dlo <= p < dlo + dsz and int(r['donor_line']) > 20
    r = first(lambda r: got_ok(r) and dlo + val(r['donor']) - glo != val(r['port_core']))
    if r:
        plants.append(('got-offset', r, dlo + val(r['donor']) - glo, 'the transport cell at the same .got offset as the '
                                                                      'donor cell (rule gap), other content'))
    else:
        r = first(got_ok)
        plants.append(('got-offset', r, val(r['port_core']) + 8, 'the next .got cell (the two tables align by '
                                                                 'offset here, so the offset cell is the content cell)'))
    # model-const: the AT_HWCAP range bound, written as alreloc's rule-symbol value
    r = first(lambda r: r['donor'].upper() == '0X20112D' and r['port_core'].upper() == '0X20112D')
    if r:
        pv = val(r['alreloc']) if r['alreloc'] not in ('-', r['donor']) else val(r['donor']) + 0x1000
        plants.append(('model-const', r, pv, 'a model constant moved as an address (alreloc rule %s)' % r['alreloc_rule']))
    # address: an address both tools moved alike, + 8
    r = first(lambda r: r['class'] == 'agree' and r['alreloc_rule'].startswith('OBJECT start') and
              int(r['donor_line']) > 20 and r['donor'].startswith('0x'))
    plants.append(('address', r, val(r['port_core']) + 8, 'symbol + offset off by 8'))
    # donor-value: a relocated address written back to the donor's value (A/AE3m.v STDOUT_BUFA, stdout's buffer, when
    # the tree has it; else the first other address both tools moved alike)
    r, so = None, None
    for q in rows:
        if q['file'] == 'A/AE3m.v' and q['class'] == 'agree' and q['out_line'] != '-':
            so = so or open(os.path.join(a.stage_out, q['file'])).read().split('\n')
            if re.match(r'Definition STDOUT_BUFA : Z := ', so[int(q['out_line']) - 1]):
                r = q
                break
    if r is None:
        r = first(lambda r: r['class'] == 'agree' and r['alreloc_rule'].startswith('OBJECT start') and
                  int(r['donor_line']) > 20 and r['donor'].startswith('0x') and
                  (r['file'], r['out_line']) != (plants[-1][1]['file'], plants[-1][1]['out_line']))
    plants.append(('donor-value', r, val(r['donor']), 'a relocated address written back to the donor\'s value'))
    # decimal address: a decimal address both tools moved alike, + 4
    r = first(lambda r: r['class'] == 'agree' and r['donor'].isdigit() and int(r['donor_line']) > 20 and
              0x10000 <= val(r['donor']) < G.top)
    if r:
        plants.append(('decimal-address', r, val(r['port_core']) + 4, 'a decimal address off by 4'))
    # added for fuzz_transport (one plant per decision group this unit added):
    # rodata-const: an 8-byte binary .rodata constant (8-aligned, a non-text byte among its 8) port_core moved with the
    # merged constants by 8 or 16 (the 8 bytes at the donor address in fuzz_grant.asan are the 8 bytes at port_core's
    # address in fuzz_transport.asan), written back at the donor's address, where fuzz_transport.asan holds other bytes
    ro_lo, ro_sz = G.secrange('.rodata')
    used = {(p[1]['file'], p[1]['out_line']) for p in plants}
    binary = lambda b: b is not None and any(x < 0x20 or x >= 0x7f for x in b)
    r = first(lambda r: (r['file'], r['out_line']) not in used and ro_lo <= val(r['donor']) < ro_lo + ro_sz and
              val(r['donor']) % 8 == 0 and val(r['port_core']) - val(r['donor']) in (8, 16) and
              binary(G.rd(val(r['donor']), 8)) and G.rd(val(r['donor']), 8) == D.rd(val(r['port_core']), 8) and
              D.rd(val(r['donor']), 8) != G.rd(val(r['donor']), 8))
    if r:
        plants.append(('rodata-const', r, val(r['donor']), 'a moved .rodata constant written back at the donor\'s '
                                                          'address (other bytes there in the target)'))
    # region-split: a count of A/AD2f.v's IMG_B_eq that the unit's region list changes, written back as the donor's
    # (what a count + offset reading without the split gives)
    so_cache = {}

    def so_line(q):
        if q['file'] not in so_cache:
            so_cache[q['file']] = open(os.path.join(a.stage_out, q['file'])).read().split('\n')
        return so_cache[q['file']][int(q['out_line']) - 1]
    r = first(lambda r: r['file'] == 'A/AD2f.v' and r['port_core'] != r['donor'] and
              so_line(r).startswith('Lemma IMG_B_eq ') and r['tok'] == '2')
    if r:
        plants.append(('region-split', r, val(r['donor']), 'an IMG_B_eq count written back as the donor\'s'))
    # czone: the CZONE bound written back as the donor's 0x80050000 (below the target's highest constant shadow byte)
    used = {(p[1]['file'], p[1]['out_line']) for p in plants}
    r = first(lambda r: (r['file'], r['out_line']) not in used and r['donor'].lower() == '0x80050000' and
              r['port_core'] != r['donor'])
    if r:
        plants.append(('czone', r, val(r['donor']), 'the CZONE bound written back as the donor\'s'))

    done = set()
    with open(a.plants, 'w') as fh:
        fh.write('plant\tfile\tout_line\ttok\tport_core\tplanted\twhy\n')
        for name, r, pv, why in plants:
            k = (r['file'], r['out_line'])
            assert k not in done, k
            done.add(k)
            p = os.path.join(a.stage_out, r['file'])
            L = open(p).read().split('\n')
            i = int(r['out_line']) - 1
            ms = list(TOK.finditer(L[i]))
            m = ms[int(r['tok'])]
            assert m.group(1) == r['port_core'], (r, m.group(1))
            new = fmt(r['port_core'], pv)
            L[i] = L[i][:m.start()] + new + L[i][m.end():]
            open(p, 'w').write('\n'.join(L))
            fh.write('\t'.join([name, r['file'], r['out_line'], r['tok'], r['port_core'], new, why]) + '\n')
            print('alreloc_plant.py: %s %s:%s tok %s %s -> %s (%s)' % (name, r['file'], r['out_line'], r['tok'],
                                                                       r['port_core'], new, why))


if __name__ == '__main__':
    main()
