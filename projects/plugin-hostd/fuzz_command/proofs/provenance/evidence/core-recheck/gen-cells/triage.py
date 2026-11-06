#!/usr/bin/env python3
"""Triage the flagged gate rows of the generated files AF0m/AE3i/AD2j (key A) and YF0m/YE3i/YD2j (key B).

  triage.py --lib OURS_LIB --donor-lib DONOR_LIB --img IMG_DIR --gate-dir GATE_DIR --gen-a RA.gen.tsv
            --gen-b RB.gen.tsv --out OUT_DIR

OURS_LIB    the unit's proofs folder lib/ (plugin-hostd/fuzz_command at the series head)
DONOR_LIB   cgif_file_fuzzer's lib/ at the donor commit
IMG_DIR     cmd.A.pin cmd.A.twin cmd.B.pin cmd.B.twin cgif.A.pin cgif.A.twin cgif.B.pin cgif.B.twin
GATE_DIR    port_addr_check 3d2eee813cce (its sentences() gives the numeral list the gate judged)

Every numeral of the six files gets a rule (f0m_rules, e3i_rules, d2j_rules) that measures the image or the file's
own text.  Each flagged row is the judgement of its numeral (matched by line and value); a donor numeral with no
ported numeral (UNPAIRED-SOURCE) is matched to the ported numeral that takes its place.  Known-answer control: every
row's rule re-judges the value + 4 and the donor's value (the gate's src_value, else the donor numeral at the same
position); a rule that accepts a perturbed value is reported.

Writes OUT_DIR/triage-rows.tsv, OUT_DIR/controls.tsv, OUT_DIR/numerals-<file>.tsv (whole files) and prints counts.
"""
import argparse
import collections
import csv
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import imgmeas  # noqa: E402
import f0m_rules  # noqa: E402
import e3i_rules  # noqa: E402
import d2j_rules  # noqa: E402

csv.field_size_limit(10 ** 9)
FILES = {'A': {'F0m': 'A/AF0m.v', 'E3i': 'A/AE3i.v', 'D2j': 'A/AD2j.v', 'glob': 'A/Prog/CmdGlob.v'},
         'B': {'F0m': 'B/YF0m.v', 'E3i': 'B/YE3i.v', 'D2j': 'B/YD2j.v', 'glob': 'B/Prog/CmdGlob.v'}}
DONOR = {'A': {'F0m': 'A/AF0m.v', 'D2j': 'A/AD2j.v'}, 'B': {'F0m': 'YF0m.v', 'D2j': 'YD2j.v'}}
ROLE = {'A': 'fuzz_command.asan', 'B': 'fuzz_command.asan-ubsan'}
DROLE = {'A': 'cgif_file_fuzzer.asan', 'B': 'cgif_file_fuzzer.asan-ubsan'}


def h(x):
    return f'{x:#x}'


def build(k, a, im, dm):
    rd = lambda p: open(os.path.join(a.lib, p), encoding='utf-8').read()  # noqa: E731
    dd = lambda p: open(os.path.join(a.donor_lib, p), encoding='utf-8').read()  # noqa: E731
    f = FILES[k]
    gF = f0m_rules.F0m(rd(f['F0m']), dd(DONOR[k]['F0m']), im, dm, k)
    gE = e3i_rules.E3i(rd(f['E3i']), rd(f['F0m']), im)
    gD = d2j_rules.D2j(rd(f['D2j']), dd(DONOR[k]['D2j']), rd(f['F0m']), rd(f['glob']), im, dm)
    return {os.path.basename(f['F0m']): (gF, gF.slots()), os.path.basename(f['E3i']): (gE, gE.slots()),
            os.path.basename(f['D2j']): (gD, gD.slots())}


def unpaired_source(row, g, slots, dtext):
    """a donor numeral with no ported numeral: the ported numeral that takes its place, judged."""
    dl, dv = int(row['src_line']), int(row['src_value'], 16)
    dline = dtext.split('\n')[dl - 1]
    if row['sentence'].startswith('Record'):
        field = dline.split(' :')[0]
        ln = [s for s in slots if s.block == 'CmdBSyms' and g.b['CmdBSyms'] and
              any(t.startswith(field + ' ') for l2, t in g.b['CmdBSyms'] if l2 == s.line)]
        dn = [int(x, 0) for x in re.findall(r'(?<![\w.])(0x[0-9a-fA-F]+|\d+)(?![\w])', dline)]
        idx = [i for i, x in enumerate(dn) if x == dv]
        k = idx[row['_occ']] if row['_occ'] < len(idx) else (idx[0] if idx else 0)
        cand = [s for s in ln if s.pos == k]
        if not cand:
            return 'OPEN', f'no ported numeral for donor {h(dv)} at donor line {dl}', 'OPEN', None
        s = cand[0]
        ok, r, m, e = s.judge(s.value)
        return ('RENAMED-SENTENCE', f'donor Record TfibSyms is the ported Record CmdBSyms (renamed, the file header '
                f'says so); donor {h(dv)} at donor line {dl} ({field}) is the ported {h(s.value)} at line {s.line}, '
                f'judged {r}: {m}', 'OK' if ok else 'FINDING', s)
    if row['sentence'] == 'Definition Tfib_owned_static':
        drows = f0m_rules.pairs([(dl, dline)])
        dg = g._donor_guard_los()
        for (l2, lo, x2, sub) in drows:
            if lo in dg and dv in (lo, x2):
                dd = [f for d, f in g.dm.descriptors() if f[0] + f[1] == lo][0]
                return ('DONOR-GUARD-ROW-DROPPED', f'donor row ({h(lo)}, {h(x2)}) is beg+size, size_with_redzone-size '
                        f'of a donor registered global (beg {h(dd[0])} size {h(dd[1])} size_with_redzone {h(dd[2])}, '
                        f'donor asan_globals); the ported file lists instead the guard rows of its own '
                        f'{len(g.D)} descriptors (OWNED-GUARD-RANGE, all measured)', 'OK', None)
            if sub is not None and dv == x2:
                donor_rows = [r for r in g.down if r[1] not in dg]
                j = [i for i, r in enumerate(donor_rows) if r[0] == dl and r[1] == lo][0]
                own = g.own[j]
                s = [s for s in slots if s.line == own[0] and s.pos == 1][0]
                ok, r, m, e = s.judge(s.value)
                return ('DONOR-HI-AS-SIZE', f'donor writes ({h(lo)}, {h(x2)} - {h(lo)}); the ported row {j} writes '
                        f'({h(own[1])}, {h(own[2])}) at line {own[0]}: its size is the donor\'s hi - lo, judged {r}: {m}',
                        'OK' if ok else 'FINDING', s)
    return 'OPEN', 'no rule for this donor numeral', 'OPEN', None


def neighbours(slots):
    """id(slot) -> the value of the previous slot of the same block, role and position (the next one for the first):
    the 'shift' control, a value the same rule accepts one row away."""
    groups = collections.defaultdict(list)
    for s in slots:
        groups[(s.block, s.role, s.pos)].append(s)
    nb = {}
    for g in groups.values():
        for i, s in enumerate(g):
            o = g[i - 1] if i > 0 else (g[1] if len(g) > 1 else None)
            nb[id(s)] = o.value if o is not None else None
    return nb


def perturb(c, s, v, dv, nb):
    """the known-answer control of one numeral: value + 4, the donor's value, the neighbour row's value."""
    c['rows'] += 1
    c['plus4_refused' if not s.judge(v + 4)[0] else 'plus4_ACCEPTED'] += 1
    if dv is None:
        c['donor_na'] += 1
    elif dv == v:
        c['donor_same'] += 1
    else:
        c['donor_refused' if not s.judge(dv)[0] else 'donor_ACCEPTED'] += 1
    if nb is None or nb == v:
        c['nb_na'] += 1
    else:
        c['nb_refused' if not s.judge(nb)[0] else 'nb_ACCEPTED'] += 1


def main():
    ap = argparse.ArgumentParser()
    for x in ('--lib', '--donor-lib', '--img', '--gate-dir', '--gen-a', '--gen-b', '--out'):
        ap.add_argument(x, required=True)
    a = ap.parse_args()
    sys.path.insert(0, a.gate_dir)
    import port_addr_check as pac
    os.makedirs(a.out, exist_ok=True)
    out_rows, ctl = [], collections.defaultdict(collections.Counter)
    whole, nbs = [], {}
    for k, gen in (('A', a.gen_a), ('B', a.gen_b)):
        I = lambda n: os.path.join(a.img, n)  # noqa: E731
        im = imgmeas.Img(I(f'cmd.{k}.pin'), I(f'cmd.{k}.twin'), k)
        dm = imgmeas.Img(I(f'cgif.{k}.pin'), I(f'cgif.{k}.twin'), k)
        fams = build(k, a, im, dm)
        # whole-file numeral judgements, and the gate's own numeral list of each file
        for fname, (g, slots) in fams.items():
            rel = FILES[k][{'F0m': 'F0m', 'E3i': 'E3i', 'D2j': 'D2j'}[
                'F0m' if 'F0m' in fname else 'E3i' if 'E3i' in fname else 'D2j']]
            text = open(os.path.join(a.lib, rel), encoding='utf-8').read()
            gate = collections.Counter()
            for key, name, line, toks, nums, st in pac.sentences(text):
                for n in nums:
                    if n.kind in ('hex', 'dec'):
                        gate[(n.line, n.v)] += 1
            mine = collections.Counter((s.line, s.value) for s in slots)
            res = collections.Counter()
            nbm = neighbours(slots)
            nbs[fname] = nbm
            with open(os.path.join(a.out, f'numerals-{fname[:-2]}.tsv'), 'w') as fh:
                fh.write('file\tline\tpos\tkind\tvalue\tblock\trole\treason\tmeasurement\tresult\texpected\n')
                for s in slots:
                    ok, r, m, e = s.judge(s.value)
                    res[(r, ok)] += 1
                    perturb(ctl[('whole-file', fname, r)], s, s.value, s.donor, nbm[id(s)])
                    fh.write(f'lib/{rel}\t{s.line}\t{s.pos}\t{s.kind}\t{h(s.value)}\t{s.block}\t{s.role}\t{r}\t{m}\t'
                             f'{"OK" if ok else "FINDING"}\t{h(e) if isinstance(e, int) else "-"}\n')
            whole.append((f'lib/{rel}', len(slots), sum(gate.values()), sum((gate - mine).values()), res))
        # flagged rows
        rows = [r for r in csv.DictReader((l for l in open(gen) if not l.startswith('#')), delimiter='\t')]
        hdr = list(rows[0].keys()) if rows else []
        occ = collections.Counter()
        for row in rows:
            fname = row['dst_file'] or row['src_file']
            if fname not in fams:
                continue
            g, slots = fams[fname]
            if not row['dst_value']:
                key = (fname, row['src_line'], row['src_value'])
                row['_occ'] = occ[key]
                occ[key] += 1
                dtext = open(os.path.join(a.donor_lib, DONOR[k]['F0m' if 'F0m' in fname else 'D2j']),
                             encoding='utf-8').read()
                reason, meas, result, s = unpaired_source(row, g, slots, dtext)
                out_rows.append([row[c] for c in hdr] + [reason, meas, result, '-' if result == 'OK' else 'code',
                                                         '-', '-'])
                c = ctl[('flagged', fname, reason)]
                if s is not None:
                    perturb(c, s, s.value, int(row['src_value'], 16), nbs[fname][id(s)])
                else:
                    c['rows'] += 1
                    c['no_ported_numeral'] += 1
                continue
            v = int(row['dst_value'], 16)
            ln = int(row['dst_line'])
            key = (fname, ln, v)
            cand = [s for s in slots if s.line == ln and s.value == v]
            if not cand:
                out_rows.append([row[c] for c in hdr] + ['OPEN', 'no rule covers this numeral', 'OPEN', '-', '-', '-'])
                ctl[('flagged', fname, 'OPEN')]['rows'] += 1
                continue
            s = cand[min(occ[key], len(cand) - 1)]
            occ[key] += 1
            ok, reason, meas, exp = s.judge(v)
            prefix = ''
            if row['verdict'] == 'STALE-DONOR-DATA-POINTER' or row['verdict'] == 'STALE-DONOR-CODE-POINTER':
                prefix = 'the gate reads the value as a donor address; measured: '
            out_rows.append([row[c] for c in hdr] + [reason, prefix + meas, 'OK' if ok else 'FINDING',
                                                     '-' if ok else 'code', '-' if ok or not isinstance(exp, int)
                                                     else h(exp), '-'])
            dv = int(row['src_value'], 16) if row['src_value'] else s.donor
            perturb(ctl[('flagged', fname, reason)], s, v, dv, nbs[fname][id(s)])
    cols = hdr + ['reason', 'measurement', 'result', 'finding_kind', 'new_value', 'read_by']
    with open(os.path.join(a.out, 'triage-rows.tsv'), 'w') as fh:
        fh.write('\t'.join(cols) + '\n')
        for r in out_rows:
            fh.write('\t'.join(str(x).replace('\t', ' ') for x in r) + '\n')
    with open(os.path.join(a.out, 'controls.tsv'), 'w') as fh:
        keys = ['rows', 'plus4_refused', 'plus4_ACCEPTED', 'donor_refused', 'donor_ACCEPTED', 'donor_same', 'donor_na',
                'nb_refused', 'nb_ACCEPTED', 'nb_na', 'no_ported_numeral']
        fh.write('scope\tfile\treason\t' + '\t'.join(keys) + '\n')
        for (sc, f, r), c in sorted(ctl.items()):
            fh.write(f'{sc}\t{f}\t{r}\t' + '\t'.join(str(c[x]) for x in keys) + '\n')
    cnt = collections.Counter((r[5] or r[3], r[-6], r[-4]) for r in out_rows)
    for x in sorted(cnt.items()):
        print(*x[0], x[1], sep='\t')
    print('flagged rows', len(out_rows), 'OK', sum(1 for r in out_rows if r[-4] == 'OK'),
          'FINDING', sum(1 for r in out_rows if r[-4] == 'FINDING'), 'OPEN', sum(1 for r in out_rows if r[-4] == 'OPEN'))
    for f, n, ng, nmiss, res in whole:
        print('whole', f, 'slots', n, 'gate numerals', ng, 'gate numerals without a slot', nmiss,
              'OK', sum(v for (r, ok), v in res.items() if ok), 'FINDING', sum(v for (r, ok), v in res.items() if not ok))


if __name__ == '__main__':
    main()
