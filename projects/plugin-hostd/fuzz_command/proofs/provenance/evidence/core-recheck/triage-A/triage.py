#!/usr/bin/env python3
"""Measured triage of the OPEN flagged rows of gate run RA (port_addr_check 3d2eee813cce; donor
cgif_file_fuzzer lib/A -> plugin-hostd/fuzz_command lib/A, image A).

Every row is judged by a RULE (rules.py). A rule applies to a row by the row's SLOT only: the place of the
numeral in its line (the line's own text around the numeral, the file, the sentence), never by the row's value.
Each slot has an EXPECTED value that a measurement gives independently of the row (facts.py, rules.py): a
symbol-table entry, bytes or a GOT word of fuzz_command.asan, its section / segment headers, the DWARF of its
unstripped twin, the generated start-up certificate lib/A/AB01.v (written from the image), or the definition
elsewhere in the unit that the sentence restates. The row is OK when its value equals the expected value (or,
for a BOUND slot, lies in the measured interval), else a FINDING whose new_value is the measured value.
For an UNPAIRED-PORTED row the stale-donor test is also run (measurement column): is the value the donor image's
address of a symbol X that our image has elsewhere, while our image has something else at the value?

Known-answer controls (controls.tsv): every settled row is judged again with value + 4 and with the donor's
value (the row's src_value; for an UNPAIRED-PORTED row, the value the rule measures on the donor side when it
can); a rule must refuse them.

Usage: triage.py --open RA.open.tsv --ours LIB --donor LIB --img DIR --outdir DIR
  LIB = a unit's .../lib folder (lib/A below it); DIR holds cmd.A.pin cmd.A.twin cgif.A.pin cgif.A.twin."""
import argparse, collections, csv, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import imgtools  # noqa: E402
from facts import Facts  # noqa: E402
import rules as R  # noqa: E402

csv.field_size_limit(10 ** 9)
TOK = re.compile(r"0x[0-9a-fA-F]+|\d+|[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*|\S")
HDR16 = ['verdict', 'kernel_checked', 'image', 'src_file', 'src_line', 'dst_file', 'dst_line', 'sentence', 'idx',
         'kind', 'src_value', 'dst_value', 'src_class', 'src_res', 'dst_res', 'note']
OUT_COLS = HDR16 + ['reason', 'measurement', 'result', 'finding_kind', 'new_value', 'read_by']


_CT = re.compile(r'\(\*|\*\)')
_NONNL = re.compile(r'[^\n]')


def blank_comments(text):
    """the text with every (* .. *) comment (nested) replaced by spaces; newlines and offsets kept."""
    out, depth, pos = [], 0, 0
    for m in _CT.finditer(text):
        seg = text[pos:m.start()]
        out.append(_NONNL.sub(' ', seg) if depth else seg)
        if m.group() == '(*':
            depth += 1
            out.append('  ')
        elif depth:
            depth -= 1
            out.append('  ')
        else:
            out.append(m.group())
        pos = m.end()
    tail = text[pos:]
    out.append(_NONNL.sub(' ', tail) if depth else tail)
    return ''.join(out)


class Unit:
    """read access to a unit's lib folder."""
    def __init__(self, lib):
        self.lib = lib
        self._raw, self._code, self._lines = {}, {}, {}

    def text(self, rel):
        if rel not in self._raw:
            p = os.path.join(self.lib, rel)
            self._raw[rel] = open(p, encoding='utf-8', errors='replace').read() if os.path.exists(p) else None
        return self._raw[rel]

    def code(self, rel):
        if rel not in self._code:
            t = self.text(rel)
            self._code[rel] = blank_comments(t) if t is not None else None
        return self._code[rel]

    def code_lines(self, rel):
        if rel not in self._lines:
            c = self.code(rel)
            self._lines[rel] = c.split('\n') if c is not None else None
        return self._lines[rel]

    def files(self, sub=''):
        out = []
        for root, _, fs in os.walk(os.path.join(self.lib, sub)):
            for f in fs:
                if f.endswith('.v'):
                    out.append(os.path.relpath(os.path.join(root, f), self.lib))
        return sorted(out)

    def files_with(self, needle, sub=''):
        """the files of sub whose raw text holds needle (a cheap filter before a by-use grep)."""
        return [rel for rel in self.files(sub) if needle in (self.text(rel) or '')]


def num_tokens(line):
    """[(start, end, value, kind)] of the numerals of a comment-blanked line (the gate's TOK lexer)."""
    out = []
    for t in TOK.finditer(line):
        tx = t.group(0)
        if tx[0].isdigit():
            out.append((t.start(), t.end(), int(tx, 16) if tx.startswith('0x') else int(tx),
                        'hex' if tx.startswith('0x') else 'dec'))
    return out


def stale_test(v, F):
    """the stale-donor test of one value: text, and True when the value is a stale donor address. A value below
    the donor image base addresses nothing (TLS offsets and absolute symbols are not addresses)."""
    O, D = F.O, F.D
    probe, tag = v, ''
    if F.shadow_off <= v < F.shadow_off + (1 << 40) // 8 and v >= 0x7fff8000:
        probe, tag = (v - F.shadow_off) * 8, f'shadow of {(v - F.shadow_off) * 8:#x}: '
    if probe < D.hull()[0]:
        return f'stale-donor test: {tag}{probe:#x} is below the donor image base {D.hull()[0]:#x}: no donor address', False
    ds = [s for s in D.at(probe) if s[4] != 'SHN_ABS' and s[3] != 'STT_TLS']
    if not ds:
        # informational only: a value inside a donor object (X + off). It decides nothing: the row's own rule has
        # measured what the value names in our image.
        cov = D.covering(probe)
        inside = ''
        if cov:
            s = cov[0]
            ours = [x for x in O.byname.get(s[2], []) if x[4] != 'SHN_UNDEF']
            moved = f'; ours has {s[2]} at {ours[0][0]:#x}' if len(ours) == 1 and ours[0][0] != s[0] else ''
            inside = f' (it lies inside donor {s[2]}+{probe - s[0]:#x}{moved}; ours at {probe:#x}: {O.describe(probe)})'
        return f'stale-donor test: {tag}donor symtab {D.sha_twin} has no symbol starting at {probe:#x}{inside}: not a donor symbol address', False
    names = sorted({s[2] for s in ds})
    moved = []
    for n in names:
        ours = [s[0] for s in O.byname.get(n, []) if s[4] != 'SHN_UNDEF']
        if ours and probe not in ours:
            moved.append((n, ours))
    here = O.describe(probe)
    if moved and not any(probe in [s[0] for s in O.byname.get(n, [])] for n in names):
        n, ours = moved[0]
        return (f'stale-donor test: {tag}donor has {n} at {probe:#x}, ours has {n} at {ours[0]:#x} and {here} at {probe:#x}: '
                f'STALE'), True
    return f'stale-donor test: {tag}donor has {", ".join(names[:3])} at {probe:#x}; ours at {probe:#x}: {here} (same name or none moved)', False


def proof_lines(L):
    """line numbers inside Proof .. Qed / Defined / Admitted blocks of a comment-blanked file."""
    inside, out = False, set()
    for i, l in enumerate(L, 1):
        if re.search(r'\bProof\b', l):
            inside = True
        if inside:
            out.add(i)
        if re.search(r'\b(Qed|Defined|Admitted|Abort)\s*\.', l):
            inside = False
    return out


def read_by(U, sentence, file, line):
    """first statement / definition over lib/ that uses the sentence's name (by-use grep, comments blanked, lines
    inside Proof .. Qed skipped); if none, the first proof that uses it."""
    m = re.match(r"(?:Definition|Lemma|Hypothesis|Hypotheses|Variables?|Let|Class|Record|Fixpoint|Theorem|Notation)\s+([A-Za-z_][\w']*)", sentence)
    if not m:
        return '-'
    name = m.group(1)
    rx = re.compile(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])")
    defn = f'A/{file}'
    first_proof = None
    for rel in U.files_with(name):
        L = U.code_lines(rel)
        if not any(rx.search(l) for l in L):
            continue
        pl = proof_lines(L)
        for i, l in enumerate(L, 1):
            if (rel == defn and i == line) or not rx.search(l):
                continue
            if i in pl:
                first_proof = first_proof or f'lib/{rel}:{i}'
                continue
            return f'lib/{rel}:{i}'
    return f'no statement or definition; proofs only (first lib/{first_proof[4:]})' if first_proof else 'none'


SENT_END = re.compile(r'(?<!\.)\.(?=\s|$)')
IDHEX = re.compile(r"(?:(?<=_)|(?<=0x))([0-9a-fA-F]{5,})(?=_|$|')")


def sentence_numerals(code):
    """[[(offset, value, kind)]] numerals of each sentence of a comment-blanked file, in the gate's order (TOK lexer;
    hex digit runs inside identifiers count, as the gate's IDHEX does)."""
    out, pos = [], 0
    ends = [m.end() for m in SENT_END.finditer(code)] + [len(code)]
    for e in ends:
        s, base, pos = code[pos:e], pos, e
        nums = []
        for t in TOK.finditer(s):
            tx = t.group(0)
            if tx[0].isdigit():
                nums.append((base + t.start(), base + t.end(), int(tx, 16) if tx.startswith('0x') else int(tx)))
            elif tx[0].isalpha() or tx[0] == '_':
                for hx in IDHEX.finditer(tx):
                    nums.append((None, None, int(hx.group(1), 16)))
        out.append(nums)
    return out


def assign_positions(rows, U):
    """{row index: (start, end, [spans of the same value on the line])} the numeral token of each row on its line.
    A row with an idx (a paired row) is the idx-th numeral of its sentence (the gate's own ordinal); a row without
    one (UNPAIRED-PORTED) is matched in the gate's row order among the line's numerals of that value."""
    pos, groups, cache = {}, collections.OrderedDict(), {}
    for i, r in enumerate(rows):
        groups.setdefault((r[5], int(r[6])), []).append(i)
    for (f, ln), idxs in groups.items():
        L = U.code_lines('A/' + f)
        toks = num_tokens(L[ln - 1]) if L and ln <= len(L) else []
        lstart = sum(len(x) + 1 for x in L[:ln - 1])
        p = 0
        for i in idxs:
            v, kind = int(rows[i][11], 16), rows[i][9]
            same = [k for k in range(len(toks)) if toks[k][2] == v]
            k = None
            if rows[i][8] != '':
                if f not in cache:
                    cache[f] = sentence_numerals('\n'.join(L))
                idx = int(rows[i][8])
                for nums in cache[f]:
                    if idx < len(nums) and nums[idx][0] is not None and lstart <= nums[idx][0] < lstart + len(L[ln - 1]) + 1 \
                            and nums[idx][2] == v:
                        k = [c for c in same if toks[c][0] == nums[idx][0] - lstart]
                        k = k[0] if k else None
                        break
            if k is None:
                cand = [c for c in same if toks[c][3] == kind] or same
                after = [c for c in cand if c >= p]
                k = after[0] if after else (cand[0] if cand else None)
            if k is None:
                pos[i] = None
                continue
            pos[i] = (toks[k][0], toks[k][1], [(toks[c][0], toks[c][1]) for c in same])
            p = k + 1
    return pos


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--open', required=True)
    ap.add_argument('--ours', required=True)
    ap.add_argument('--donor', required=True)
    ap.add_argument('--img', required=True)
    ap.add_argument('--outdir', required=True)
    a = ap.parse_args()
    O, D = imgtools.load(a.img.rstrip('/') + '/')
    U, UD = Unit(a.ours), Unit(a.donor)
    F = Facts(O, D, U, UD)
    rules = R.make_rules(F)
    lines = [l.rstrip('\n').split('\t') for l in open(a.open) if not l.startswith('#')]
    hdr, rows = lines[0], lines[1:]
    assert hdr[:16] == HDR16, hdr
    pos = assign_positions(rows, U)
    out, ctl = [], collections.defaultdict(lambda: collections.Counter())
    for i, r in enumerate(rows):
        f, ln = r[5], int(r[6])
        line = U.code_lines('A/' + f)[ln - 1]
        p = pos[i]
        v = int(r[11], 16)
        verdicts = []
        spans = [(p[0], p[1])] + [s for s in p[2] if s != (p[0], p[1])] if p else []
        for sp in spans[:1]:
            verdicts.append(R.judge(rules, F, r, line, sp, v))
        reason, meas, res, kind, newv, kind_slot = verdicts[0] if verdicts else ('NO-TOKEN', 'numeral not found on the line', 'OPEN', '-', '-', None)
        # the other occurrences of the same value on the line must get the same verdict (else say which one)
        if p and len(p[2]) > 1:
            others = [R.judge(rules, F, r, line, sp, v) for sp in p[2] if sp != (p[0], p[1])]
            if any(o[2] != res for o in others):
                meas += f' [the value occurs {len(p[2])} times on the line; this row is the occurrence at column {p[0] + 1} by the gate\'s row order]'
        if r[0] == 'UNPAIRED-PORTED':
            st, stale = stale_test(v, F)
            meas += '; ' + st
            if stale and res == 'OK':
                res, reason = 'FINDING', reason + '+STALE'
        rb = '-'
        if res == 'FINDING':
            rb = read_by(U, r[7], f, ln)
        out.append(r[:16] + [reason, meas, res, kind if res == 'FINDING' else '-', newv if res == 'FINDING' else '-', rb])
        # controls: the rule must refuse value + 4 and the donor's value; a BOUND slot also its edge + 4; and the
        # stale-donor test must call the donor's value of an UNPAIRED-PORTED address slot stale
        if res == 'OK' and kind_slot is not None and p:
            rid = reason.split('+')[0]
            sp = (p[0], p[1])
            e = R.slot_exp(rules, F, r, line, sp)
            dv = R.donor_value(rules, F, r, line, sp, v)
            pert = [('value+4', v + 4), ('donor value', dv)]
            if e is not None and (e.lo is not None or e.hi is not None):
                pert.append(('4 beyond the measured bound', e.hi + 4 if e.hi is not None else e.lo - 4))
            for lab, pv in pert:
                if pv is None:
                    ctl[rid][f'{lab}: no donor value'] += 1
                    continue
                if pv == v:
                    ctl[rid][f'{lab}: equals the row value (not a perturbation)'] += 1
                    continue
                cr = R.judge(rules, F, r, line, sp, pv)
                ctl[rid][f'{lab}: ' + ('refused' if cr[2] != 'OK' else 'ACCEPTED')] += 1
            if r[0] == 'UNPAIRED-PORTED' and dv is not None and dv != v and dv >= F.D.hull()[0]:
                st, stale = stale_test(dv, F)
                ctl['STALE-DONOR-TEST'][f'donor value of the slot ({rid}): ' + ('called STALE' if stale else 'NOT called stale')] += 1
            if r[0] == 'UNPAIRED-PORTED':
                # planted: the donor address of the symbol the row's value names in our image (the value a port that
                # forgot to move it would hold) must be called stale
                for s in O.at(v):
                    dd = [x[0] for x in D.byname.get(s[2], []) if x[4] != 'SHN_UNDEF']
                    if len(dd) == 1 and dd[0] != v:
                        st, stale = stale_test(dd[0], F)
                        ctl['STALE-DONOR-TEST'][f'planted donor address of the named symbol ({rid}): ' + ('called STALE' if stale else 'NOT called stale')] += 1
                        break
        if res == 'FINDING' and p and newv not in ('-', 'None'):
            cr = R.judge(rules, F, r, line, (p[0], p[1]), int(newv))
            ctl[reason]['measured new value: ' + ('accepted' if cr[2] == 'OK' else 'REFUSED')] += 1
    os.makedirs(a.outdir, exist_ok=True)
    with open(os.path.join(a.outdir, 'triage-rows.tsv'), 'w') as fh:
        fh.write('\t'.join(OUT_COLS) + '\n')
        for r in out:
            fh.write('\t'.join(x.replace('\t', ' ').replace('\n', ' ') for x in r) + '\n')
    with open(os.path.join(a.outdir, 'controls.tsv'), 'w') as fh:
        fh.write('reason\tperturbation\tresult\trows\n')
        for rid in sorted(ctl):
            for k, n in sorted(ctl[rid].items()):
                lab, resu = k.split(': ', 1)
                fh.write(f'{rid}\t{lab}\t{resu}\t{n}\n')
    cnt = collections.Counter((r[16], r[18]) for r in out)
    for k in sorted(cnt):
        print(*k, cnt[k], sep='\t')
    print('rows', len(out), 'OK', sum(1 for r in out if r[18] == 'OK'), 'FINDING', sum(1 for r in out if r[18] == 'FINDING'),
          'OPEN', sum(1 for r in out if r[18] not in ('OK', 'FINDING')))


if __name__ == '__main__':
    main()
