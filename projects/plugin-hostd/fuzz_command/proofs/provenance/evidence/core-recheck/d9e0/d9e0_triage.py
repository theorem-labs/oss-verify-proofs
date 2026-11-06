#!/usr/bin/env python3
"""Class, reason and measurement for every row of d9e0_diff.py's rows.raw.tsv.

Classes (the slice's task): provenance-only, patched, refused, VALUE, slot (a file d9e0 stages as donor text by design,
to be regenerated from our image); plus not-in-tree (the file is not in the unit) and other (our file holds a third
value with no hand-note row, or the line is gone from our file).

Every row whose class is not provenance-only / not-in-tree is judged: is OUR value right for our image? The donor value
(the d9e0 stage file = donor text with the module-path and name renames, at the same place) is resolved in the donor's
unstripped twin and our value in ours; a rule settles the row only when both sides resolve to the same thing:
  SAME-SYMBOL    same symbol name and same offset (symtab of both twins; code rows also compare the 4-byte word)
  SECTION-EDGE   same section start or end (section headers of both twins)
  SEGMENT        same PT_LOAD quantity (base, end, file end, sizes, page-rounded base/end/size) of both pins
  IMAGE-TOP      image top (page-rounded end of the last PT_LOAD), top/8, top/4096, its shadow
  GOT-WORD       a .got cell whose 8-byte content resolves to the same symbol+offset in both pins
  SHADOW-OF      (v - 0x7fff8000) * 8 is settled by one of the rules above on both sides
  QUOTIENT       v*4 or v*8 is settled by one of the rules above on both sides
  MANUAL         a row of the hand-measured table (--manual), whose measurement column says what was measured
The known-answer controls re-judge every rule-settled row with our value + 4 and with our value := the donor value and
count how many the rules still accept (--controls).
"""
import argparse, bisect, csv, os, re, sys
from elftools.elf.elffile import ELFFile

SHADOW_OFF = 0x7fff8000


def as_int(tok):
    if tok is None or tok in ('-', '') or tok.startswith('port_core_refused_') or '|' in tok:
        return None
    try:
        return int(tok, 16) if tok.lower().startswith('0x') else int(tok)
    except ValueError:
        return None


def h(v):
    return '-' if v is None else hex(v)


class Img:
    def __init__(self, role, pin, twin):
        self.role = role
        self.fh = open(pin, 'rb')
        e = ELFFile(self.fh)
        self.segs = [(p['p_vaddr'], p['p_memsz'], p['p_offset'], p['p_filesz'], p['p_flags'])
                     for p in e.iter_segments() if p['p_type'] == 'PT_LOAD']
        t = ELFFile(open(twin, 'rb'))
        self.secs = [(s.name, s['sh_addr'], s['sh_size']) for s in t.iter_sections() if s['sh_addr']]
        syms = []
        for y in t.get_section_by_name('.symtab').iter_symbols():
            if (y['st_value'] and y['st_size'] and y.name and not y.name.startswith(('$', '.L'))
                    and y['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT', 'STT_NOTYPE')):
                syms.append((y['st_value'], y['st_size'], y.name, y['st_info']['type']))
        syms.sort()
        # symbols up to 64 KiB are found by a bounded walk back from the bisect point; the few larger ones by a scan
        self.syms = [s for s in syms if s[1] <= 0x10000]
        self.big = [s for s in syms if s[1] > 0x10000]
        self.starts = [s[0] for s in self.syms]
        self.maxsize = 0x10000
        self.got = next(((a, a + n) for nm, a, n in self.secs if nm == '.got'), (0, 0))
        keys = {}

        def add(k, v):
            keys.setdefault(v, set()).add(k)
        for nm, a, n in self.secs:
            add(f'section {nm} start', a)
            add(f'section {nm} end', a + n)
        top = 0
        for i, (va, ms, off, fs, fl) in enumerate(self.segs):
            lo, hi = va & ~0xfff, (va + ms + 0xfff) & ~0xfff
            for k, v in ((f'PT_LOAD{i} base', va), (f'PT_LOAD{i} end', va + ms), (f'PT_LOAD{i} file end', va + fs),
                         (f'PT_LOAD{i} memsz', ms), (f'PT_LOAD{i} filesz', fs), (f'PT_LOAD{i} page base', lo),
                         (f'PT_LOAD{i} page end', hi), (f'PT_LOAD{i} page size', hi - lo)):
                add(k, v)
            top = max(top, hi)
        self.top = top
        base = min(va for va, *_ in self.segs) & ~0xfff
        size = top - base
        for k, v in (('image top', top), ('image top / 8', top // 8), ('image top / 4096', top // 4096),
                     ('shadow of image top', SHADOW_OFF + top // 8), ('image size (top - base)', size),
                     ('image size / 8', size // 8), ('image size / 4096', size // 4096)):
            add(k, v)
        self.keys = keys
        self.rodata = next(((a, a + n) for nm, a, n in self.secs if nm == '.rodata'), (0, 0))

    def sym_offs(self, a):
        """{(name, offset)} of sized symbols with start <= a <= end (offset == size marks the symbol's end)."""
        out = set()
        i = bisect.bisect_right(self.starts, a) - 1
        while i >= 0 and self.starts[i] >= a - self.maxsize:
            v, sz, nm, ty = self.syms[i]
            if v <= a <= v + sz:
                out.add((nm, a - v, ty))
            i -= 1
        for v, sz, nm, ty in self.big:
            if v <= a <= v + sz:
                out.add((nm, a - v, ty))
        return out

    def read(self, a, n):
        for va, ms, off, fs, fl in self.segs:
            if va <= a and a + n <= va + fs:
                self.fh.seek(off + a - va)
                return self.fh.read(n)
            if va <= a < va + ms:
                return bytes(n)
        return None

    def word(self, a, n):
        b = self.read(a, n)
        return None if b is None else int.from_bytes(b, 'little')


def rule_symbol(d, u, O, N):
    so = {(nm, off) for nm, off, ty in O.sym_offs(d)}
    su = {(nm, off) for nm, off, ty in N.sym_offs(u)}
    both = so & su
    if not both:
        return None
    nm, off = sorted(both, key=lambda x: (x[1] == 0, len(x[0])))[0]
    ty = next((t for n_, o_, t in O.sym_offs(d) if n_ == nm), '')
    m = f'{nm}+{off:#x} in both twins (donor {d:#x}, ours {u:#x})'
    if ty == 'STT_FUNC':
        wd, wu = O.word(d, 4), N.word(u, 4)
        if wd is not None and wu is not None:
            if wd != wu:
                # same 32-bit instruction with a different pc-relative immediate (jal / auipc: opcode and rd equal;
                # branch: opcode, funct3, rs1, rs2 equal) is the same code at a different distance
                same = False
                if wd & 3 == 3 and wu & 3 == 3 and wd & 0x7f == wu & 0x7f:
                    op = wd & 0x7f
                    if op in (0x6f, 0x17):
                        same = (wd & 0xfff) == (wu & 0xfff)
                    elif op == 0x63:
                        same = (wd & 0x01fff07f) == (wu & 0x01fff07f)
                if same:
                    return 'SAME-SYMBOL', m + (f'; 4-byte words {wd:#010x} / {wu:#010x}: same pc-relative '
                                               f'instruction (opcode {wd & 0x7f:#x}), immediate differs')
                return 'SAME-SYMBOL-INSN-DIFFERS', m + f'; 4-byte words differ ({wd:#010x} vs {wu:#010x})'
            m += f'; 4-byte word {wd:#010x} in both'
    return 'SAME-SYMBOL', m


def rule_keys(d, u, O, N):
    both = O.keys.get(d, set()) & N.keys.get(u, set())
    if not both:
        return None
    k = sorted(both)[0]
    tag = 'IMAGE-TOP' if k.startswith(('image', 'shadow of image')) else (
        'SECTION-EDGE' if k.startswith('section') else 'SEGMENT')
    return tag, f'{k} in both images (donor {d:#x}, ours {u:#x})'


def rule_got(d, u, O, N):
    if not (O.got[0] <= d < O.got[1] and N.got[0] <= u < N.got[1]):
        return None
    cd, cu = O.word(d, 8), N.word(u, 8)
    if cd is None or cu is None:
        return None
    r = rule_symbol(cd, cu, O, N)
    if r and r[0] == 'SAME-SYMBOL':
        return 'GOT-WORD', f'.got cell donor {d:#x} holds {cd:#x}, ours {u:#x} holds {cu:#x}: ' + r[1]
    return None


def rule_string(d, u, O, N):
    """Both values start a NUL-terminated .rodata string (the byte before is NUL) and the strings are equal."""
    if not (O.rodata[0] < d < O.rodata[1] and N.rodata[0] < u < N.rodata[1]):
        return None
    bd, bu = O.read(d - 1, 65), N.read(u - 1, 65)
    if bd is None or bu is None or bd[0] != 0 or bu[0] != 0:
        return None
    sd, su = bd[1:].split(b'\0')[0], bu[1:].split(b'\0')[0]
    if len(sd) < 4 or sd != su or not all(32 <= c < 127 for c in sd):
        return None
    return 'SAME-STRING', f'both start the .rodata string {sd[:40]!r} (donor {d:#x}, ours {u:#x}; byte before is NUL)'


def judge_base(d, u, O, N):
    for f in (rule_keys, rule_got, rule_symbol, rule_string):
        r = f(d, u, O, N)
        if r and r[0] != 'SAME-SYMBOL-INSN-DIFFERS':
            return r
    return rule_symbol(d, u, O, N)


def judge(d, u, O, N):
    if d is None or u is None:
        return None
    r = judge_base(d, u, O, N)
    if r and r[0] != 'SAME-SYMBOL-INSN-DIFFERS':
        return r
    insn = r
    lo, hi = SHADOW_OFF, SHADOW_OFF + max(O.top, N.top) // 8 + 0x1000
    if lo <= d < hi and lo <= u < hi:
        s = judge_base((d - SHADOW_OFF) * 8, (u - SHADOW_OFF) * 8, O, N)
        if s and s[0] != 'SAME-SYMBOL-INSN-DIFFERS':
            return 'SHADOW-OF', f'shadow of: {s[1]}'
    if d >= 0x1000 and u >= 0x1000:
        # a quotient is settled only by a symbol (a geometry key times 4 or 8 is too easy to hit by chance:
        # 8192 * 8 = 0x10000 = PT_LOAD0 base)
        for k in (4, 8):
            s = rule_symbol(d * k, u * k, O, N)
            if s and s[0] == 'SAME-SYMBOL':
                return 'QUOTIENT', f'value * {k}: {s[1]}'
    return insn


def parse_hand(paths):
    """{file: [(old ints, new ints, source)]} from the lanes' hand-resolve tables."""
    out = {}
    numre = re.compile(r'(?<![A-Za-z0-9_])(0x[0-9a-fA-F]+|\d{2,})(?![A-Za-z0-9_])')
    for p in paths:
        src = os.path.basename(p)
        with open(p, encoding='utf-8') as fh:
            for line in fh:
                if p.endswith('.tsv'):
                    c = line.rstrip('\n').split('\t')
                    if len(c) < 4 or c[0] == 'file':
                        continue
                    files, oc, nc = [c[0]], c[2], c[3]
                else:
                    if not line.startswith('|'):
                        continue
                    c = [x.strip() for x in line.strip().strip('|').split('|')]
                    if len(c) < 4:
                        continue
                    if c[0].isdigit():
                        c = c[1:]
                    files = re.findall(r'A/[A-Za-z0-9_]+\.v', c[0])
                    oc, nc = c[1], c[2]
                ov = {as_int(x) for x in numre.findall(oc)}
                nv = {as_int(x) for x in numre.findall(nc)}
                for f in files:
                    out.setdefault(f, []).append((ov, nv, src))
    return out


def load_gate(paths, want):
    """{(dst_file, dst_line, dst_value): (verdict, src_value, src_res, dst_res)} for dst files in `want`."""
    g = {}
    for p in paths:
        with open(p, encoding='utf-8', errors='replace') as fh:
            for line in fh:
                if line.startswith('#'):
                    continue
                c = line.rstrip('\n').split('\t')
                if len(c) < 15 or c[5] not in want:
                    continue
                try:
                    k = (c[5], int(c[6]), int(c[11], 16))
                except ValueError:
                    continue
                g.setdefault(k, (c[0], c[10], c[13], c[14]))
    return g


def load_d9e0_reasons(work):
    """{(file, donor value, d9e0 value): status} from d9e0's own check/fixed/review/decimals tables."""
    out = {}
    for fn in ('check.tsv', 'review.tsv', 'fixed.tsv'):
        p = os.path.join(work, fn)
        if not os.path.exists(p):
            continue
        with open(p) as fh:
            hdr = fh.readline().rstrip('\n').split('\t')
            for line in fh:
                c = dict(zip(hdr, line.rstrip('\n').split('\t')))
                o, n = as_int(c.get('old', '')), as_int(c.get('new', ''))
                st = c.get('status') or ('fixed ' + c.get('new_sym', '')) if fn == 'fixed.tsv' else c.get('status', '')
                if o is not None:
                    out.setdefault((c['file'], o, n), f'{fn[:-4]}: {st}'[:160])
    p = os.path.join(work, 'decimals.tsv')
    if os.path.exists(p):
        with open(p) as fh:
            hdr = fh.readline().rstrip('\n').split('\t')
            for line in fh:
                c = dict(zip(hdr, line.rstrip('\n').split('\t')))
                o, n = as_int(c.get('old', '')), as_int(c.get('new', ''))
                if o is not None:
                    out.setdefault((c['file'], o, n), f"decimals: {c.get('action', '')} {c.get('why', '')}"[:160])
    return out


def read_lines(p):
    with open(p, encoding='utf-8') as fh:
        return fh.read().split('\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--rows', required=True)
    ap.add_argument('--stage', action='append', required=True, help='SET=d9e0 stage dir (donor text, renamed)')
    ap.add_argument('--work', action='append', default=[], help="SET=d9e0 work dir (its check/fixed/review tables)")
    ap.add_argument('--ours', required=True)
    ap.add_argument('--old-img', required=True)
    ap.add_argument('--old-syms', required=True)
    ap.add_argument('--new-img', required=True)
    ap.add_argument('--new-syms', required=True)
    ap.add_argument('--hand', action='append', default=[])
    ap.add_argument('--gate', action='append', default=[])
    ap.add_argument('--manual', default=None)
    ap.add_argument('--slots', required=True, help='comma list: files d9e0 handled as generated slots')
    ap.add_argument('--generated', required=True, help="comma list: files the unit's generators write")
    ap.add_argument('--out', required=True)
    ap.add_argument('--controls', required=True)
    a = ap.parse_args()

    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import d9e0_diff as dd

    O = Img('donor', a.old_img, a.old_syms)
    N = Img('ours', a.new_img, a.new_syms)
    stage = dict(x.split('=', 1) for x in a.stage)
    work = dict(x.split('=', 1) for x in a.work)
    slots = set(a.slots.split(','))
    generated = set(a.generated.split(','))
    hand = parse_hand(a.hand)
    manual = {}
    if a.manual:
        with open(a.manual) as fh:
            hdr = fh.readline().rstrip('\n').split('\t')
            for line in fh:
                if not line.strip() or line.startswith('#'):
                    continue
                c = dict(zip(hdr, line.rstrip('\n').split('\t')))
                manual[(c['set'], c['file'], c['stage_line'], c['pos'])] = c

    with open(a.rows) as fh:
        rd = csv.reader(fh, delimiter='\t', quoting=csv.QUOTE_NONE)
        hdr = next(rd)
        rows = [dict(zip(hdr, r)) for r in rd]
    want = {os.path.basename(r['file']) for r in rows}
    gate = load_gate(a.gate, want)
    reasons = {s: load_d9e0_reasons(w) for s, w in work.items()}

    # donor value per token row: the token at the same place in the d9e0 stage file
    cache = {}

    def donor_tok(r):
        key = (r['set'], r['file'])
        if key not in cache:
            so = read_lines(os.path.join(os.path.dirname(stage[r['set']]), 'stage-out', r['file'][4:]))
            st = read_lines(os.path.join(stage[r['set']], r['file'][4:]))
            cache[key] = (so, st, dd.align(so, st))
        so, st, m = cache[key]
        j = int(r['d9e0_line']) - 1
        if j not in m:
            return None
        sl = st[m[j][0]]
        a_, b_ = dd.tokens(so[j]), dd.tokens(sl)
        if dd.norm(so[j]) != dd.norm(sl) or len(a_) != len(b_):
            return None
        return b_[int(r['pos'])][0]

    out = []
    ctl = {'rows': 0, 'plus4_accepted': 0, 'donor_accepted': 0, 'donor_skipped_equal': 0}
    ctl_by_rule = {}
    numerals = {}
    for r in rows:
        f, base = r['file'], os.path.basename(r['file'])[:-2]
        o = {'set': r['set'], 'file': f, 'line': r['our_line'], 'stage_line': r['old_line'],
             'd9e0_line': r['d9e0_line'], 'pos': r['pos'], 'old_val': r['old_val'], 'd9e0_val': r['d9e0_val'],
             'our_val': r['our_val'], 'donor_val': '-', 'class': '', 'reason': '', 'measurement': '',
             'code_or_comment': r['where'], 'read_by': '-', 'result': '', 'finding_kind': '-', 'new_value': '-'}
        ours_present = os.path.exists(os.path.join(a.ours, f[4:]))
        if r['kind'] != 'token':
            ov, nv, uv = r['old_val'], r['d9e0_val'], r['our_val']
            if 'Modified by Theorem Labs, 2026-10: copied from' in ov:
                o.update({'class': 'provenance-only', 'reason': 'HEADER', 'result': 'OK',
                          'measurement': "d9e0's provenance header adds the donor image sha256 7093581aab04 and "
                                         "names the renames of its own command line; comment text only",
                          'old_val': '<header>', 'd9e0_val': '<header>', 'our_val': '<header>'})
            elif re.sub(r'\bCmd(B)?Syms\b', 'S', ov) == re.sub(r'\bCmd(B)?Syms\b', 'S', nv) or \
                    re.sub(r'\b(TfibB|CmdB)_pair\b', 'P', ov) == re.sub(r'\b(TfibB|CmdB)_pair\b', 'P', nv):
                o.update({'class': 'provenance-only', 'reason': 'RENAME', 'result': 'OK',
                          'measurement': f'identifier rename only (the run command lines name different renames); '
                                         f'our line: {uv[:120]}'})
            else:
                o.update({'class': 'text', 'reason': 'STRUCTURE', 'result': 'OPEN',
                          'measurement': f'old: {ov[:150]} | d9e0: {nv[:150]} | ours: {uv[:150]}'})
            mk = (r['set'], f, r['old_line'], r['pos'])
            if mk in manual:
                c = manual[mk]
                o.update({k: c[k] for k in ('class', 'reason', 'measurement', 'result', 'finding_kind', 'new_value',
                                            'read_by') if c.get(k)})
            out.append(o)
            continue

        d_tok = donor_tok(r)
        o['donor_val'] = d_tok or '-'
        d, old, n9, u = as_int(d_tok), as_int(r['old_val']), as_int(r['d9e0_val']), as_int(r['our_val'])
        cand_note = ''
        if '|' in r['our_val']:
            # several tokens of our line share the place's numeral-blind context: take the one equal to the old run's
            # value if a rule settles it, else the first one a rule settles
            cands = [as_int(x) for x in r['our_val'].split('|')]
            order = sorted((c for c in cands if c is not None), key=lambda c: c != old)
            for c in order:
                rc = judge(d, c, O, N)
                if rc and rc[0] != 'SAME-SYMBOL-INSN-DIFFERS':
                    u = c
                    cand_note = f'our token at this place is one of {len(cands)} with the same context; took {c:#x}; '
                    break
        refused = r['d9e0_val'].startswith('port_core_refused_')
        if not ours_present:
            o.update({'class': 'not-in-tree', 'reason': 'FILE-DROPPED', 'result': 'OK',
                      'measurement': f'{f} is not in the unit (no file of that name under lib/)'})
            out.append(o)
            continue
        if base in slots:
            o['class'], o['reason'] = 'slot', 'GEN-SLOT'
            pre = (f"d9e0 stages this generated start-up slot as donor text by design (d9e0 value = donor {d_tok}); ")
        elif refused:
            o['class'], o['reason'] = 'refused', 'REFUSED-MARKER'
            pre = f"d9e0 wrote {r['d9e0_val']} (donor {d_tok}); "
        elif u is not None and u == n9 or r['our_val'] == r['d9e0_val']:
            o['class'], o['reason'] = 'patched', 'OURS-EQ-D9E0'
            pre = 'our file holds the d9e0 value; '
        elif u is not None and u == old:
            o['class'], o['reason'] = 'VALUE', 'OURS-EQ-OLD'
            pre = f"our file holds the old run's value, d9e0 wrote {r['d9e0_val']}; "
        else:
            hits = [src for ov_, nv_, src in hand.get(f[4:], []) if u is not None and u in nv_ and
                    (old in ov_ or d in ov_)]
            if hits:
                o['class'], o['reason'] = 'patched', 'HAND-NOTE'
                pre = f"hand row in {hits[0]} ({h(old)} -> {h(u)}); "
            else:
                o['class'], o['reason'] = 'other', ('LINE-GONE' if r['our_val'] == '-' else
                                                    'AMBIGUOUS' if '|' in r['our_val'] else 'OURS-THIRD')
                pre = ''
        pre += cand_note
        if base in generated:
            pre += "the unit's generator writes this file from our image; "
        rs = reasons.get(r['set'], {})
        why9 = rs.get((f[4:], d, n9)) if d is not None else None
        if why9:
            pre += f'd9e0 table row: {why9}; '
        res = judge(d, u, O, N)
        g = gate.get((f[4:], int(r['our_line']) if r['our_line'].isdigit() else -1, u)) if u is not None else None
        gtxt = f' gate RA row: {g[0]} ({g[2]} -> {g[3]})' if g else ''
        if res and res[0] != 'SAME-SYMBOL-INSN-DIFFERS':
            o['reason'] += '/' + res[0]
            o['measurement'] = pre + res[1] + ';' + gtxt
            o['result'] = 'OK'
            ctl['rows'] += 1
            cr = ctl_by_rule.setdefault(res[0], [0, 0, 0, 0])
            cr[0] += 1
            p4 = judge(d, u + 4, O, N)
            if p4 and p4[0] != 'SAME-SYMBOL-INSN-DIFFERS':
                ctl['plus4_accepted'] += 1
                cr[1] += 1
            if u == d:
                ctl['donor_skipped_equal'] += 1
                cr[3] += 1
            else:
                pd = judge(d, d, O, N)
                if pd and pd[0] != 'SAME-SYMBOL-INSN-DIFFERS':
                    ctl['donor_accepted'] += 1
                    cr[2] += 1
        else:
            o['measurement'] = pre + (res[1] + ';' if res else f'no rule settles donor {d_tok} -> ours '
                                      f"{r['our_val'][:120]};") + gtxt
            if o['class'] == 'patched':
                o['result'] = 'OK'
            elif d is not None and d >= 0x10000 and (base in generated or r['our_val'] == '-'):
                # a generated file, or a line our file no longer has: settled when the donor value occurs nowhere in
                # our file (no donor carry); the generated values themselves are measured by the generated-file checks
                if f not in numerals:
                    numerals[f] = {as_int(t) for line in read_lines(os.path.join(a.ours, f[4:]))
                                   for t, _ in dd.tokens(line)}
                if d not in numerals[f]:
                    o['reason'] += '/GEN-NO-CARRY' if base in generated else '/NO-CARRY'
                    o['measurement'] += (f' the donor value {d:#x} occurs nowhere in our file (scan of every numeral)'
                                         + ("; our file's own values are measured by the generated-file checks"
                                            if base in generated else '; the line has no counterpart in our file'))
                    o['result'] = 'OK'
                else:
                    o['result'] = 'OPEN'
            else:
                o['result'] = 'OPEN'
        mk = (r['set'], f, r['old_line'], r['pos'])
        if mk in manual:
            c = manual[mk]
            o.update({k: c[k] for k in ('class', 'reason', 'measurement', 'result', 'finding_kind', 'new_value',
                                        'read_by') if c.get(k)})
            if c.get('measurement_append'):
                o['measurement'] += ' ' + c['measurement_append']
        out.append(o)

    cols = ['set', 'file', 'line', 'stage_line', 'd9e0_line', 'pos', 'old_val', 'd9e0_val', 'our_val', 'donor_val',
            'class', 'reason', 'measurement', 'code_or_comment', 'read_by', 'result', 'finding_kind', 'new_value']
    with open(a.out, 'w') as fh:
        fh.write('\t'.join(cols) + '\n')
        for o in out:
            fh.write('\t'.join(str(o[c]).replace('\t', ' ').replace('\n', ' ') for c in cols) + '\n')
    with open(a.controls, 'w') as fh:
        fh.write('rule\trows_settled\tplus4_still_accepted\tdonor_value_still_accepted\tdonor_equal_skipped\n')
        for k, v in sorted(ctl_by_rule.items()):
            fh.write('\t'.join([k] + [str(x) for x in v]) + '\n')
        fh.write('\t'.join(['ALL', str(ctl['rows']), str(ctl['plus4_accepted']), str(ctl['donor_accepted']),
                            str(ctl['donor_skipped_equal'])]) + '\n')
    from collections import Counter
    c = Counter((o['set'], o['class'], o['result']) for o in out)
    for k, v in sorted(c.items()):
        print('\t'.join(k), v, file=sys.stderr)


if __name__ == '__main__':
    main()
