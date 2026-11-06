#!/usr/bin/env python3
"""rule_ab1w.py -- measured check of every definition of the function-row table A/AB1w.v (B/YB1w.v), the triage of
the value gate's flagged rows of that file, and the known-answer controls.

    rule_ab1w.py --file F.v --rel lib/A/AB1w.v --pin PIN --twin TWIN --kit KIT --donor-file D.v --donor-pin DPIN
                 --donor-twin DTWIN --rows RUN.gen.tsv --out-rows R.tsv --out-defs D.tsv --out-ctl C.tsv

Rules (all measured in the pin's headers / bytes and the twin's symbol table; donor facts in the donor's own image):
  ROW-FUNC      tfib_A_X = start of a FUNC symbol and tfib_E_X = its start + st_size; the row label X is a run of the
                symbol's name (the name check is reported; the extent decides)
  ROW-TRAMP     the row is one 4-byte instruction that is a jump (`j target` / `j .`); the target's symbol is reported
  SECTION       tfib_<sec>_lo / _hi = sh_addr / sh_addr + sh_size of the section of that name
  HULL          tfib_img_* / tfib_at_img_* = the page-rounded hull of the PT_LOADs
  ENTRY / GP    e_entry / the value of __global_pointer$
  DATA-SYM      tfib_D_X = the start of an OBJECT symbol whose name holds X (or the cell inside it the label names)
  GOT-WORD      tfib_D_GOT_X is an 8-byte .got word whose content (pin bytes) is the address of the symbol named X
  PHDR          tfib_at_ph_addr_z / _ent_z / _num_z = PT_PHDR p_vaddr / e_phentsize / e_phnum
  RW-PAGES      tfib_at_rw_lo / _len = the page-rounded writable PT_LOADs (start, length)
  NLOAD         tfib_at_n_res = the number of PT_LOAD headers
  INSN-IN       tfib_at_x_* / stops_more entries are instruction starts inside a FUNC symbol (name reported)
  SHADOW-OFF    tfib_at_shadow_off = the value the start-up states store at __asan_shadow_memory_dynamic_address
                (given with --so, measured by rule_states.py)
Donor rows the port dropped (gate: UNPAIRED-SOURCE) are settled in the donor image: the donor FUNC at the donor value
and whether our twin has a FUNC of that name (DONOR-ROW-DROPPED / DONOR-ROW-RENAMED).
"""
import argparse
import collections
import csv
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import imgfacts  # noqa: E402
import rule_states as rs  # noqa: E402

DEF = re.compile(r"Definition\s+(\w+)\s*:\s*(?:Z|nat)\s*:=\s*(0x[0-9a-fA-F]+|\d+)(?:%nat)?\s*\.")
LST = re.compile(r"Definition\s+(\w+)\s*:\s*list Z\s*:=\s*\(([^)]*)\)")
SECNAME = {'rodata': '.rodata', 'text': '.text', 'init_array': '.init_array', 'fini_array': '.fini_array',
           'preinit_array': '.preinit_array', 'data_rel_ro': '.data.rel.ro', 'got': '.got', 'data': '.data',
           'asan_globals': 'asan_globals', 'bss': '.bss', 'tbss': '.tbss'}


def defs_of(text):
    """[(name, value, line)] in file order, and {list name: [(value, line)]}."""
    out, lists = [], {}
    for i, line in enumerate(text.split('\n'), 1):
        for m in DEF.finditer(line):
            out.append((m.group(1), int(m.group(2), 0), i))
        for m in LST.finditer(line):
            lists[m.group(1)] = [(int(x, 0), i) for x in re.findall(r'0x[0-9a-fA-F]+|\d+', m.group(2))]
    return out, lists


def name_hit(label, sym):
    """A run of the label's tokens (>= 5 characters) that occurs in the symbol name."""
    toks = [t for t in label.split('_') if t]
    for n in range(len(toks), 0, -1):
        for i in range(len(toks) - n + 1):
            run = '_'.join(toks[i:i + n])
            if len(run) >= 5 and run.lower() in sym.lower():
                return run
    return None


class Tab:
    def __init__(self, img, so=None):
        self.img, self.so = img, so
        self.fstart = collections.defaultdict(list)
        for v, z, ty, n in img.syms:
            if ty == 'STT_FUNC' and z:
                self.fstart[v].append((v + z, n))
        self.fend = collections.defaultdict(list)
        for v, ends in self.fstart.items():
            for e, n in ends:
                self.fend[e].append((v, n))
        self.sec = {n: (lo, hi) for lo, hi, n, nb, fl in img.sections}

    def row(self, label, a, e):
        """(rule, ok, measurement) for the row [a, e) named label."""
        img = self.img
        cands = self.fstart.get(a, [])
        hit = [(end, n) for end, n in cands if end == e]
        if hit:
            names = [n for _, n in hit]
            nh = [n for n in names if name_hit(label, n)]
            return ('ROW-FUNC', True, f'[{a:#x}, {e:#x}) = FUNC {names[0]} (st_value {a:#x}, st_size {e - a:#x}); '
                                      f'label {label!r} ' + (f'matches {name_hit(label, nh[0])!r}' if nh else
                                                             'shares no 5-character run with the symbol name'))
        if e - a == 4 and img.is_insn(a):
            w = img.word(a, 4)
            if w is not None and (w & 0x7f) == 0x6f and ((w >> 7) & 31) == 0:
                imm = ((w >> 31) & 1) << 20 | ((w >> 12) & 0xff) << 12 | ((w >> 20) & 1) << 11 | \
                    ((w >> 21) & 0x3ff) << 1
                if imm & (1 << 20):
                    imm -= 1 << 21
                t = a + imm
                f = img.func_of(t)
                return ('ROW-TRAMP', True, f'[{a:#x}, {e:#x}) is one instruction `j {t:#x}`'
                        + (' (j .)' if t == a else f' to {f[2]}+{t - f[0]:#x}' if f else '')
                        + (f' inside {img.func_of(a)[2]}' if img.func_of(a) else ''))
        f = img.func_of(a)
        return ('ROW-FUNC', False, f'[{a:#x}, {e:#x}): no FUNC symbol starts at {a:#x} with that size'
                + (f'; {a:#x} is {f[2]}+{a - f[0]:#x} (size {f[1] - f[0]:#x})' if f else ''))

    def cover(self, a, e):
        """The FUNC symbols a row [a, e) covers, as (offset from a, sorted names) per start, and the names of the
        FUNC symbols that start exactly at e."""
        img = self.img
        starts = collections.defaultdict(set)
        for v, z, ty, n in img.syms:
            if ty == 'STT_FUNC' and a <= v <= e:
                starts[v].add(n)
        inside = tuple((v - a, tuple(sorted(starts[v]))) for v in sorted(starts) if v < e)
        return inside, tuple(sorted(starts.get(e, ())))

    def single(self, name, v, ctx):
        """(rule, ok, measurement) for one non-row definition, or None when no rule applies."""
        img = self.img
        m = re.match(r'tfib_(\w+?)_(lo|hi)$', name)
        if m and m.group(1) in SECNAME:
            lo, hi = self.sec[SECNAME[m.group(1)]]
            want = lo if m.group(2) == 'lo' else hi
            return ('SECTION', v == want, f'{SECNAME[m.group(1)]} sh_addr {lo:#x}, sh_addr + sh_size {hi:#x}: '
                                          f'{m.group(2)} {"=" if v == want else "!="} {v:#x}')
        if name in ('tfib_img_lo', 'tfib_at_img_lo', 'tfib_img_hi', 'tfib_at_img_hi'):
            want = img.hull[0] if name.endswith('lo') else img.hull[1]
            return ('HULL', v == want, f'page-rounded PT_LOAD hull [{img.hull[0]:#x}, {img.hull[1]:#x})')
        if name in ('tfib_entry', 'tfib_at_a_entry'):
            return ('ENTRY', v == img.entry, f'e_entry {img.entry:#x}')
        if name == 'tfib_gp':
            g = img.byname.get('__global_pointer$', [(None,)])[0][0]
            return ('GP', v == g, f'__global_pointer$ = {g:#x}' if g is not None else 'no __global_pointer$')
        if name == 'tfib_at_ph_addr_z':
            return ('PHDR', img.phdr is not None and v == img.phdr[0], f'PT_PHDR p_vaddr {img.phdr[0]:#x} '
                                                                       f'(= first PT_LOAD vaddr + e_phoff {img.phoff:#x})')
        if name == 'tfib_at_ph_ent_z':
            return ('PHDR', v == img.phentsize, f'e_phentsize {img.phentsize}')
        if name == 'tfib_at_ph_num_z':
            return ('PHDR', v == img.phnum, f'e_phnum {img.phnum}')
        if name == 'tfib_at_n_res':
            return ('NLOAD', v == len(img.loads), f'{len(img.loads)} PT_LOAD headers')
        if name in ('tfib_at_rw_lo', 'tfib_at_rw_len'):
            s, fs, m_, fl, off = max(x for x in img.loads if x[3] & 2)
            lo, hi = s & ~4095, (s + m_ + 4095) & ~4095
            want = lo if name.endswith('lo') else hi - lo
            return ('RW-PAGES', v == want, f'the last writable PT_LOAD (p_vaddr {s:#x}, p_memsz {m_:#x}) '
                                           f'page-rounded = [{lo:#x}, {hi:#x}): start {lo:#x}, length {hi - lo:#x}')
        if name == 'tfib_at_shadow_off':
            return ('SHADOW-OFF', self.so is not None and v == self.so,
                    f'the start-up states store {self.so:#x} at __asan_shadow_memory_dynamic_address'
                    if self.so is not None else 'no measured shadow offset')
        if name.startswith('tfib_D_GOT_'):
            target = name[len('tfib_D_GOT_'):]
            w = img.word(v, 8)
            sec = img.section_of(v)
            tn = None
            if w is not None:
                o = img.obj_of(w)
                tn = o[2] if o and o[0] == w else next((n for a_, z, ty, n in img.syms if a_ == w and z), None)
            ok = sec == '.got' and v % 8 == 0 and tn is not None and name_hit(target, tn) is not None
            return ('GOT-WORD', ok, f'{v:#x} in {sec}; its 8 pin bytes hold {w:#x} = {tn or "no sized symbol"}'
                    if w is not None else f'{v:#x} not file-backed')
        if name.startswith('tfib_D_'):
            label = name[len('tfib_D_'):]
            o = img.obj_of(v)
            exact = [n for a_, z, ty, n in img.syms if a_ == v and z and ty in ('STT_OBJECT', 'STT_FUNC')]
            nm = [n for n in exact if name_hit(label, n)]
            if nm:
                return ('DATA-SYM', True, f'{v:#x} = start of {nm[0]} ({img.section_of(v)})')
            if o and name_hit(label, o[2]):
                return ('DATA-SYM', True, f'{v:#x} = {o[2]}+{v - o[0]:#x} ({img.section_of(v)})')
            return ('DATA-SYM', False, f'{v:#x} = {o[2] + "+" + hex(v - o[0]) if o else "no symbol"} in '
                                       f'{img.section_of(v)}; label {label!r} not found in the name')
        if name.startswith('tfib_at_x_') or ctx == 'list':
            if v == 0:
                return ('ZERO', True, 'value 0: the entry is unused (no image address)')
            f = img.func_of(v)
            sec = img.section_of(v)
            if sec == '.text':
                ok = f is not None and img.is_insn(v)
                return ('INSN-IN', ok, f'{v:#x} = {f[2]}+{v - f[0]:#x}, an instruction start' if ok else
                        f'{v:#x} in .text but not an instruction start in a FUNC')
            return ('DATA-SYM', sec is not None, f'{v:#x} in {sec}')
        return None


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    for o in ('--file', '--rel', '--pin', '--twin', '--kit', '--donor-file', '--donor-pin', '--donor-twin', '--rows',
              '--out-rows', '--out-defs', '--out-ctl'):
        ap.add_argument(o, required=True)
    ap.add_argument('--so', type=lambda s: int(s, 0))
    a = ap.parse_args()
    img = imgfacts.Img(a.pin, a.twin, a.kit)
    dimg = imgfacts.Img(a.donor_pin, a.donor_twin, a.kit)
    assert img.same_link and dimg.same_link
    T, D = Tab(img, a.so), Tab(dimg)
    text = open(a.file).read()
    defs, lists = defs_of(text)
    ddefs, _ = defs_of(open(a.donor_file).read())
    byname = {n: (v, ln) for n, v, ln in defs}
    dby = {n: v for n, v, ln in ddefs}
    res = {}            # name -> (rule, ok, measurement, fn)

    def row_cover(lb, lo, hi):
        """ROW-DONOR-COVER: the row covers the same FUNC names at the same offsets, and ends where the same FUNC
        names start, as the donor's row of the same label does in the donor image."""
        da, de = dby.get(f'tfib_A_{lb}'), dby.get(f'tfib_E_{lb}')
        if da is None or de is None:
            return False, f'the donor has no row {lb}'
        ours, theirs = T.cover(lo, hi), D.cover(da, de)
        ok = ours == theirs and bool(ours[0])
        names = '; '.join(f'+{o:#x} {"/".join(ns)}' for o, ns in ours[0])
        return ok, (f'[{lo:#x}, {hi:#x}) covers the FUNC symbols {names} and ends where {"/".join(ours[1]) or "no FUNC"} '
                    f'starts; the donor row {lb} [{da:#x}, {de:#x}) covers {"the same" if ok else "DIFFERENT"} names '
                    f'at the same offsets in the donor image')

    def donor_same(n, v):
        """A non-row definition settled against the donor's definition of the same name, in the donor image."""
        d = dby.get(n)
        if d is None:
            return None
        if v == 0 and d == 0:
            return 'ZERO-SAME-DONOR', True, 'value 0 in ours and in the donor: the entry is unused'
        s, t = rs.sym_at(img, v), rs.sym_at(dimg, d)
        if s and s == t:
            return 'DONOR-SAME-SYM', True, f'{v:#x} = {rs.hx(s)}; the donor\'s {d:#x} = the same symbol + offset'
        so, to = rs.sec_off(img, v), rs.sec_off(dimg, d)
        if so and to and so[0] == to[0] == '.got':
            w, dw = img.word(v, 8), dimg.word(d, 8)
            ws, dws = rs.sym_at(img, w), rs.sym_at(dimg, dw)
            ok = ws is not None and ws == dws
            return 'DONOR-SAME-GOTWORD', ok, (f'.got word {v:#x} holds {w:#x} = {rs.hx(ws)}; the donor\'s .got word '
                                              f'{d:#x} holds {dw:#x} = {rs.hx(dws)}')
        cs, cd = rs.cstr(img, v), rs.cstr(dimg, d)
        if so and to and so[0] == to[0] and cs and cs == cd:
            return 'DONOR-SAME-STRING', True, f'{v:#x} and the donor\'s {d:#x} hold the same NUL-terminated bytes ' \
                                              f'{cs[:40]!r} in {so[0]}'
        if so and so == to:
            return 'DONOR-SAME-SECOFF', True, f'{v:#x} = {so[0]}+{so[1]:#x}; the donor\'s {d:#x} = the same section + ' \
                                              f'offset'
        return None

    for n, v, ln in defs:
        m = re.match(r'tfib_([AE])_(\w+)$', n)
        if m:
            other = f'tfib_{"E" if m.group(1) == "A" else "A"}_{m.group(2)}'
            if other not in byname:
                res[n] = ('ROW-FUNC', False, f'no partner {other}', None)
                continue
            lo, hi = (v, byname[other][0]) if m.group(1) == 'A' else (byname[other][0], v)
            lb = m.group(2)
            r = T.row(lb, lo, hi)
            if r[1]:
                fn = (lambda w, hi=hi, lb=lb: T.row(lb, w, hi)[1]) if m.group(1) == 'A' else \
                    (lambda w, lo=lo, lb=lb: T.row(lb, lo, w)[1])
                res[n] = r + (fn,)
            else:
                ok, meas = row_cover(lb, lo, hi)
                fn = (lambda w, hi=hi, lb=lb: row_cover(lb, w, hi)[0]) if m.group(1) == 'A' else \
                    (lambda w, lo=lo, lb=lb: row_cover(lb, lo, w)[0])
                res[n] = ('ROW-DONOR-COVER', ok, meas, fn)
            continue
        r = T.single(n, v, 'def')
        if r and r[1]:
            res[n] = r + ((lambda w, n=n: T.single(n, w, 'def')[1]),)
            continue
        q = donor_same(n, v)
        if q:
            res[n] = q + ((lambda w, n=n: (donor_same(n, w) or (0, False))[1]),)
        else:
            res[n] = (r + (None,)) if r else ('NO-RULE', False, 'no rule', None)
    for ln_name, items in lists.items():
        for k, (v, ln) in enumerate(items):
            r = T.single(ln_name, v, 'list')
            res[f'{ln_name}[{k}]'] = r + ((lambda w, n=ln_name: T.single(n, w, 'list')[1]),)
    with open(a.out_defs, 'w') as fh:
        fh.write('file\tline\tname\tvalue\trule\tok\tmeasurement\n')
        for n, v, ln in defs:
            r = res[n]
            fh.write(f'{a.rel}\t{ln}\t{n}\t{v:#x}\t{r[0]}\t{"OK" if r[1] else "FAIL"}\t{r[2]}\n')
        for ln_name, items in lists.items():
            for k, (v, ln) in enumerate(items):
                r = res[f'{ln_name}[{k}]']
                fh.write(f'{a.rel}\t{ln}\t{ln_name}[{k}]\t{v:#x}\t{r[0]}\t{"OK" if r[1] else "FAIL"}\t{r[2]}\n')
    print(a.rel, img.describe(), 'definitions', len(defs), collections.Counter((r[0], r[1]) for r in res.values()))

    # ---- flagged rows ------------------------------------------------------------------------------------------
    base = os.path.basename(a.rel)
    rows = [r for r in csv.reader(open(a.rows), delimiter='\t') if r and r[5] == base]
    rowsym = {}                       # our FUNC start -> our row label
    for n, v, ln in defs:
        if n.startswith('tfib_A_'):
            rowsym[v] = n
    out, ctl = [], []
    for r in rows:
        sent = r[7].split()[-1] if r[7] else ''
        if r[11]:
            name = sent
            if name not in res:
                out.append(r + ['OPEN', f'definition {name} not found in {a.rel}', 'OPEN', '-', '-', '-'])
                continue
            rule, ok, meas, fn = res[name]
            v = int(r[11], 16)
            if byname[name][0] != v:
                out.append(r + ['OPEN', f'{name} holds {byname[name][0]:#x}, the row says {v:#x}', 'OPEN', '-', '-',
                                '-'])
                continue
            note = ''
            if name in ('tfib_rodata_hi', 'tfib_text_hi'):
                dv = int(r[10], 16)
                sec = SECNAME[name.split('_')[1]]
                dlo, dhi = D.sec[sec]
                note = (f'. Donor value {dv:#x} vs the donor image {sec} end {dhi:#x}'
                        f'{" (donor .tbss starts at " + hex(D.sec[".tbss"][0]) + ")" if name == "tfib_text_hi" else ""}'
                        f'; no statement or definition of lib/ other than its own definition names {name} '
                        f'(by-use grep), so no proof reads it')
            out.append(r + [rule, (meas + note)[:1200], 'OK' if ok else 'OPEN', '-', '-', '-'])
            for kind, w in (('plus4', v + 4), ('donor', int(r[10], 16) if r[10] else None)):
                if w is None:
                    ctl.append((a.rel, r[6], r[11], rule, kind, 'n/a'))
                elif kind == 'donor' and w == v:
                    ctl.append((a.rel, r[6], r[11], rule, kind, 'same-value'))
                else:
                    ctl.append((a.rel, r[6], r[11], rule, kind, 'descriptive' if fn is None else
                                'refused' if not fn(w) else 'accepted'))
            continue
        # a donor row with no ported value: settle it in the donor image
        dv = int(r[10], 16)
        m = re.match(r'tfib_([AE])_(\w+)$', sent)
        dl = [x for x in ddefs if x[0] == sent]
        if r[9] == 'ident':
            f = dimg.func_of(dv)
            meas = (f'the name {sent} carries the donor address {dv:#x} = {f[2]}+{dv - f[0]:#x} in the donor image; '
                    f'{a.rel} has no definition {sent}') if f else f'donor name-embedded {dv:#x}'
            ours = [n for n in (f[2],) if f and img.byname.get(n)]
            out.append(r + ['DONOR-ROW-DROPPED', meas + (f'; our twin has {f[2]}' if ours else
                                                         f'; our twin has no FUNC {f[2]}' if f else ''), 'OK',
                            '-', '-', '-'])
            continue
        if not m:
            out.append(r + ['OPEN', f'donor definition {sent} {dv:#x} not in {a.rel}', 'OPEN', '-', '-', '-'])
            continue
        if m.group(1) == 'A':
            fs = [(dv, e, n) for e, n in D.fstart.get(dv, [])]
        else:
            fs = [(s, dv, n) for s, n in D.fend.get(dv, [])]
        if not fs:
            out.append(r + ['OPEN', f'donor {sent} {dv:#x}: no donor FUNC {"starts" if m.group(1) == "A" else "ends"} '
                                    f'there', 'OPEN', '-', '-', '-'])
            continue
        lo, hi, dn = fs[0]
        ours = [(v, z) for v, z, ty in img.byname.get(dn, []) if ty == 'STT_FUNC' and z]
        if not ours:
            out.append(r + ['DONOR-ROW-DROPPED', f'donor {sent} = {dv:#x} {"starts" if m.group(1) == "A" else "ends"} '
                            f'FUNC {dn} [{lo:#x}, {hi:#x}) of the donor image; our twin has no FUNC named {dn}, so the '
                            f'table has no row for it', 'OK', '-', '-', '-'])
            continue
        ov, oz = ours[0]
        holder = rowsym.get(ov)
        if holder:
            hr = res[holder]
            out.append(r + ['DONOR-ROW-RENAMED', f'donor {sent} = {dv:#x} {"starts" if m.group(1) == "A" else "ends"} '
                            f'FUNC {dn} of the donor image (the donor label names another function); our FUNC {dn} '
                            f'[{ov:#x}, {ov + oz:#x}) is our row {holder} / {holder.replace("tfib_A_", "tfib_E_")}: '
                            f'{hr[2]}', 'OK' if hr[1] else 'OPEN', '-', '-', '-'])
        else:
            out.append(r + ['OPEN', f'donor {sent} = FUNC {dn}; our twin has {dn} at {ov:#x} but no row starts there',
                            'OPEN', '-', '-', '-'])
    with open(a.out_rows, 'w') as fh:
        for r in out:
            fh.write('\t'.join(r) + '\n')
    with open(a.out_ctl, 'w') as fh:
        for r in ctl:
            fh.write('\t'.join(r) + '\n')
    print('rows', collections.Counter((r[16], r[18]) for r in out).most_common())
    print('controls', sorted(collections.Counter((r[3], r[4], r[5]) for r in ctl).items()))


if __name__ == '__main__':
    main()
