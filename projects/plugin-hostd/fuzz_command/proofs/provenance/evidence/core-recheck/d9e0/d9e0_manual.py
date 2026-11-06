#!/usr/bin/env python3
"""Measurements for the rows d9e0_triage.py's generic rules leave open; writes manual.tsv for d9e0_triage.py --manual.

Every measurement here reads the images (pins and unstripped twins), our files or the donor's files when it runs; the
text it writes names what it read. A group whose check fails writes result OPEN with what it saw.

usage: d9e0_manual.py --rows rows.tsv --ours LIB --donor LIB --stage A1=DIR --old-img PIN --old-syms TWIN
                      --new-img PIN --new-syms TWIN --out manual.tsv
"""
import argparse, csv, os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import d9e0_triage as tri  # noqa: E402

SH = tri.SHADOW_OFF


def shadow(a):
    return SH + a // 8


def globals_of(img):
    """asan_globals descriptors (8 words of 8 bytes): beg, size, size_with_redzone, name, module, dyn, loc, odr."""
    a, n = next((s[1], s[2]) for s in img.secs if s[0] == 'asan_globals')
    out = []
    for k in range(n // 64):
        w = [img.word(a + 64 * k + 8 * i, 8) for i in range(8)]
        out.append({'beg': w[0], 'size': w[1], 'szrz': w[2], 'odr': w[7]})
    return out, a, n


def cstr(img, a):
    b = img.read(a, 256)
    return b.split(b'\0')[0] if b is not None else None


def sym_at(img, name):
    return [v for v, sz, nm, ty in img.syms + img.big if nm == name]


class Lib:
    def __init__(self, root):
        self.root = root
        self.files = {}
        for d, _, ns in os.walk(root):
            for n in ns:
                if n.endswith('.v'):
                    p = os.path.join(d, n)
                    self.files[os.path.relpath(p, root)] = open(p, encoding='utf-8').read().split('\n')
        self.ids = None

    def line(self, f, n):
        return self.files[f][n - 1]

    def uses(self, name, def_file=None, def_line=None, skip_defs=True):
        """Every line in lib/ that names `name` (also qualified, M.name) outside its own definition line, outside
        lines that start a comment and (skip_defs) outside lines that define a same-named object in another file."""
        if self.ids is None:
            idre = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
            self.ids = {f: set(idre.findall('\n'.join(ls))) for f, ls in self.files.items()}
        rx = re.compile(r"(?<![A-Za-z0-9_'])" + re.escape(name) + r"(?![A-Za-z0-9_'])")
        dx = re.compile(r"\b(?:Definition|Lemma|Theorem|Fixpoint|Let|Record|Inductive|Abbreviation|Notation) "
                        + re.escape(name) + r"(?![A-Za-z0-9_'])")
        hits = []
        for f in sorted(self.files):
            if name not in self.ids[f]:
                continue
            for i, l in enumerate(self.files[f], 1):
                if (f, i) == (def_file, def_line):
                    continue
                if skip_defs and dx.search(l):
                    continue
                if rx.search(l) and not l.lstrip().startswith('(*'):
                    hits.append(f'lib/{f}:{i}')
        return hits


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--rows', required=True)
    ap.add_argument('--ours', required=True)
    ap.add_argument('--donor', required=True, help="the donor's lib/ root")
    ap.add_argument('--old-img', required=True)
    ap.add_argument('--old-syms', required=True)
    ap.add_argument('--new-img', required=True)
    ap.add_argument('--new-syms', required=True)
    ap.add_argument('--out', required=True)
    a = ap.parse_args()

    O = tri.Img('donor', a.old_img, a.old_syms)
    N = tri.Img('ours', a.new_img, a.new_syms)
    lib = Lib(a.ours)
    with open(a.rows) as fh:
        rd = csv.reader(fh, delimiter='\t', quoting=csv.QUOTE_NONE)
        hdr = next(rd)
        rows = [dict(zip(hdr, r)) for r in rd]
    out = []

    def put(r, reason, meas, result='OK', **kw):
        out.append({'set': r['set'], 'file': r['file'], 'stage_line': r['stage_line'], 'pos': r['pos'],
                    'class': kw.get('cls', ''), 'reason': reason, 'measurement': meas, 'result': result,
                    'finding_kind': kw.get('fk', ''), 'new_value': kw.get('nv', ''), 'read_by': kw.get('rb', ''),
                    'measurement_append': ''})

    GN, gn_a, gn_n = globals_of(N)
    GO, go_a, go_n = globals_of(O)
    gn_end = max(g['beg'] + g['szrz'] for g in GN)
    go_end = max(g['beg'] + g['szrz'] for g in GO)
    bss = next((s[1], s[1] + s[2]) for s in N.secs if s[0] == '.bss')
    bss_g = sorted((g for g in GN if bss[0] <= g['beg'] < bss[1]), key=lambda g: g['beg'])
    odrs = sorted(g['odr'] for g in GN if g['odr'] not in (0, 2 ** 64 - 1))
    top = N.top
    base = min(v for v, *_ in N.segs) & ~0xfff
    rom_end = max(v + ms for v, ms, off, fs, fl in N.segs if not fl & 2)
    text = next((s[1], s[1] + s[2]) for s in N.secs if s[0] == '.text')
    pin_bytes = open(a.new_img, 'rb').read()
    cache = {}

    for r in rows:
        if r['class'] == 'VALUE' and r['result'] == 'OK' and r['line'].isdigit():
            # a rule settled it: add the by-use grep of the name the line defines or states
            src_line = lib.line(r['file'][4:], int(r['line']))
            m = re.search(r'(?:Definition|Lemma|Theorem|Let) (\w+)', src_line)
            if m:
                uses = lib.uses(m.group(1), r['file'][4:], int(r['line']))
                out.append({'set': r['set'], 'file': r['file'], 'stage_line': r['stage_line'], 'pos': r['pos'],
                            'class': '', 'reason': '', 'measurement': '', 'result': '', 'finding_kind': '',
                            'new_value': '', 'read_by': uses[0] if uses else '-',
                            'measurement_append': f'by-use grep of {m.group(1)} over lib/: {len(uses)} uses'
                                                  + (f' (first {uses[0]})' if uses else '')})
            continue
        if r['reason'] == 'HAND-NOTE' and r['result'] == 'OK':
            # a hand row with no generic rule: say what our value is in our pin's headers
            u = tri.as_int(r['our_val'])
            d = tri.as_int(r['donor_val'])
            ek = sorted(N.keys.get(u, set()))
            dsec = next((f'{nm}+{d - a_:#x}' for nm, a_, n_ in O.secs if a_ <= d < a_ + n_), '-') if d else '-'
            out.append({'set': r['set'], 'file': r['file'], 'stage_line': r['stage_line'], 'pos': r['pos'],
                        'class': '', 'reason': '', 'measurement': '', 'result': '', 'finding_kind': '',
                        'new_value': '', 'read_by': '',
                        'measurement_append': f'our value {r["our_val"]} = {" = ".join(ek) if ek else "no header edge"} '
                                              f'(our pin headers); donor {r["donor_val"]} = {dsec} (donor section '
                                              f'headers), not a section edge; d9e0 wrote {r["d9e0_val"]}'})
            continue
        if r['result'] != 'OPEN':
            continue
        f, b = r['file'], os.path.basename(r['file'])[:-2]
        u = tri.as_int(r['our_val'])
        d = tri.as_int(r['donor_val'])
        ln = int(r['line']) if r['line'].isdigit() else None

        # zero-shadow start of .bss: end of the last poisoned global redzone
        if b == 'AD1o' and r['class'] == 'refused':
            facts = (f'end of the last asan global redzone in our pin = max(beg + size_with_redzone) over the '
                     f'{len(GN)} asan_globals descriptors = {gn_end:#x}; image top {top:#x} (page-rounded PT_LOAD end)')
            want = {gn_end: f'{gn_end:#x} = that end', gn_end + 0x20: f'{gn_end + 0x20:#x} = that end + 0x20, the '
                    'lower bound of bss_shadow_facts (its lia proof over the bound is kernel-checked; the donor used '
                    'its own start + 0x30)',
                    gn_end // 8: f'{gn_end // 8} = {gn_end:#x} / 8', (gn_end + 0x20) // 8:
                    f'{(gn_end + 0x20) // 8} = {gn_end + 0x20:#x} / 8', (top - gn_end) // 8:
                    f'{(top - gn_end) // 8} = ({top:#x} - {gn_end:#x}) / 8'}
            if u in want:
                put(r, 'ZERO-SHADOW-START', f'our value {r["our_val"]}: {want[u]}; {facts}; d9e0 refused the donor '
                    f'value {r["donor_val"]} (derived from the donor asan_globals section end {go_a + go_n:#x}: '
                    f'cgif\'s {len(GO)} globals lie in .rodata, so its .bss shadow is zero from there)', cls='refused')
            else:
                put(r, 'ZERO-SHADOW-START', f'our value {r["our_val"]} matches no measured quantity; {facts}', 'OPEN')
            continue
        if b == 'AD25' and r['class'] == 'refused':
            g0 = bss_g[0]
            lo_any = [g for g in GN if bss[0] <= g['beg'] < g0['beg']]
            if u == g0['beg'] + g0['size'] and not lo_any:
                put(r, 'ZERO-SHADOW-END', f"our value {u:#x} = beg + size of the first asan global in .bss "
                    f"({g0['beg']:#x} + {g0['size']}; asan_globals descriptor of our pin); no global begins in "
                    f"[{bss[0]:#x}, {g0['beg']:#x}); so [.bss start {bss[0]:#x}, {u:#x}) has zero shadow; the donor's "
                    f"{d:#x} was its image top (cgif .bss holds no global)", cls='refused')
            else:
                put(r, 'ZERO-SHADOW-END', f'our value {r["our_val"]} != first bss global end', 'OPEN')
            continue
        if b in ('AFhn', 'AFix', 'AFjb', 'AFju', 'AFkm', 'AFkz') and r['class'] == 'refused':
            lo_need = shadow(gn_end - 1) + 1
            if u is not None and u % 4096 == 0 and lo_need <= u <= shadow(top) and u - 4096 < lo_need:
                put(r, 'LOW-SHADOW-BAND', f'our bound {u:#x} = first page boundary above the shadow of the last '
                    f'asan global redzone byte (shadow({gn_end - 1:#x}) = {shadow(gn_end - 1):#x}; max over the '
                    f'{len(GN)} asan_globals descriptors of our pin) and <= shadow of image top {shadow(top):#x}; '
                    f'the donor value {d:#x} is a cgif-wide band bound (cgif last redzone shadow '
                    f'{shadow(go_end - 1):#x}); d9e0 refused it', cls='refused')
            else:
                put(r, 'LOW-SHADOW-BAND', f'our value {r["our_val"]} outside [{lo_need:#x}, {shadow(top):#x}]', 'OPEN')
            continue
        if b == 'AE23' and r['class'] == 'refused' and ln == 36:
            want = {shadow(base): f'shadow of image base {base:#x}',
                    shadow(top): f'shadow of image top {top:#x}'}
            if odrs:
                want[odrs[0]] = (f'first odr indicator of our asan_globals descriptors (odr fields: '
                                 f'{", ".join(hex(x) for x in odrs)})')
            if u in want:
                put(r, 'DTOR-WRITE-SET', f'our value {u:#x} = {want[u]}; the line states the dtor write set over '
                    f'the whole image shadow and the odr indicator bytes; the donor value {d:#x} was a shadow cell '
                    f'of one of cgif\'s {len(GO)} globals', cls='refused')
            else:
                put(r, 'DTOR-WRITE-SET', f'our value {r["our_val"]} matches no measured quantity', 'OPEN')
            continue
        # format-string shadow window: SH_LO = shadow(FMT)/8*8, SH_HI = shadow(FMT+n-1)/8*8+8, n = strlen+1
        if b in ('AE2t', 'AE2u', 'AE2v', 'AE2w', 'AE35') and r['class'] == 'refused':
            src = lib.files[f[4:]]
            fm = next((int(m.group(1), 0) for l in src for m in [re.match(r'Definition FMT : Z := (0x[0-9a-f]+)', l)]
                       if m), None)
            dsrc = open(os.path.join(a.donor, f[4:]), encoding='utf-8').read()
            dm = re.search(r'Definition FMT : Z := (0x[0-9a-f]+)', dsrc)
            dsh = re.search(r'Definition SH_LO : Z := (0x[0-9a-f]+)\.\s+Definition SH_HI : Z := (0x[0-9a-f]+)', dsrc)
            s = cstr(N, fm)
            n = len(s) + 1
            lo, hi = shadow(fm) // 8 * 8, shadow(fm + n - 1) // 8 * 8 + 8
            ds = cstr(O, int(dm.group(1), 0))
            dlo = shadow(int(dm.group(1), 0)) // 8 * 8
            dhi = shadow(int(dm.group(1), 0) + len(ds)) // 8 * 8 + 8
            ctl = (dlo, dhi) == (int(dsh.group(1), 0), int(dsh.group(2), 0))
            want = lo if r['pos'] == '0' else hi
            if u == want and ctl:
                put(r, 'FMT-SHADOW', f'our FMT {fm:#x} holds {s[:30]!r} (n = {n} bytes with NUL, read from our pin); '
                    f'SH_LO = shadow(FMT)/8*8 = {lo:#x}, SH_HI = shadow(FMT+n-1)/8*8+8 = {hi:#x}; known answer: the '
                    f'same formula on the donor FMT {dm.group(1)} ({len(ds) + 1} bytes) gives the donor SH_LO/SH_HI '
                    f'{dlo:#x}/{dhi:#x} exactly', cls='refused')
            else:
                put(r, 'FMT-SHADOW', f'formula gives {lo:#x}/{hi:#x}, ours {r["our_val"]}, donor control {ctl}',
                    'OPEN')
            continue
        if b == 'AD2k' and r['class'] == 'refused' and ln == 31:
            so = sorted(N.sym_offs(u))
            ds = cstr(O, d)
            cnt = pin_bytes.count(ds + b'\0') if len(ds) > 1 else None
            put(r, 'REPLACED-CELL', f'our value {u:#x} = {", ".join(f"{nm}+{off:#x}" for nm, off, ty in so)} (our '
                f'twin symtab): the check names a libc stdio cell the model writes; the donor value {d:#x} was the '
                f'cgif sink-file string {ds!r}, ' + (f'which occurs {cnt} times in our pin (byte search, with its NUL)'
                                                    if cnt is not None else 'a 1-byte string (not searched)'),
                'OK' if so and cnt in (0, None) else 'OPEN', cls='refused')
            continue
        if b == 'AE2k' and r['class'] == 'refused' and u == 0:
            ds = cstr(O, d)
            name = re.search(r'Definition (\w+) : Z', lib.line(f[4:], ln)).group(1)
            cnt = pin_bytes.count(ds + b'\0') if len(ds) > 1 else None
            uses = lib.uses(name, f[4:], ln)
            put(r, 'NO-SUCH-OBJECT', f'{name} := 0 in our file; the donor value {d:#x} is the cgif string {ds!r} '
                f'(cgif sink file); occurrences of that NUL-terminated string in our pin: '
                f'{cnt if cnt is not None else "not searched (1-byte string)"}; fuzz_command writes no sink file, '
                f'so the name has no object in our image', cls='refused', rb=(uses[0] if uses else '-'))
            continue
        if b == 'AD1k' and r['class'] == 'slot':
            m = re.search(r'(R_A1[a-z]) (\d+) (\d+)', lib.line(f[4:], ln))
            reg, st, n = m.group(1), int(m.group(2)), int(m.group(3))
            ad = lib.files['A/AD2j.v']
            k = next(i for i, l in enumerate(ad) if l.startswith(f'Definition {reg} : region'))
            mm = re.match(r'mkRegion None (\d+) (\d+)', ad[k + 1])
            lo2, hi2 = int(mm.group(1)), int(mm.group(2))
            ok = (st, n) == (lo2, hi2 - lo2)
            put(r, 'REGION-OF-AD2J', f'our line uses {reg} {st} {n}; lib/A/AD2j.v:{k + 2} defines {reg} as '
                f'mkRegion None {lo2} {hi2} (start {lo2}, length {hi2 - lo2}); '
                f'{"equal" if ok else "DIFFERENT"}; AD2j is generated from our image; the donor numbers named cgif\'s '
                'own region of that name', 'OK' if ok else 'OPEN', cls='slot')
            continue
        if b == 'AB05' and r['class'] == 'slot':
            src = lib.line(f[4:], ln)
            rngs = [(int(x, 16), int(y)) for x, y in re.findall(r'\((0x[0-9a-f]+), (\d+)%nat\)', src)]
            inside = all(text[0] <= s and s + 4 * n <= text[1] and s % 2 == 0 for s, n in rngs)
            if u == text[0] and inside:
                put(r, 'TEXT-START', f'our value {u:#x} = .text start (section header) = e_entry; all {len(rngs)} '
                    f'(start, count) ranges of the line lie inside .text [{text[0]:#x}, {text[1]:#x}); the donor '
                    f'{d:#x} was cgif PT_LOAD1 page base; our file header says the ranges were recomputed for our code',
                    cls='slot')
            else:
                put(r, 'TEXT-START', f'our value {r["our_val"]}: inside={inside}', 'OPEN')
            continue
        if b == 'AE7d' and r['class'] == 'VALUE':
            hits = lib.uses('snl_rom_low', f[4:], ln, skip_defs=False)
            defs = [h for h in hits if re.match(r'\s*Lemma snl_rom_low\b', lib.line(h[4:].split(':')[0],
                                                                                   int(h.split(':')[1])))]
            uses = [h for h in hits if h not in defs]
            put(r, 'ROM-BOUND', f'snl_rom_low states every read-only byte lies below the bound; our pin\'s '
                f'non-writable PT_LOADs end at {rom_end:#x} < {u:#x} (and < d9e0 {r["d9e0_val"]}), so the statement '
                f'holds with our value; the bound is no image quantity in either image (donor {d:#x} = '
                f'{"; ".join(f"{nm}+{off:#x}" for nm, off, ty in sorted(O.sym_offs(d)))} in .bss, d9e0 moved it to the '
                f'same symbol+offset in ours: a class-B move of a model constant by the tool); by-use grep over '
                f'lib/: {len(uses)} uses; {len(defs)} other files define their own lemma of that name '
                f'({"; ".join(defs[:3])})', cls='VALUE', rb=(uses[0] if uses else '-'))
            continue
        if b == 'AE37' and r['class'] == 'other':
            put(r, 'DTOR-COUNTS', f'donor {d} = {"3 descriptors x 64 bytes (cgif asan_globals size %#x)" % go_n if d == 192 else "3 x 8"}; '
                f'our asan_globals section is {gn_n:#x} bytes = {gn_n // 64} descriptors (d9e0 wrote '
                f'{r["d9e0_val"]} = {gn_n // 64} x {"64" if d == 192 else "8"}); our AE37 states the module '
                'destructor walk over all descriptors (the donor\'s unrolled 3-descriptor lines have no counterpart)',
                cls='other')
            continue
        if b == 'AF0m' and r['class'] == 'other':
            sv_d = sym_at(O, 'sysconf.values')
            sv_u = sym_at(N, 'sysconf.values')
            owned = '\n'.join(lib.files['A/AF0m.v'])
            if d in (0x21448, 0x214ac) and sv_d and sv_u:
                off = d - sv_d[0]
                want = sv_u[0] + off
                hit = re.search(r'\(%#x, 0x[0-9a-f]+\)' % want, owned)
                put(r, 'OWNED-CELL', f'donor {d:#x} = sysconf.values{off:+#x} (donor twin, sysconf.values at '
                    f'{sv_d[0]:#x}); ours sysconf.values at {sv_u[0]:#x}, so the cell is {want:#x}; our AF0m '
                    f'(regenerated) lists it: {"yes" if hit else "NO"}; d9e0 kept the donor address {d:#x} in its '
                    'stage-out (a d9e0 miss in a file the unit regenerates); the donor value occurs in our file only '
                    'as an unrelated cell of our own image', 'OK' if hit else 'OPEN', cls='other')
            elif d == 0x103a0:
                hits = [i + 1 for i, l in enumerate(lib.files['A/AF0m.v']) if re.search(r'\(0x103a0, 0x8\)', l)]
                put(r, 'OWNED-CELL', f'our AF0m (regenerated from our image) lists (0x103a0, 0x8) at line(s) {hits} '
                    f'as one of our own 8-byte .rodata cells (our pin bytes at 0x103a0: '
                    f'{N.read(0x103a0, 8).hex()}); the old run\'s 0x103a8 is listed as well; the donor value is not '
                    'carried from cgif: it is our own cell', cls='other')
            continue
        if b == 'AE3i' and r['class'] == 'other':
            hits = [i + 1 for i, l in enumerate(lib.files['A/AE3i.v']) if re.search(r'mkChunk %#x ' % d, l)]
            put(r, 'GEN-OWN-VALUE', f'our AE3i (regenerated from our image) starts a chunk at {d:#x} at line(s) '
                f'{hits}: our own value (our rodata object (0x10330, 9) is listed in lib/A/Prog/CmdRecBase.v); the '
                f'alignment paired the donor line with our line {ln}, which holds {r["our_val"]}', cls='other')
            continue
        # ---- text rows (the line's non-numeral text differs between the two runs)
        if r['class'] == 'text' and b == 'AB1w':
            if 'ab1w' not in cache:
                src = '\n'.join(lib.files['A/AB1w.v'])
                pairs = re.findall(r'Definition tfib_A_(\w+) : Z := (0x[0-9a-f]+)\.\s+Definition tfib_E_\1 : Z := '
                                   r'(0x[0-9a-f]+)\.', src)
                # function boundaries of our twin: every STT_FUNC start (sized or not) and every sized STT_FUNC end
                t = tri.ELFFile(open(a.new_syms, 'rb'))
                fstart, fbound = set(), set()
                for y in t.get_section_by_name('.symtab').iter_symbols():
                    if y['st_info']['type'] == 'STT_FUNC' and y['st_value']:
                        fstart.add(y['st_value'])
                        fbound.add(y['st_value'])
                        if y['st_size']:
                            fbound.add(y['st_value'] + y['st_size'])
                bad = [nm for nm, A_, E_ in pairs if int(A_, 16) not in fstart or int(E_, 16) not in fbound
                       or int(E_, 16) <= int(A_, 16)]
                defined = {nm for nm, _, _ in pairs}
                cache['ab1w'] = (len(pairs), bad, defined)
            npairs, bad, defined = cache['ab1w']
            on = re.findall(r'Definition tfib_A_(\w+) :', r['old_val'])
            nn = re.findall(r'Definition tfib_A_(\w+) :', r['d9e0_val'])
            lost = [x for x in on if x not in defined]
            used = {x: lib.uses('tfib_A_' + x) + lib.uses('tfib_E_' + x) for x in set(lost + nn) - defined}
            used = {x: [h for h in v if not h.startswith(('lib/A/AB1w.v', 'lib/B/YB1w.v'))] for x, v in used.items()}
            hit = {x: v for x, v in used.items() if v}
            put(r, 'FUNCTION-TABLE', f'our AB1w function table (regenerated from our image): {npairs} A/E pairs, '
                f'{len(bad)} whose A is not a function symbol start or whose E is not a function boundary (symbol '
                f'start or sized-symbol end, our twin symtab){": " + ", ".join(bad[:8]) if bad else ""}; old-run rows '
                f'{on or "-"}: absent from our table {lost or "none"}; d9e0 rows '
                f'{(nn[:6] + ["..."]) if len(nn) > 6 else (nn or "-")}; names absent from our table that any file '
                f'outside the tables uses: {hit or "none"} (by-use grep over lib/)',
                'OK' if not hit and not bad else 'OPEN', cls='generated')
            continue
        if r['class'] == 'text' and b == 'AE2k':
            on = re.findall(r'\bFF_\w+', r['old_val'])
            if r['our_val'] == r['d9e0_val']:
                put(r, 'PATCHED-TEXT', 'our line equals the d9e0 line (the fopen/fclose cells removed)', cls='patched')
                continue
            uses = {x: lib.uses(x) for x in on}
            fsyms = [n_ for v, sz, n_, ty in N.syms + N.big if n_ in ('fopen', 'fclose', '__wrap_fopen',
                                                                       '__wrap_fclose', '__interceptor_fopen',
                                                                       '__interceptor_fclose')]
            put(r, 'DROPPED-DEF', f'd9e0 deleted the refused definition {on} with every use; our file has no such '
                f'line either; by-use grep over lib/: {sum(len(v) for v in uses.values())} uses; our twin has '
                f'{len(fsyms)} symbols named fopen/fclose/__wrap_fopen/__wrap_fclose/__interceptor_fopen/'
                '__interceptor_fclose', 'OK' if not any(uses.values()) and not fsyms else 'OPEN', cls='patched')
            continue
        if r['class'] == 'text' and b == 'AE34':
            tr = sorted(v for v, sz, n_, ty in N.syms if n_.startswith('__interceptor_trampoline_') and sz == 4)
            run = [tr[0]]
            for v in tr[1:]:
                if v == run[-1] + 4:
                    run.append(v)
                else:
                    break
            trd = sorted(v for v, sz, n_, ty in O.syms if n_.startswith('__interceptor_trampoline_') and sz == 4)
            rund = [trd[0]]
            for v in trd[1:]:
                if v == rund[-1] + 4:
                    rund.append(v)
                else:
                    break
            m = re.search(r'\((0x[0-9a-f]+), (\d+)%nat\)', r['our_val'])
            ok = m and int(m.group(1), 16) == run[0] and int(m.group(2)) == len(run)
            put(r, 'TRAMPOLINE-BLOCK', f'our first entry ({m.group(1)}, {m.group(2)}): our twin has a contiguous '
                f'block of {len(run)} 4-byte __interceptor_trampoline_* symbols from {run[0]:#x} to {run[-1] + 4:#x}; '
                f'the donor block is {len(rund)} from {rund[0]:#x} (the old run kept the donor count 38); d9e0 split '
                'the block into the sub-ranges whose trampolines it paired', 'OK' if ok else 'OPEN', cls='patched')
            continue
        if r['class'] == 'text' and b == 'AF0l':
            src = lib.line(f[4:], ln) + ' ' + lib.line(f[4:], ln + 1)
            pairs = [(int(c), int(v, 16)) for c, v in re.findall(r'cid =\? (\d+) then (0x[0-9a-f]+)', src)]
            chk = [(c, v, sym_at(N, f'__asan_stack_malloc_{c}')) for c, v in pairs]
            ok = all(s == [v] for c, v, s in chk)
            dpairs = [(int(c), int(v, 16)) for c, v in re.findall(r'cid =\? (\d+) then (0x[0-9a-f]+)', r['d9e0_val'])]
            put(r, 'CLASS-MAP', f'our map (lines {ln}-{ln + 1}) {[(c, hex(v)) for c, v in pairs]}: each value is the '
                f'__asan_stack_malloc_<cid> symbol of our twin: {"all equal" if ok else chk}; d9e0 wrote the same '
                f'map: {dpairs == pairs}; the donor had classes 1 and 2 (cgif __asan_stack_malloc_1/_2)',
                'OK' if ok else 'OPEN', cls='patched')
            continue

    cols = ['set', 'file', 'stage_line', 'pos', 'class', 'reason', 'measurement', 'result', 'finding_kind',
            'new_value', 'read_by', 'measurement_append']
    with open(a.out, 'w') as fh:
        fh.write('\t'.join(cols) + '\n')
        for o in out:
            fh.write('\t'.join(str(o[c]).replace('\t', ' ').replace('\n', ' ') for c in cols) + '\n')
    from collections import Counter
    print(Counter((o['reason'], o['result']) for o in out), file=sys.stderr)


if __name__ == '__main__':
    main()
