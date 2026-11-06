"""The rules of triage.py. A rule = (reason id, a regex over the comment-blanked line whose named groups mark
numeral SLOTS, a slot -> expectation map, optional file / sentence filters). Group names `slot` or
`slot__k` (k distinguishes repeats). An expectation is a fact key of facts.Facts (exact value) or a function
(F, m, row, line) -> Exp. Applicability never reads the row's value: only the line's text."""
import re

N = r'(?:0x[0-9a-fA-F]+|\d+)'


def ival(s):
    return int(s, 16) if s.lower().startswith('0x') else int(s)


class Exp:
    """an expectation: exact value, or a closed interval [lo, hi] (BOUND), with its measurement text and, when
    the rule can measure it, the donor side's value of the same slot (for the known-answer control)."""
    def __init__(self, value=None, text='', lo=None, hi=None, donor=None):
        self.value, self.text, self.lo, self.hi, self.donor = value, text, lo, hi, donor

    def ok(self, v):
        if self.lo is not None or self.hi is not None:
            return (self.lo is None or v >= self.lo) and (self.hi is None or v <= self.hi)
        return self.value is not None and v == self.value

    def want(self):
        if self.lo is not None or self.hi is not None:
            return f'[{self.lo if self.lo is not None else "-inf"}, {self.hi if self.hi is not None else "+inf"}]'
        return str(self.value)


class Rule:
    def __init__(self, rid, pat, slots, files=None, sents=None):
        self.rid, self.rx, self.slots = rid, re.compile(pat), slots
        self.files = re.compile(files) if files else None
        self.sents = re.compile(sents) if sents else None


def fact(key):
    return lambda F, m, row, line: Exp(F[key][0], F[key][1], donor=F.dv.get(key))


def exp_of(spec, F, m, row, line):
    if isinstance(spec, str):
        return Exp(F[spec][0], F[spec][1], donor=F.dv.get(spec))
    return spec(F, m, row, line)


def judge(rules, F, row, line, span, v):
    """(reason, measurement, result, finding_kind, new_value, slot) for value v at span of the line."""
    f, sent = row[5], row[7]
    for rule in rules:
        if rule.files and not rule.files.search(f):
            continue
        if rule.sents and not rule.sents.search(sent):
            continue
        for m in rule.rx.finditer(line):
            for g, val in m.groupdict().items():
                if val is None or m.span(g) != span:
                    continue
                slot = g.split('__')[0]
                e = exp_of(rule.slots[slot], F, m, row, line)
                txt = f'slot {slot}: {e.text}; expected {e.want()}, written {v}'
                if e.ok(v):
                    return rule.rid, txt, 'OK', 'code', '-', slot
                nv = e.value if e.value is not None else (e.lo if e.lo is not None and v < e.lo else e.hi)
                return rule.rid, txt, 'FINDING', 'code', str(nv), slot
    return 'UNSETTLED', 'no rule measures this slot', 'OPEN', '-', '-', None


def slot_exp(rules, F, row, line, span):
    """the Exp of the slot at span (None when no rule applies)."""
    f, sent = row[5], row[7]
    for rule in rules:
        if rule.files and not rule.files.search(f):
            continue
        if rule.sents and not rule.sents.search(sent):
            continue
        for m in rule.rx.finditer(line):
            for g, val in m.groupdict().items():
                if val is not None and m.span(g) == span:
                    return exp_of(rule.slots[g.split('__')[0]], F, m, row, line)
    return None


def donor_value(rules, F, row, line, span, v):
    if row[10]:
        return int(row[10], 16)
    f, sent = row[5], row[7]
    for rule in rules:
        if rule.files and not rule.files.search(f):
            continue
        if rule.sents and not rule.sents.search(sent):
            continue
        for m in rule.rx.finditer(line):
            for g, val in m.groupdict().items():
                if val is not None and m.span(g) == span:
                    e = exp_of(rule.slots[g.split('__')[0]], F, m, row, line)
                    return e.donor
    return None


# ------------------------------------------------------------------------------------------- measured families
def gen_cert(F):
    """the generated start-up certificate lib/A/AB01.v: per state a_maps [(var or None, base text, len, kind)],
    a_vis, a_eager, and the KRange kentries; and the same of the donor's AB01.v."""
    if hasattr(F, '_gen'):
        return F._gen
    def parse(t):
        st = []
        for mm in re.finditer(r'a_maps := \[(.*?)\]; a_totsz', t):
            maps = []
            for x in re.finditer(r'\{\| am_base := (.*?); am_len := ELit (\d+); am_kind := (\w+) \|\}', mm.group(1)):
                v = re.fullmatch(r'EMd Instr\.M_MUL \(ELit 4096\) \(EVar (\d+)\)', x.group(1))
                maps.append((int(v.group(1)) if v else None, x.group(1), int(x.group(2)), x.group(3)))
            st.append(maps)
        eag = [int(x) for x in re.findall(r'a_eager := (\d+)', t)]
        vis = set()
        for mm in re.finditer(r'a_vis := \[(.*?)\]; a_', t):
            for x in re.finditer(r'\(EMd Instr\.M_MUL \(ELit 4096\) \(EVar (\d+)\), ELit (\d+)\)', mm.group(1)):
                vis.add((int(x.group(1)), int(x.group(2))))
        kr = {}
        for x in re.finditer(r'KRange \(EVar (\d+)\) (\d+) (\d+)', t):
            kr.setdefault(int(x.group(1)), set()).add((int(x.group(2)), int(x.group(3))))
        return {'states': st, 'eager': eag, 'vis': vis, 'krange': kr}
    F._gen = (parse(F.U.text('A/AB01.v')), parse(F.UD.text('A/AB01.v') or ''))
    return F._gen


GEN = 'the generated start-up certificate lib/A/AB01.v (written from fuzz_command.asan c0661b96b5bd)'


def head_maps(F):
    g, gd = gen_cert(F)
    heads = {tuple((x[0], x[2], x[3]) for x in s[:4]) for s in g['states']}
    tails = {tuple((x[0], x[2], x[3]) for x in s[-12:]) for s in g['states']}
    nm = {len(s) - 16 for s in g['states']}
    return heads, tails, nm, g, gd


def e_head(i, what):
    """TFIB_HEAD4's i-th map (var / len) against the certificate's first four maps of every state."""
    def f(F, m, row, line):
        heads, tails, nm, g, gd = head_maps(F)
        if len(heads) != 1:
            return Exp(None, f'{GEN}: the first four maps differ between states ({len(heads)} forms)')
        h = list(heads)[0][i]
        return Exp(h[0] if what == 'var' else h[1],
                   f'{GEN}: map {i} of all {len(g["states"])} states is (4096 * EVar {h[0]}, len {h[1]}, {h[2]})')
    return f


def e_epg_pair(what):
    """AVIS14's (epg v, ELit len): the pair must be a visible zone of the certificate (a_vis of its states)."""
    def f(F, m, row, line):
        heads, tails, nm, g, gd = head_maps(F)
        v, ln = int(m.group('pv')), int(m.group('pl'))
        if what == 'var':
            c = sorted({x[0] for x in g['vis'] if x[1] == ln})
            return Exp(v if (v, ln) in g['vis'] else (c[0] if len(c) == 1 else None),
                       f'{GEN}: a_vis of its {len(g["states"])} states holds (4096 * EVar {v}, {ln}): {(v, ln) in g["vis"]}')
        c = sorted({x[1] for x in g['vis'] if x[0] == v})
        return Exp(c[0] if len(c) == 1 else None,
                   f'{GEN}: a_vis zone of 4096 * EVar {v} has length {c}')
    return f


def e_krange(what):
    def f(F, m, row, line):
        g, gd = gen_cert(F)
        v = int(m.group('kv'))
        rs = g['krange'].get(v, set())
        if len(rs) != 1:
            return Exp(None, f'{GEN}: {len(rs)} KRange entries for EVar {v}')
        lo, hi = list(rs)[0]
        val = {'var': v if rs else None, 'lo': lo, 'hi': hi}[what]
        return Exp(val, f'{GEN}: kentry KRange (EVar {v}) {lo} {hi}')
    return f


def e_musl(which):
    def f(F, m, row, line):
        heads, tails, nm, g, gd = head_maps(F)
        if which == 'head':
            return Exp(4 if len(heads) == 1 else None, f'TFIB_HEAD4 has 4 maps (lib/A/AD1g.v:34) = the first 4 maps of the {len(g["states"])} states of {GEN}')
        if which == 'fixed':
            return Exp(16 if len(heads) == 1 and len(tails) == 1 else None,
                       f'head 4 + tail 12 fixed maps (AD1g.v:34-38) = every state of {GEN} has 16 + (0..2 musl) maps: {sorted(nm)} musl maps')
        if which in ('known2', 'known3'):
            h = list(heads)[0]
            k = [i for i, x in enumerate(h) if x[2] == 'KRWLAZY' or x[1] == 1048576]
            want = {'known2': 2, 'known3': 3}[which]
            return Exp(want if [x[0] for x in h[2:4]] == [501, 500] else None,
                       f'the known head maps eSB (EVar 501) and eNB (EVar 500) sit at ALLMAPS indices 2 and 3 (TFIB_HEAD4 = [eDM; eGV; eSB; eNB], AD1g.v:34; {GEN} maps 2-3 = {h[2:4]})')
    return f


def e_eager(F, m, row, line):
    g, gd = gen_cert(F)
    mx, dmx = max(g['eager']), (max(gd['eager']) if gd['eager'] else None)
    return Exp(mx, f'{GEN}: max a_eager over its {len(g["eager"])} states = {mx} (values {sorted(set(g["eager"]))}); the donor certificate\'s max = {dmx}',
               donor=dmx)


def e_eDM_len(F, m, row, line):
    heads, tails, nm, g, gd = head_maps(F)
    h = list(heads)[0][0]
    return Exp(h[1] if h[0] == 1639 else None, f'eDM = epg 1639 (AD1g.v:29); {GEN} map 0 = (4096 * EVar {h[0]}, len {h[1]}, {h[2]})')


# ---- program statics (DWARF of the twin, asan_globals descriptors, symtab)
def asan_globals(I):
    lo, hi = I.sec('asan_globals')
    out = []
    for a in range(lo, hi, 64):
        w = [I.u64(a + 8 * k) for k in range(8)]
        out.append((w[0], w[1], w[2], I.cstr(w[3], 80).decode(errors='replace') if w[3] else '', w[7]))
    return out


def gi_table(F):
    """[(base, lo, hi or None, fields covered)] of lib/A/Prog/CmdGlob.v GI_cmdA's zero_atA list, each run checked
    against the DWARF field extents of the program statics in the twin (hi None when they disagree)."""
    if hasattr(F, '_gi'):
        return F._gi
    cg = F.U.code('A/Prog/CmdGlob.v')
    body = cg[cg.find('Definition GI_cmdA'):]
    body = body[:body.find('.\n')]
    gi = [(x.group(1) or x.group(3), int(x.group(2) or 0), int(x.group(4)))
          for x in re.finditer(r'zero_atA rd (?:\((A_G_REC) \+ (\d+)\)|(A_REC_SPILL|A_G_QUITTING)) (\d+)', body)]
    dwf = F.dwarf()
    rec = {x[0]: (x[1], x[2]) for x in dwf['struct']['recorder'][1]}
    rc = {x[0]: (x[1], x[2]) for x in dwf['struct']['rec_call'][1]}
    gq = dwf['var']['g_quitting'][0]
    fields = {'A_G_REC': sorted((o, o + s, n) for n, (o, s) in rec.items()),
              'A_REC_SPILL': sorted((o, o + s, n) for n, (o, s) in rc.items()),
              'A_G_QUITTING': [(0, gq, 'g_quitting')]}
    out = []
    for base, lo, n in gi:
        fl = fields[base]
        ok = lo in {a for a, b, _ in fl} and (lo + n) in {b for a, b, _ in fl}
        out.append((base, lo, lo + n if ok else None, [nm for a, b, nm in fl if lo <= a and b <= lo + n]))
    txt = (f'lib/A/Prog/CmdGlob.v:25-27 GI_cmdA zero_atA {[(b, l, k) for b, l, k in gi]}; DWARF of the twin {F.O.sha_twin}: g_rec is '
           f'struct recorder ({dwf["struct"]["recorder"][0]} bytes) with ' +
           ', '.join(f'{n}@{o}+{s}' for n, (o, s) in rec.items() if n in ('ncalls', 'answer', 'nreplies', 'reply', 'reply_size')) +
           f'; record.spill is struct rec_call, fn@{rc["fn"][0]}+{rc["fn"][1]} nargs@{rc["nargs"][0]}+{rc["nargs"][1]}; '
           f'g_quitting is a volatile int of {gq} bytes')
    F._gi = (out, txt)
    return F._gi


def e_gi_slot(which):
    """the k-th GI_IVS pair of an object = its k-th GI_cmdA run; lo = the field offset, hi = lo + zeroed length."""
    def f(F, m, row, line):
        out, txt = gi_table(F)
        base = m.group('gb')
        k = len(re.findall(r'\(CmdGlob\.' + base + r'\b', line[:m.start()]))
        runs = [x for x in out if x[0] == base]
        if k >= len(runs):
            return Exp(None, txt + f'; no run {k} of {base}')
        b, lo, hi, cov = runs[k]
        t = txt + f'; run {k} of {base}: [+{lo}, +{hi}) = fields {cov}'
        if hi is None:
            return Exp(None, t)
        if which == 'lo':
            return Exp(lo, t)
        return Exp(hi if base == 'A_G_REC' else hi - lo, t)
    return f


def e_pg_hull(which):
    def f(F, m, row, line):
        O = F.O
        g0 = O.sym('g_rec')[0]
        gq = O.sym('g_quitting')[0]
        n = F.dwarf()['var']['g_quitting'][0]
        cg = F.U.text('A/Prog/CmdGlob.v')
        if which == 'lo':
            return Exp(g0, f'{F.img()} symtab g_rec = {g0:#x} = CmdGlob.A_G_REC, the lowest byte of cmd_PG (lib/A/Prog/CmdGlob.v:13-17)')
        return Exp(gq + n, f'{F.img()} symtab g_quitting = {gq:#x}, DWARF volatile int {n} bytes: end {gq + n:#x} = A_G_QUITTING + 4, the highest end of cmd_PG (CmdGlob.v:15-17)')
    return f


def e_bss_lo(F, m, row, line):
    return Exp(F['bss_lo'][0], F['bss_lo'][1] + ' (GI_IVS objects g_rec, record.spill, g_quitting all lie in .bss)')


def e_drv(which):
    def f(F, m, row, line):
        O = F.O
        if which == 'statics_end':
            v, sz = O.sym('oft_aligned_copy.empty')
            g = O.sym('g_rec')[0]
            return Exp(v + sz if v + sz == g else None,
                       f'{F.img()} symtab: oft_aligned_copy.empty {v:#x} size {sz} ends at {v + sz:#x} = g_rec {g:#x}: the driver statics '
                       f'[0x5e3710, {v + sz:#x}) end where the program statics start (lib/A/AD1y.v header)')
        if which == 'errno':
            ev, esz = O.sym('__errno_location')
            w0, w1 = O.u32(ev), O.u32(ev + 4)
            imm = (w1 >> 20) - (4096 if (w1 >> 31) else 0)
            af0m = F.U.text('A/AF0m.v')
            tp = int(re.search(r'Definition TFIB_TP : Z := (0x[0-9a-f]+)', af0m).group(1), 16)
            okc = w0 == 0x00020513 and (w1 & 0xfffff) == 0x50513
            dv, dsz = F.D.sym('__errno_location')
            dimm = (F.D.u32(dv + 4) >> 20) - 4096
            return Exp(tp + imm if okc else None,
                       f'{F.img()}: __errno_location {ev:#x} = addi a0, tp, 0 ({w0:#010x}); addi a0, a0, {imm} ({w1:#010x}); '
                       f'TFIB_TP = {tp:#x} (lib/A/AF0m.v:13): errno cell = {tp + imm:#x} (= lib/A/AD20.v:49 R_errno)')
    return f


def e_cmdb(which):
    def f(F, m, row, line):
        O, D = F.O, F.D
        if which == 'shadow':
            v = O.sym('__asan_shadow_memory_dynamic_address')[0]
            return Exp(v, f'{F.img()} symtab __asan_shadow_memory_dynamic_address = {v:#x}',
                       donor=D.sym('__asan_shadow_memory_dynamic_address')[0])
        if which == 'uar':
            v = O.sym('__asan_option_detect_stack_use_after_return')[0]
            return Exp(v, f'{F.img()} symtab __asan_option_detect_stack_use_after_return = {v:#x}',
                       donor=D.sym('__asan_option_detect_stack_use_after_return')[0])
        if which in ('got_shadow', 'got_uar'):
            tgt = O.sym('__asan_shadow_memory_dynamic_address' if which == 'got_shadow' else '__asan_option_detect_stack_use_after_return')[0]
            lo, hi = O.sec('.got')
            hits = [a for a in range(lo, hi, 8) if O.u64(a) == tgt]
            dt = D.sym('__asan_shadow_memory_dynamic_address' if which == 'got_shadow' else '__asan_option_detect_stack_use_after_return')[0]
            dlo, dhi = D.sec('.got')
            dh = [a for a in range(dlo, dhi, 8) if D.u64(a) == dt]
            return Exp(hits[0] if len(hits) == 1 else None,
                       f'{F.img()} .got [{lo:#x}, {hi:#x}): the words holding {tgt:#x} are {[hex(x) for x in hits]} (GOT word content read from the image)',
                       donor=dh[0] if len(dh) == 1 else None)
        if which in ('junk', 'junklen'):
            iv, isz = O.sym('_ZN6__asanL8instanceE')
            dv, dsz = D.sym('_ZN6__asanL8instanceE')
            dl = F.UD.text('A/AD2l.v')
            dm = re.search(r'as_junk := fun _ => \[\(ANum (0x[0-9a-f]+), (\d+)\)\]', dl)
            doff, dlen = int(dm.group(1), 16) - dv, int(dm.group(2))
            if which == 'junk':
                return Exp(iv + doff if isz == dsz else None,
                           f'donor lib/A/AD2l.v as_junk = ({dm.group(1)}, {dlen}) = __asan::instance {dv:#x} + {doff:#x} in the donor; '
                           f'{F.img()} __asan::instance = {iv:#x} (size {isz}, donor {dsz}): same offset -> {iv + doff:#x}', donor=int(dm.group(1), 16))
            return Exp(dlen if isz == dsz else None, f'donor lib/A/AD2l.v as_junk length {dlen} bytes inside __asan::instance (same object size {isz} in both images)', donor=dlen)
        if which in ('cst_lo', 'cst_hi'):
            want = {'g_rec': O.sym('g_rec')[0], 'g_quitting': O.sym('g_quitting')[0]}
            lo, hi = O.sec('.got')
            words = [(a, O.u64(a)) for a in range(lo, hi, 8)]
            idx = [k for k, (a, w) in enumerate(words) if w in want.values()]
            run = words[min(idx):max(idx) + 1]
            desc = ', '.join(f'{a:#x}={O.describe(w)}' for a, w in words[min(idx) - 1:max(idx) + 2])
            val = run[0][0] if which == 'cst_lo' else run[-1][0] + 8
            return Exp(val, f'{F.img()} .got words {desc}: the program GOT words run from {run[0][0]:#x} (g_rec) to {run[-1][0] + 8:#x} (end of the g_quitting word)')
    return f


def e_mu(which):
    def f(F, m, row, line):
        O, D = F.O, F.D
        v, sz = O.sym('_ZN6__asanL14mu_for_globalsE')
        dv = D.sym('_ZN6__asanL14mu_for_globalsE')[0]
        af0m = F.U.text('A/AF0m.v')
        cell = re.search(r'z8 \(ANum (0x[0-9a-f]+)\) 0x0', af0m[af0m.find(f'{v:#x}') - 20:af0m.find(f'{v:#x}') + 40]) if f'{v:#x}' in af0m else None
        dl = F.UD.text('A/AE37.v')
        dm = re.search(r'Hypothesis MU0 : forall ly, cell_lookup \(Tfib_const ly\) \(ANum (0x[0-9a-f]+)\) = Some \(ACell \(ANum 0x[0-9a-f]+\) (\d+) \(AV \(ANum (\d+)\)\)\)', dl)
        base = (f'{F.img()} symtab __asan::mu_for_globals = {v:#x} (size {sz}; donor {dv:#x} = donor lib/A/AE37.v MU0 {dm.group(1) if dm else "?"}); '
                f'lib/A/AF0m.v Tfib_const has {"z8 (ANum %#x) 0x0" % v if cell else "no z8 cell"} at it')
        if which == 'addr':
            return Exp(v if cell else None, base, donor=dv)
        if which == 'w':
            return Exp(8 if cell else None, base + ' (z8 = an 8-byte cell)', donor=int(dm.group(2)) if dm else None)
        return Exp(0 if cell else None, base + ' (value 0; .bss)', donor=int(dm.group(3)) if dm else None)
    return f


def e_sm_key(F, m, row, line):
    O = F.O
    a = ival(m.group('sma'))
    s = [x[2] for x in O.at(a) if re.fullmatch(r'__asan_stack_malloc_\d+', x[2])]
    k = int(s[0].rsplit('_', 1)[1]) if len(s) == 1 else None
    return Exp(k, f'{F.img()} symtab: {a:#x} = {s[0] if s else O.describe(a)} (the class key of an arm is the N of the __asan_stack_malloc_N it maps to)')


def e_ret(F, m, row, line):
    O = F.O
    a = ival(m.group('reta')) if 'reta' in m.groupdict() and m.group('reta') else None
    fn = O.sym('_ZN6__asan11asan_mallocEmPN11__sanitizer18BufferedStackTraceE')
    rets = [x for x in range(fn[0], fn[0] + fn[1], 4) if O.u32(x) == 0x00008067]
    return Exp(rets[0] if rets else None,
               f'{F.img()}: asan_malloc {fn[0]:#x}..{fn[0] + fn[1]:#x}; its `ret` words (0x00008067, jalr x0, 0(ra)) are at {[hex(x) for x in rets]}; '
               f'"asan_malloc\'s ret" (lib/A/AFi0.v:46) = the first')


def e_reg_head(F, m, row, line):
    """skipn N REGx: N = the count of stack regions at the head of the region list (AFhy.v REG0 / AFi1.v REG0K)."""
    U = F.U
    t = U.code('A/AFhy.v')
    hm = re.search(r'Definition REG0 : smem :=\s*\[\s*((?:R_\w+;\s*)+)', t)
    head = [x.strip() for x in hm.group(1).split(';') if x.strip()]
    t1 = U.code('A/AFi1.v')
    hk = re.search(r'Definition REG0K : smem :=\s*\[\s*((?:R_\w+;\s*)+)', t1)
    headk = [x.strip() for x in hk.group(1).split(';') if x.strip()]
    td = F.UD.code('A/AFhy.v')
    dh = re.search(r'Definition REG0 : smem :=\s*\[\s*((?:YP09\.mkRegion \(Some 2%nat\)[^;]*;\s*)+)', td)
    nd = len(re.findall(r'YP09\.mkRegion', dh.group(1))) if dh else None
    ok = len(head) == len(headk) == 3
    return Exp(3 if ok else None,
               f'lib/A/AFhy.v:94 REG0 starts with {len(head)} stack regions [{"; ".join(head)}], lib/A/AFi1.v REG0K with [{"; ".join(headk)}]; '
               f'MREG0 / MKREG0 / SREG0 keep that head (firstn 40 / 43 of REG0 / REG0K, AFi4.v:22,115, AFi9.v:84); the donor REG0 had {nd}',
               donor=nd)


def e_reg_keep(F, m, row, line):
    """firstn N REG0 of SREG0: the donor's N shifted by the growth of REG0's head (1 -> 3 stack regions)."""
    dt = F.UD.code('A/AFi9.v')
    dn = int(re.search(r'Definition SREG0 : smem :=\s*firstn (\d+) REG0', dt).group(1))
    e = e_reg_head(F, m, row, line)
    shift = 3 - e.donor if e.donor is not None and e.value is not None else None
    return Exp(dn + shift if shift is not None else None,
               f'donor lib/A/AFi9.v SREG0 = firstn {dn} REG0 ++ ..; the region list REG0 grew at its head from {e.donor} to 3 stack regions '
               f'(lib/A/AFhy.v:94 [R_bst; R_scr1; R_nofr]), so the same regions are the first {dn} + {shift} = {dn + shift if shift is not None else "?"}; '
               f'MREG0 shows the same shift (firstn 38 -> 40)', donor=dn)


def e_img_hull(which):
    def f(F, m, row, line):
        return Exp(F[which][0], F[which][1])
    return f


def e_ab12(F, m, row, line):
    O = F.O
    lo, hi = O.sec('.text')
    return Exp((hi - lo) // 4 if (hi - lo) % 4 == 0 else None,
               f'{F.img()} section header .text [{lo:#x}, {hi:#x}): size {hi - lo:#x} / 4 = {(hi - lo) // 4} words (header line of lib/A/AB12.v: whole .text)',
               donor=(lambda d: (d[1] - d[0]) // 4)(F.D.sec('.text')))


def e_phdr(F, m, row, line):
    ph = [p for p in F.O.phdrs if p[0] == 'PT_PHDR']
    dp = [p for p in F.D.phdrs if p[0] == 'PT_PHDR']
    return Exp(ph[0][1] if len(ph) == 1 else None, f'{F.img()} program headers: PT_PHDR p_vaddr = {ph[0][1]:#x}',
               donor=dp[0][1] if dp else None)


def e_itab(F, m, row, line):
    """startup_plan_tfib_ranges (addr, count): AB1m.v:27-29 IT0 = mk_itab_ranges TSEGS ranges, sound for ANY ranges
    (mk_itab_ranges_sound decodes the image's own words); the count only bounds coverage. Measured: the range lies in
    .text and starts on an instruction."""
    O = F.O
    a = ival(m.group('ia'))
    lo, hi = O.sec('.text')
    return Exp(None, f'IT0 (lib/A/AB1m.v:27-29) = mk_itab_ranges TSEGS startup_plan_tfib_ranges, itab_sound by mk_itab_ranges_sound for any '
                     f'(addr, count): the table is decoded from the image words; range at {a:#x} must lie in .text [{lo:#x}, {hi:#x})',
               lo=1, hi=(hi - a) // 4 if lo <= a < hi else -1)


def jimm(w):
    return ((w >> 31) & 1) << 20 | ((w >> 12) & 0xff) << 12 | ((w >> 20) & 1) << 11 | ((w >> 21) & 0x3ff) << 1


def e_jal(F, m, row, line):
    """Jal 1 off of D_<k>: decode_any (word) = Some (Jal 1 off, 4): off = the J-immediate of the IMAGE word at the
    pc of the sibling fact F_<k> (fetch_word tfibsegs pc = Some word) of the same file; the call target is named."""
    O = F.O
    k = re.search(r'D_([0-9a-f]+)', row[7]).group(1)
    code = F.U.code(f'A/{row[5]}')
    fm = re.search(r'Lemma F_' + k + r' : fetch_word tfibsegs \((0x[0-9a-f]+)%bv : word\) = Some \((0x[0-9a-f]+)%bv : bv 32\)', code)
    if not fm:
        return Exp(None, f'no fetch fact F_{k} in lib/A/{row[5]}')
    pc, wf = int(fm.group(1), 16), int(fm.group(2), 16)
    wi = O.u32(pc)
    imm = jimm(wi)
    sv = imm - (1 << 21) if imm >> 20 else imm
    tgt = pc + sv
    return Exp(imm if (wi & 0xfff) == 0x0ef else None,
               f'{F.img()} word at {pc:#x} (lib/A/{row[5]} F_{k}) = {wi:#010x} (the fact writes {wf:#010x}): jal ra, J-immediate {imm} = {sv:+#x}, '
               f'target {tgt:#x} = {O.describe(tgt)}')


def e_depot(which):
    def f(F, m, row, line):
        v = F[which]
        donor = {'depot_ids': 4097, 'depot_ids1': 4098, 'depot_tot': 127070}.get(which)
        return Exp(v[0], v[1], donor=donor)
    return f


def e_shadow_run(which):
    """zero-shadow run ends from the asan_globals descriptors (beg, size, size_with_redzone) of the image."""
    def f(F, m, row, line):
        O = F.O
        G = asan_globals(O)
        rlo, rhi = O.sec('.rodata')
        if which == 'ro_first':
            ro = sorted(g[0] for g in G if rlo <= g[0] < rhi)
            return Exp(ro[0], f'{F.img()} asan_globals: {len(G)} descriptors, {len(ro)} in .rodata; the lowest .rodata global starts at {ro[0]:#x} '
                              f'(the zero-shadow run [0x10000, it) of lib/A/AF0m.v)')
        if which == 'ro_hull':
            ro = sorted(g[0] for g in G if rlo <= g[0] < rhi)
            Z = ro[0]
            so = F.shadow_off
            # largest p + n whose 8-aligned shadow hull end (shadow(p + n - 1) / 8 * 8 + 8) is <= shadow(Z)
            best = max(x for x in range(Z - 256, Z + 1, 8) if ((so + (x - 1) // 8) // 8) * 8 + 8 <= so + Z // 8)
            return Exp(best, f'run [0x10000, {Z:#x}) (lowest .rodata asan global); the largest p + n whose 8-aligned shadow hull '
                             f'(shadow(p + n - 1) / 8 * 8 + 8) stays <= shadow({Z:#x}) = {so + Z // 8:#x} is {best:#x}')
        bss = sorted((g for g in G if g[0] >= O.sec('.bss')[0]), key=lambda g: g[0])
        if which == 'bss_last_end':
            g = bss[-1]
            return Exp(g[0] + g[2], f'{F.img()} asan_globals: last .bss global {g[3]} beg {g[0]:#x} size_with_redzone {g[2]}: its redzone ends at '
                                    f'{g[0] + g[2]:#x}; the zero-shadow run [{g[0] + g[2]:#x}, 0x606000) of lib/A/AF0m.v starts there')
        if which == 'bss_first_beg_end':
            g = bss[0]
            return Exp(g[0] + g[1], f'{F.img()} asan_globals: first .bss global {g[3]} beg {g[0]:#x} size {g[1]}: its poisoned redzone starts at '
                                    f'{g[0] + g[1]:#x}, the end of the zero-shadow run [0xada00, it) of lib/A/AF0m.v')
        if which == 'bss_p_lo':
            g = bss[-1]
            start = g[0] + g[2]
            so = F.shadow_off
            mn = min(x for x in range(start, start + 4096) if ((so + x // 8) // 8) * 8 >= so + start // 8)
            ae = F.U.code('A/AE3m.v')
            buf = int(re.search(r'Definition STDOUT_BUFA : Z := (0x[0-9a-f]+)', ae).group(1), 16)
            bs = [s for s in O.covering(buf) if s[2] == 'buf']
            return Exp(None, f'Lemma bss_shadow_facts (Qed) needs the 8-aligned shadow hull of [p, p + n) inside the run [{start:#x}, 0x606000): '
                             f'p >= {mn:#x}; its only users (lib/A/AD1o.v:213-214) pass STDOUT_BUFA {buf:#x} (lib/A/AE3m.v:33; symtab: '
                             f'{"buf %#x+%#x" % (bs[0][0], buf - bs[0][0]) if bs else O.describe(buf)}): a premise bound in [{mn:#x}, {buf:#x}] '
                             f'is true and keeps the users', lo=mn, hi=buf)
    return f


def e_sink0(F, m, row, line):
    """A_RWA / A_WB / A_TRAILER / A_PATH := 0: the donor strings are absent from our image and nothing in
    fuzz_command's lib/A reads the four fields (ak_path ak_mode ak_rwa ak_trailer) of tfib_K."""
    O, D, U = F.O, F.D, F.U
    name = re.search(r'Definition (\w+)', row[7]).group(1)
    dv = int(row[10], 16) if row[10] else None
    s = D.cstr(dv, 64) if dv else b''
    lo, hi = O.sec('.rodata')
    data = O.read(lo, hi - lo)
    found = s + b'\0' in data and (data.find(b'\0' + s + b'\0') >= 0 or data.startswith(s + b'\0'))
    rx = re.compile(r'\b(astdio_env|asink_at|aenv_addr|astr_addr|aopen_env_laws|afopen_spec|aunlink_spec|afwrite_spec|ak_path|ak_mode|ak_rwa|ak_trailer)\b')
    if not hasattr(F, '_sink_users'):
        users = []
        cand = set()
        for nd in ('astdio_env', 'asink_at', 'aenv_addr', 'astr_addr', 'aopen_env_laws', 'afopen_spec', 'aunlink_spec',
                   'afwrite_spec', 'ak_path', 'ak_mode', 'ak_rwa', 'ak_trailer'):
            cand.update(U.files_with(nd, 'A'))
        for rel in sorted(cand):
            for k, l in enumerate(U.code_lines(rel), 1):
                if rx.search(l):
                    users.append(f'lib/{rel}:{k}')
        F._sink_users = users
    users = F._sink_users
    ok = (not found) and not users
    return Exp(0 if ok else None,
               f'donor string at {dv:#x} = {s!r}: in {F.img()} .rodata as its own NUL-terminated string: {found}; by-use grep of '
               f'astdio_env|asink_at|aenv_addr|astr_addr|aopen_env_laws|afopen_spec|aunlink_spec|afwrite_spec|ak_path|ak_mode|ak_rwa|ak_trailer '
               f'over lib/A: {len(users)} uses {users[:3]} (fuzz_command\'s chain takes aclosed_stdio_env, lib/Reusable/YE00.v:112); '
               f'{name} is a placeholder no statement reads')


def e_runto(F, m, row, line):
    """runto <pc> of a run that must stop only at its own end: the unit's sentinel pc, the one lib/A/AFi0.v:48
    st_RET uses, which must lie in no PT_LOAD of the image; and the by-use grep of the defined name."""
    O = F.O
    s0 = re.search(r'Definition st_RET \(ss : sstate\) : sstate := runto (0x[0-9a-f]+) ss', F.U.code('A/AFi0.v') or '')
    sv = int(s0.group(1), 16) if s0 else None
    inload = [l for l in O.loads if sv is not None and l[0] <= sv < l[0] + l[1]]
    name = re.search(r'Definition (\w+)', row[7]).group(1)
    users = []
    rx = re.compile(r'(?<![\w\'])' + name + r'(?![\w\'])')
    for rel in F.U.files_with(name, 'A'):
        for k, l in enumerate(F.U.code_lines(rel), 1):
            if rx.search(l) and not (rel == f'A/{row[5]}' and k == int(row[6])):
                users.append(f'lib/{rel}:{k}')
    return Exp(sv if (sv is not None and not inload) else None,
               f'the unit\'s run-to-the-end sentinel is lib/A/AFi0.v:48 st_RET runto {sv:#x}; {sv:#x} lies in no PT_LOAD of {F.img()} '
               f'(code ends at {O.sec(".text")[1]:#x}), so runto never stops on a pc and the run goes to its own end; MK_NR is computed by '
               f'vm_compute; by-use grep of {name} over lib/A: {len(users)} uses {users[:3]}')


def e_sm_lb(F, m, row, line):
    """map_zoneN (AFjm.v:427-430) restates map_zone (AFjm.v:418-420) with numbers: its low-zone SMv lower bound is
    kLowShadowBeg + TFIB_IMG_END / 8; sm_bounds (AFk1.v:696) restates map_zoneN's."""
    yg0f = F.U.text('Reusable/YG0f.v')
    klb = int(re.search(r'Definition kLowShadowBeg : Z := (0x[0-9a-f]+)', yg0f).group(1), 16)
    top = F['img_top'][0]
    b = klb + top // 8
    code = F.U.code('A/AFjm.v')
    ok = 'kLowShadowBeg + TFIB_IMG_END / 8 <= SMv' in code
    return Exp(b if ok else None,
               f'lib/A/AFjm.v:418-420 map_zone states kLowShadowBeg + TFIB_IMG_END / 8 <= SMv in the low zone, which map_zoneN restates '
               f'with numbers (its other numbers 6316032 = TFIB_IMG_END, 2147446784 = kLowShadowBeg, 2415881728 = kLowShadowEnd): '
               f'kLowShadowBeg {klb:#x} (lib/Reusable/YG0f.v:21) + {top:#x} ({F.img()} image top) / 8 = {b:#x} = {b}; a smaller number is '
               f'a true weaker bound (both lemmas are closed by Qed), here the donor bound moved as a shadow address')


def e_ev_lib(F, m, row, line):
    t = F.U.text(f'A/{row[5]}')
    mm = re.search(r"measured worst case is ([\d,]+)", t) or re.search(r'EV_LIB = (\d+) as in lib/A/ACfn\.v', t)
    acfn = F.U.text('A/ACfn.v')
    wc = int(re.search(r"measured worst case is ([\d,]+)", acfn).group(1).replace(',', ''))
    yg00 = F.U.text('Reusable/YG00.v')
    evmax = int(re.search(r'Definition EV_MAX : Z := (\d+)', yg00).group(1))
    return Exp(None, f'EV_LIB is the per-call event budget of the program contract (a model parameter, not an image count): lib/A/ACfn.v:27-28 '
                     f'records fuzz_command\'s measured worst case {wc} events per call; the budget must be >= {wc} and <= EV_MAX {evmax} '
                     f'(lib/Reusable/YG00.v:38); ACfl.v / ACfn.v carry the same 2900', lo=wc, hi=evmax, donor=2000)


def e_topf(which):
    def f(F, m, row, line):
        t = F.U.code('A/AD1v.v')
        d = re.search(r'Definition TOPF \(usp : Z\) : Z := (\d+) \* \(\(usp - (\d+) \+ (\d+)\) / (\d+)\)', t)
        pg, slack, pm1 = int(d.group(1)), int(d.group(2)), int(d.group(3))
        if which == 'slack':
            if 'Definition TOPF' in line:
                return Exp(None, f'TOPF\'s own slack (lib/A/AD1v.v:20) is a model parameter: any slack >= 0 keeps TOPF <= the entry stack page '
                                 f'top (lib/A/AD1p.v:74-80 TOPF_le_page_top, Qed, discharges stk_top at entry AD1p.v:176-179); a slack >= 4096 '
                                 f'would put TOPF at or below usp', lo=0, hi=pm1)
            return Exp(slack if pg == 4096 else None,
                       f'the slack of lib/A/AD1v.v:20 TOPF is {slack} (this lemma restates TOPF)')
        if which == 'up':
            return Exp(pm1 - slack, f'TOPF usp <= usp - {slack} + {pm1} = usp + {pm1 - slack} (ceiling, AD1v.v:20; Lemma TOPF_range, Qed)')
        if which == 'eq_up':
            return Exp(None, f'TOPF_eq (Qed): t a page multiple in [usp - {slack}, usp + B] is TOPF usp iff B <= {pm1 - slack} '
                             f'(TOPF usp is the least page multiple >= usp - {slack})', lo=0, hi=pm1 - slack)
    return f


def e_c_off(F, m, row, line):
    t = F.U.code(f'A/{row[5]}')
    v = re.findall(r'b = Some aMAP /\\ 0 <= lo /\\ hi <= (\d+)', t)
    z = re.findall(r'SOff aMAP (\d+)', F.U.code('A/AFjz.v') or '')
    return Exp(int(v[0]) if v else None,
               f'the map\'s first {v[0] if v else "?"} bytes are the aMAP region of the same file (lib/A/AFjo.v:637 b = Some aMAP /\\ hi <= {v[0] if v else "?"}); '
               f'the user block starts at map + {z[0] if z else "?"} (lib/A/AFjz.v:828 SOff aMAP {z[0] if z else "?"}); Lemma runs_off_stack is closed by Qed')


def e_atom0(F, m, row, line):
    if row[5] == 'AD1p.v':
        y = F.U.code('Reusable/YP08.v')
        ok = 'Definition R_hdr (two : bool) : region :=\nmkRegion (Some 0%nat) 0 (if two then 24 else 16)' in y
        return Exp(0 if ok else None, 'start-up env: lib/Reusable/YP08.v:267-268 R_hdr is based at atom Some 0%nat (the entry sp)')
    y = F.U.code('A/AD1y.v')
    ok = '| Some 0%nat => (- 65536 <=? r_wlo r) && (r_whi r <=? 0)' in y
    return Exp(0 if ok else None, 'driver env: lib/A/AD1y.v:41-44 drv_win_ok windows are based at atom Some 0%nat = usp (AD1y.v:49 in_wrange_drv)')


def e_hdr(F, m, row, line):
    y = F.U.code('Reusable/YP08.v')
    mm = re.search(r'Definition R_hdr \(two : bool\) : region :=\s*mkRegion \(Some 0%nat\) 0 \(if two then (\d+) else (\d+)\)', y)
    return Exp(int(mm.group(1)), f'lib/Reusable/YP08.v:267-270 R_hdr true = [sp, sp + {mm.group(1)}): argc, argv[0], argv[1] words (3 x 8)')


def e_trace_region(slot):
    return lambda F, m, row, line: Exp(F[slot][0], F[slot][1] + '; lib/A/AFhy.v:84-87 R_bst = the caller\'s BufferedStackTrace at atom 11 = pT')


def e_ro_wr(F, m, row, line):
    return Exp(0, 'R_bst is read-only (wlo = whi = 0): the trace object is the caller\'s, asan_malloc only reads it (RtDDefs.v:106-111); '
                  'chunk offsets 0 / 8 and the length chunk\'s atom offset 0 follow astrace_at')


def e_aln_log2(F, m, row, line):
    v = F['tr_al'][0]
    return Exp(v.bit_length() - 1 if v else None, f'mkAF lo hi k: k = log2 of the alignment (AFhy.v:50 sp 16 -> 4, :53 4096 -> 12); trace object 8-aligned ({F["tr_al"][1]}) -> 3')


def e_gfill(name):
    return lambda F, m, row, line: Exp(F[name][0], F[name][1])


def e_one_min(F, m, row, line):
    L = F.UD.code_lines('A/AD1g.v') or []
    hits = [i for i, l in enumerate(L, 1) if 'let w := Z.max 1 (Z.of_nat (c_w c)) in' in l]
    return Exp(1 if hits else None, 'a cell covers at least one byte (w = Z.max 1 (c_w c)), a model constant; cmd_xowned restates the donor\'s '
                  f'xowned, whose text is the same at donor lib/A/AD1g.v:{hits[0] if hits else "?"}', donor=1 if hits else None)


# -------------------------------------------------------------------------------------------------- the rules
def make_rules(F):
    E = fact
    S = []
    add = lambda *a, **k: S.append(Rule(*a, **k))
    # ISA / ABI
    add('FCSR-FRM', r"Z\.land \(Z\.shiftr \(bv_unsigned \(@fp_csr fx'?\)\) (?P<frm_shift>\d+)\) (?P<frm_mask>\d+) = (?P<rne>\d+)",
        {'frm_shift': 'frm_shift', 'frm_mask': 'frm_mask', 'rne': 'rne'})
    add('FREG-FA0', r"forall k0 : bv (?P<fregbits>\d+), bv_unsigned k0 <> (?P<fa0>\d+)", {'fregbits': 'fregbits', 'fa0': 'fa0'})
    add('XREG-WIDTH', r"bvmap (?P<xregbits>\d+) word", {'xregbits': 'xregbits'})
    add('XREG-WIDTH', r"forall r : bv (?P<xregbits>\d+),", {'xregbits': 'xregbits'})
    add('REG-SP', r"r <> (?P<sp>\d+)%bv -> getr regsI r = getr regs0 r", {'sp': 'sp'})
    add('REG-SP', r"getr regs(?:I|') (?P<sp>\d+) = w64 \(sp0 - IFRAME\)", {'sp': 'sp'})
    add('REG-SP', r"(?P<sp>\d+)%bv \(SOff (?P<atom_sp>\d+) \(- IFRAME\)\)", {'sp': 'sp', 'atom_sp': 'atom_sp'})
    add('REG-SP', r"sr_get \(ss_regs ss\) (?P<sp>\d+)%bv = SOff (?P<atom_sp>\d+) \(- IFRAME\)", {'sp': 'sp', 'atom_sp': 'atom_sp'})
    add('REG-SP', r"mkRegion \(Some (?P<atom_sp>\d+)%nat\) \(- (?:MALLOC_IN_STK|IFRAME)\)", {'atom_sp': 'atom_sp'})
    add('REG-TP', r"(?P<tp>\d+)%bv \(SLit TFIB_TP\)", {'tp': 'atom_tp'})
    add('REG-TP', r"sr_get \(ss_regs ss\) (?P<tp>\d+)%bv = SLit TFIB_TP", {'tp': 'atom_tp'})
    add('REG-A1', r"getr regs0 (?P<a1>\d+)\)", {'a1': 'a1'})
    add('REG-A1', r"\((?P<atom_a1>\d+)%nat, mkAF kHighMemBeg kHighMemEnd (?P<aln>\d+)\)", {'atom_a1': 'atom_a1', 'aln': e_aln_log2})
    add('TRACE-REGION', r"mkRegion \(Some (?P<atom_a1>\d+)%nat\) (?P<z>\d+) (?P<tr_buf>\d+) (?P<w0>\d+) (?P<w1>\d+) \[YP09\.mkChunk (?P<z__2>\d+) "
        r"\(CVal (?P<wordb>\d+) \(SOff (?P<atom_a1__2>\d+) (?P<tr_buf__2>\d+)\)\); YP09\.mkChunk (?P<tr_len>\d+) \(CVal (?P<wordb__2>\d+) "
        r"\(SOff aLEN (?P<z__3>\d+)\)\)\]",
        {'atom_a1': 'atom_a1', 'z': E('zero'), 'tr_buf': e_trace_region('tr_buf'), 'w0': e_ro_wr, 'w1': e_ro_wr, 'wordb': 'wordb',
         'tr_len': e_trace_region('tr_len')})
    add('TRACE-REGION', r"Nat\.eqb k (?P<atom_a1>\d+) && \((?P<z>\d+) <=\? (?:lo|YP09\.r_lo r)\) && \((?:hi|YP09\.r_hi r) <=\? (?P<tr_obj>\d+)\)",
        {'atom_a1': 'atom_a1', 'z': 'zero', 'tr_obj': 'tr_obj'})
    add('TRACE-REGION', r"b = Some (?P<atom_a1>\d+)%nat /\\ (?P<z>\d+) <= lo /\\ hi <= (?P<tr_obj>\d+)", {'atom_a1': 'atom_a1', 'z': 'zero', 'tr_obj': 'tr_obj'})
    # the caller's trace object (RtDDefs.v astrace_at / amalloc_inner_realizes)
    add('TRACE-OBJ', r"\((?P<tr_min>\d+) <= length (?:ch|tr) <= (?P<tr_max>\d+)\)%nat /\\ pT mod (?P<tr_al>\d+) = (?P<z>\d+) /\\ pT \+ (?P<tr_buf>\d+) "
        r"\+ (?P<tr_frame>\d+) \* (?P<tr_max__2>\d+) <= ly_stk_hi ly",
        {'tr_min': 'tr_min', 'tr_max': 'tr_max', 'tr_al': 'tr_al', 'z': 'zero', 'tr_buf': 'tr_buf', 'tr_frame': 'tr_frame'})
    add('TRACE-OBJ', r"val_mem tfibsegs \(mrestrict \(w_H W\) mem0\) pT (?P<wordb>\d+) \(pT \+ (?P<tr_buf>\d+)\)", {'wordb': 'wordb', 'tr_buf': 'tr_buf'})
    add('TRACE-OBJ', r"\(pT \+ (?P<tr_len>\d+)\) (?P<wordb>\d+) \(Z\.of_nat \(length tr\)\)", {'tr_len': 'tr_len', 'wordb': 'wordb'})
    add('TRACE-OBJ', r"\(pT \+ (?P<tr_buf>\d+) \+ (?P<tr_frame>\d+) \* Z\.of_nat i\) (?P<wordb>\d+) \(nth i tr (?P<z>\d+)\)",
        {'tr_buf': 'tr_buf', 'tr_frame': 'tr_frame', 'wordb': 'wordb', 'z': 'zero'})
    add('TRACE-OBJ', r"pT \+ (?P<tr_obj>\d+) <=", {'tr_obj': 'tr_obj'})
    add('TRACE-OBJ', r"pT \+ (?P<tr_buf>\d+) \+ (?P<tr_frame>\d+) \* Z\.of_nat i \+ Z\.of_nat k", {'tr_buf': 'tr_buf', 'tr_frame': 'tr_frame'})
    add('TRACE-OBJ', r"\(k < (?P<wordb>\d+)\)%nat", {'wordb': 'wordb'})
    add('TRACE-OBJ', r"/\\ (?P<z>\d+) <= pT \+", {'z': 'zero'})
    add('OWNED-EXTENT', r"ly_C ly \+ (?P<c_ext>\d+)", {'c_ext': 'c_ext'})
    # widths
    add('WIDTH', r"(?P<z>\d+) <= v < (?P<byte_card>\d+)", {'z': 'zero', 'byte_card': 'byte_card'})
    add('WIDTH', r"rdword \(aview tfibsegs H mem\) a = Some v -> val_mem tfibsegs \(mrestrict H mem\) a (?P<wordb>\d+) v", {'wordb': 'wordb'})
    add('WIDTH', r"rd32 \(aview tfibsegs H mem\) a v -> val_mem tfibsegs \(mrestrict H mem\) a (?P<w32b>\d+) v", {'w32b': 'w32b'})
    add('WIDTH', r"Z_to_bv (?P<xlen>\d+) ", {'xlen': 'xlen'})
    add('WIDTH', r"(?:\ba|usp \+ \d+|Z\.of_nat k) <=? (?P<two>\d+) \^ (?P<xlen>\d+)", {'two': 'two', 'xlen': 'xlen'})
    add('WIDTH', r"\(a - a mod (?P<wordb>\d+)\)", {'wordb': 'wordb'})
    add('WIDTH', r"\(snd r \+ (?P<g7>\d+)\) / (?P<g8>\d+)\)", {'g7': 'shadow_gran_m1', 'g8': 'shadow_gran'})
    add('WIDTH', r"MSv / (?P<g8>\d+)\)", {'g8': 'shadow_gran'})
    # start-up certificate (generated lib/A/AB01.v)
    add('GEN-AVIS', r"\(epg (?P<pv>\d+), ELit (?P<pl>\d+)\)", {'pv': e_epg_pair('var'), 'pl': e_epg_pair('len')})
    add('GEN-HEAD', r"Definition eDM : expr := epg (?P<v0>\d+)", {'v0': e_head(0, 'var')})
    add('GEN-HEAD', r"mk eDM (?P<l0>\d+) KRW; mk eGV (?P<l1>\d+) KRW; mk eSB (?P<l2>\d+) KRWLAZY; mk eNB (?P<l3>\d+) KRW",
        {'l0': e_head(0, 'len'), 'l1': e_head(1, 'len'), 'l2': e_head(2, 'len'), 'l3': e_head(3, 'len')})
    add('GEN-HEAD', r"dm eDM (?P<l>\d+) KRW", {'l': e_eDM_len})
    add('GEN-HEAD', r"wzp dDM = \(u eDM, (?P<l>\d+)\)", {'l': e_eDM_len})
    add('GEN-KRANGE', r"KRange \(EVar (?P<kv>\d+)\) (?P<klo>\d+) (?P<khi>\d+)", {'kv': e_krange('var'), 'klo': e_krange('lo'), 'khi': e_krange('hi')})
    add('GEN-MAPIDX', r"firstn \(length \(a_maps ch\) - (?P<fx>\d+)\) \(skipn (?P<hd>\d+) \(a_maps ch\)\)", {'fx': e_musl('fixed'), 'hd': e_musl('head')})
    add('GEN-MAPIDX', r"(?:\(|<> )(?P<hd>\d+) \+ length \(musl_maps ch\) \+", {'hd': e_musl('head')})
    add('GEN-MAPIDX', r"\(i <> (?P<k2>\d+)\)%nat -> \(i <> (?P<k3>\d+)\)%nat", {'k2': e_musl('known2'), 'k3': e_musl('known3')})
    add('GEN-EAGER', r"a_eager ch <= (?P<eg>\d+)", {'eg': e_eager})
    add('IMG-SHADOW', r"kn_vis TFIB ch \(ELit (?P<b>\d+)\) (?P<lo>0x[0-9a-f]+) (?P<len>0x[0-9a-f]+)", {'b': 'elit0', 'lo': 'img_sh_lo', 'len': 'img_sh_len'})
    # start-up stack / driver frame
    add('STARTUP-STACK', r"bv_unsigned \(ew E (?P<a0>\d+)\) (?:=|<=) usp", {'a0': e_atom0})
    add('STARTUP-STACK', r"usp \+ (?P<hdr>\d+) <=", {'hdr': e_hdr})
    add('STARTUP-STACK', r"usp <= a < usp \+ (?P<hdr>\d+)", {'hdr': e_hdr})
    add('TOPF', r"(?P<pg>\d+) \* \(\(usp - (?P<sl>\d+) \+ (?P<pm1>\d+)\) / (?P<pg__2>\d+)\)", {'pg': 'page', 'sl': e_topf('slack'), 'pm1': 'page_m1'})
    add('TOPF', r"usp - (?P<sl>\d+) <= t <= usp \+ (?P<equp>\d+) -> t mod (?P<pg>\d+) = (?P<z>\d+)", {'sl': e_topf('slack'), 'equp': e_topf('eq_up'), 'pg': 'page', 'z': 'zero'})
    add('TOPF', r"usp - (?P<sl>\d+) <= TOPF usp <= usp \+ (?P<up>\d+)", {'sl': e_topf('slack'), 'up': e_topf('up')})
    # program statics (DWARF, symtab, asan_globals)
    add('GI-IVS', r"\(CmdGlob\.(?P<gb>A_G_REC) \+ (?P<glo>\d+), CmdGlob\.A_G_REC \+ (?P<ghi>\d+)\)", {'glo': e_gi_slot('lo'), 'ghi': e_gi_slot('hi')})
    add('GI-IVS', r"\(CmdGlob\.(?P<gb>A_REC_SPILL|A_G_QUITTING), CmdGlob\.(?:A_REC_SPILL|A_G_QUITTING) \+ (?P<ghi>\d+)\)", {'ghi': e_gi_slot('hi')})
    add('GI-IVS', r"rd a = Some (?P<z>\d+)", {'z': 'zero'})
    add('GI-IVS', r"gi_byte a -> (?P<blo>0x[0-9a-f]+) <= a < (?P<top>0x[0-9a-f]+)", {'blo': e_bss_lo, 'top': 'img_top'})
    add('GI-IVS', r"a <> (?P<z>\d+) -> ~ inFP FPC a", {'z': 'zero'})
    add('GI-IVS', r"\(a < (?P<plo>0x[0-9a-f]+) \\/ (?P<phi>0x[0-9a-f]+) <= a\)", {'plo': e_pg_hull('lo'), 'phi': e_pg_hull('hi')})
    add('DRV-IVS', r"\(0x5e3710, (?P<se>0x[0-9a-f]+)\); \((?P<er>0x[0-9a-f]+), 0x5e4540\)", {'se': e_drv('statics_end'), 'er': e_drv('errno')})
    add('DRV-IVS', r"\(0x5e3710 <= a < (?P<se>0x[0-9a-f]+)\) \\/ \((?P<er>0x[0-9a-f]+) <= a < 0x5e4540\)", {'se': e_drv('statics_end'), 'er': e_drv('errno')})
    add('CMDB-CELL', r"as_shadow_cell := (?P<c>0x[0-9a-f]+)", {'c': e_cmdb('shadow')})
    add('CMDB-CELL', r"as_uar_cell := (?P<c>0x[0-9a-f]+)", {'c': e_cmdb('uar')})
    add('GOT-WORD', r"as_got_shadow := (?P<c>0x[0-9a-f]+)", {'c': e_cmdb('got_shadow')})
    add('GOT-WORD', r"as_got_uar := (?P<c>0x[0-9a-f]+)", {'c': e_cmdb('got_uar')})
    add('CMDB-CELL', r"as_junk := fun _ => \[\(ANum (?P<j>0x[0-9a-f]+), (?P<jl>\d+)\)\]", {'j': e_cmdb('junk'), 'jl': e_cmdb('junklen')})
    add('GOT-WORD', r"\(fst r \+ snd r <=\? (?P<lo>0x[0-9a-f]+)\) \|\| \((?P<hi>0x[0-9a-f]+) <=\? fst r\)", {'lo': e_cmdb('cst_lo'), 'hi': e_cmdb('cst_hi')})
    add('OWNED-EXTENT', r"\| (?:YG0f\.AT|AC|AQ|ANB|ASB|AD) o => \((?P<z>\d+) <=\? o\)", {'z': 'zero'})
    add('OWNED-EXTENT', r"\| AC o => \(0 <=\? o\) && \(o \+ w <=\? (?P<c>\d+)\)", {'c': 'c_ext'})
    add('OWNED-EXTENT', r"\| AD o => \(0 <=\? o\) && \(o \+ w <=\? (?P<d>\d+)\)", {'d': 'd_ext'})
    add('OWNED-EXTENT', r"let w := Z\.max (?P<one>\d+) \(Z\.of_nat \(c_w c\)\)", {'one': e_one_min})
    add('MU-CELL', r"cell_lookup \(Tfib_const ly\) \(ANum (?P<a>0x[0-9a-f]+)\) = Some \(ACell \(ANum (?P<a__2>0x[0-9a-f]+)\) (?P<w>\d+) \(AV \(ANum (?P<v>\d+)\)\)\)",
        {'a': e_mu('addr'), 'w': e_mu('w'), 'v': e_mu('v')})
    add('STACK-MALLOC-KEY', r"cid =\? (?P<k>\d+) then (?P<sma>0x[0-9a-f]+)", {'k': e_sm_key})
    add('ASAN-MALLOC-RET', r"Definition A_MALLOC_RET : Z := (?P<r>0x[0-9a-f]+)", {'r': e_ret})
    add('ASAN-MALLOC-RET', r"ss_pc ss = (?P<r>0x[0-9a-f]+) \\/ ss_pc ss = 0x[0-9a-f]+\)", {'r': e_ret})
    add('REGION-HEAD', r"skipn (?P<n>\d+) (?:REG0K?|MREG0|MKREG0|SREG0)\b", {'n': e_reg_head})
    add('REGION-HEAD', r"firstn (?P<n>\d+) REG0 \+\+", {'n': e_reg_keep})
    add('AMAP-PREFIX', r"\(mb \+ (?P<o>\d+) <= a < mb \+ MSv\)", {'o': e_c_off})
    # NON-ADDRESS-CHANGED families
    add('TEXT-WORDS', r"Definition TFIB_TEXT_N : nat := (?P<n>\d+)", {'n': e_ab12})
    add('PHDR', r"ph_addr_z := (?P<p>0x[0-9a-f]+)", {'p': e_phdr})
    add('ITAB-RANGES', r"\((?P<ia>0x[0-9a-f]+), (?P<ic>\d+)%nat\)", {'ic': e_itab}, files=r'^AB05\.v$')
    add('JAL-DECODE', r"decode_any \((?P<jw>0x[0-9a-f]+)%bv : bv 32\) = Some \(Jal 1 (?P<off>\d+), 4%Z\)", {'off': e_jal})
    add('EV-BUDGET', r"Definition EV_LIB : Z := (?P<e>\d+)", {'e': e_ev_lib})
    add('DEPOT-BOUND', r"depot_ids S'? <= (?P<n>\d+)\.?$", {'n': e_depot('depot_ids')})
    add('DEPOT-BOUND', r"depot_ids S' <= (?P<n>\d+) ->", {'n': e_depot('depot_ids1')})
    add('DEPOT-BOUND', r"\(a(?:N|HD|ID|NL), mkAF (?P<lo>\d+) (?P<n>\d+) 0\)", {'n': e_depot('depot_ids')})
    add('DEPOT-BOUND', r"1 <= nD <= (?P<n>\d+)", {'n': e_depot('depot_ids')})
    add('DEPOT-BOUND', r"2 <= TOT <= (?P<t>\d+)", {'t': e_depot('depot_tot')})
    add('DEPOT-BOUND', r"\(aTOT, mkAF 2 (?P<t>\d+) 0\)", {'t': e_depot('depot_tot')})
    add('FREE-ARRAY', r"SB \+ 24 \* 2 \^ 32 \+ (?P<k>\d+) /\\ b mod 8192", {'k': lambda F, m, r, l: Exp(F['kfao'][0], F['kfao'][1], donor=None)})
    add('FREE-ARRAY', r"0 <= CPv < 2 \^ (?P<e>\d+)", {'e': lambda F, m, r, l: Exp(F['cp_exp'][0], F['cp_exp'][1], donor=27)})
    add('FREE-ARRAY', r"\(41%nat, mkAF 0 \(2 \^ (?P<e>\d+)\) 0\)", {'e': lambda F, m, r, l: Exp(F['cp_exp'][0], F['cp_exp'][1] + '; the same bound as atom 41 = CPv (header of lib/A/AFgq.v)', donor=27)})
    add('TRACE-OBJ', r"Lemma Hch : \(1 <= length ch <= (?P<tr_max>\d+)\)", {'tr_max': 'tr_max'})
    # image geometry and zero-shadow runs
    add('ZSHADOW-RUN', r"SHADOW_OFF 0x10000 \((?P<z>0x[0-9a-f]+) - 0x10000\)", {'z': e_shadow_run('ro_first')})
    add('ZSHADOW-RUN', r"0x10568 <= p -> p \+ n <= (?P<h>0x[0-9a-f]+)", {'h': e_shadow_run('ro_hull')})
    add('ZSHADOW-RUN', r"SHADOW_OFF (?P<s>0x[0-9a-f]+) \(0x606000 - (?P<s__2>0x[0-9a-f]+)\)", {'s': e_shadow_run('bss_last_end')}, files=r'^AD1o\.v$')
    add('ZSHADOW-RUN', r"(?P<p>0x[0-9a-f]+) <= p -> p \+ n <= 0x606000", {'p': e_shadow_run('bss_p_lo')})
    add('ZSHADOW-RUN', r"SHADOW_OFF 0xada00 \((?P<e>0x[0-9a-f]+) - 0xada00\)", {'e': e_shadow_run('bss_first_beg_end')})
    add('SINK-UNREAD', r"Definition A_(?:RWA|WB|TRAILER|PATH) : Z := (?P<z>\d+)", {'z': e_sink0})
    add('RUNTO-SENTINEL', r"runto (?P<rt>0x[0-9a-f]+) MK_N0", {'rt': e_runto})
    add('SMV-LOWER-BOUND', r"(?P<s>\d+) <= SMv", {'s': e_sm_lb})
    return S
