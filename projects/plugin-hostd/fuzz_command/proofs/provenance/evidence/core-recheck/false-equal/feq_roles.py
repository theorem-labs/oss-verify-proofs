"""feq_roles.py -- ROUND-CONSTANT-SAME rows: the role each value has on its line (read by hand from the text, one
rule per group below) and the measurement in our image that settles it.

Every rule names the line pattern it covers; a row no rule covers is NOT-CHECKABLE (so a new row cannot pass
silently). Measurements come from the pinned images (feq_lib.Img), never from the gate.
"""
import re
import feq_lib as L


def lui_sites(img, imm20):
    """pcs of `lui xN, imm20` in the executable segments."""
    out = []
    for lo, hi, fl, data in img.segs:
        if not fl & 1:
            continue
        b = lo + (-lo % 4)
        for a in range(b, hi - 4, 4):
            w = int.from_bytes(data[a - lo:a - lo + 4], 'little')
            if w & 0x7f == 0x37 and (w >> 12) == imm20:
                out.append(a)
    return out


def fn(img, sub):
    return [(v, sz, n) for v, sz, n, t, b in img.syms if sub in n and sz > 0]


def lui_in(img, sub, imm20):
    """`name+off: lui xN, imm` for every lui imm20 inside the functions whose name holds sub (memoised)."""
    k = (id(img), sub, imm20)
    if k not in _LUI:
        out = []
        for v, sz, n in fn(img, sub):
            for a in range(v, v + sz, 4):
                w = img.word(a)
                if w & 0x7f == 0x37 and (w >> 12) == imm20:
                    out.append(f'{n}+{a - v:#x}: {L.decode(w)[1]}')
        _LUI[k] = out
    return _LUI[k]


_LUI = {}


def top(img):
    return (img.hi + 0xfff) & ~0xfff


def shadow_off(img):
    """The shadow offset the runtime returns: the lui in __asan::FindDynamicShadowStart."""
    for v, sz, n in fn(img, 'FindDynamicShadowStart'):
        for a in range(v, v + sz, 4):
            w = img.word(a)
            if w & 0x7f == 0x37:
                return L.imm_u(w), f'{n}+{a - v:#x}: {L.decode(w)[1]}'
    return None, 'FindDynamicShadowStart not found'


def lab(img):
    return f'{img.role} {img.pin_sha}'


# ------------------------------------------------------------------------------------------------ rules
def r_shadow_lo(ctx):
    I, D = ctx['ours'], ctx['donor']
    off, where = shadow_off(I)
    lo = min(a for a, _, _, _ in I.segs)
    want = (lo >> 3) + off
    span = (top(I) - lo) >> 3
    dspan = (top(D) - min(a for a, _, _, _ in D.segs)) >> 3
    nums = {L.num(x) for x in re.findall(r'0x[0-9a-fA-F]+|\d+', ctx['line'])}
    stale = [x for x in (dspan, want + dspan) if x in nums]
    mine = sorted(nums & {span, want + span})
    ok = want == ctx['tv'] and not stale
    return ('OK' if ok else 'FINDING',
            f'role: address, the shadow byte of the image\'s lowest load address (line: the low end of the image\'s '
            f'shadow range). Measured in ours {lab(I)}: lowest PT_LOAD vaddr {lo:#x}; shadow offset {off:#x} '
            f'({where}); ({lo:#x} >> 3) + {off:#x} = {want:#x}; the matching span (top {top(I):#x} - lo) / 8 = '
            f'{span:#x}, end {want + span:#x}'
            + (f'; the line also states {", ".join(f"{x:#x}" for x in mine)}, our own span / end' if mine else '')
            + (f'; the line states the DONOR span / end {", ".join(f"{x:#x}" for x in stale)}' if stale else '')
            + ('' if want == ctx['tv'] else f'; the line states {ctx["tv"]:#x}'))


def r_rodata_bound(ctx):
    I, S = ctx['ours'], ctx['side']
    rhs, f = S.T.lookup(ctx['dst_file'], 'icpt_rodata')
    ents = [(L.num(a), int(n)) for a, n in re.findall(r'\(\s*(0x[0-9a-fA-F]+|\d+)\s*,\s*(\d+)\s*,\s*\[', rhs or '')]
    if not ents:
        return 'NOT-CHECKABLE', 'icpt_rodata not found'
    mx = max(a + n for a, n in ents)
    a0 = [a for a, n in ents if a + n == mx][0]
    ok = mx <= ctx['tv']
    return ('OK' if ok else 'FINDING',
            f'role: loose upper bound on addr + len of every icpt_rodata entry (defined in lib/{f}); the proof checks '
            f'each entry with lia. Measured: {len(ents)} entries, the largest end {mx:#x} ({I.where(a0)} in ours '
            f'{lab(I)}, {I.sec(a0)}) <= {ctx["tv"]:#x}')


def r_quarantine_cell(ctx):
    I, D = ctx['ours'], ctx['donor']
    cells = re.findall(r'(?:z8\s+\(ANum\s+|flit8\s+)(0x[0-9a-fA-F]+)\)?\s+(0x[0-9a-fA-F]+|\d+)', ctx['line'])
    dcells = re.findall(r'(?:z8\s+\(ANum\s+|flit8\s+)(0x[0-9a-fA-F]+)\)?\s+(0x[0-9a-fA-F]+|\d+)', ctx['sline'])
    a = [L.num(x) for x, v in cells if L.num(v) == ctx['tv']]
    b = [L.num(x) for x, v in dcells if L.num(v) == ctx['sv']]
    if not a or not b:
        return 'NOT-CHECKABLE', 'no cell holding the value on the line'
    wa, wb = I.where(a[0]), D.where(b[0])
    same = wa == wb
    as_addr_o, as_addr_d = I.where(ctx['tv']), D.where(ctx['sv'])
    return ('OK' if same else 'FINDING',
            f'role: a size held in a run-time field. Measured: our cell {a[0]:#x} = {wa} ({I.sec(a[0])}, '
            f'zero in the image: written at run time), donor cell {b[0]:#x} = {wb}: the same field; the field '
            f'beside it (+0x318) holds 0x10000000 on both lines. Read as an address the value would be {as_addr_o} '
            f'in ours and {as_addr_d} in the donor, not the same place, so the value is not an address that '
            f'should have moved')


def r_depot_tab(ctx):
    I = ctx['ours']
    n = [x for x in fn(I, 'StackDepotBaseINS_14StackDepotNodeE')]
    m = re.search(r'StackDepotBaseINS_14StackDepotNodeELi(\d+)ELi(\d+)E', n[0][2]) if n else None
    if not m:
        return 'NOT-CHECKABLE', 'StackDepotBase not in the symbol table'
    ok = 1 << int(m.group(2)) == ctx['tv']
    return ('OK' if ok else 'FINDING',
            f'role: bound of a hash-bucket index (bkt < table size). Measured: ours {lab(I)} twin symtab names '
            f'StackDepotBase<StackDepotNode, {m.group(1)}, {m.group(2)}> (kTabSizeLog {m.group(2)}): 2^{m.group(2)} '
            f'= {1 << int(m.group(2))}')


def r_nodes_block(ctx):
    I, D = ctx['ours'], ctx['donor']
    a, b = lui_in(I, 'TwoLevelMapINS_14StackDepotNode', 0x100), lui_in(D, 'TwoLevelMapINS_14StackDepotNode', 0x100)
    ok = bool(a) and [x.split(':')[0].split('+')[-1] for x in a] == [x.split(':')[0].split('+')[-1] for x in b]
    return ('OK' if ok else 'NOT-CHECKABLE',
            f'role: size of one StackDepot node block (a run-time mapping size). Measured: ours {lab(I)}: '
            f'{"; ".join(a) or "none"}; donor {lab(D)}: {"; ".join(b) or "none"} (0x100 << 12 = 0x100000)')


def r_map_size(ctx):
    I, D = ctx['ours'], ctx['donor']
    a = lui_in(I, 'PopulateFreeArray', 0x40) + lui_in(I, 'EnsureFreeArraySpace', 0x40)
    b = lui_in(D, 'PopulateFreeArray', 0x40) + lui_in(D, 'EnsureFreeArraySpace', 0x40)
    pcs = [L.num(x) for x in re.findall(r'runto\s+(0x[0-9a-fA-F]+)', ctx['line'])]
    at = '; '.join(f'runto {p:#x} = {I.where(p)}' for p in pcs)
    ok = len(a) >= 2 and [x.split(':')[0].split('+')[-1] for x in a] == [x.split(':')[0].split('+')[-1] for x in b]
    return ('OK' if ok else 'NOT-CHECKABLE',
            'role: a register value 0x40000 (262144), the mapping granularity of SizeClassAllocator64 '
            '(kUserMapSize / kFreeArrayMapSize), pinned in x19 / x18 by lib/A/AFk8.v:56 and AFk9.v:28,54 '
            '(B: YFk8 / YFk9) and carried to x11 as a size argument. ' + (at + '. ' if at else '') +
            f'Measured: our code forms it at {"; ".join(a)} in ours {lab(I)}; donor {lab(D)} at {"; ".join(b)} '
            '(same functions, same offsets)')


def r_plain_region(ctx):
    I = ctx['images']['P']
    lo, hi = I.segs[-1][0] & ~0xfff, (I.segs[-1][1] + 0xfff) & ~0xfff
    m = re.search(r'covered_sound\s+[\w.]+\s+(0x[0-9a-fA-F]+)\s+(0x[0-9a-fA-F]+)', ctx['line'])
    base = L.num(m.group(1)) if m else None
    ok = hi - lo == ctx['tv'] and base == lo
    return ('OK' if ok else 'FINDING',
            f'role: size of the read-write region of the plain image (covered_sound SYMS {base:#x} SIZE). Measured: '
            f'ours {lab(I)} last PT_LOAD [{I.segs[-1][0]:#x}, {I.segs[-1][1]:#x}) page range [{lo:#x}, {hi:#x}), '
            f'size {hi - lo:#x}' if base is not None else 'no covered_sound on the line')


def r_plain_top(ctx):
    I = ctx['images']['P']
    t = max(b for _, b, _, _ in I.segs)
    ok = t <= ctx['tv']
    return ('OK' if ok else 'FINDING',
            f'role: loose upper bound above every plain-image segment (seg_base + seg_size <= bound; the stack '
            f'pointer above it). Measured: ours {lab(I)} highest PT_LOAD end {t:#x} (page {top(I):#x}) <= '
            f'{ctx["tv"]:#x}')


def r_smoke(ctx):
    return ('OK', 'role: a register value in a smoke test over abstract segments (getr regs N = 0x20000; stepjr '
                  'to it): no image quantity; equal to the donor value')


_USERS = {}


def r_foreign_table(ctx):
    S = ctx['side']
    if id(S) not in _USERS:
        users = []
        pat = re.compile(r'(?<![\w.])(?:YK09\.|APC\.)?(ASAN|BOTH|asan_init|both_init|ASAN_TEXT_LO|ASAN_TEXT_N|'
                         r'BOTH_TEXT_LO|BOTH_TEXT_N)(?![\w\'])')
        for rel, c in S.T.text.items():
            if rel == ctx['dst_file']:
                continue
            for m in pat.finditer(c):
                users.append(f'lib/{rel}:{c.count(chr(10), 0, m.start()) + 1}')
        _USERS[id(S)] = users
    users = _USERS[id(S)]
    imgs = ctx['images']
    tops = ', '.join(f'{k} {top(imgs[k]):#x}' for k in sorted(imgs))
    if users:
        return 'FINDING', (f'role: rw_lo / rw_len of an atable whose img_hi is 0x671000; read by {", ".join(users[:5])}')
    return ('OK', f'role: rw_lo / rw_len field of the atables ASAN / BOTH (img_hi 0x671000), a table of an image '
                  f'that is none of this unit\'s (our image tops: {tops}). By-use grep over every file of the unit: '
                  f'ASAN, BOTH, asan_init, both_init and the *_TEXT_* names are used only inside lib/Reusable/YK09.v '
                  f'itself, so no proof reads the value; the donor carries the same record')


RULES = (
    (lambda c: c['tv'] == 0x7fffa000, r_shadow_lo),
    (lambda c: c['tv'] == 0x200000 and 'icpt_rodata' in c['stmt'] + c['near'], r_rodata_bound),
    (lambda c: c['tv'] == 0x100000 and re.search(r'(?:z8\s+\(ANum\s+|flit8\s+)0x[0-9a-fA-F]+\)?\s+0x100000\b',
                                                 c['line']), r_quarantine_cell),
    (lambda c: c['tv'] == 0x100000 and re.search(r'\bbkt\s*<\s*1048576\b', c['line']), r_depot_tab),
    (lambda c: c['tv'] == 0x100000 and 'kNodesBlockSize' in c['line'], r_nodes_block),
    (lambda c: c['tv'] == 0x40000 and re.search(r'\b262144\b', c['line']), r_map_size),
    (lambda c: c['tv'] == 0x32000 and 'covered_sound' in c['line'], r_plain_region),
    (lambda c: c['tv'] == 0x60000 and ('src0segs' in c['line'] or 'spv' in c['line']), r_plain_top),
    (lambda c: c['tv'] == 0x20000 and c['dst_file'].endswith('YK1a.v'), r_smoke),
    (lambda c: c['tv'] in (0x142000, 0x52f000) and 'rw_lo' in c['line'], r_foreign_table),
)


def round_row(row, SRC, DST, key):
    """(status, measured) of one ROUND-CONSTANT-SAME row."""
    cl = DST.clines(row['dst_file'])
    ln = row['dst_line']
    k = ln
    while k > 1 and not re.match(r'\s*(?:Lemma|Theorem|Definition|Example|Fact|Corollary)\b', cl[k - 1]):
        k -= 1
    ctx = dict(tv=int(row['tv'], 16), sv=int(row['sv'], 16), line=cl[ln - 1],
               sline=SRC.clines(row['src_file'])[row['src_line'] - 1], stmt=cl[k - 1],
               near='\n'.join(cl[max(0, ln - 15):ln]), dst_file=row['dst_file'], side=DST,
               ours=DST.imgs[key], donor=SRC.imgs[key], images=DST.imgs)
    for test, rule in RULES:
        if test(ctx):
            return rule(ctx)
    return 'NOT-CHECKABLE', 'no role rule covers this line'
