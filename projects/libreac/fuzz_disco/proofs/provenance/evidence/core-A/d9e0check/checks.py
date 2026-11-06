#!/usr/bin/env python3
"""checks.py WORK DONOR_ELF DONOR_SYMS TARGET_ELF TARGET_TWIN OUT_TXT

The four checks that every output of port_core d9e0589898fd needs (its scoring on the relocation plant set found 57
silent wrong rows in four classes), run on the --work directory of the d9e0589898fd check run. Every numeral comes
from the run's own symbol-gate table WORK/gate-raw.tsv (one row per numeral of the 13 files: donor value, ported
value). Values are recomputed from the images' own headers and symbol tables, never taken from the tool.
  1. kept image-derived counts: every numeral the run KEPT (ported value = donor value) that equals a donor image
     quantity whose same-named target quantity DIFFERS (a quantity equal in both images cannot make a kept value
     wrong). Quantities: per PT_LOAD memsz / filesz / page-rounded length, per allocated section size, every span
     between two image bounds (PT_LOAD starts / ends, page-rounded, section starts / ends), image extent and top,
     each also /4, /8 and /4096 when exact; per symbol of the same name in both images (DONOR_SYMS: the donor's
     recovered symbols; TARGET_TWIN: the target's unstripped twin): size, /4, /8. A hit >= 0x100 is a FLAG row
     (decide by hand); the hits below 0x100 are listed by value (every small integer is some quotient or span).
  2. GOT[0]: every numeral whose donor value lies in the donor's .got must be ported to the same offset in the
     target's .got; GOT[0] (the .got start) to the target's .got start.
  3. shadow offsets and model constants by role: the shadow offset 0x7fff8000 is measured in both images' code
     (each `lui rd, 0x7fff8`, with its function); every numeral that is an ASan mapping constant (kLowMemEnd,
     kLowShadowBeg, kHighMemBeg, kHighMemEnd) or lies in 0x7fff7f00 .. 0x10007fff8000 must be KEPT when both images
     use the offset in the same functions (a moved one is the silent 'moved shadow offset' class); a numeral
     >= 2^63 is a negative immediate (kept); any other numeral above the donor image top is a FLAG row.
  4. 'no twin' drops: every row of WORK/no-twin.tsv, and every row of WORK/check.tsv / review.tsv whose text says
     'no twin', is looked up by its source name in the target's twin symbol table; a name present there is a wrong
     drop (FLAG).
Writes OUT_TXT; exit 0 when no check has a FLAG row, else 1.
"""
import collections, csv, os, struct, sys
from elftools.elf.elffile import ELFFile

work, donor_elf, donor_syms, target_elf, target_twin, out_txt = sys.argv[1:7]
PAGE = 0x1000
MIN = 0x100  # check 1's floor (the registered by-value gate's): below it every small integer is some quotient or span
SHADOW_OFFSET = 0x7fff8000
# the ASan x86-64-style mapping of both images: model constants by name (the shadow offset fixes all of them)
MODEL = {0x7fff7fff: 'kLowMemEnd', 0x7fff8000: 'kLowShadowBeg (shadow offset)', 0x10007fff8000: 'kHighMemBeg',
         0x7fffffffffff: 'kHighMemEnd'}
MAP_LO, MAP_HI = 0x7fff7f00, 0x10007fff8000  # inclusive: shadow offset - 0x100 .. kHighMemBeg


def num(s):
    s = s.strip()
    try:
        return int(s, 16) if s.lower().startswith('0x') else int(s)
    except ValueError:
        return None


def geometry(path):
    """name -> value for every image quantity of check 1, and the image's .got / top / code."""
    e = ELFFile(open(path, 'rb'))
    q, bounds = {}, {}
    loads = [s for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
    for i, s in enumerate(loads):
        lo, hi = s['p_vaddr'], s['p_vaddr'] + s['p_memsz']
        q[f'load{i}.memsz'], q[f'load{i}.filesz'] = s['p_memsz'], s['p_filesz']
        plo, phi = lo // PAGE * PAGE, -(-hi // PAGE) * PAGE
        q[f'load{i}.pagelen'] = phi - plo
        bounds.update({f'load{i}.lo': lo, f'load{i}.hi': hi, f'load{i}.plo': plo, f'load{i}.phi': phi})
    for sec in e.iter_sections():
        if sec['sh_flags'] & 2 and sec.name:  # SHF_ALLOC
            q[f'{sec.name}.size'] = sec['sh_size']
            bounds[f'{sec.name}.lo'], bounds[f'{sec.name}.hi'] = sec['sh_addr'], sec['sh_addr'] + sec['sh_size']
    top = max(bounds[f'load{i}.phi'] for i in range(len(loads)))
    q['image.top'], q['image.extent'] = top, top - bounds['load0.plo']
    names = sorted(bounds)
    for a in names:
        for b in names:
            if bounds[b] > bounds[a]:
                q[f'span({a},{b})'] = bounds[b] - bounds[a]
    for k, v in list(q.items()):
        for d in (4, 8, PAGE):
            if v and v % d == 0:
                q[f'{k}/{d}'] = v // d
    got = e.get_section_by_name('.got')
    text = e.get_section_by_name('.text')
    return q, (got['sh_addr'], got['sh_size']) if got else None, top, (text['sh_addr'], text.data())


def symsizes_text(path):
    out = {}
    for l in open(path):
        f = l.split()
        if len(f) >= 3 and not l.startswith('#'):
            out.setdefault(f[0], int(f[2]))
    return out


def symsizes_elf(path):
    e = ELFFile(open(path, 'rb'))
    st = e.get_section_by_name('.symtab')
    out = {}
    for s in st.iter_symbols():
        if s.name and s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT') and s['st_size']:
            out.setdefault(s.name, s['st_size'])
    return out


def shadow_luis(code):
    """addresses of the `lui rd, 0x7fff8` instructions in .text (opcode 0x37, imm[31:12] = 0x7fff8: the shadow offset
    0x7fff8000), by a linear sweep of the RV64GC instruction stream (2-byte RVC words, 4-byte words)."""
    lo, data = code
    out, i = [], 0
    while i + 1 < len(data):
        if data[i] & 3 != 3:
            i += 2
            continue
        if i + 3 < len(data):
            w = struct.unpack_from('<I', data, i)[0]
            if w & 0x7f == 0x37 and w >> 12 == 0x7fff8:
                out.append(lo + i)
        i += 4
    return out


def namer(syms):
    """address -> 'function+off' from (lo, size, name) triples."""
    fs = sorted((lo, lo + n, nm) for lo, n, nm in syms if n)

    def name(a):
        for lo, hi, nm in fs:
            if lo <= a < hi:
                return f'{nm}+{a - lo:#x}'
        return '?'
    return name


def syms_text(path):
    return [(int(f[1], 16), int(f[2]), f[0]) for f in (l.split() for l in open(path) if not l.startswith('#'))
            if len(f) >= 3]


def syms_elf(path):
    st = ELFFile(open(path, 'rb')).get_section_by_name('.symtab')
    return [(s['st_value'], s['st_size'], s.name) for s in st.iter_symbols()
            if s.name and s['st_info']['type'] == 'STT_FUNC']


rows = list(csv.DictReader((l for l in open(os.path.join(work, 'gate-raw.tsv')) if not l.startswith('#')),
                           delimiter='\t'))  # the gate writes an INPUTS USED comment block above its header
Dq, Dgot, Dtop, Dcode = geometry(donor_elf)
Tq, Tgot, Ttop, Tcode = geometry(target_elf)
Ds, Ts = symsizes_text(donor_syms), symsizes_elf(target_twin)
for name, v in Ds.items():
    if name in Ts:
        Dq[f'sym {name}.size'], Tq[f'sym {name}.size'] = v, Ts[name]
        for d in (4, 8):
            if v % d == 0:
                Dq[f'sym {name}.size/{d}'] = v // d
                Tq[f'sym {name}.size/{d}'] = Ts[name] // d if Ts[name] % d == 0 else None
inv = collections.defaultdict(list)
for k, v in Dq.items():
    if Tq.get(k) != v:  # only a quantity that differs in the target can make a kept value wrong
        inv[v].append(k)

out = []
flags = collections.Counter()


def put(s=''):
    out.append(s)


put('# The four checks on the port_core d9e0589898fd check run (written by checks.py)')
put(f'# numerals in gate-raw.tsv: {len(rows)}; '
    f'verdicts: ' + ', '.join(f'{k} {v}' for k, v in sorted(collections.Counter(r["verdict"] for r in rows).items())))

# 1
kept = [r for r in rows if r['kind'] != 'ident' and num(r['src_value']) is not None
        and num(r['src_value']) == num(r['dst_value'])]
hits = [(r, inv[num(r['src_value'])]) for r in kept if num(r['src_value']) in inv]
big = [(r, n) for r, n in hits if num(r['src_value']) >= MIN]
small = collections.Counter(num(r['src_value']) for r, n in hits if num(r['src_value']) < MIN)
put('')
put(f'## 1. kept image-derived counts: {len(kept)} kept numerals; donor quantities that differ in the target: '
    f'{sum(len(v) for v in inv.values())}; kept numerals >= {MIN:#x} equal to one of them: {len(big)}')
for r, names in big:
    put(f'FLAG\t{r["dst_file"]}:{r["dst_line"]}\t{r["src_value"]}\tdonor {", ".join(sorted(names)[:4])}'
        f'{" ..." if len(names) > 4 else ""}\ttarget {", ".join(hex(Tq[n]) if Tq.get(n) is not None else "none" for n in sorted(names)[:4])}')
    flags[1] += 1
put(f'below {MIN:#x} (not decided by value: every small integer coincides with some quotient or span; the registered '
    f'by-value gate has the same floor): kept numerals equal to a differing donor quantity, by value: '
    + (', '.join(f'{v:#x} x{c} ({sorted(inv[v])[0]}{" ..." if len(inv[v]) > 1 else ""})' for v, c in sorted(small.items())) or 'none'))
put(f'check 1: {"FLAG " + str(flags[1]) if flags[1] else "PASS"}')

# 2
put('')
glo, gsz = Dgot
tlo, tsz = Tgot
gr = [r for r in rows if num(r['src_value']) is not None and glo <= num(r['src_value']) < glo + gsz]
put(f'## 2. GOT[0] and .got cells: donor .got {glo:#x}+{gsz:#x}, target .got {tlo:#x}+{tsz:#x}; numerals whose donor '
    f'value is in the donor .got: {len(gr)}')
for r in gr:
    want = tlo + num(r['src_value']) - glo
    ok = num(r['dst_value']) == want
    put(f'{"ok" if ok else "FLAG"}\t{r["dst_file"]}:{r["dst_line"]}\t{r["src_value"]} -> {r["dst_value"]}\twant {want:#x}')
    flags[2] += not ok
put(f'check 2: {"FLAG " + str(flags[2]) if flags[2] else "PASS"}')

# 3
put('')
dl, tl = shadow_luis(Dcode), shadow_luis(Tcode)
dn, tn = namer(syms_text(donor_syms)), namer(syms_elf(target_twin))
dfun = sorted(dn(a).split('+')[0] for a in dl)
tfun = sorted(tn(a).split('+')[0] for a in tl)
put(f'## 3. shadow offsets and model constants by role: `lui rd, 0x7fff8` (shadow offset {SHADOW_OFFSET:#x}) in .text: '
    f'donor {len(dl)} at ' + ', '.join(f'{a:#x} {dn(a)}' for a in dl) + f'; target {len(tl)} at '
    + ', '.join(f'{a:#x} {tn(a)}' for a in tl) + f'; same functions: {"yes" if dfun == tfun and dl else "NO"}')
if not (dl and dfun == tfun):
    flags[3] += 1
roles = collections.Counter()
for r in rows:
    s, d = num(r['src_value']), num(r['dst_value'])
    if s is None or d is None:
        continue
    if s in MODEL:
        role = MODEL[s]
    elif MAP_LO <= s <= MAP_HI:
        role = 'shadow offset + k' if s < SHADOW_OFFSET + 0x10000000 else 'ASan shadow range'
    elif s >= 1 << 63:
        role = 'negative immediate'
    elif s >= Dtop:
        role = 'above the donor image top, no role'
    else:
        continue
    ok = s == d and role != 'above the donor image top, no role'
    roles[(role, 'kept' if s == d else 'MOVED', 'ok' if ok else 'FLAG')] += 1
    if not ok:
        put(f'FLAG\t{r["dst_file"]}:{r["dst_line"]}\t{r["src_value"]} -> {r["dst_value"]}\t{role}')
        flags[3] += 1
for (role, kind, ok), c in sorted(roles.items()):
    put(f'{ok}\t{role}\t{kind}\t{c}')
put(f'check 3: {"FLAG " + str(flags[3]) if flags[3] else "PASS"}')

# 4
put('')
drops = []
nt = os.path.join(work, 'no-twin.tsv')
if os.path.exists(nt):
    rd = list(csv.reader(open(nt), delimiter='\t'))
    for f in rd[1:]:
        if f:
            drops.append((f'{f[0]}:{f[1]}', f[5] if len(f) > 5 else f[-1], 'no-twin.tsv'))
for t in ('check.tsv', 'review.tsv'):
    p = os.path.join(work, t)
    if os.path.exists(p):
        for f in list(csv.reader(open(p), delimiter='\t'))[1:]:
            if any('no twin' in c for c in f):
                drops.append((f'{f[0]}:{f[1]}', f[-1], t))
put(f'## 4. no-twin drops: {len(drops)} rows (no-twin.tsv, and check.tsv / review.tsv rows saying \'no twin\')')
for where, name, src in drops:
    present = name in Ts
    put(f'{"FLAG" if present else "ok"}\t{where}\t{name}\t{src}\t'
        f'{"in the target symtab: a wrong drop" if present else "not in the target symtab"}')
    flags[4] += present
put(f'check 4: {"FLAG " + str(flags[4]) if flags[4] else "PASS"}')

open(out_txt, 'w').write('\n'.join(out) + '\n')
print('checks: ' + ', '.join(f'{i} {"FLAG " + str(flags[i]) if flags[i] else "PASS"}' for i in (1, 2, 3, 4)))
sys.exit(1 if sum(flags.values()) else 0)
