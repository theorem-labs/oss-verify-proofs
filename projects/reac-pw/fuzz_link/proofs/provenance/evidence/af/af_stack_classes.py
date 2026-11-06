#!/usr/bin/env python3
"""af_stack_classes.py: check reac-pw/fuzz_link's asan fake-stack class table against the pinned ELF.

Checks on the side-stack class table of the AsanAPI record (aa_stack_malloc admits a class iff the table maps it to a
nonzero pc):
 (2) Tfib_code's pc_stack_malloc (lib/A/AF0l.v) maps each fake-stack class 0..10 that link's code calls and whose
     entry zeroes the whole frame's shadow ('whole') to the entry __asan_stack_malloc_<c> of the pinned image, and
     every other class (never called, or called with an 'asked' entry) to 0; a called class <= 6 must be 'whole'
     and a called class > 6 must be 'asked' (the poison call's length register comes from the entry's a0);
 (3) only classes 8 and 9 reach __asan_stack_free_<c> (classes <= 6 free inline in the caller).

Inputs: the pinned image (its sha256 must start with the PIN_SHA256 argument), its unstripped twin (for .symtab), and the
AF0l.v text. The script checks that the PT_LOAD segments of the pin and of the twin are the same, byte for byte,
except the ELF header's section-table fields and the build-id note (which strip rewrites), so the twin's symbols name
the pin's code. Calls are found in the pin's executable segments: `jal rd, t` (any rd, so tail jumps count) and
`auipc rX, u` + `jalr rd, off(rX)` pairs; of the compressed (2-byte) words, a c.j to an entry fails the check (RV64
has no c.jal; c.jr / c.jalr have no static target and are not followed).
Exit status 0 iff every check passes. Usage:
  af_stack_classes.py PIN UNSTRIPPED AF0L_V [PIN_SHA256]
"""
import hashlib, os, re, struct, sys
from elftools.elf.elffile import ELFFile

pin_path, twin_path, af0l_path = sys.argv[1:4]
want_sha = sys.argv[4] if len(sys.argv) > 4 else None

def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()

ok = True
pin_sha, twin_sha = sha(pin_path), sha(twin_path)
print(f"pin   {os.path.basename(pin_path)} sha256 {pin_sha}")
print(f"twin  {os.path.basename(twin_path)} (unstripped) sha256 {twin_sha}")
if want_sha and not pin_sha.startswith(want_sha):
    print(f"FAIL pin sha256 is not {want_sha}"); ok = False

pin, twin = ELFFile(open(pin_path, 'rb')), ELFFile(open(twin_path, 'rb'))
def loads(e):
    return [(s['p_vaddr'], s['p_memsz'], s['p_flags'], s['p_offset'], s.data()) for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
lp, lt = loads(pin), loads(twin)
# strip rewrites the ELF header's section-table fields (e_shoff 0x28..0x30, e_shnum 0x3c, e_shstrndx 0x3e) and the
# build-id note's 20-byte descriptor; those two ranges are the only bytes of a load segment allowed to differ.
bid = [s for s in twin.iter_sections() if s.name == '.note.gnu.build-id']
allowed = [(0x28, 0x30), (0x3c, 0x40)]  # file offsets in the segment at offset 0
if bid:
    allowed.append((bid[0]['sh_offset'] + 16, bid[0]['sh_offset'] + bid[0]['sh_size']))
same = len(lp) == len(lt)
for a, b in zip(lp, lt):
    if a[:4] != b[:4] or len(a[4]) != len(b[4]):
        same = False; continue
    diff = [i for i in range(len(a[4])) if a[4][i] != b[4][i]]
    bad = [i for i in diff if not any(lo <= a[3] + i < hi for lo, hi in allowed)]
    kind = 'X' if a[2] & 1 else ('W' if a[2] & 2 else 'R')
    print(f"  load {a[0]:#x} {kind}: {len(diff)} differing bytes, {len(bad)} outside the ELF header / build-id note")
    if bad or (a[2] & 1 and diff):
        same = False
print(f"pin and twin load the same bytes (code identical; only ELF header / build-id differ): {same} ({len(lp)} segments)")
ok &= same

syms = [(s.name, s['st_value'], s['st_size'], s['st_info']['type']) for s in twin.get_section_by_name('.symtab').iter_symbols()]
entry = {}
for n, v, sz, t in syms:
    m = re.fullmatch(r'__asan_stack_(malloc|free)_(\d+)', n)
    if m and t == 'STT_FUNC':
        entry[(m.group(1), int(m.group(2)))] = v
funcs = sorted((v, sz, n) for n, v, sz, t in syms if t == 'STT_FUNC' and sz > 0)
def fn_of(a):
    best = None
    for v, sz, n in funcs:
        if v <= a < v + sz: best = n
    return best
target = {v: k for k, v in entry.items()}

def sx(v, b): return v - (1 << b) if (v >> (b - 1)) & 1 else v
calls = {k: [] for k in entry}
cj = []
for vaddr, memsz, flags, _foff, data in lp:
    if not flags & 1: continue  # PF_X
    off = 0
    while off + 2 <= len(data):
        h = struct.unpack_from('<H', data, off)[0]
        a = vaddr + off
        if h & 3 != 3:
            op, f3 = h & 3, h >> 13
            if op == 1 and f3 == 5:   # c.j
                imm = ((h >> 12) & 1) << 11 | ((h >> 11) & 1) << 4 | ((h >> 9) & 3) << 8 | ((h >> 8) & 1) << 10 | \
                      ((h >> 7) & 1) << 6 | ((h >> 6) & 1) << 7 | ((h >> 3) & 7) << 1 | ((h >> 2) & 1) << 5
                t = a + sx(imm, 12)
                if t in target: cj.append((a, t))
            off += 2; continue
        if off + 4 > len(data): break
        w = struct.unpack_from('<I', data, off)[0]
        op = w & 0x7f
        if op == 0x6f:
            imm = ((w >> 31) & 1) << 20 | ((w >> 12) & 0xff) << 12 | ((w >> 20) & 1) << 11 | ((w >> 21) & 0x3ff) << 1
            t = a + sx(imm, 21)
            if t in target: calls[target[t]].append((a, fn_of(a), 'jal x%d' % ((w >> 7) & 31)))
        elif op == 0x17 and off + 8 <= len(data):
            w2 = struct.unpack_from('<I', data, off + 4)[0]
            if w2 & 0x7f == 0x67 and (w2 >> 15) & 31 == (w >> 7) & 31:
                t = a + sx(w & 0xfffff000, 32) + sx(w2 >> 20, 12)
                if t in target: calls[target[t]].append((a, fn_of(a), 'auipc+jalr'))
        off += 4
if cj:
    print("FAIL c.j to a fake-stack entry:", [(hex(a), hex(t)) for a, t in cj]); ok = False

# The Coq table: pc_stack_malloc := fun cid => if cid =? c then pc else ... else 0;
txt = open(af0l_path).read()
m = re.search(r'pc_stack_malloc\s*:=\s*fun\s+cid\s*=>\s*(.*?);', txt, re.S)
arms = re.findall(r'if cid =\? (\d+) then (0x[0-9a-fA-F]+|\d+)', m.group(1))
tail = re.search(r'else (0x[0-9a-fA-F]+|\d+)\s*$', m.group(1).strip())
coq = {}
for c, pc in arms:
    coq.setdefault(int(c), int(pc, 0))
default = int(tail.group(1), 0)
print(f"AF0l.v pc_stack_malloc arms: {[(c, hex(p)) for c, p in sorted(coq.items())]} else {default}")

# How each malloc entry marks the new frame's shadow usable. 'whole': after its MemToShadow call it stores zero
# words `sd zero, k(a1)` covering the frame's whole shadow ((64 << c) / 8 bytes); 'asked': it calls PoisonShadow with
# a1 = a register set once from the entry's a0 (`mv rX, a0`; rX written nowhere else but the epilogue restore after
# the call), i.e. the byte count the caller asked, not the class size.
X = [(v, d) for v, ms, fl, fo, d in lp if fl & 1][0]
def word(a):
    return struct.unpack_from('<I', X[1], a - X[0])[0]
symat = {v: n for n, v, sz, t in syms if t == 'STT_FUNC' and sz > 0}
size_of = {v: sz for n, v, sz, t in syms if t == 'STT_FUNC' and sz > 0}
def dec(a):
    w = word(a); op = w & 0x7f; rd = (w >> 7) & 31; rs1 = (w >> 15) & 31; rs2 = (w >> 20) & 31; f3 = (w >> 12) & 7
    if op == 0x6f:
        imm = ((w >> 31) & 1) << 20 | ((w >> 12) & 0xff) << 12 | ((w >> 20) & 1) << 11 | ((w >> 21) & 0x3ff) << 1
        return ('jal', rd, a + sx(imm, 21))
    if op == 0x13 and f3 == 0: return ('addi', rd, rs1, sx(w >> 20, 12))
    if op == 0x23 and f3 == 3: return ('sd', rs1, rs2, sx(((w >> 25) << 5) | ((w >> 7) & 31), 12))
    if op in (0x03, 0x13, 0x17, 0x33, 0x37, 0x1b, 0x3b): return ('w', rd)
    return ('o',)
def shadow_kind(e, c):
    n = size_of[e] // 4
    ins = [(e + 4 * i, dec(e + 4 * i)) for i in range(n)]
    m2s = [i for i, (a, d) in enumerate(ins) if d[0] == 'jal' and 'MemToShadow' in symat.get(d[2], '')]
    pois = [i for i, (a, d) in enumerate(ins) if d[0] == 'jal' and 'PoisonShadow' in symat.get(d[2], '')]
    if m2s and not pois:
        k = 0
        j = m2s[0] + 1
        while j < n and not (ins[j][1][0] == 'sd' and ins[j][1][1] == 11 and ins[j][1][2] == 0): j += 1
        while j < n and ins[j][1][0] == 'sd' and ins[j][1][1] == 11 and ins[j][1][2] == 0 and ins[j][1][3] == 8 * k:
            k += 1; j += 1
        return ('whole' if 8 * k == (64 << c) // 8 else 'partial'), f"{k} zero words after MemToShadow@{ins[m2s[0]][0]:#x}"
    if pois:
        p = pois[0]
        a1 = [i for i in range(p) if ins[i][1][:2] == ('addi', 11) and ins[i][1][3] == 0]
        if not a1: return 'unknown', 'no mv a1 before PoisonShadow'
        rx = ins[a1[-1]][1][2]
        writes = [i for i, (a, d) in enumerate(ins) if len(d) > 1 and d[0] in ('addi', 'w') and d[1] == rx]
        init = [i for i in writes if ins[i][1][0] == 'addi' and ins[i][1][2] == 10 and ins[i][1][3] == 0]
        others = [i for i in writes if i not in init and i < p]
        if len(init) == 1 and init[0] < a1[-1] and not others:
            return 'asked', f"mv x{rx}, a0 @{ins[init[0]][0]:#x}; mv a1, x{rx} @{ins[a1[-1]][0]:#x}; PoisonShadow @{ins[p][0]:#x}"
        return 'unknown', f"a1 from x{rx}, writes {[hex(ins[i][0]) for i in writes]}"
    return 'unknown', 'no shadow call found'

print("class  malloc entry  called from (link's code)                                   shadow   AF0l.v   expected  verdict")
for c in range(0, 11):
    k = ('malloc', c)
    e = entry.get(k)
    sites = calls.get(k, [])
    kind, why = shadow_kind(e, c) if e else ('-', '')
    if sites and c <= 6 and kind != 'whole': ok = False; print(f"FAIL class {c} is called, <= 6, but its entry is {kind}: {why}")
    if sites and c > 6 and kind != 'asked': ok = False; print(f"FAIL class {c} is called, > 6, but its entry is {kind}: {why}")
    exp = e if (sites and kind == 'whole') else 0
    got = coq.get(c, default)
    v = 'OK' if got == exp else 'MISMATCH'
    ok &= v == 'OK'
    s = ', '.join(f"{n}@{a:#x}" for a, n, _ in sites) or '-'
    print(f"{c:5}  {('%#x' % e) if e else '-':12}  {s:58}  {kind:7}  {got:#8x}  {exp:#8x}  {v}")
    if why: print(f"         {why}")
print("class  free entry    called from (link's code)")
freed = []
for c in range(0, 11):
    k = ('free', c)
    e = entry.get(k)
    sites = calls.get(k, [])
    if sites: freed.append(c)
    s = ', '.join(f"{n}@{a:#x}" for a, n, _ in sites) or '-'
    print(f"{c:5}  {('%#x' % e) if e else '-':12}  {s}")
fr_ok = freed == [8, 9]
print(f"classes that reach __asan_stack_free_N: {freed} -> {'OK (8 and 9 only)' if fr_ok else 'FAIL'}")
ok &= fr_ok
print("RESULT", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
