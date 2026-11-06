#!/usr/bin/env python3
"""sm_roles.py WORK DONOR_TWIN TARGET_TWIN OUT.tsv -- every numeral of the relocated stack_malloc files decided by its
ROLE, measured on fuzz_wire's own image (TARGET_TWIN), with fuzz_grant's (DONOR_TWIN) as the source.

WORK is port_core's work directory: WORK/stage/<F> is fuzz_grant's text at the target path, WORK/stage-out/<F> the
relocated text. The two are aligned by line (difflib; equal-length replaced blocks pair line by line) and inside a line
the numerals pair in order. A row is written for every numeral that CHANGED, and for every numeral that did not change
but lies in [0x10000, the higher image top) (a value that may name an address in either image). Comment text is
skipped (nested comments, strings kept).

Roles, each measured from the ELF files (program headers, section headers, .symtab, file bytes):
  pc          the donor value lies in a sized FUNC of the donor image: the target value must be the same function
              (name, and its STT_FILE when the name is not unique) at the same offset
  got         the donor value lies in .got: the target value must lie in the target's .got, and the 8-byte words both
              slots hold must name the same thing (a symbol + offset, by the rule of `pc` / `data`; a tls_index pair
              {1, TLS offset - 0x800} must give the same STT_TLS symbol + offset)
  got-word    the value is the word a .got cell of this file's table holds (the table entry `(cell, 8, [(0, 8%N, V)])`):
              V must equal the 8 file bytes of the target's cell
  data        the donor value lies in a sized OBJECT (or the TLS image): the same symbol + offset in the target, and
              the two objects have the same size
  thread      the donor value lies in the main thread's static TLS block (builtin_tls): the same offset from
              builtin_tls in the target image
  img-top     the donor value is the donor's IMG_TOP (the page-rounded end of the last PT_LOAD) or IMG_TOP / 8: the
              target value must be the target's
  pc-decimal  a decimal numeral equal to a `pc` row's donor value: the same rule as `pc`
  constant    an unchanged numeral that lies in no section of either image and is no image top: a model constant or an
              instruction word (listed; it names nothing in either image)
  CHECK       anything else: printed, and the run exits 1
Writes OUT.tsv (file, line, donor, target, role, measurement, verdict RIGHT / WRONG / CHECK) and prints the counts."""
import bisect
import difflib
import re
import sys

# elftools from the environment (PYTHONPATH), as the rest of the unit's evidence scripts
from elftools.elf.elffile import ELFFile  # noqa: E402

FILES = ['A/Rt/StackMalloc0Tbl.v', 'A/Rt/StackMalloc0.v', 'A/Rt/AF0r.v', 'A/Rt/AF0s.v', 'Reusable/YF0v.v']
NUM = re.compile(r'(?<![\w.])(0x[0-9a-fA-F]+|\d+)(?![\w])')


class Img:
    def __init__(self, p):
        self.data = open(p, 'rb').read()
        e = ELFFile(open(p, 'rb'))
        self.loads = [(s['p_vaddr'], s['p_filesz'], s['p_memsz'], s['p_offset']) for s in e.iter_segments()
                      if s['p_type'] == 'PT_LOAD']
        self.top = (max(v + m for v, _, m, _ in self.loads) + 0xfff) & ~0xfff
        self.secs = [(s.name, s['sh_addr'], s['sh_size']) for s in e.iter_sections() if s['sh_addr']]
        self.syms, fil = [], None
        for s in e.get_section_by_name('.symtab').iter_symbols():
            t = s['st_info']['type']
            if t == 'STT_FILE':
                fil = s.name
            elif s.name and s['st_shndx'] != 'SHN_UNDEF' and t in ('STT_FUNC', 'STT_OBJECT', 'STT_TLS'):
                self.syms.append((s['st_value'], s['st_size'], s.name, t, fil if s['st_info']['bind'] == 'STB_LOCAL' else None))
        self.byname = {}
        for v, z, n, t, f in self.syms:
            self.byname.setdefault(n, []).append((v, z, t, f))
        tls = [s for s in e.iter_segments() if s['p_type'] == 'PT_TLS']
        self.tls = (tls[0]['p_vaddr'], tls[0]['p_memsz']) if tls else None
        bt = [v for v, z, n, t, f in self.syms if n == 'builtin_tls' and t == 'STT_OBJECT']
        self.builtin_tls = (bt[0], [z for v, z, n, t, f in self.syms if n == 'builtin_tls'][0]) if bt else None

    def sec(self, a):
        return next((n for n, v, z in self.secs if v <= a < v + z), None)

    def word(self, a, n=8):
        for v, fz, _m, o in self.loads:
            if v <= a and a + n <= v + fz:
                return int.from_bytes(self.data[o + a - v:o + a - v + n], 'little')
        return None

    def holder(self, a, kinds):
        c = [(v, z, n, t, f) for v, z, n, t, f in self.syms if t in kinds and z > 0 and v <= a < v + z]
        return min(c, key=lambda x: x[1]) if c else None

    def find(self, name, fil, kinds):
        c = [(v, z, t, f) for v, z, t, f in self.byname.get(name, []) if t in kinds and (f == fil or fil is None)]
        return c


def strip_comments(t):
    out, d, i, s = [], 0, 0, False
    while i < len(t):
        if not s and t.startswith('(*', i):
            d += 1; i += 2; continue
        if not s and d and t.startswith('*)', i):
            d -= 1; i += 2; continue
        ch = t[i]
        if d == 0:
            if ch == '"':
                s = not s
            out.append(ch)
        elif ch == '\n':
            out.append(ch)
        i += 1
    return ''.join(out)


def pairs(a_text, b_text):
    a, b = strip_comments(a_text).split('\n'), strip_comments(b_text).split('\n')
    sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == 'equal':
            for i, j in zip(range(i1, i2), range(j1, j2)):
                for x in NUM.findall(a[i]):
                    yield j + 1, x, x, b[j]
        elif op == 'replace' and i2 - i1 == j2 - j1:
            for i, j in zip(range(i1, i2), range(j1, j2)):
                na, nb = NUM.findall(a[i]), NUM.findall(b[j])
                if len(na) == len(nb):
                    for x, y in zip(na, nb):
                        yield j + 1, x, y, b[j]
                else:
                    yield j + 1, '(%d numerals)' % len(na), '(%d numerals)' % len(nb), b[j]
        else:
            for j in range(j1, j2):
                for y in NUM.findall(b[j]):
                    yield j + 1, '(none)', y, b[j]


def decide(G, W, dv, tv, line, pcs):
    """(role, measurement, verdict)"""
    if dv in (G.top, G.top // 8):
        want = W.top if dv == G.top else W.top // 8
        return 'img-top', 'donor IMG_TOP %#x; target IMG_TOP %#x -> %d' % (G.top, W.top, want), 'RIGHT' if tv == want else 'WRONG'
    if G.builtin_tls and G.builtin_tls[0] <= dv < G.builtin_tls[0] + G.builtin_tls[1]:
        off = dv - G.builtin_tls[0]
        want = W.builtin_tls[0] + off
        return 'thread', 'builtin_tls+%#x (target builtin_tls %#x)' % (off, W.builtin_tls[0]), 'RIGHT' if tv == want else 'WRONG'
    gs = G.sec(dv)
    if gs == '.got':
        gw, tw = G.word(dv), W.word(tv)
        if W.sec(tv) != '.got' or gw is None or tw is None:
            return 'got', 'target value not a .got cell', 'WRONG'
        if gw == 1:  # a tls_index pair {module, offset - 0x800}
            go, to = G.word(dv + 8), W.word(tv + 8)
            gn = G.holder((go + 0x800) % 2 ** 64 + (G.tls[0] if G.tls else 0), ('STT_OBJECT', 'STT_TLS'))
            tn = W.holder((to + 0x800) % 2 ** 64 + (W.tls[0] if W.tls else 0), ('STT_OBJECT', 'STT_TLS'))
            ok = tw == 1 and go == to
            return 'got', 'tls_index {1, %#x} both images%s' % (go, '' if go == to else ' (target %#x)' % to), 'RIGHT' if ok else 'WRONG'
        r1, m1, v1 = decide(G, W, gw, tw, line, pcs)
        return 'got', 'cell holds %#x | %#x: %s %s' % (gw, tw, r1, m1), v1
    if dv in pcs or G.holder(dv, ('STT_FUNC',)):
        h = G.holder(dv, ('STT_FUNC',))
        if not h:
            return 'pc-decimal', '-', 'CHECK'
        c = W.find(h[2], h[4], ('STT_FUNC',))
        if len(c) != 1:
            return 'pc', '%s{%s}: %d copies in the target' % (h[2], h[4], len(c)), 'CHECK'
        want = c[0][0] + dv - h[0]
        return 'pc', '%s%s+%#x' % (h[2][:60], '{%s}' % h[4] if h[4] else '', dv - h[0]), 'RIGHT' if tv == want else 'WRONG'
    h = G.holder(dv, ('STT_OBJECT',))
    if h:
        c = W.find(h[2], h[4], ('STT_OBJECT',))
        if len(c) != 1:
            return 'data', '%s: %d copies in the target' % (h[2], len(c)), 'CHECK'
        want = c[0][0] + dv - h[0]
        return 'data', '%s+%#x (size %d | %d)' % (h[2][:60], dv - h[0], h[1], c[0][1]), \
            'RIGHT' if tv == want and h[1] == c[0][1] else 'WRONG'
    if dv == tv and not G.sec(dv) and not W.sec(tv):
        return 'constant', 'in no section of either image', 'RIGHT'
    return 'CHECK', 'donor in %s, target in %s' % (G.sec(dv), W.sec(tv)), 'CHECK'


def model_constants(work):
    """the model constants these files state as numerals, each computed from the target lib's own definitions
    (Reusable/YG00.v kStackSizeLog, Reusable/YG0f.v kFakeStackSize / kFakeFramesOff) -> {value: why}"""
    lib = work.rstrip('/') + '/../lib'
    g00 = open(lib + '/Reusable/YG00.v').read()
    g0f = open(lib + '/Reusable/YG0f.v').read()
    ssl = int(re.search(r'Definition kStackSizeLog : Z := (\d+)\.', g00).group(1))
    fss = int(re.search(r'Definition kFakeStackSize : Z := (0x[0-9a-f]+|\d+)\.', g0f).group(1), 0)
    m = re.search(r'Definition kFakeFramesOff : Z := (\d+) \+ (\d+)\.', g0f)
    ffo = int(m.group(1)) + int(m.group(2))
    return {1 << ssl: 'Z.shiftl 1 kStackSizeLog (kStackSizeLog = %d, Reusable/YG00.v)' % ssl,
            ffo + (1 << ssl): 'kFakeFramesOff + 1 * 2^kStackSizeLog = %#x: class 1 FS_FROFF (frame_addr_cid; '
                              'kFakeFramesOff = %#x, Reusable/YG0f.v)' % (ffo + (1 << ssl), ffo),
            ffo: 'kFakeFramesOff + 0 * 2^kStackSizeLog = %#x: class 0 FS_FROFF (Reusable/YG0f.v)' % ffo,
            (fss - ffo) // 8: '(kFakeStackSize - kFakeFramesOff) / 8 = %#x: the shadow of the frames area '
                              '(kFakeStackSize = %#x, Reusable/YG0f.v)' % ((fss - ffo) // 8, fss)}


def range_rows(G, W, f, ln, a, text):
    """the code table line `[(addr, n%nat); ...]`: each target row is the twin of a donor row (same function, same
    offset, same word count); each donor row without a twin must name a function the target does not define"""
    src = next(l for l in strip_comments(a).split('\n') if l.lstrip().startswith('[(') and '%nat' in l)
    dr = [(int(x, 16), int(n)) for x, n in re.findall(r'\((0x[0-9a-f]+), (\d+)%nat\)', src)]
    tr = [(int(x, 16), int(n)) for x, n in re.findall(r'\((0x[0-9a-f]+), (\d+)%nat\)', text)]
    out, used = [], set()
    for tv, n in tr:
        th = W.holder(tv, ('STT_FUNC',))
        m = []
        for dv, dn in dr:
            gh = G.holder(dv, ('STT_FUNC',))
            if th and gh and gh[2] == th[2] and gh[4] == th[4] and dv - gh[0] == tv - th[0] and dn == n:
                m.append((dv, dn))
        ok = th is not None and len(m) == 1
        if ok:
            used.add(m[0])
        out.append([f, ln, '%#x' % m[0][0] if ok else '-', '%#x' % tv, 'pc', 'code-table row %s+%#x, %d words%s' % (
            th[2][:60] if th else '-', tv - th[0] if th else 0, n, '' if ok else ': no single donor twin'),
            'RIGHT' if ok else 'WRONG'])
    for dv, dn in dr:
        if (dv, dn) in used:
            continue
        h = G.holder(dv, ('STT_FUNC',))
        absent = h is not None and not W.find(h[2], h[4], ('STT_FUNC',))
        out.append([f, ln, '%#x' % dv, '(dropped)', 'pc', 'donor code-table row %s, %d words: no such function in '
                    'the target (A-fs-ranges.patch)' % (h[2] if h else '-', dn), 'RIGHT' if absent else 'WRONG'])
    return out


def main():
    work, gtw, wtw, out = sys.argv[1:5]
    G, W = Img(gtw), Img(wtw)
    hi = max(G.top, W.top)
    rows = []
    texts = {}
    for f in FILES:
        try:
            a = open('%s/stage/%s' % (work, f)).read()
        except FileNotFoundError:
            a = open('%s/stage/%s' % (work, f.split('/', 1)[1])).read()
        texts[f] = (a, open('%s/stage-out/%s' % (work, f)).read())
    pcs = set()
    consts = model_constants(work)
    for f, (a, b) in texts.items():
        defs = {m.group(1): int(m.group(2), 0) for m in
                re.finditer(r'Definition (\w+) : Z := (0x[0-9a-fA-F]+|\d+)\.', strip_comments(b))}
        fetched = set()
        for ln, x, y, text in pairs(a, b):
            if x.startswith('(') or y.startswith('('):
                if text.lstrip().startswith('[(') and '%nat' in text:
                    rows.extend(range_rows(G, W, f, ln, a, text))
                    continue
                rows.append([f, ln, x, y, 'CHECK', 'numeral count or position differs: ' + text.strip()[:100], 'CHECK'])
                continue
            dv, tv = int(x, 0), int(y, 0)
            if dv == tv and not (0x10000 <= dv < hi):
                continue
            fm = re.search(r'fetch_word tfibsegs \(Z_to_bv 64 \((\w+) \+ (0x[0-9a-fA-F]+|\d+)\)\) = Some \(' + re.escape(y)
                           + r'%bv', text)
            if fm and fm.group(1) in defs:
                pc = defs[fm.group(1)] + int(fm.group(2), 0)
                w = W.word(pc, 4)
                fetched.add(tv)
                rows.append([f, ln, x, y, 'insn-word', 'the target word at %s + %s = %#x is %s' % (
                    fm.group(1), fm.group(2), pc, '%#010x' % w if w is not None else 'unreadable'),
                    'RIGHT' if w == tv and dv == tv else 'WRONG'])
                continue
            if re.search(r'decode_any \(' + re.escape(y) + r'%bv', text):
                rows.append([f, ln, x, y, 'insn-word', 'the decode of a fetched word (the fetch row of this file)',
                             'RIGHT' if tv in fetched and dv == tv else 'CHECK'])
                continue
            if dv == tv and dv in consts:
                rows.append([f, ln, x, y, 'model-constant', consts[dv], 'RIGHT'])
                continue
            # a .got table entry `(cell, 8, [(0, 8%N, V)])`: V is the cell's word
            m = re.search(r'\((0x[0-9a-f]+), 8, \[\(0, 8%N, ' + re.escape(y) + r'\)\]\)', text)
            if m and m.group(1) != y:
                cell = int(m.group(1), 16)
                tw = W.word(cell)
                if tw is not None and W.sec(cell) in ('.got', '.data.rel.ro'):
                    rows.append([f, ln, x, y, 'got-word', 'the %s word at %#x is %#x' % (W.sec(cell), cell, tw),
                                 'RIGHT' if tw == tv else 'WRONG'])
                    continue
            role, meas, verdict = decide(G, W, dv, tv, ln, pcs)
            if role == 'constant' and not x.startswith('0x') and any(int(r[2], 0) == dv for r in rows if r[4] == 'pc' and r[2].startswith('0x')):
                role = 'pc-decimal'
            rows.append([f, ln, x, y, role, meas, verdict])
    # decimal pcs: a decimal numeral equal to a pc row's donor value
    pcv = {int(r[2], 0) for r in rows if r[4] == 'pc'}
    for r in rows:
        if not r[2].startswith('0x') and r[2].isdigit() and int(r[2]) in pcv and r[4] in ('constant', 'CHECK', 'pc'):
            r[4] = 'pc-decimal'
    with open(out, 'w') as o:
        o.write('file\tline\tdonor\ttarget\trole\tmeasurement\tverdict\n')
        for r in rows:
            o.write('\t'.join(map(str, r)) + '\n')
    from collections import Counter
    c = Counter(r[6] for r in rows)
    print('sm_roles: %d numeral(s): %s; by role %s; donor IMG_TOP %#x, target IMG_TOP %#x' % (
        len(rows), dict(c), dict(Counter(r[4] for r in rows)), G.top, W.top))
    sys.exit(0 if set(c) <= {'RIGHT'} else 1)


if __name__ == '__main__':
    main()
