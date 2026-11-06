#!/usr/bin/env python3
"""Semantic diff of two palist.py listings (old pin vs new pin), per function of the listed range.

Each slot is put in a position-free form:
  PCall S rd / PTail S -> kept (names)
  auipc rd             -> ('PHi', rd)   (its value depends on the pc; what it reaches is compared at each use)
  a load, store, addi or jalr whose base register holds an auipc value (linear scan inside the function; a write
  to the register ends it), and every PLdHi / PAddHi -> (kind, word with the immediate masked, resolved target)
  any other reader of such a register -> ('OPAQUE', w, targets)  (raw word: shows up if it moves)
  any other word       -> ('PW', w)     (raw)
A target is resolved through the unstripped twin's symbol table: 'sym+off' when a sized symbol covers it; a .got cell
as 'GOT->' + the resolution of the cell's value; a NUL-ended printable string by content; a .rodata table of 4-byte
table-relative entries whose targets lie in one function as 'jt:' + the targets as function offsets; otherwise
section name + 16 bytes.
Usage: semdiff.py PALIST_PY OLD_IMAGE OLD_TWIN NEW_IMAGE NEW_TWIN  (range and extras as run.sh)
"""
import bisect
import difflib
import importlib.util
import sys
from collections import Counter

from elftools.elf.elffile import ELFFile

IMASK = 0x000fffff  # I-type word without its immediate
SMASK = 0x01fff07f  # S-type word without its immediate


def load_palist(path):
    spec = importlib.util.spec_from_file_location('palist', path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


class Resolver:
    def __init__(self, twin):
        self.f = ELFFile(open(twin, 'rb'))
        self.secs = [s for s in self.f.iter_sections() if s['sh_addr'] and s['sh_size']]
        self.data = {}
        syms = []
        for s in self.f.get_section_by_name('.symtab').iter_symbols():
            if s['st_value'] and s['st_size'] and s.name and not s.name.startswith('$'):
                syms.append((s['st_value'], s['st_size'], s.name))
        syms.sort()
        self.syms = syms
        self.keys = [v for v, _, _ in syms]

    def sec(self, a):
        for s in self.secs:
            if s['sh_addr'] <= a < s['sh_addr'] + s['sh_size']:
                return s
        return None

    def read(self, a, n):
        s = self.sec(a)
        if s is None or s['sh_type'] == 'SHT_NOBITS':
            return None
        if s.name not in self.data:
            self.data[s.name] = s.data()
        o = a - s['sh_addr']
        return self.data[s.name][o:o + n]

    def cover(self, a, text_only=False):
        i = bisect.bisect_right(self.keys, a) - 1
        best = None
        while i >= 0 and self.syms[i][0] > a - (1 << 20):
            v, sz, n = self.syms[i]
            if v <= a < v + sz and (best is None or (v, -sz) > (best[0], -best[1])):
                best = (v, sz, n)
            i -= 1
        if best and text_only:
            s = self.sec(a)
            if s is None or s.name != '.text':
                return None
        return best

    def name(self, a, depth=0):
        best = self.cover(a)
        if best:
            return '%s+0x%x' % (best[2], a - best[0])
        s = self.sec(a)
        if s is None:
            return 'abs:0x%x' % a
        if s.name == '.got' and depth == 0:
            return 'GOT->' + self.name(int.from_bytes(self.read(a, 8), 'little'), 1)
        b = self.read(a, 64)
        if b is None:
            return '%s+0x%x' % (s.name, a - s['sh_addr'])
        if 0 in b and b.index(0) > 0 and all(32 <= c < 127 or c in (9, 10) for c in b[:b.index(0)]):
            return '%s:str:%r' % (s.name, b[:b.index(0)].decode())
        jt = self.jump_table(a)
        if jt:
            return jt
        return '%s:bytes:%s' % (s.name, b[:16].hex())

    def jump_table(self, a):
        b = self.read(a, 4 * 64)
        if not b or len(b) < 4:
            return None
        ents = [int.from_bytes(b[4 * i:4 * i + 4], 'little', signed=True) for i in range(len(b) // 4)]
        f = self.cover(a + ents[0], text_only=True)
        if f is None:
            return None
        out = []
        for e in ents:
            t = a + e
            if not (f[0] <= t < f[0] + f[1]):
                break
            out.append('+0x%x' % (t - f[0]))
        return 'jt:%s[%s]' % (f[2], ','.join(out))


def build(pl, image, twin):
    fu = ELFFile(open(twin, 'rb'))
    names = {}
    for s in fu.get_section_by_name('.symtab').iter_symbols():
        if s['st_value'] and s.name and not s.name.startswith('$'):
            names.setdefault(s['st_value'], []).append((s.name, s['st_info']['type']))
    byname = {n: v for v, l in names.items() for n, _ in l}
    base, end = byname['LLVMFuzzerTestOneInput'], byname['__wrap_getenv']
    img = pl.Img(image)
    nslots = (end - base) // 4
    funcs = sorted((v, n) for v, l in names.items() if base <= v < end for n, t in l if t == 'STT_FUNC')

    def pick(t):
        ns = [n for n, ty in names.get(t, []) if ty == 'STT_FUNC'] or [n for n, _ in names.get(t, [])]
        if len(ns) > 1:
            return [n for n in ns if n.startswith('__interceptor_trampoline_')][0]
        return ns[0]
    symname = {}
    for k in range(nslots):
        w = img.word(base + 4 * k)
        if w & 0x7f == 0x6f:
            t = pl.zcanon(base + 4 * k + pl.jimm(w))
            if t in names:
                symname[t] = pl.ident(pick(t))
    extra = [byname['__asan_shadow_memory_dynamic_address'], byname['__asan_option_detect_stack_use_after_return']]
    words, slots, his, objs, syms = pl.listing(img, base, nslots, symname, [v for v, _ in funcs], extra)
    return dict(base=base, nslots=nslots, funcs=funcs, words=words, slots=slots, his=his, objs=objs, syms=syms,
                sigma={n: t for t, n in symname.items()})


def norm_func(pl, R, L, a, b):
    words, slots, his, base = L['words'], L['slots'], L['his'], L['base']
    # reg -> (value, kind): kind 'hi' = a bare auipc value (pc-dependent until a low part is added), 'addr' = an
    # address (an auipc value plus a low part, or one moved by addi / mv)
    state = {}
    spills = {}  # (base reg, offset) -> (value, kind) stored there by sd

    def shown(v):
        return 'hi' if v[1] == 'hi' else R.name(v[0])
    out = []
    for k in range(a, b):
        w, s = words[k], slots[k]
        F = pl.fields(w)
        op = F['op']
        simm = pl.sext(((w >> 25) << 5) | ((w >> 7) & 31), 12)
        if s is not None and s[0] in ('PCall', 'PTail'):
            out.append(s)
        elif op == 0x17:
            out.append(('PHi', F['rd']))
        elif s is not None and s[0] == 'PLdHi':
            out.append(('LD', w & IMASK, R.name(s[4])))
        elif s is not None and s[0] == 'PAddHi':
            out.append(('ADDI', w & IMASK, R.name(s[4])))
        elif F['rs1'] in state and (op in (0x03, 0x07, 0x67) or (op == 0x13 and F['f3'] == 0)):
            out.append(('I', w & IMASK, R.name(pl.zcanon(state[F['rs1']][0] + F['iimm']))))
        elif F['rs1'] in state and op in (0x23, 0x27):
            out.append(('S', w & SMASK, R.name(pl.zcanon(state[F['rs1']][0] + simm)),
                        shown(state[F['rs2']]) if F['rs2'] in state else ''))
        elif op == 0x23 and F['f3'] == 3 and F['rs2'] in state:
            out.append(('SPILL', w, shown(state[F['rs2']])))
        elif op == 0x03 and F['f3'] == 3 and (F['rs1'], F['iimm']) in spills:
            out.append(('RELOAD', w, shown(spills[(F['rs1'], F['iimm'])])))
        elif op not in (0x6f, 0x37) and pl.reads(w) & set(state):
            out.append(('OPAQUE', w, tuple(sorted(shown(state[r]) for r in pl.reads(w) & set(state)))))
        else:
            out.append(('PW', w))
        if op == 0x23:
            if F['f3'] == 3 and F['rs2'] in state and F['rs1'] not in state:
                spills[(F['rs1'], simm)] = state[F['rs2']]
            else:
                spills.pop((F['rs1'], simm), None)
        if op == 0x17:
            v = his[s[2]] if s is not None else pl.zcanon(base + 4 * k + pl.sext((w >> 12) << 12, 32))
            state[F['rd']] = (v, 'hi')
        elif op == 0x13 and F['f3'] == 0 and F['rs1'] in state and F['rd'] != 0:
            state[F['rd']] = (pl.zcanon(state[F['rs1']][0] + F['iimm']), 'addr')
        elif op == 0x03 and F['f3'] == 3 and (F['rs1'], F['iimm']) in spills and F['rd'] != 0:
            state[F['rd']] = spills[(F['rs1'], F['iimm'])]
        else:
            r = pl.writes_int(w)
            if r is not None:
                state.pop(r, None)
                for key in [x for x in spills if x[0] == r]:
                    del spills[key]
    return out


def per_func(pl, R, L):
    offs = [v - L['base'] for v, _ in L['funcs']] + [4 * L['nslots']]
    return {n: (v, norm_func(pl, R, L, offs[i] // 4, offs[i + 1] // 4)) for i, (v, n) in enumerate(L['funcs'])}


def kinds(L):
    return Counter('PW' if s is None else s[0] for s in L['slots'])


def main():
    pl = load_palist(sys.argv[1])
    Lo = build(pl, sys.argv[2], sys.argv[3])
    Ln = build(pl, sys.argv[4], sys.argv[5])
    Ro, Rn = Resolver(sys.argv[3]), Resolver(sys.argv[5])
    print('# range: old 0x%x +%d slots, new 0x%x +%d slots' % (Lo['base'], Lo['nslots'], Ln['base'], Ln['nslots']))
    print('# slot kinds old: %s' % dict(sorted(kinds(Lo).items())))
    print('# slot kinds new: %s' % dict(sorted(kinds(Ln).items())))
    print('# objects old %d new %d; hi old %d new %d; syms old %d new %d'
          % (len(Lo['objs']), len(Ln['objs']), len(Lo['his']), len(Ln['his']), len(Lo['syms']), len(Ln['syms'])))
    so, sn = set(Lo['syms']), set(Ln['syms'])
    print('# syms only-old: %s; only-new: %s; order changed: %s'
          % (sorted(so - sn), sorted(sn - so), Lo['syms'] != Ln['syms']))
    for nm in sorted(so & sn):
        a, b = Ro.name(Lo['sigma'][nm]), Rn.name(Ln['sigma'][nm])
        if a != b:
            print('# SIGMA-NAME-DIFFERS %s %s %s' % (nm, a, b))
    ob = Counter(Ro.name(t) for t in Lo['objs'])
    nb = Counter(Rn.name(t) for t in Ln['objs'])
    print('# objects by name only-old: %s' % sorted((ob - nb).elements()))
    print('# objects by name only-new: %s' % sorted((nb - ob).elements()))
    Fo, Fn = per_func(pl, Ro, Lo), per_func(pl, Rn, Ln)
    for tag, F in (('old', Fo), ('new', Fn)):
        c = Counter(x[0] for _, xs in F.values() for x in xs)
        print('# normalized forms %s: %s' % (tag, dict(sorted(c.items()))))
    print('# functions only-old: %s; only-new: %s' % (sorted(set(Fo) - set(Fn)), sorted(set(Fn) - set(Fo))))
    print('# function order changed: %s' % ([n for _, n in Lo['funcs']] != [n for _, n in Ln['funcs']]))
    print('function\told_addr\tnew_addr\told_slots\tnew_slots\tverdict\tdetail')
    tally = Counter()
    details = []
    for v, n in Ln['funcs']:
        if n not in Fo:
            continue
        (va, so_), (vb, sn_) = Fo[n], Fn[n]
        if so_ == sn_:
            verdict, detail = 'EQUAL', ''
        else:
            verdict = 'DIFFERENT'
            sm = difflib.SequenceMatcher(a=so_, b=sn_, autojunk=False)
            ops = [o for o in sm.get_opcodes() if o[0] != 'equal']
            detail = 'size %d -> %d slots; %d edit blocks; first at old +0x%x' % (
                len(so_), len(sn_), len(ops), 4 * ops[0][1])
            for tag, i1, i2, j1, j2 in ops:
                details.append('%s\t%s old +0x%x..+0x%x new +0x%x..+0x%x\t%s\t->\t%s'
                               % (n, tag, 4 * i1, 4 * i2, 4 * j1, 4 * j2, so_[i1:i2], sn_[j1:j2]))
        tally[verdict] += 1
        print('%s\t0x%x\t0x%x\t%d\t%d\t%s\t%s' % (n, va, vb, len(so_), len(sn_), verdict, detail))
    print('# tally: %s' % dict(tally))
    print('# edit blocks of DIFFERENT functions:')
    for d in details:
        print('#  ' + d)


if __name__ == '__main__':
    main()
