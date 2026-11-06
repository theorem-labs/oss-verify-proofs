#!/usr/bin/env python3
"""escape.py -- for EVERY C-string row this record certifies (settlement CSTR-* in out/fulldiff.tsv), the facts the criterion
needs: who reads the string, and how far the two images agree past it.

CRITERION (stated once, in RECORD.md): a target is settled by the extent a NAMED reader can read; when the pointer escapes the
compared function, the record names that reader, or gives a measured equal window.

Per row, by ADDRESS (X = cgif-B twin, Y = decode-B twin; the function addresses from fulldiff.tsv), and in BOTH images:
  - uses: the register the target word writes is followed forward through the function's code (capstone): copies (mv,
    addi _, _, 0) extend it, any other write ends it, both arms of every branch are followed, a store to a stack slot is
    followed into every later `ld` of that slot. A use is
      ARG <callee> <reg>      passed in a0..a7 to a direct call (the callee is the reader),
      TAILARG <callee> <reg>  the same through a tail jump out of the function,
      RET                     returned in a0 (the readers are the callers: each caller is followed the same way, 2 levels),
      STORE <base>+<imm>      stored to memory that is not a stack slot (an object field),
      READ <width>@<imm>      loaded inside the function,
      INDIRECT                reaches an indirect jump / call while live,
      LIMIT                   the exploration budget ran out.
  - window: the number of bytes, from the target, that are equal in both images (file bytes, read until the first
    difference or the end of the file-backed segment); `past NUL` = window - string length (incl. the NUL).
Writes out/escape.tsv and prints the counts. usage: escape.py"""
import collections, os, re, sys, importlib.util
from capstone import Cs, CS_ARCH_RISCV, CS_MODE_RISCV64, CS_MODE_RISCVC
TOOLS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLS)
import common
sc = common.kit_module(common.CMP_PY)
md = Cs(CS_ARCH_RISCV, CS_MODE_RISCV64 | CS_MODE_RISCVC)
ARGS = ['a%d' % i for i in range(8)]
CLOBBER = set(ARGS) | {'ra'} | {'t%d' % i for i in range(7)}
BR = {'beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu', 'beqz', 'bnez', 'blez', 'bgez', 'bltz', 'bgtz', 'bgt', 'ble', 'bgtu', 'bleu'}
LD = {'lb': 1, 'lbu': 1, 'lh': 2, 'lhu': 2, 'lw': 4, 'lwu': 4, 'ld': 8}
ST = {'sb', 'sh', 'sw', 'sd'}
BUDGET = 6000


class Image:
    def __init__(self, path):
        self.I = sc.Img(path)
        self.funcs = sorted((v, z, n) for v, z, n, t in self.I.syms if t == 'STT_FUNC' and z > 0)
        self.starts = collections.defaultdict(list)
        for v, z, n in self.funcs:
            self.starts[v].append(n)
        self._dis, self._callers, self.cases = {}, None, {}
        from elftools.elf.elffile import ELFFile
        g = ELFFile(open(path, 'rb')).get_section_by_name('.got')
        self._got = (g['sh_addr'], g['sh_addr'] + g['sh_size'], 8) if g is not None else None

    def gotrange(self):
        return self._got

    def name_at(self, a):
        l = self.starts.get(a)
        return sorted(l)[0] if l else '%#x' % a

    def home(self, a):
        best = None
        for v, z, n, t in self.I.syms:
            if t in ('STT_OBJECT', 'STT_FUNC') and z > 0 and v <= a < v + z and (best is None or z < best[1]):
                best = (n, z, a - v)
        return '%s+%#x' % (best[0], best[2]) if best else '%#x' % a

    def dis(self, a, z):
        if (a, z) not in self._dis:
            b = sc.frd(self.I, a, z)
            ins = [] if b is None else [(i.address - a, i.mnemonic.replace('c.', ''), i.op_str, i.size)
                                        for i in md.disasm(b, a)]
            self._dis[(a, z)] = ins
        return self._dis[(a, z)]

    def _index(self):
        """one pass over every FUNC: direct calls (target -> [(caller, size, call offset)]) and every word the kit's
        `targets` resolves to an absolute address (address -> [(function, size, word offset, opcode)])"""
        self._callers, self.refs, self.wtarget = collections.defaultdict(list), collections.defaultdict(list), {}
        for v, z, n in self.funcs:
            b = sc.frd(self.I, v, z)
            if b is None:
                continue
            w = sc.bc_words(b); t = sc._g['targets'](v, b)
            for i, (o, x, nb) in enumerate(w):
                if i not in t or nb != 4:
                    continue
                tg = t[i][1]
                self.wtarget[v + o] = tg
                rdx = (x >> 7) & 31
                if (x & 0x7f) in (0x6f, 0x67) and (rdx == 1 or (rdx == 0 and tg in self.starts and not v <= tg < v + z)):
                    self._callers[tg].append((v, z, o))      # a call (rd = ra) or a tail jump to a function start
                self.refs[tg].append((v, z, o, x & 0x7f))

    def callers(self, target):
        """[(caller start, caller size, offset of the call)] for direct calls (jal ra / auipc+jalr ra) to target"""
        if self._callers is None:
            self._index()
        return sorted(set(self._callers.get(target, [])))

    def reg_value(self, a, z, k, reg, depth=3):
        """the absolute address register `reg` holds just before instruction index k of the function at a, when the
        instruction that last wrote it is an auipc-pair word the kit's `targets` resolves (or a mv from such a register)"""
        if self._callers is None:
            self._index()
        ins = self.dis(a, z)
        for j in range(k - 1, -1, -1):
            o, mn, op, n = ins[j]
            ops = [x.strip() for x in op.split(',')] if op else []
            if not ops or ops[0] != reg or mn in ST or mn in BR:
                continue
            if a + o in self.wtarget and mn in ('addi', 'ld'):
                tg = self.wtarget[a + o]
                if mn == 'addi':
                    return tg
                if self.I.sec(tg) == '.got':          # `ld r, lo(auipc)` of a .got cell: the address the cell holds
                    c8 = sc.frd(self.I, tg, 8)
                    return int.from_bytes(c8, 'little') if c8 else None
                return None
            if mn == 'mv' and depth:
                return self.reg_value(a, z, j, ops[1], depth - 1)
            return None
        return None

    def field_readers(self, addr, owner, limit=8):
        """functions that load the 8-byte field at `addr` (owner = the object's start): a load word the kit resolves to
        addr, or `ld x, (addr - owner)(r)` within 48 instructions after an auipc-pair word that puts owner in r. Each
        loaded register is followed with track()."""
        if self._callers is None:
            self._index()
        found = []
        for v, z, o, opc in self.refs.get(addr, []):
            if opc == 0x03:
                ins = self.dis(v, z); k = [i for i, x in enumerate(ins) if x[0] == o]
                if k:
                    found.append((v, z, k[0], ins[k[0]][2].split(',')[0].strip()))
        # words that put `owner` in a register: an auipc-pair addi resolved to owner, or a load of a .got cell that holds owner
        cells = [g for g in range(*self.gotrange()) if sc.frd(self.I, g, 8) == owner.to_bytes(8, 'little')] if self.gotrange() else []
        srcs = [(v, z, o) for v, z, o, opc in self.refs.get(owner, []) if opc == 0x13] + \
               [(v, z, o) for g in cells for v, z, o, opc in self.refs.get(g, []) if opc == 0x03]
        for v, z, o in srcs:
            ins = self.dis(v, z); k = [i for i, x in enumerate(ins) if x[0] == o]
            if not k:
                continue
            r = ins[k[0]][2].split(',')[0].strip()
            for j in range(k[0] + 1, min(len(ins), k[0] + 48)):
                oj, mj, pj, nj = ins[j]
                m = re.match(r'(\w+), (-?(?:0x[0-9a-f]+|\d+))\(%s\)$' % r, pj)
                if mj == 'ld' and m and imm(m.group(2)) == addr - owner:
                    found.append((v, z, j, m.group(1)))
                pj0 = pj.split(',')[0].strip() if pj else ''
                if pj0 == r and mj not in ST and mj not in BR:
                    break
        out = []
        for v, z, j, x in sorted(set(found))[:limit]:
            us = track(self, v, z, j + 1, {x})
            out.append('%s: %s' % (self.name_at(v), ' '.join(sorted(' '.join(u) for u in us)) or 'no use found'))
        return out, len(set(found))


def imm(s):
    return int(s, 0)


def track(img, a, z, start_idx, live, depth=0):
    """uses of the pointer held in the registers `live`, from instruction index start_idx of the function at a"""
    ins = img.dis(a, z)
    at = {o: k for k, (o, m, p, n) in enumerate(ins)}
    uses, seen, work, steps = set(), set(), [(start_idx, frozenset(live))], 0
    stack_done = set()
    while work:
        k, T = work.pop()
        while 0 <= k < len(ins) and T:
            if (k, T) in seen:
                break
            seen.add((k, T)); steps += 1
            if steps > BUDGET:
                uses.add(('LIMIT',)); return uses
            o, mn, op, n = ins[k]
            ops = [x.strip() for x in op.split(',')] if op else []
            pc = a + o
            if mn == 'mv' or (mn == 'addi' and len(ops) == 3 and ops[2] in ('0', '0x0')):
                T = (T | {ops[0]}) if ops[1] in T else (T - {ops[0]})
                k += 1; continue
            if mn in ST:
                m = re.match(r'(-?(?:0x[0-9a-f]+|\d+))?\((\w+)\)', ops[1])
                if ops[0] in T:
                    off_, base = imm(m.group(1) or '0'), m.group(2)
                    if base == 'sp':
                        if off_ not in stack_done:
                            stack_done.add(off_)
                            for k2, (o2, m2, p2, n2) in enumerate(ins):
                                if m2 == 'ld' and re.match(r'(\w+), %s\(sp\)$' % re.escape(m.group(1) or '0'), p2):
                                    work.append((k2 + 1, frozenset({p2.split(',')[0].strip()})))
                    else:
                        owner = img.reg_value(a, z, k, base)
                        owners = ['%#x' % owner] if owner is not None else []
                        entry_a0 = base == 'a0' and not any(x[2].split(',')[0].strip() == 'a0' for x in ins[:k]
                                                            if x[1] not in ST and x[1] not in BR and x[2])
                        if owner is None and entry_a0:
                            # base is the entry a0 (the object the caller passes): each direct caller's a0 at the call --
                            # a global (auipc pair / .got cell) or a local of the caller (`addi a0, sp, K` before the call)
                            for cv, cz, co in img.callers(a):
                                cins = img.dis(cv, cz)
                                ck = [i for i, x in enumerate(cins) if x[0] == co]
                                if not ck:
                                    continue
                                ov = img.reg_value(cv, cz, ck[0], 'a0')
                                if ov is not None:
                                    owners.append('%#x' % ov)
                                    continue
                                w = [x for x in cins[:ck[0]] if x[2].split(',')[0].strip() == 'a0' and x[1] not in ST and x[1] not in BR]
                                mm = re.match(r'a0, sp, (0x[0-9a-f]+|\d+)$', w[-1][2]) if w and w[-1][1] == 'addi' else None
                                owners.append('stack:%s+%#x' % (img.name_at(cv), imm(mm.group(1))) if mm else '?')
                        elif owner is None:
                            owners.append('heap@%#x' % o)        # neither a global nor the caller's object: followed by its vtable
                        objs = ','.join(sorted(set(owners))) or '?'
                        uses.add(('STORE', '%s+%#x' % (base, off_), 'object=' + objs))
                k += 1; continue
            if mn in LD:
                m = re.match(r'(-?(?:0x[0-9a-f]+|\d+))?\((\w+)\)', ops[1])
                if m.group(2) in T:
                    uses.add(('READ', '%d@%s' % (LD[mn], m.group(1) or '0')))
                T = T - {ops[0]}
                k += 1; continue
            if mn in BR:
                tgt = o + imm(ops[-1])
                if tgt in at:
                    work.append((at[tgt], T))
                k += 1; continue
            if mn == 'ret':
                if 'a0' in T:
                    uses.add(('RET',))
                break
            if mn in ('j', 'jal'):
                callee_off = imm(ops[-1])
                tgt = pc + callee_off
                is_call = mn == 'jal' and (len(ops) == 1 or ops[0] == 'ra')
                if not is_call:
                    if a <= tgt < a + z and (tgt - a) in at:
                        k = at[tgt - a]; continue
                    for r in sorted(T & set(ARGS)):
                        uses.add(('TAILARG', img.name_at(tgt), r))
                    break
                for r in sorted(T & set(ARGS)):
                    uses.add(('ARG', img.name_at(tgt), r))
                T = T - CLOBBER
                k += 1; continue
            if mn in ('jr', 'jalr'):
                if mn == 'jalr' and (len(ops) == 1 or ops[0] == 'ra' or re.match(r'.*\(\w+\)$', op)):
                    # a call: the kit resolves `auipc r ; jalr ra, lo(r)` itself; for `auipc r ; ld r, lo(r) ; jalr r` the
                    # target is the function the .got cell holds (reg_value dereferences it)
                    base = re.findall(r'\((\w+)\)', op) or [ops[-1]]
                    off_ = re.match(r'(?:ra, )?(-?(?:0x[0-9a-f]+|\d+))\(', op)
                    if img._callers is None:
                        img._index()
                    tgt = img.wtarget.get(pc)
                    if tgt is None:
                        bv = img.reg_value(a, z, k, base[0])
                        tgt = None if bv is None else bv + (imm(off_.group(1)) if off_ else 0)
                    if tgt is not None:
                        for r in sorted(T & set(ARGS)):
                            uses.add(('ARG', img.name_at(tgt), r))
                    elif T & set(ARGS):
                        uses.add(('INDIRECT',))
                    T = T - CLOBBER
                    k += 1; continue
                cs = img.cases.get(a)
                if mn == 'jr' and cs:          # a switch dispatch: follow every case of this function's measured jump tables
                    for c in cs:
                        if c in at:
                            work.append((at[c], T))
                    break
                uses.add(('INDIRECT',))
                break
            if ops and mn not in ST and not mn.startswith('fence') and mn not in ('ecall', 'ebreak', 'nop'):
                T = T - {ops[0]}
            k += 1
    return uses


def row_uses(img, fn_a, fn_z, word, levels=2):
    ins = img.dis(fn_a, fn_z)
    k = [i for i, x in enumerate(ins) if x[0] == word][0]
    rd = ins[k][2].split(',')[0].strip()
    uses = track(img, fn_a, fn_z, k + 1, {rd})
    out = sorted(uses)
    if ('RET',) in uses and levels > 0:
        sub = collections.Counter()
        for cv, cz, co in img.callers(fn_a):
            cins = img.dis(cv, cz)
            ck = [i for i, x in enumerate(cins) if x[0] == co]
            if not ck:
                continue
            cu = track(img, cv, cz, ck[0] + 1, {'a0'})
            for u in cu:
                if u == ('RET',) and levels > 1:
                    for u2 in row_uses_ret(img, cv, cz, levels - 1):
                        sub['%s -> %s' % (img.name_at(cv), u2)] += 1
                else:
                    sub['%s: %s' % (img.name_at(cv), ' '.join(u))] += 1
        out = out + [('CALLERS', '; '.join(sorted(sub)) or 'none found (no direct caller)')]
    for u in sorted(uses):
        if u[0] != 'STORE':
            continue
        off_ = int(u[1].split('+')[1], 16)
        for ob in u[2][len('object='):].split(','):
            if not ob.startswith('0x'):
                out.append(('FIELD', '%s: object %s' % (u[1], ob)))
                continue
            ob = int(ob, 16)
            h = img.home(ob)
            rd_, nfound = img.field_readers(ob + off_, ob)
            out.append(('FIELD', '%s+%#x: %d loads; %s' % (h, off_, nfound, ' | '.join(rd_) or 'no load found')))
    return out


def row_uses_ret(img, fa, fz, levels):
    res = []
    for cv, cz, co in img.callers(fa):
        cins = img.dis(cv, cz)
        ck = [i for i, x in enumerate(cins) if x[0] == co]
        if ck:
            for u in track(img, cv, cz, ck[0] + 1, {'a0'}):
                res.append('%s: %s' % (img.name_at(cv), ' '.join(u)))
    return res or ['no direct caller']


def window(C, tc, D, td, cap=1 << 16):
    n = 0
    while n < cap:
        bc, bd = sc.frd(C, tc + n, 256), sc.frd(D, td + n, 256)
        if bc is None or bd is None:
            for k in range(256):
                x, y = sc.frd(C, tc + n, 1), sc.frd(D, td + n, 1)
                if x is None or y is None or x != y:
                    return n, 'end of file-backed bytes' if (x is None or y is None) else 'first difference'
                n += 1
            continue
        if bc != bd:
            return n + next(i for i in range(256) if bc[i] != bd[i]), 'first difference'
        n += 256
    return n, 'cap'


def load_tables():
    """objscan.tsv / ptrfollow.tsv / ptrfollow.out (reuse verdicts) when present: the whole-image field results"""
    p1, p2, p3 = (os.path.join(common.OUT, n) for n in ('objscan.tsv', 'ptrfollow.tsv', 'ptrfollow.out'))
    if not (os.path.exists(p1) and os.path.exists(p2) and os.path.exists(p3)):
        return None
    hd = lambda p: [dict(zip(open(p).readline().rstrip('\n').split('\t'), l.rstrip('\n').split('\t')))
                    for l in list(open(p))[1:] if l.strip()]
    verdict = collections.defaultdict(list)
    for l in open(p3):
        m = re.match(r'REUSE-VERDICT (cgif B|decode B) field \+(0x[0-9a-f]+): call \+0x[0-9a-f]+ (\S+) \((\S*)\) sees (.+) \((.+)\)$', l.strip())
        if m:
            verdict[(m.group(1), int(m.group(2), 16), m.group(3))].append((m.group(5), m.group(6)))
    return hd(p1), hd(p2), verdict


def heap_readers(img, a, z, so, base, h):
    """a field pointer / string stored at base+h of a heap object (store at offset so of the function at a): its vtable is the
    word-0 store on the same base register between the allocating call before the store and the next call; every vtable
    method that loads h(a0) (this, before a0 is overwritten) is a reader, and the loaded value is followed with track()"""
    ins = img.dis(a, z)
    k = [i for i, x in enumerate(ins) if x[0] == so][0]
    iscall = lambda x: x[1] in ('jal', 'jalr') and not x[2].startswith('zero')
    lo = max([j for j in range(k) if iscall(ins[j])] or [0])
    hi = min([j for j in range(k + 1, len(ins)) if iscall(ins[j])] or [len(ins)])
    vt = None
    for j in range(lo + 1, hi):
        mm = re.match(r'(\w+), (-?(?:0x[0-9a-f]+|\d+))?\(%s\)$' % base, ins[j][2])
        if ins[j][1] == 'sd' and mm and imm(mm.group(2) or '0') == 0:
            vt = img.reg_value(a, z, j, mm.group(1))
            if vt is not None:
                break
    sym = [(v, zz, n) for v, zz, n, t in img.I.syms if t == 'STT_OBJECT' and vt is not None and v <= vt < v + zz]
    if not sym or not sym[0][2].startswith('_ZTV'):
        return ['UNRESOLVED heap object (no vtable found at the store)']
    out = []
    for slot in range(vt, sym[0][0] + sym[0][1], 8):
        f = int.from_bytes(sc.frd(img.I, slot, 8), 'little')
        fz = [x for x in img.funcs if x[0] == f]
        if not fz:
            continue
        fins = img.dis(f, fz[0][1])
        for j, (oj, mj, pj, nj) in enumerate(fins):
            mm = re.match(r'(\w+), (-?(?:0x[0-9a-f]+|\d+))?\(a0\)$', pj)
            if mj in LD and mm and imm(mm.group(2) or '0') == h:
                us = track(img, f, fz[0][1], j + 1, {mm.group(1)})
                out.append('%s (vtable %s slot +%#x) +%#x: %s' % (img.name_at(f), sym[0][2], slot - vt, oj,
                                                                  ' '.join(sorted(' '.join(u) for u in us)) or 'no use found'))
            if pj and pj.split(',')[0].strip() == 'a0' and mj not in ST and mj not in BR:
                break
    return out or ['no vtable method loads this+%#x (vtable %s): UNREAD' % (h, sym[0][2])]


def primary(tag, uses, tabs, img=None, fa=None, fz=None):
    """the primary settlement of one row: the named readers, read by name from the uses and, for a store into an object
    field, from the whole-image field results (objscan.tsv: every load of the field, any base, through any pointer or
    copy; ptrfollow.tsv: the readers behind a stored field pointer; heap objects: their vtable methods)"""
    objrows, pfrows, verdict = tabs
    parts = []

    def field_text(r, off, lab):
        rd = []
        if r['load sites'] != '-':
            rd.append('loads: ' + r['load sites'])
        for p in pfrows:
            if p['image'] == tag and p['object'] == r['object'] and int(p['field'], 16) == off and \
                    p['reads of the field (and their uses)'] != 'none':
                rd.append('via the field pointer stored at %s: %s -> %s' % (p['site storing the field pointer'], p['method'],
                                                                            p['reads of the field (and their uses)']))
        for c in ([] if r['copies carrying the field'] == '-' else r['copies carrying the field'].split(' | ')):
            for cr in [x for x in objrows if x['image'] == tag and x['object'] == c and int(x['field'], 16) == off]:
                if cr['load sites'] == '-':
                    rd.append('copy %s: no load' % c)
                    continue
                for site in cr['load sites'].split(' ; '):
                    callee = site.split(' > ')[1].split(' +')[0] if ' > ' in site else None
                    v = verdict.get((tag, off, callee), [])
                    if v and all(s == 'rewritten' for s, src in v):
                        rd.append('copy %s: load %s is of the reused slot (the word is rewritten at %s before every call to %s)' % (
                            c, site, ','.join(sorted({src for s, src in v})), callee))
                    else:
                        rd.append('copy %s: load %s' % (c, site))
        unread = r['load sites'] == '-' and r['field pointers stored'] == '0' and r['copies carrying the field'] == '-'
        return 'field %s +%#x (%s): %s' % (r['object'], off, lab, 'UNREAD (whole-image scan: 0 loads, 0 field pointers '
                                          'stored, no copy)' if unread else ' | '.join(rd) or 'see objscan.out')

    for u in uses:
        if u[0] == 'ARG':
            parts.append('reader %s (%s)' % (u[1], u[2]))
        elif u[0] == 'TAILARG':
            parts.append('reader %s (%s, tail call)' % (u[1], u[2]))
        elif u[0] == 'READ':
            parts.append('in-function load %s' % u[1])
        elif u[0] == 'CALLERS':
            parts.append('returned; callers: %s' % u[1])
        elif u[0] in ('INDIRECT', 'LIMIT'):
            parts.append('UNRESOLVED %s' % u[0])
        elif u[0] == 'STORE':
            base, off = u[1].split('+')[0], int(u[1].split('+')[1], 16)
            for ob in u[2][len('object='):].split(','):
                if ob.startswith('heap@') and img is not None:
                    parts.append('field of a heap object +%#x: %s' % (off, ' | '.join(heap_readers(img, fa, fz, int(ob[5:], 16), base, off))))
                    continue
                rows = [r for r in objrows if r['image'] == tag and r['base'] == ob and int(r['field'], 16) == off] \
                    if ob.startswith(('0x', 'stack:')) else []
                # a copy written back into an object is the object itself: its loads are on the object's row
                rows = [r for r in rows if not r['object'].startswith('copy of')] or rows
                if not rows:
                    parts.append('field %s+%#x: UNRESOLVED object' % (ob, off))
                    continue
                for r in rows:
                    parts.append(field_text(r, off, ob))
    return ' ;; '.join(parts) or 'none'


def main():
    X, Y = Image(common.CGIF_B_TWIN), Image(common.DECODE_B_TWIN)
    tabs = load_tables()
    rows = [l.rstrip('\n').split('\t') for l in list(open(os.path.join(common.OUT, 'fulldiff.tsv')))[1:]]
    common.jump_cases(X, Y)                         # every measured rel4 jump table: a `jr` goes to its cases
    rows = [r for r in rows if r[5].startswith('CSTR')]
    out, kinds, minpast = [], collections.Counter(), {}
    for fn, ax, ay, word, kind, settle, tx, ty, why in rows:
        ax, ay, w, tc, td = int(ax, 16), int(ay, 16), int(word, 16), int(tx, 16), int(ty, 16)
        zx, zy = X.I.fsym(fn)[1], Y.I.fsym(fn)[1]
        ux = row_uses(X, ax, zx, w)
        uy = row_uses(Y, ay, zy, w)
        if tabs:                                    # the whole-image field results replace the narrower field search
            ux = [u for u in ux if u[0] != 'FIELD']
            uy = [u for u in uy if u[0] != 'FIELD']
        norm = lambda us: sorted(' '.join(u[:2]) if u[0] == 'STORE' else
                                 (u[0] + ' ' + re.sub(r'0x[0-9a-f]+', '#', u[1]) if u[0] == 'FIELD' else ' '.join(u))
                                 for u in us if u[0] != 'CALLERS')
        same = 'same' if norm(ux) == norm(uy) else 'DIFFER: %s' % ' | '.join(norm(uy))
        s = sc.frd(X.I, tc, 4096)
        L = s.index(b'\0') + 1
        wn, why_end = window(X.I, tc, Y.I, td)
        esc = [u for u in ux if u[0] in ('RET', 'STORE', 'INDIRECT', 'LIMIT', 'TAILARG')]
        cls = 'ESCAPES' if esc else ('ARG-ONLY' if all(u[0] == 'ARG' for u in ux) and ux else
                                     ('NO-USE-FOUND' if not ux else 'IN-FUNCTION'))
        kinds[(settle, cls)] += 1
        minpast.setdefault(cls, []).append(wn - L)
        px = primary('cgif B', ux, tabs, X, ax, zx) if tabs else '-'
        py = primary('decode B', uy, tabs, Y, ay, zy) if tabs else '-'
        pn = lambda t: re.sub(r'0x[0-9a-f]+', '#', t)
        out.append((fn, word, settle, tx, ty, str(L), str(wn - L), why_end, cls,
                    ' ; '.join(' '.join(u) for u in ux), same, px, 'same' if pn(px) == pn(py) else 'DIFFER: ' + py))
    with open(os.path.join(common.OUT, 'escape.tsv'), 'w') as f:
        f.write('function\tword\tsettlement\tX target\tY target\tstring bytes incl NUL\tequal bytes past NUL (both images; '
                'the SECOND measurement)\twindow ends at\tuse class\tuses in X\tuses in Y\tPRIMARY settlement: the named '
                'readers (cgif B)\tprimary in decode B\n')
        for r in out:
            f.write('\t'.join(r) + '\n')
    print('C-string rows %d: %s' % (len(out), dict(sorted(kinds.items()))))
    for c, l in sorted(minpast.items()):
        print('  %s: %d rows, equal bytes past the NUL: min %d, max %d' % (c, len(l), min(l), max(l)))
    print('rows whose uses differ between the images: %d' % sum(1 for r in out if r[10] != 'same'))
    print('rows whose primary settlement differs between the images: %d' % sum(1 for r in out if r[12] != 'same'))
    print('rows with an UNRESOLVED or NOT SCANNED part: %d' % sum(1 for r in out if 'UNRESOLVED' in r[11] or 'NOT SCANNED' in r[11]))

if __name__ == '__main__':
    main()
