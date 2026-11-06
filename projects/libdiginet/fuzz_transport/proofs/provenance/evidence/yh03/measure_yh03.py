#!/usr/bin/env python3
"""measure_yh03.py: measure every cell of a unit's YH03.v against the unit's OWN pinned image.

Usage:
  measure_yh03.py --image P=<pin>:<unstripped twin> --image U=<pin>:<unstripped twin> \
                  --file P=lib/Reusable/YH03.v --file U=lib/U/Reusable/YH03.v [--out cells.tsv]

The pin gives the loaded bytes; the twin gives the symbol and section tables. The twin is used only if its
program headers equal the pin's and its PT_LOAD bytes equal the pin's except e_shoff / e_shnum / e_shstrndx
(ELF header) and the .note.gnu.build-id descriptor (exit 2 otherwise).

One rule per cell kind (no donor value is read):
  src0_A_<n>  start (st_value) of the STT_FUNC that <n> names; every symbol that answers <n> must agree.
  src0_E_<n>  st_value + st_size of that function.
  src0_D_got_<s>         the one .got slot whose 8 bytes hold the address of data symbol <s>.
  src0_D_const_<N>_0x<h> the one 8-byte little-endian occurrence of 0x<h> in the loaded image (if it occurs
                         more than once: the one occurrence the code forms an address of).
  src0_D_debruijn32      the one 32-byte count-trailing-zeros table in the loaded image: musl's debruijn32, or
                         the 0x077cb531 table LLVM emits when it turns musl's a_ctz_32 into cttz.
  src0_D_str_<s>         the one occurrence of the bytes <s> + NUL in the loaded image.
  src0_D_<n>  start of the data symbol that <n> names (STT_OBJECT / STT_NOTYPE, never a mapping symbol $d / $x).
  src0_vmlock (option Z) None iff the image links no vmlock object; Some v iff v is vmlock's address.
Name map: <n>, _<n>, __<n>, ___<n>, plus ALIAS below (musl's mallocng renames).
Every D cell also lists the code sites that form its address (auipc / lui + addi / load / store pairs).
Verdicts: OK (value = measured), WRONG (value != measured), UNMEASURABLE (no unique answer; reason given).
Exit 0 iff no cell is WRONG or UNMEASURABLE; 1 otherwise.
"""
import argparse, fnmatch, hashlib, re, struct, sys
from elftools.elf.elffile import ELFFile

ALIAS = {
    'alloc_meta': ['__malloc_alloc_meta'],            # mallocng glue.h: #define alloc_meta __malloc_alloc_meta
    'size_classes': ['__malloc_size_classes'],        # mallocng meta.h: #define size_classes __malloc_size_classes
    'oft_aligned_copy_empty': ['*_aligned_copy.empty'],  # the harness's aligned-copy `static ... empty[]`
}
DEB_MUSL = bytes([0, 1, 23, 2, 29, 24, 19, 3, 30, 27, 25, 11, 20, 8, 4, 13,
                  31, 22, 28, 18, 26, 10, 7, 12, 21, 17, 9, 6, 16, 5, 15, 14])
DEB_LLVM = bytes([0, 1, 28, 2, 29, 14, 24, 3, 30, 22, 20, 15, 25, 17, 4, 8,
                  31, 27, 13, 23, 21, 19, 16, 7, 26, 12, 18, 6, 11, 5, 10, 9])


class Image:
    def __init__(self, key, pin, twin):
        self.key, self.pin, self.twin = key, pin, twin
        self.sha = {p: hashlib.sha256(open(p, 'rb').read()).hexdigest() for p in (pin, twin)}
        with open(pin, 'rb') as f:
            e = ELFFile(f)
            self.phdrs = [dict(s.header) for s in e.iter_segments()]
            self.loads = [(s['p_vaddr'], s['p_memsz'], s['p_flags'], s.data())
                          for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
        with open(twin, 'rb') as f:
            e = ELFFile(f)
            phdrs = [dict(s.header) for s in e.iter_segments()]
            tloads = [(s['p_vaddr'], s['p_memsz'], s['p_flags'], s.data())
                      for s in e.iter_segments() if s['p_type'] == 'PT_LOAD']
            self.secs = {s.name: (s['sh_addr'], s['sh_addr'] + s['sh_size'])
                         for s in e.iter_sections() if s['sh_addr']}
            self.syms = [(s.name, s['st_value'], s['st_size'], s['st_info']['type'])
                         for s in e.get_section_by_name('.symtab').iter_symbols()
                         if s['st_shndx'] not in ('SHN_UNDEF', 'SHN_ABS') and s.name]
        bid = self.secs.get('.note.gnu.build-id')
        allowed = set(range(0x28, 0x30)) | {0x3c, 0x3d, 0x3e, 0x3f}   # e_shoff, e_shnum, e_shstrndx (file offsets)
        self.pindiff = []
        ok = phdrs == self.phdrs and len(tloads) == len(self.loads)
        for (va, msz, fl, a), (vb, mszb, flb, b) in zip(self.loads, tloads):
            ok &= (va, msz, fl, len(a)) == (vb, mszb, flb, len(b))
            for i in (i for i in range(min(len(a), len(b))) if a[i] != b[i]):
                addr = va + i
                in_hdr = self.loads[0][0] == va and i in allowed
                in_bid = bid is not None and bid[0] + 16 <= addr < bid[1]
                self.pindiff.append(addr)
                ok &= in_hdr or in_bid
        self.pin_ok = ok
        self.funcs = sorted({(a, sz, n) for n, a, sz, t in self.syms if t == 'STT_FUNC'})
        self.xrefs = self._xrefs()

    def read(self, a, n):
        for va, msz, fl, d in self.loads:
            if va <= a and a + n <= va + len(d):
                return d[a - va:a - va + n]
        return None

    def find(self, pat):
        out = []
        for va, msz, fl, d in self.loads:
            i = d.find(pat)
            while i >= 0:
                out.append(va + i)
                i = d.find(pat, i + 1)
        return out

    def _xrefs(self):
        """address -> code sites that form it (RV64GC, one linear pass per function): a register holds a known
        value after lui / auipc and keeps it through addi / c.addi / c.mv chains and, for the callee-saved
        registers, across calls; a site is an addi that yields a value, or a load / store whose address is one."""
        xr = {}
        sx = lambda v, b: v - (1 << b) if v & (1 << (b - 1)) else v
        caller_saved = {1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31}
        for fa, sz, n in self.funcs:
            code = self.read(fa, sz)
            if not code:
                continue
            val, pc = {}, 0
            site = lambda a: xr.setdefault(a, []).append('%s+%#x' % (n, pc))
            while pc + 2 <= len(code):
                h = struct.unpack_from('<H', code, pc)[0]
                if h & 3 != 3:
                    q, f3, r = h & 3, h >> 13, (h >> 7) & 31
                    rs1p, rp2 = 8 + ((h >> 7) & 7), 8 + ((h >> 2) & 7)
                    if q == 1 and f3 == 0 and r:                                   # c.addi
                        if r in val:
                            val[r] += sx(((h >> 12) & 1) << 5 | ((h >> 2) & 31), 6)
                            site(val[r])
                    elif q == 2 and f3 == 4 and not (h >> 12) & 1 and (h >> 2) & 31 and r:   # c.mv
                        if (h >> 2) & 31 in val:
                            val[r] = val[(h >> 2) & 31]
                        else:
                            val.pop(r, None)
                    elif q == 0 and f3 in (2, 3, 6, 7):                            # c.lw / c.ld / c.sw / c.sd
                        off = ((h >> 10) & 7) << 3 | (((h >> 6) & 1) << 2 | ((h >> 5) & 1) << 6 if f3 in (2, 6)
                                                      else ((h >> 5) & 3) << 6)
                        if rs1p in val:
                            site(val[rs1p] + off)
                        if f3 in (2, 3):
                            val.pop(rp2, None)
                    else:   # any other compressed op: drop every register it can write
                        for x in (r, rs1p, rp2):
                            val.pop(x, None)
                        if q == 2 and h >> 12 == 0b1001 and not (h >> 2) & 31 and r:   # c.jalr: a call
                            for x in caller_saved:
                                val.pop(x, None)
                    pc += 2
                    continue
                if pc + 4 > len(code):
                    break
                i = struct.unpack_from('<I', code, pc)[0]
                op, rd, rs1, f3 = i & 0x7f, (i >> 7) & 31, (i >> 15) & 31, (i >> 12) & 7
                if op in (0x17, 0x37):                                             # auipc / lui
                    val[rd] = sx(i & 0xfffff000, 32) + (fa + pc if op == 0x17 else 0)
                elif op == 0x13 and f3 == 0:                                       # addi
                    if rs1 in val:
                        val[rd] = val[rs1] + sx(i >> 20, 12)
                        site(val[rd])
                    else:
                        val.pop(rd, None)
                elif op in (0x03, 0x07, 0x23, 0x27):                               # loads / stores
                    imm = sx(i >> 20, 12) if op in (0x03, 0x07) else sx(((i >> 25) << 5) | ((i >> 7) & 31), 12)
                    if rs1 in val:
                        site(val[rs1] + imm)
                    if op == 0x03:
                        val.pop(rd, None)
                elif op in (0x67, 0x6f):                                           # jalr / jal
                    if rd:
                        for x in caller_saved | {rd}:
                            val.pop(x, None)
                elif op != 0x63:                                                   # any other non-branch op
                    val.pop(rd, None)
                val.pop(0, None)
                pc += 4
        return xr

    def names(self, n):
        pats = ALIAS.get(n, []) + [n, '_' + n, '__' + n, '___' + n]
        return [s for s in self.syms if any(fnmatch.fnmatchcase(s[0], p) for p in pats)]


def measure(M, cell, value):
    """-> (measured, evidence) or (None, reason)."""
    xs = lambda a: ', '.join(sorted(set(M.xrefs.get(a, [])))) or 'none'
    if cell == 'src0_vmlock':
        v = [s for s in M.syms if s[0] in ('vmlock', '__vmlock_lockptr') and s[3] == 'STT_OBJECT']
        vw = [s for s in M.syms if s[0] == '__vm_wait']
        if not v:
            return 'None', 'no vmlock / __vmlock_lockptr object in symtab; __vm_wait %s' % (
                ', '.join('%#x+%d' % (a, sz) for _, a, sz, _ in vw) or 'absent')
        vm = [s for s in v if s[0] == 'vmlock']
        return ('Some %#x' % vm[0][1], 'vmlock+0') if len(vm) == 1 else (None, 'vmlock not unique')
    m = re.match(r'src0_([AED])_(.+)$', cell)
    if not m:
        return None, 'not an address / size cell kind this script knows'
    k, n = m.groups()
    if k in 'AE':
        fs = [s for s in M.names(n) if s[3] == 'STT_FUNC']
        ext = {(a, sz) for _, a, sz, _ in fs}
        if not fs:
            return None, 'no STT_FUNC answers %s' % n
        if len(ext) != 1:
            return None, 'functions answering %s disagree: %s' % (n, sorted(ext))
        (a, sz), = ext
        names = ' = '.join(sorted({s[0] for s in fs}))
        return (a if k == 'A' else a + sz), '%s is %#x..%#x (STT_FUNC, size %d)' % (names, a, a + sz, sz)
    if n.startswith('got_'):
        tgt = [s for s in M.names(n[4:]) if s[3] in ('STT_OBJECT', 'STT_NOTYPE') and not s[0].startswith('$')]
        if len({s[1] for s in tgt}) != 1:
            return None, 'data symbol %s not unique: %s' % (n[4:], tgt)
        t = tgt[0][1]
        lo, hi = M.secs['.got']
        slots = [a for a in range(lo, hi, 8) if M.read(a, 8) == struct.pack('<Q', t)]
        if len(slots) != 1:
            return None, '.got slots holding %#x: %s' % (t, [hex(s) for s in slots])
        return slots[0], '.got [%#x, %#x) slot %#x holds %s = %#x; xref %s' % (lo, hi, slots[0], tgt[0][0], t, xs(slots[0]))
    if n.startswith('const_') or n == 'debruijn32' or n.startswith('str_'):
        if n == 'debruijn32':
            pats = {'musl debruijn32': DEB_MUSL, 'LLVM cttz table (0x077cb531)': DEB_LLVM}
        elif n.startswith('str_'):
            pats = {'"%s\\0"' % n[4:]: n[4:].encode() + b'\0'}
        else:
            h = re.search(r'_0x([0-9a-fA-F]{1,16})$', n)
            if not h:
                return None, 'constant cell without a 0x<hex> suffix'
            pats = {'8 bytes LE %#018x' % int(h.group(1), 16): struct.pack('<Q', int(h.group(1), 16))}
        occ = [(a, what) for what, p in pats.items() for a in M.find(p)]
        if len(occ) > 1:
            byx = [(a, w) for a, w in occ if M.xrefs.get(a)]
            if len(byx) == 1:
                a, w = byx[0]
                return a, '%s at %s; the one the code forms: %#x (xref %s)' % (
                    w, ', '.join(hex(o) for o, _ in occ), a, xs(a))
            return None, 'ambiguous: %s at %s' % ('/'.join(pats), ', '.join(hex(o) for o, _ in occ))
        if not occ:
            return None, 'no occurrence of %s in the loaded image' % ' / '.join(pats)
        (a, w), = occ
        return a, 'the only %s in the loaded image is at %#x; xref %s' % (w, a, xs(a))
    ds = [s for s in M.names(n) if s[3] in ('STT_OBJECT', 'STT_NOTYPE') and not s[0].startswith('$')]
    if len({s[1] for s in ds}) != 1:
        return None, 'data symbols answering %s: %s' % (n, [(s[0], hex(s[1])) for s in ds] or 'none')
    s = ds[0]
    return s[1], '%s = %#x (size %d); xref %s' % (' = '.join(sorted({d[0] for d in ds})), s[1], s[2], xs(s[1]))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--image', action='append', required=True, help='KEY=PIN:UNSTRIPPED')
    ap.add_argument('--file', action='append', required=True, help='KEY=path/to/YH03.v')
    ap.add_argument('--out')
    a = ap.parse_args()
    imgs = {}
    for spec in a.image:
        k, rest = spec.split('=', 1)
        pin, twin = rest.split(':', 1)
        M = Image(k, pin, twin)
        imgs[k] = M
        print('IMAGE %s pin %s sha256 %s; twin %s sha256 %s; PT_LOAD %s (differing bytes: %s)' % (
            k, pin, M.sha[pin], twin, M.sha[twin], 'EQUAL' if M.pin_ok else 'DIFFERENT',
            ' '.join(hex(x) for x in M.pindiff) or 'none'))
        if not M.pin_ok:
            sys.exit(2)
    rows = []
    for spec in a.file:
        k, path = spec.split('=', 1)
        M = imgs[k]
        for ln, line in enumerate(open(path), 1):
            d = re.match(r'\s*Definition\s+(\S+)\s*:\s*(Z|option Z)\s*:=\s*(.+?)\s*\.\s*$', line)
            if not d:
                continue
            cell, ty, val = d.groups()
            meas, ev = measure(M, cell, val)
            if meas is None:
                rows.append((path, ln, cell, val, '-', 'UNMEASURABLE', ev))
                continue
            if ty == 'Z':
                want = '%#x' % meas
                v = int(val, 0) if re.fullmatch(r'0x[0-9a-fA-F]+|\d+', val) else None
                verdict = 'OK' if v == meas else 'WRONG'
            else:
                want = meas
                sv = re.fullmatch(r'Some\s+\(?\s*(0x[0-9a-fA-F]+|\d+)\s*\)?', val)
                same_some = sv is not None and meas.startswith('Some ') and int(sv.group(1), 0) == int(meas[5:], 0)
                verdict = 'OK' if (val == meas == 'None') or same_some else 'WRONG'
            rows.append((path, ln, cell, val, want, verdict, ev))
    out = ['file\tline\tcell\tvalue\tmeasured\tverdict\tevidence'] + ['\t'.join(map(str, r)) for r in rows]
    text = '\n'.join(out) + '\n'
    if a.out:
        open(a.out, 'w').write(text)
    else:
        sys.stdout.write(text)
    cnt = {}
    for r in rows:
        cnt[(r[0], r[5])] = cnt.get((r[0], r[5]), 0) + 1
    for (f, v), c in sorted(cnt.items()):
        print('COUNT %s %s %d' % (f, v, c))
    sys.exit(0 if all(r[5] == 'OK' for r in rows) else 1)


if __name__ == '__main__':
    main()
