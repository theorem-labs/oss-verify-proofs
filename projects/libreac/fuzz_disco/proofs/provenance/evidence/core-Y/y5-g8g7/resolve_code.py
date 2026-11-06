#!/usr/bin/env python3
"""resolve_code.py -- OLD -> NEW code addresses by FUNCTION pairing, not by elf_symbols's position runs.

elf_symbols aligns the two instruction streams by position. Where several functions have the same masked stream (the
1-instruction trampolines `j target`, the __asan_stack_malloc_N family, memset/memmove, fwrite/write, the program's
entry), it can pair a function with the wrong twin, and numeral_map then writes a wrong value for every literal inside it.
This module pairs functions instead:

  OLD functions = .eh_frame FDE ranges of OLD (works on a stripped OLD binary).
  NEW functions = FUNC symbols of NEW's unstripped twin (its symbol extract, or nm text), else NEW's FDE ranges.
  A pair needs the same length and the same masked instruction stream (kit rvelf.Code tokens: pc-relative and
  auipc-lo12 immediates masked). Several NEW candidates: keep the one whose pc-relative calls/jumps out of the function
  land on the NEW twins of the OLD targets (iterated to a fixed point); then elf_symbols's run value as a last tiebreak only
  when it is itself one of the identical candidates.
  OLD trampolines (a 4-byte `j T` outside every FDE): paired with the NEW 4-byte `j T'` outside every function body
  whose target T' is the NEW twin of T (pairing by target).

map_code(a) -> NEW address of OLD code address a (function start + same offset), or None when a's function has no
unique twin. Run as a script: prints the pairs elf_symbols gets wrong:  resolve_code.py OLD NEW NEWSYMS MAP.json
(with the kit directory, which holds rvelf.py and elf_symbols.py, on PYTHONPATH).

Symbol inputs (NEWSYMS, the source's recovered symbols) are text: a symbol extract `*.tsv` of an unstripped twin
(extract_symbols.py: tab-separated name, value hex, size, type, bind, section, in .symtab order, `#` header lines),
nm text `*.txt`, or a recovery cache `*.json`. An ELF with a .symtab is still read as before.
"""
import bisect, collections, json, re, struct, sys

import rvelf  # the kit's rvelf.py: its directory is on sys.path (port_core.py --kit-dir puts it there)
from elftools.elf.elffile import ELFFile
from elftools.dwarf.callframe import FDE


def fde_ranges(path):
    out = []
    with open(path, 'rb') as fh:
        e = ELFFile(fh)
        if not e.has_dwarf_info():
            return out
        d = e.get_dwarf_info()
        if not d.has_EH_CFI():
            return out
        for ent in d.EH_CFI_entries():
            if isinstance(ent, FDE):
                lo = ent.header['initial_location']
                out.append((lo, lo + ent.header['address_range']))
    return sorted(set(out))


def fde_records(path):
    """{function lo: (record address, record length)} of the .eh_frame FDEs (a literal inside an FDE record moves
    with the FDE of the paired function: the .eh_frame layouts of two builds are the same records reordered)."""
    out = {}
    with open(path, 'rb') as fh:
        e = ELFFile(fh)
        s = e.get_section_by_name('.eh_frame')
        if s is None or not e.has_dwarf_info():
            return out
        d = e.get_dwarf_info()
        if not d.has_EH_CFI():
            return out
        for ent in d.EH_CFI_entries():
            if isinstance(ent, FDE):
                out[ent.header['initial_location']] = (s['sh_addr'] + ent.offset, ent.header['length'] + 4)
    return out


def extract_rows(path):
    """the rows (name, value, size, type) of a symbol extract (.tsv), in its .symtab order."""
    out = []
    for l in open(path):
        if l.startswith('#'):
            continue
        f = l.rstrip('\n').split('\t')
        out.append((f[0], int(f[1], 16), int(f[2]), f[3]))
    return out


def sym_ranges(path):
    """FUNC symbols (lo, hi, name) from an unstripped ELF, its symbol extract (.tsv), or an nm text file (addr size
    type name)."""
    out = []
    if path.endswith('.tsv'):
        return sorted({(v, v + s, n) for n, v, s, t in extract_rows(path) if t == 'STT_FUNC' and s > 0})
    if path.endswith('.txt'):
        for l in open(path):
            p = l.split()
            if len(p) >= 4 and p[2] in 'Tt' and int(p[1], 16) > 0:
                lo = int(p[0], 16)
                out.append((lo, lo + int(p[1], 16), p[3]))
        return sorted(set(out))
    with open(path, 'rb') as fh:
        e = ELFFile(fh)
        st = e.get_section_by_name('.symtab')
        for s in st.iter_symbols():
            if s['st_info']['type'] == 'STT_FUNC' and s['st_size'] > 0:
                out.append((s['st_value'], s['st_value'] + s['st_size'], s.name))
    return sorted(set(out))


def old_syms_list(path):
    """the source's recovered symbols as (lo, size, name): `name addr size` text lines, port_addr_check.py's
    recovery cache JSON (`syms`: [addr, size, [names], type, kind]), or the symbol extract (.tsv) of the source
    image's unstripped twin (its sized FUNC and OBJECT symbols, in .symtab order)."""
    if path.endswith('.json'):
        out = [(s[0], s[1], s[2][0]) for s in json.load(open(path))['syms'] if s[2]]
    elif path.endswith('.tsv'):
        out = [(v, s, n) for n, v, s, t in extract_rows(path) if t in ('STT_FUNC', 'STT_OBJECT') and s > 0]
    else:
        out = []
        for l in open(path):
            f = l.split()
            if len(f) >= 3 and not l.startswith('#'):
                out.append((int(f[1], 16), int(f[2]), f[0]))
    return [x for x in out if not x[2].startswith('$')]  # never anchor on a mapping symbol ($d, $x)


def all_syms(path):
    """every sized FUNC/OBJECT symbol (lo, hi, name) of an unstripped ELF, its symbol extract (.tsv) or nm text."""
    out = []
    if path.endswith('.tsv'):
        return sorted({(v, v + s, n) for n, v, s, t in extract_rows(path)
                       if t in ('STT_FUNC', 'STT_OBJECT', 'STT_TLS') and s > 0})
    if path.endswith('.txt'):
        for l in open(path):
            p = l.split()
            if len(p) >= 4 and p[2] in 'TtDdBbRrVv' and int(p[1], 16) > 0 and not p[3].startswith('$'):
                lo = int(p[0], 16)
                out.append((lo, lo + int(p[1], 16), p[3]))
        return sorted(set(out))
    with open(path, 'rb') as fh:
        st = ELFFile(fh).get_section_by_name('.symtab')
        for s in st.iter_symbols():
            if s['st_info']['type'] in ('STT_FUNC', 'STT_OBJECT', 'STT_TLS') and s['st_size'] > 0:
                out.append((s['st_value'], s['st_value'] + s['st_size'], s.name))
    return sorted(set(out))


class NameMap:
    """OLD address -> NEW address by symbol NAME: the source's recovered symbols (`name addr size` lines) and the
    target's symbols; a name counts only when it is unique on both sides (after dropping `.llvm.N`) and the two
    sizes agree (an offset inside a symbol keeps its offset)."""

    def __init__(self, old_syms_txt, new_syms_path):
        norm = lambda n: re.sub(r'\.llvm\.\d+$', '', n)
        olds = []
        for lo, n, name in old_syms_list(old_syms_txt):
            olds.append((lo, lo + max(n, 1), norm(name)))
        news = [(lo, hi, norm(n)) for lo, hi, n in all_syms(new_syms_path)]
        on, nn = collections.Counter(n for _, _, n in olds), collections.Counter(n for _, _, n in news)
        nidx = {n: (lo, hi) for lo, hi, n in news if nn[n] == 1}
        self.old = sorted((lo, hi, n) for lo, hi, n in olds if on[n] == 1)
        self.olos = [x[0] for x in self.old]
        self.nidx = nidx

    def name_of(self, a):
        k = bisect.bisect_right(self.olos, a) - 1
        if k >= 0 and a < self.old[k][1]:
            return self.old[k]
        return None

    def map(self, a):
        s = self.name_of(a)
        if s is None or s[2] not in self.nidx:
            return None
        lo, hi = self.nidx[s[2]]
        if hi - lo != s[1] - s[0] and a != s[0]:
            return None
        return lo + (a - s[0])


def text_code(elf):
    r = next(s for s in elf.sections if s.kind == 'exec' and s.name == '.text')
    return rvelf.Code(elf.region_bytes(r), r.vaddr)


class Resolver:
    def __init__(self, old_path, new_path, new_syms=None, map_json=None, old_syms=None):
        self.old, self.new = rvelf.Elf(old_path), rvelf.Elf(new_path)
        self.co, self.cn = text_code(self.old), text_code(self.new)
        self.ofn = fde_ranges(old_path)
        # OLD is stripped: its functions are the FDE ranges, plus (FDE-less musl code) the source's recovered symbols
        # (`name addr size`, port_addr_check.py's recovery) that overlap no FDE range
        self.oname = {}
        if old_syms:
            xlo, xhi = self.co.pcs[0], self.co.pcs[-1] + 4
            fl = [lo for lo, _ in self.ofn]
            extra = []
            for lo, n, name in old_syms_list(old_syms):
                if not (xlo <= lo < xhi) or n <= 0:
                    continue
                self.oname.setdefault(lo, re.sub(r'\.llvm\.\d+$', '', name))
                k = bisect.bisect_right(fl, lo + n - 1) - 1
                if k >= 0 and self.ofn[k][1] > lo:
                    continue  # overlaps an FDE range: the FDE stands
                extra.append((lo, lo + n))
            self.ofn = sorted(set(self.ofn) | set(extra))
        self.nfn = [(lo, hi) for lo, hi, _ in sym_ranges(new_syms)] if new_syms else fde_ranges(new_path)
        seen = set(); nf = []
        for lo, hi in self.nfn:  # aliases (__wrap_f and __interceptor_trampoline_f) share one range
            if lo not in seen:
                seen.add(lo); nf.append((lo, hi))
        self.nfn = nf
        self.nnames = collections.defaultdict(set)
        for lo, hi, n in (sym_ranges(new_syms) if new_syms else []):
            self.nnames[lo].add(re.sub(r'\.llvm\.\d+$', '', n))
        self.nname = {lo: n for lo, hi, n in sorted(sym_ranges(new_syms), reverse=True)} if new_syms else {}
        self._nlos = sorted(self.nname)
        self.nhi = dict(self.nfn)
        self.look = None  # elf_symbols's run map: a CROSS-CHECK only, never a value
        if map_json:
            from elf_symbols import Lookup
            self.look = Lookup(json.load(open(map_json))['runs'])
        self.olos = [lo for lo, _ in self.ofn]
        self.ohi = dict(self.ofn)
        self.pairs, self.ambig = {}, {}
        self._ends = None
        self._pair_functions()
        self._pair_trampolines()
        self._pair_entries()
        self._data_refs()

    def _slice(self, code, lo, hi):
        i, j = code.index_of(lo), code.index_of(hi)
        if i is None:
            return None
        if j is None:
            j = bisect.bisect_left(code.pcs, hi)
        return i, j

    def _key(self, code, lo, hi):
        s = self._slice(code, lo, hi)
        return None if s is None else (hi - lo, tuple(code.tok[s[0]:s[1]]))

    def _outs(self, code, lo, hi):
        """pc-relative jal/c.j/branch targets that leave [lo, hi), in order."""
        s = self._slice(code, lo, hi)
        out = []
        for k in range(*s):
            sv = code.sens[k]
            if sv and sv[0] in ('jal', 'c.j', 'branch', 'c.bxxz') and not (lo <= sv[1] < hi):
                out.append(sv[1])
        return out

    def _pair_functions(self):
        idx = collections.defaultdict(list)
        for lo, hi in self.nfn:
            k = self._key(self.cn, lo, hi)
            if k:
                idx[k].append((lo, hi))
        cand = {}
        for lo, hi in self.ofn:
            if hi - lo == 4 and self._jtarget(self.co, lo) is not None:
                continue  # a trampoline: paired by its target in _pair_trampolines
            k = self._key(self.co, lo, hi)
            if k and idx.get(k):
                cand[(lo, hi)] = [c for c, _ in idx[k]]
        for o, cs in cand.items():
            if len(cs) == 1:
                self.pairs[o[0]] = cs[0]
        self.by_name, self.by_ref = {}, {}
        exec_lo = self.co.pcs[0]; exec_hi = self.co.pcs[-1] + 4
        dref = {}

        def refresh():
            """the data identities paired code forms so far (auipc+lo12 at the same instruction)."""
            dref.clear()
            for o0, n0 in self.pairs.items():
                hi = self.ohi[o0]
                so, sn = self._slice(self.co, o0, hi), self._slice(self.cn, n0, n0 + (hi - o0))
                for ko, kn in zip(range(*so), range(*sn)):
                    a, b = self.co.sens[ko], self.cn.sens[kn]
                    if a and b and a[0] == 'lo12' and b[0] == 'lo12':
                        dref.setdefault(a[1], b[1])

        def refmap(t):
            return self._fn_map(t) if exec_lo <= t < exec_hi else dref.get(t)

        def score(o, c):
            """(consistent, known): every address the OLD function forms (calls, jumps, auipc/lo12 data) that is
            already known maps to the address the NEW candidate forms at the same instruction."""
            so, sn = self._slice(self.co, *o), self._slice(self.cn, c, c + (o[1] - o[0]))
            known = 0
            for ko, kn in zip(range(*so), range(*sn)):
                a, b = self.co.sens[ko], self.cn.sens[kn]
                if not a or not b or a[0] not in ('jal', 'c.j', 'branch', 'c.bxxz', 'lo12'):
                    continue
                if o[0] <= a[1] < o[1]:
                    continue
                m = refmap(a[1])
                if m is not None:
                    known += 1
                    if m != b[1]:
                        return False, known
            return True, known
        changed = True
        while changed:
            changed = False
            refresh()
            for o, cs in cand.items():
                if o[0] in self.pairs or len(cs) < 2:
                    continue
                sc = {c: score(o, c) for c in cs}
                good = [c for c in cs if sc[c][0] and sc[c][1] > 0]
                if len(good) == 1:
                    self.pairs[o[0]] = good[0]; self.by_ref[o[0]] = cs; changed = True
            # callers: a paired function that calls OLD f at instruction k calls NEW g at the same instruction
            for o0, n0 in list(self.pairs.items()):
                f = self._fn_of(o0)
                if f is None:
                    continue
                so, sn = self._slice(self.co, *f), self._slice(self.cn, n0, n0 + (f[1] - f[0]))
                for ko, kn in zip(range(*so), range(*sn)):
                    a, b = self.co.sens[ko], self.cn.sens[kn]
                    if not a or not b or a[0] not in ('jal', 'c.j'):
                        continue
                    tf = self._fn_of(a[1])
                    if tf and tf[0] == a[1] and tf[0] not in self.pairs and b[1] in cand.get(tf, []):
                        self.pairs[tf[0]] = b[1]; self.by_ref[tf[0]] = cand[tf]; changed = True
            # names: the source's recovered name picks the one candidate of the same name
            for o, cs in cand.items():
                if o[0] in self.pairs or o[0] not in self.oname:
                    continue
                hit = [c for c in cs if self.oname[o[0]] in self.nnames.get(c, ())]
                if len(hit) == 1:
                    self.pairs[o[0]] = hit[0]; self.by_name[o[0]] = cs; changed = True
        self.tiebreak = []  # no elf_symbols tiebreak: what references and names leave open stays open
        for o, cs in cand.items():
            if o[0] not in self.pairs:
                self.ambig[o[0]] = cs

    def _fn_of(self, a):
        k = bisect.bisect_right(self.olos, a) - 1
        if k >= 0 and a < self.ofn[k][1]:
            return self.ofn[k]
        return None

    def _fn_map(self, a):
        tr = getattr(self, 'tramp', None)
        if tr:
            for o in (a, a - 1, a - 2, a - 3):  # a trampoline is one 4-byte `j`: its interior moves with it
                if o in tr:
                    return tr[o] + (a - o)
        f = self._fn_of(a)
        if f and f[0] in self.pairs:
            return self.pairs[f[0]] + (a - f[0])
        return None

    def name_conflicts(self):
        """pairs whose two sides carry different names (the source's recovered name is known and the NEW twin has
        no symbol of that name), for the name report."""
        out = []
        for o, n in sorted(list(self.pairs.items()) + list(self.tramp.items())):
            on = self.oname.get(o)
            if on and self.nnames.get(n) and on not in self.nnames[n]:
                out.append((o, n, on, sorted(self.nnames[n])))
        return out

    def _jtarget(self, code, pc):
        k = code.index_of(pc)
        if k is None or code.lens[k] != 4:
            return None
        raw = code.raws[k]
        if raw & 0x7f == rvelf.OP_JAL and (raw >> 7) & 31 == 0:
            return pc + rvelf.j_imm(raw)
        return None

    def _pair_trampolines(self):
        self.tramp = {}
        nfl = [lo for lo, _ in self.nfn]
        def in_new_fn(a):
            k = bisect.bisect_right(nfl, a) - 1
            return k >= 0 and a < self.nfn[k][1] and self.nfn[k][1] - self.nfn[k][0] > 4
        ntr = collections.defaultdict(list)
        for pc in self.cn.pcs:
            if in_new_fn(pc):
                continue
            t = self._jtarget(self.cn, pc)
            if t is not None:
                ntr[t].append(pc)
        for pc in self.co.pcs:
            f = self._fn_of(pc)
            if f and f[1] - f[0] != 4:
                continue
            t = self._jtarget(self.co, pc)
            if t is None:
                continue
            mt = self._fn_map(t)
            if mt is not None and len(ntr.get(mt, [])) == 1:
                self.tramp[pc] = ntr[mt][0]
        # check each pair by name: the NEW trampoline's symbol and its target's symbol name the same function
        self.tramp_check = {}
        for o, n in self.tramp.items():
            tn = self.nname.get(n)
            tgt = n + rvelf.j_imm(self.cn.raws[self.cn.index_of(n)])
            gn = self.nname.get(tgt)
            ok = None if not (tn and gn) else stem(tn) == stem(gn)
            self.tramp_check[o] = (n, tn, tgt, gn, ok)

    def _pair_entries(self):
        """OLD function STARTS with no twin (the program's own functions, called from paired code): the NEW target of
        the call at the same instruction of the paired caller. Kept only when every call site agrees."""
        votes = collections.defaultdict(set)
        for o, n in self.pairs.items():
            hi = self.ohi.get(o)
            so, sn = self._slice(self.co, o, hi), self._slice(self.cn, n, n + (hi - o))
            if not so or not sn:
                continue
            for ko, kn in zip(range(*so), range(*sn)):
                a, b = self.co.sens[ko], self.cn.sens[kn]
                if a and b and a[0] in ('jal', 'c.j') and not (o <= a[1] < hi) and self._fn_map(a[1]) is None:
                    votes[a[1]].add(b[1])
        self.entries = {o: next(iter(s)) for o, s in votes.items() if len(s) == 1}
        # a call-paired start whose function has the same length and the same stream except a 12-bit immediate of a
        # load/store/addi whose auipc partner the linear decode did not see (a non-adjacent pair): the whole function
        # pairs, so its interior and its end move with it
        self.by_call = {}
        for o, n in self.entries.items():
            hi = self.ohi.get(o)
            if hi is None or o in self.pairs or self.nhi.get(n) != n + (hi - o):
                continue
            if self.same_fn_at(o, hi, n, lo12_tolerant=True):
                self.pairs[o] = n
                self.by_call[o] = n

    def _data_refs(self):
        """coderef map: every address an auipc+lo12 pair forms in OLD code that maps (a paired function, a trampoline,
        FDE-less musl code accepted by _by_new_function, the entry), mapped to the address the NEW instruction at the
        mapped pc forms (the identity of a GOT word, a .bss cell, a string is the code that loads it). Conflicting
        votes are kept apart in cref_conflict. Also the switch tables: a .rodata base the code forms whose 4-byte
        entries, added to the base, land in code next to the referencing instruction (`case = base + entry`)."""
        votes = collections.defaultdict(collections.Counter)
        self.jtab = {}  # OLD entry address -> (NEW entry address, OLD table base, entry index)
        ro = [(s.vaddr, s.end) for s in self.old.sections if s.name == '.rodata']
        xlo, xhi = self.co.pcs[0], self.co.pcs[-1] + 4
        bases = {}
        for k, sv in enumerate(self.co.sens):
            if not sv or sv[0] != 'lo12':
                continue
            pc = self.co.pcs[k]
            pn = self.map_code(pc)
            kn = self.cn.index_of(pn) if pn is not None else None
            if kn is None or self.cn.tok[kn] != self.co.tok[k]:
                continue
            b = self.cn.sens[kn]
            if not b or b[0] != 'lo12':
                continue
            votes[sv[1]][b[1]] += 1
            if any(lo <= sv[1] < rh for lo, rh in ro):
                bases.setdefault(sv[1], (pc, b[1]))
        for t, (pc, tn) in bases.items():
            f = self._fn_of(pc)
            lo, hi = f if f else (pc - 0x10000, pc + 0x10000)
            ent = []
            while True:
                w = self.old.read(t + 4 * len(ent), 4)
                e = struct.unpack('<i', w)[0] if w and len(w) == 4 else 0
                if not e or not (lo <= t + e < hi and xlo <= t + e < xhi):
                    break
                ent.append(e)
            if len(ent) >= 2:
                for i in range(len(ent)):
                    self.jtab[t + 4 * i] = (tn + 4 * i, t, i)
        self.cref = {t: c.most_common(1)[0][0] for t, c in votes.items() if len(c) == 1}
        self.cref_conflict = {t: c for t, c in votes.items() if len(c) > 1}

    def same_fn_at(self, olo, ohi, nlo, lo12_tolerant=False):
        """the NEW code at nlo is OLD [olo, ohi) moved: same masked stream, every jump or call out of it lands on
        the NEW twin of its OLD target, and every jump inside it keeps its offset. lo12_tolerant: an instruction may
        also differ in the 12-bit immediate of a load/store/addi (an auipc partner the linear decode missed)."""
        ko, kn = self._key(self.co, olo, ohi), self._key(self.cn, nlo, nlo + (ohi - olo))
        if ko is None or kn is None or ko[0] != kn[0] or len(ko[1]) != len(kn[1]):
            return False
        if ko != kn:
            if not lo12_tolerant:
                return False
            so, sn = self._slice(self.co, olo, ohi), self._slice(self.cn, nlo, nlo + (ohi - olo))
            for io, inn in zip(range(*so), range(*sn)):
                if self.co.tok[io] == self.cn.tok[inn]:
                    continue
                x, y = self.co.raws[io], self.cn.raws[inn]
                if self.co.lens[io] != 4 or self.cn.lens[inn] != 4 or x & 0x7f != y & 0x7f:
                    return False
                op = x & 0x7f
                if op in (0x03, 0x07, 0x13, 0x1b, 0x67):
                    if x & 0xfffff != y & 0xfffff:
                        return False
                elif op in (0x23, 0x27):
                    if x & 0x01fff07f != y & 0x01fff07f:
                        return False
                else:
                    return False
        so, sn = self._slice(self.co, olo, ohi), self._slice(self.cn, nlo, nlo + (ohi - olo))
        for io, inn in zip(range(*so), range(*sn)):
            x, y = self.co.sens[io], self.cn.sens[inn]
            if x and y and x[0] in ('jal', 'c.j', 'branch', 'c.bxxz'):
                if olo <= x[1] < ohi:
                    if x[1] - olo != y[1] - nlo:
                        return False
                elif self._fn_map(x[1]) != y[1]:
                    return False
        return True

    def is_fn_end(self, a):
        """a is one past some OLD function and starts no function of its own (an interval end, so its NEW value is
        map(a - 1) + 1). A value that is both an end and the next function's start reads as the start: it is an
        address there, and the two agree whenever the two functions stay adjacent."""
        if self._ends is None:
            self._ends = {hi for _, hi in self.ofn} - {lo for lo, _ in self.ofn}
        return a in self._ends

    def map_code(self, a):
        """NEW address of OLD code address a: its function's twin + the same offset (FDE functions and the source's
        recovered functions, paired by stream, references and names), a trampoline's twin, or (a function START only)
        the NEW target of the paired caller's call. None when nothing pairs it."""
        r = self._fn_map(a)
        return r if r is not None else self.entries.get(a)

    def new_fn_at(self, a):
        """(lo, hi) of the NEW function (symbol) starting exactly at a, else None."""
        return (a, self.nhi[a]) if a in self.nhi else None

    def name_new(self, a):
        """NEW function name + offset of NEW address a (for reports)."""
        k = bisect.bisect_right(self._nlos, a) - 1
        return f'{self.nname[self._nlos[k]]}+{a - self._nlos[k]:#x}' if k >= 0 else hex(a)

    def sym_new(self, a):
        """NEW symbol name covering a (start <= a < end), or None."""
        k = bisect.bisect_right(self._nlos, a) - 1
        if k < 0:
            return None
        lo = self._nlos[k]
        return self.nname[lo] if a < self.nhi.get(lo, lo + 1) or a == lo else None


def stem(name):
    """A function name without the interceptor/wrapper/trampoline decorations, for name checks."""
    n = re.sub(r'\.(llvm|part|cold)\.\d+$', '', name)
    n = re.sub(r'^_*(interceptor_trampoline_|interceptor_|wrap_|real_)?', '', n)
    return re.sub(r'^_*', '', n)


def main():
    old, new, syms, mp = sys.argv[1:5]
    R = Resolver(old, new, syms, mp)
    print(f'OLD fns {len(R.ofn)}, NEW fns {len(R.nfn)}, paired {len(R.pairs)}, ambiguous {len(R.ambig)}, '
          f'trampolines {len(R.tramp)}')
    bad = 0
    for o, n in sorted(list(R.pairs.items()) + list(R.tramp.items())):
        e = R.look(o) if R.look else None
        if e != n:
            bad += 1
            print(f'elf_symbols-differs OLD {o:#x}: elf_symbols {e if e is None else hex(e)}  function pairing {n:#x} {R.name_new(n)}')
    for o, cs in sorted(R.ambig.items()):
        print(f'ambiguous OLD {o:#x}: ' + ' '.join(f'{c:#x}({R.name_new(c)})' for c in cs))
    for o, cs in R.tiebreak:
        print(f'tiebreak OLD {o:#x} -> {R.pairs[o]:#x} {R.name_new(R.pairs[o])} (elf_symbols value among identical: '
              + ' '.join(f'{c:#x}' for c in cs) + ')')
    for o, n in sorted(R.tramp.items()):
        print(f'trampoline OLD {o:#x} -> {n:#x} {R.name_new(n)}')
    print(f'{bad} pairs where elf_symbols differs; {len(R.tiebreak)} tiebreaks')


if __name__ == '__main__':
    main()
