#!/usr/bin/env python3
"""label_test.py - the test that decides which address-cell labels of lib/A/AB1w.v and lib/ReusableB/YB1w.v stay.

Each of those files gives the address range of a runtime function as two cells, tfib_A_<label> and tfib_E_<label>.
This script tests every label against the image that its file describes: lib/A/AB1w.v against image A (the asan
build), lib/ReusableB/YB1w.v against image B (the asan-ubsan build). It runs the two tests apart, and no verdict of
one image is used for the other. It prints one table row per label.

THE TEST

The held functions of a cell are the function symbols of the image that start in [tfib_A_<label>, tfib_E_<label>).
Clauses (a) to (d) are tested for each function the label names (WHAT A LABEL NAMES, below), one name at a time.
A label that THE NAME AFTER THE PREFIX (below) shows false is REMOVED, whatever (a) to (e) show. Any other label
that names at least one function is KEPT when (a), (b), (c) or (d) holds for at least one of the functions it
names, and REMOVED otherwise; its words are not counted, so a true word does not keep a label whose names are all
shown false. Any other label that names no function is KEPT when (e) holds, and REMOVED otherwise. A token that
names no function of the image is a word: it cannot make a label false.

 (a) symbol   A function the label names is a held function.
 (b) inlined  The debug information records a function the label names as inlined at an address inside the cell.
 (c) call     The code of the cell calls, or tail-jumps to, a function the label names; or the code of a function
              the label names, or of an inlined copy of it, calls or tail-jumps to a held function.
 (d) value    The code of the cell loads a global byte that the code of a function the label names, or of an
              inlined copy of it, stores. Or some function calls a function the label names, and the value
              returned in a0 then reaches, in that caller's code after the call (in address order, up to its next
              return or jump out of it), either an argument register (a0-a7) of a call to a held function that
              the held function reads, or a store to a global byte that the code of the cell loads. The value
              moves through mv and through stack slots. A held function reads an argument register when, in
              address order from its entry, an instruction uses the register before one writes it; a call, a
              tail jump or an ecall before any write passes the register on and counts as a use.
 (e) words    The label names no function, at least one of its words is shown true of the held functions, and
              no word is shown false (WORDS, below).

THE NAME AFTER THE PREFIX

This rule is the ruling of 2026-10-31T08:48:10Z on tfib cells, which a ruling of 2026-11-01T09:59Z applies to this
test: "A cell is WRONG when the name after its prefix is ITSELF a function symbol of the image and the value is a
DIFFERENT function with no relation the suffix states." The test reads it this way, regardless of inlining or call
edges. The prefix is tfib_A_ or tfib_E_. The name after it is the longest leading run of the label (WHAT A LABEL
NAMES; the cut rule does not apply) that is a spelling of at least one function symbol of the image; inline records
do not count. A label with no such run has no name after its prefix, and this rule does not apply to it. The suffix
is the label's tokens after that run; it may be empty. The value is a different function when the function symbol
whose range holds tfib_A_<label> is none of the symbols the name spells, or no function symbol holds it. The suffix
states a relation when one of its tokens is at least 3 characters long and is not a number (a number as in WORDS);
whether the relation it states holds is decided by (a) to (e), as for any label. A label whose name after its prefix
is a function symbol, whose value is a different function, and whose suffix states no relation is false.

WHAT A LABEL NAMES

The label is split at "_" into tokens. A run of consecutive tokens, joined again by "_", names a function F when it
is one of F's spellings. Every spelling is written with each run of underscores shortened to one underscore and
without leading or trailing underscores (so internal__exit is spelled internal_exit). The spellings are:
 - a C function f: f; and, when f begins with __asan_, __lsan_, __ubsan_ or __sanitizer_, also f without that
   prefix (so __asan_stack_malloc_0 is also spelled stack_malloc_0);
 - an interceptor, trampoline or wrapper symbol P+f, P one of __interceptor_trampoline_, ___interceptor_,
   __interceptor_, __wrap_: also the spellings of f, so the plain name f also names it; and for ___interceptor_
   and __interceptor_ also icpt_ followed by the spelling of f;
 - a C++ function c1::c2::...::cn (template arguments and "(anonymous namespace)" left out): ck_..._cn for each
   k; so a namespace or class may be left out, and a class name also names its constructors;
 - a function that the debug information records as inlined, by its recorded name n with template arguments
   left out (the record carries no class or namespace; names of destructors, which begin with "~", are not
   spellings): the spellings that a C function named n would have (above), and K_n where K is a component other
   than the last of the qualified name of any C++ function symbol.
In a label of 48 characters, the longest a label is, the label may have been cut: its last run also names F when
it is at least 5 characters long and begins one of F's spellings other than the K_n ones. The label names the
functions of every naming run that is not part of a longer naming run.

A function the label names is found in the image as: its symbols (all symbols with that spelling), and its inline
records (all inline records whose recorded name has that spelling).

WORDS

The words of a label are its tokens that are in no naming run, except tokens shorter than 3 characters and
numbers (decimal, 0x hex, or hex that has a decimal digit). A decimal number followed by "insns", "insn" or "ins"
is one count word, and the tokens "no" and "op" side by side are the word "no_op". A word is shown true or false
of the held functions by these tests, on the instructions of the cell [tfib_A, tfib_E):
 - count word N:    true when the cell holds N instructions, false otherwise;
 - ctor:            true when a held symbol is a constructor (its last two name components are equal) or the
                    held address is an entry of .init_array or .preinit_array, false otherwise;
 - dtor:            true when a held symbol is a destructor (last component begins with "~") or the held address
                    is an entry of .fini_array, false otherwise;
 - weak:            true when a held symbol has weak binding, false otherwise;
 - ret:             true when the last instruction of the cell is ret, false otherwise;
 - getter:          true when the cell stores nothing except through sp and makes no call, false otherwise;
 - no_op:           true when the cell holds at most 2 instructions, stores nothing and makes no call, false
                    otherwise;
 - stub, tiny, shim, thunk, trampoline:
                    true when the cell holds at most 4 instructions, false otherwise;
 - any other word:  true when, ignoring case, it is part of the demangled name of a held symbol or of the file name
                    of the held code (the compile unit of the first held function, and the line-table file of its
                    first instruction); otherwise it is not shown either way.

WHAT THE CODE IS

The code is the image's .text, decoded as RV64GC. A call is jal or jalr with rd = ra; a tail jump is j to an
address outside the jumping function, or jr through a register that holds a known address. A register holds a
known address after auipc, and keeps it through addi, andi, mv, and a load from a .got slot (which gives the
address the slot holds); any other write forgets it; a call forgets a0-a7, t0-t6 and ra; at a forward branch
target it keeps only what every incoming path agrees on. A load or store through a register that holds a known
address accesses that address (lr, sc and amo name their address register as a plain operand; lr is a load, sc
a store, amo both); such an address is a global byte. Loads from .got slots are not counted as loads of a value.
Symbols, sizes and inline records come from the debug twin of each image, whose loaded segments the script
checks against the image.

LIMITS

 - The cut rule matches widely: the last run of a 48-character label names every function with a spelling that
   begins with it, so a short common last run (for example "sanitizer") names many functions.
 - Names are matched on tokens, so a token that is both a plain word and the name of some function (add, lock,
   exit, call) counts as a name.
 - Spellings are normalised (WHAT A LABEL NAMES): runs of underscores count as one, and the prefixes __asan_,
   __lsan_, __ubsan_ and __sanitizer_ of a C name may be left out. Names that differ only in these are the same
   spelling, and a short spelling made this way (for example __asan_init spelled init) is a name too.
 - All three add names. A name added this way can keep a label, when (a) to (d) hold for it, and it stops the
   label's words from counting.
 - The value clause (d) follows a value one step only: from a store to a load of the same global byte, or from a
   return to an argument or a global store in one caller. A value that travels further, or through an object in
   memory, is not followed.
 - Code is read in address order; a path through a backward branch is not followed.
 - THE NAME AFTER THE PREFIX does not read what a suffix says: a suffix with any token of 3 or more characters that
   is not a number counts as stating a relation, and (a) to (e) then decide the label as for any other label.

The table's names_shown column gives, for each name the label spells, the clauses of (a) to (d) that hold for it;
its name_after_prefix column gives that name, the function symbols it spells, the function that holds the value,
and the suffix.

USAGE

  python3 label_test.py --unit <unit root> \\
      --image-a <fuzz_identity.asan> --debug-a <its .debug> \\
      --image-b <fuzz_identity.asan-ubsan> --debug-b <its .debug> \\
      [--cells-a FILE] [--cells-b FILE] > table.tsv

<unit root> is the directory that holds harness.yaml and proofs/. The image sha256s must be the ones harness.yaml
pins for the asan and asan-ubsan builds. --cells-X names the cells to test: a Rocq file with "Definition
tfib_A_<label> : Z := <value>." lines, or a table.tsv printed by this script (its rows for that image). The default
is the file in the tree, proofs/lib/A/AB1w.v or proofs/lib/ReusableB/YB1w.v. The column in_tree says whether the
label is in that file of the tree.
"""
import argparse
import bisect
import collections
import ctypes
import ctypes.util
import hashlib
import os
import re
import sys

from capstone import Cs, CS_ARCH_RISCV, CS_MODE_RISCV64, CS_MODE_RISCVC
from elftools.elf.elffile import ELFFile

# ------------------------------------------------------------------------------------------------ demangling

_cxx = ctypes.CDLL(ctypes.util.find_library('stdc++') or 'libstdc++.so.6')
_cxx.__cxa_demangle.restype = ctypes.c_void_p
_cxx.__cxa_demangle.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.c_void_p, ctypes.POINTER(ctypes.c_int)]
_libc = ctypes.CDLL(None)
_libc.free.argtypes = [ctypes.c_void_p]


def demangle(name):
    if not name.startswith('_Z'):
        return name
    status = ctypes.c_int(0)
    p = _cxx.__cxa_demangle(name.encode(), None, None, ctypes.byref(status))
    if status.value != 0 or not p:
        return name
    out = ctypes.string_at(p).decode()
    _libc.free(p)
    return out


def drop_templates(s):
    out, depth = [], 0
    for ch in s:
        if ch == '<':
            depth += 1
        elif ch == '>':
            depth -= 1
        elif depth == 0:
            out.append(ch)
    return ''.join(out)


def components(dem):
    """The qualified name of a demangled C++ function as components, without templates, parameters and
    "(anonymous namespace)"."""
    s = dem.replace('(anonymous namespace)::', '')
    s = drop_templates(s)
    k = s.find('(')
    if k > 0:
        s = s[:k]
    s = s.split(' ')[-1]          # drop a return type that a template function's name carries
    return [c for c in s.split('::') if c]


# ------------------------------------------------------------------------------------------------ one image

STORES = {'sb': 1, 'sh': 2, 'sw': 4, 'sd': 8, 'fsw': 4, 'fsd': 8}
LOADS = {'lb': 1, 'lbu': 1, 'lh': 2, 'lhu': 2, 'lw': 4, 'lwu': 4, 'ld': 8, 'flw': 4, 'fld': 8}
BRANCH = {'beq', 'bne', 'blt', 'bge', 'bltu', 'bgeu', 'beqz', 'bnez', 'blez', 'bgez', 'bltz', 'bgtz', 'bgt', 'ble',
          'bgtu', 'bleu'}
REG = {i + 1: n for i, n in enumerate(
    'zero ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6'.split())}
KEEP_OVER_CALL = {r for r, n in REG.items() if n.startswith('s') or n in ('sp', 'gp', 'tp', 'zero')}
ARG_REGS = {r for r, n in REG.items() if n in ('a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'a6', 'a7')}
A0 = [r for r, n in REG.items() if n == 'a0'][0]
SP = [r for r, n in REG.items() if n == 'sp'][0]
ALIAS_PREFIXES = ['__interceptor_trampoline_', '___interceptor_', '__interceptor_', '__wrap_']
RUNTIME_PREFIXES = ['__asan_', '__lsan_', '__ubsan_', '__sanitizer_']


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def access_size(mnemonic):
    m = mnemonic.split('.')
    if m[0] in ('lr', 'sc') or m[0].startswith('amo'):
        return 8 if len(m) > 1 and m[1] == 'd' else 4
    return STORES.get(mnemonic) or LOADS.get(mnemonic)


class Image:
    def __init__(self, tag, image, debug):
        self.tag, self.image_path, self.debug_path = tag, image, debug
        self.image_sha, self.debug_sha = sha256(image), sha256(debug)
        self.raw = open(debug, 'rb').read()
        self._fh = open(debug, 'rb')
        self.elf = ELFFile(self._fh)
        self.segments = [(p['p_vaddr'], p['p_offset'], p['p_filesz'])
                         for p in self.elf.iter_segments() if p['p_type'] == 'PT_LOAD']
        self._symbols()
        self._dwarf()
        self._code()

    # -- the debug twin carries the image's loaded bytes
    def twin_check(self):
        """Compare each PT_LOAD of the image with the twin's. Bytes may differ only in the ELF header and the
        build-id note. Returns (ok, text)."""
        with open(self.image_path, 'rb') as f:
            other = ELFFile(f)
            segs = [(p['p_vaddr'], p['p_offset'], p['p_filesz']) for p in other.iter_segments()
                    if p['p_type'] == 'PT_LOAD']
        raw = open(self.image_path, 'rb').read()
        if [(v, n) for v, _, n in segs] != [(v, n) for v, _, n in self.segments]:
            return False, 'PT_LOAD layout differs'
        note = self.elf.get_section_by_name('.note.gnu.build-id')
        allowed = [(self.segments[0][0], self.segments[0][0] + 64)]
        if note:
            allowed.append((note['sh_addr'], note['sh_addr'] + note['sh_size']))
        bad = 0
        for (va, o1, n), (_, o2, _) in zip(self.segments, segs):
            a, b = self.raw[o1:o1 + n], raw[o2:o2 + n]
            if a != b:
                bad += sum(1 for i in range(n) if a[i] != b[i]
                           and not any(lo <= va + i < hi for lo, hi in allowed))
        return bad == 0, f'{len(segs)} PT_LOAD segments; {bad} bytes differ outside the ELF header and build-id note'

    def read(self, addr, n):
        for va, off, size in self.segments:
            if va <= addr < va + size:
                return self.raw[off + addr - va: off + addr - va + n]
        return None

    # -- symbols
    def _symbols(self):
        self.syms = []
        for s in self.elf.get_section_by_name('.symtab').iter_symbols():
            if (s.name and not s.name.startswith('$') and s['st_shndx'] != 'SHN_UNDEF'
                    and s['st_info']['type'] in ('STT_FUNC', 'STT_NOTYPE', 'STT_OBJECT')):
                dem = demangle(s.name)
                self.syms.append(dict(name=s.name, dem=dem, addr=s['st_value'], size=s['st_size'],
                                      type=s['st_info']['type'], bind=s['st_info']['bind'],
                                      comps=components(dem) if s.name.startswith('_Z') else None))
        text = self.elf.get_section_by_name('.text')
        self.text_lo, self.text_hi = text['sh_addr'], text['sh_addr'] + text['sh_size']
        got = self.elf.get_section_by_name('.got')
        self.got_lo, self.got_hi = got['sh_addr'], got['sh_addr'] + got['sh_size']
        self.funcs = [s for s in self.syms if s['type'] == 'STT_FUNC']
        self.func_by_addr = collections.defaultdict(list)
        for s in self.funcs:
            self.func_by_addr[s['addr']].append(s)
        self.func_starts = sorted(self.func_by_addr)
        self.sym_by_addr = collections.defaultdict(list)
        for s in self.syms:
            self.sym_by_addr[s['addr']].append(s)
        self.array_entries = {}
        for sec in ('.init_array', '.preinit_array', '.fini_array'):
            sh = self.elf.get_section_by_name(sec)
            if sh:
                data = self.read(sh['sh_addr'], sh['sh_size']) or b''
                for i in range(0, len(data), 8):
                    self.array_entries.setdefault(int.from_bytes(data[i:i + 8], 'little'), set()).add(sec)

    def function_at(self, addr):
        """The function symbol whose range holds addr (the one that starts last), or None."""
        i = bisect.bisect_right(self.func_starts, addr) - 1
        while i >= 0:
            start = self.func_starts[i]
            for s in self.func_by_addr[start]:
                if start <= addr < start + max(s['size'], 1):
                    return s
            if addr - start > 0x10000:
                break
            i -= 1
        return None

    def name_of(self, s):
        return s['dem'] if len(s['dem']) <= 100 else '::'.join(s['comps'] or [s['dem']])

    # -- debug information: inline records, compile units, line table
    def _dwarf(self):
        dw = self.elf.get_dwarf_info()
        rl = dw.range_lists()
        names = {}
        self.inline = []           # dict(name, ranges)
        self.units = []            # (lo, hi, compile unit basename) of concrete functions

        def ref(die, attr):
            v = die.attributes[attr]
            local = v.form in ('DW_FORM_ref1', 'DW_FORM_ref2', 'DW_FORM_ref4', 'DW_FORM_ref8', 'DW_FORM_ref_udata')
            return v.value + (die.cu.cu_offset if local else 0)

        def ranges(die):
            at, cu = die.attributes, die.cu
            out = []
            if 'DW_AT_low_pc' in at and 'DW_AT_high_pc' in at:
                lo, hi = at['DW_AT_low_pc'].value, at['DW_AT_high_pc']
                out = [(lo, hi.value if hi.form.startswith('DW_FORM_addr') else lo + hi.value)]
            elif 'DW_AT_ranges' in at:
                base = cu.get_top_DIE().attributes.get('DW_AT_low_pc')
                base = base.value if base else 0
                for e in rl.get_range_list_at_offset(at['DW_AT_ranges'].value, cu=cu):
                    kind = type(e).__name__
                    if kind == 'RangeEntry':
                        out.append((e.begin_offset, e.end_offset) if e.is_absolute
                                   else (base + e.begin_offset, base + e.end_offset))
                    elif kind == 'BaseAddressEntry':
                        base = e.base_address
            return [(a, b) for a, b in out if b > a and self.text_lo <= a < self.text_hi]

        def walk(die):
            for ch in die.iter_children():
                if ch.tag == 'DW_TAG_inlined_subroutine':
                    self.inline.append(dict(origin=ref(ch, 'DW_AT_abstract_origin'), ranges=ranges(ch)))
                    walk(ch)
                elif ch.tag == 'DW_TAG_lexical_block':
                    walk(ch)

        for cu in dw.iter_CUs():
            unit = os.path.basename(cu.get_top_DIE().attributes['DW_AT_name'].value.decode())
            for die in cu.iter_DIEs():
                if die.tag == 'DW_TAG_subprogram' and 'DW_AT_name' in die.attributes:
                    v = die.attributes['DW_AT_name'].value
                    names[die.offset] = v.decode() if isinstance(v, bytes) else v
            for die in cu.iter_DIEs():
                if die.tag == 'DW_TAG_subprogram' and ('DW_AT_low_pc' in die.attributes
                                                       or 'DW_AT_ranges' in die.attributes):
                    for lo, hi in ranges(die):
                        self.units.append((lo, hi, unit))
                    walk(die)
        for r in self.inline:
            r['name'] = drop_templates(names.get(r['origin']) or '')
        self.inline = [r for r in self.inline if r['name'] and r['ranges']]
        self.inline_by_name = collections.defaultdict(list)
        for r in self.inline:
            self.inline_by_name[r['name']].append(r)
        self.units.sort()
        self.rows = []
        for cu in dw.iter_CUs():
            lp = dw.line_program_for_CU(cu)
            if lp is None:
                continue
            files = [os.path.basename(e.name.decode() if isinstance(e.name, bytes) else e.name)
                     for e in lp['file_entry']]
            for ent in lp.get_entries():
                st = ent.state
                if st is not None and not st.end_sequence and self.text_lo <= st.address < self.text_hi:
                    self.rows.append((st.address, files[st.file] if st.file < len(files) else ''))
        self.rows.sort()
        self.row_addrs = [r[0] for r in self.rows]

    def files_of(self, addr):
        """The compile unit of the concrete function at addr, and the line-table file of addr."""
        out = set()
        i = bisect.bisect_right(self.units, (addr, float('inf'), '')) - 1
        while i >= 0 and self.units[i][0] <= addr:
            lo, hi, unit = self.units[i]
            if lo <= addr < hi:
                out.add(unit)
                break
            i -= 1
        j = bisect.bisect_right(self.row_addrs, addr) - 1
        if j >= 0:
            out.add(self.rows[j][1])
        return {f for f in out if f}

    # -- code
    def _code(self):
        md = Cs(CS_ARCH_RISCV, CS_MODE_RISCV64 | CS_MODE_RISCVC)
        md.detail = True
        code = self.read(self.text_lo, self.text_hi - self.text_lo)
        self.ins = {}
        off = 0
        while off < len(code):
            last = None
            for x in md.disasm(code[off:], self.text_lo + off):
                self.ins[x.address] = x
                last = x
            off = (last.address + last.size - self.text_lo) if last else off + 2
            if last and off < len(code) and (self.text_lo + off) not in self.ins:
                off += 2
        self.addrs = sorted(self.ins)
        self.access = {}           # address -> (kind 'load'|'store', target, size)
        self.edges = []            # (site, target, 'call'|'jump')
        self.calls_at = {}         # site -> target of a call
        func_ranges = sorted({(s['addr'], s['addr'] + s['size']) for s in self.funcs if s['size']})
        for lo, hi in func_ranges:
            if self.text_lo <= lo < self.text_hi:
                self._walk(lo, hi)
        self.edges_to = collections.defaultdict(list)
        self.edges_from = collections.defaultdict(list)
        for site, target, kind in self.edges:
            self.edges_to[target].append((site, kind))

    def instructions(self, lo, hi):
        i = bisect.bisect_left(self.addrs, lo)
        while i < len(self.addrs) and self.addrs[i] < hi:
            yield self.ins[self.addrs[i]]
            i += 1

    def _walk(self, lo, hi):
        known, incoming, falls = {}, collections.defaultdict(list), True
        for x in self.instructions(lo, hi):
            a, m, ops = x.address, x.mnemonic, x.operands
            states = incoming.pop(a, []) + ([known] if falls else [])
            known = ({r: v for r, v in states[0].items() if all(s.get(r) == v for s in states[1:])}
                     if states else {})
            falls = True
            dest = ops[0].reg if ops and ops[0].type == 1 else None
            if m in BRANCH or m in ('j', 'jal'):
                target = a + ops[-1].imm
                if m == 'jal':
                    self.edges.append((a, target, 'call'))
                    self.calls_at[a] = target
                    known = {r: v for r, v in known.items() if r in KEEP_OVER_CALL}
                elif m == 'j' and not lo <= target < hi:
                    self.edges.append((a, target, 'jump'))
                    falls = False
                else:
                    if target > a:
                        incoming[target].append(dict(known))
                    if m == 'j':
                        falls = False
                continue
            if m in ('jalr', 'jr', 'ret'):
                if m in ('jalr', 'jr') and dest in known:
                    target = known[dest]
                    self.edges.append((a, target, 'call' if m == 'jalr' else 'jump'))
                    if m == 'jalr':
                        self.calls_at[a] = target
                known = {r: v for r, v in known.items() if r in KEEP_OVER_CALL}
                falls = m == 'jalr'
                continue
            if m == 'auipc':
                imm = ops[1].imm
                known[dest] = a + ((imm - 0x100000 if imm >= 0x80000 else imm) << 12)
                continue
            if m in ('addi', 'andi') and len(ops) == 3 and ops[1].type == 1 and ops[1].reg in known:
                v = known[ops[1].reg]
                known[dest] = v + ops[2].imm if m == 'addi' else v & ops[2].imm
                continue
            if m == 'mv' and len(ops) == 2 and ops[1].type == 1 and ops[1].reg in known:
                known[dest] = known[ops[1].reg]
                continue
            mem = [o for o in ops if o.type == 3]
            atomic = m.split('.')[0] in ('lr', 'sc') or m.startswith('amo')
            if atomic:
                base, disp = ops[-1].reg, 0          # lr, sc and amo name their address register as a plain operand
            elif mem:
                base, disp = mem[0].mem.base, mem[0].mem.disp
            else:
                base = None
            if base in known:
                target = known[base] + disp
                size = access_size(m)
                if m == 'ld' and self.got_lo <= target < self.got_hi:
                    known[dest] = int.from_bytes(self.read(target, 8), 'little')
                    continue
                if m in STORES or m.split('.')[0] == 'sc':
                    self.access[a] = ('store', target, size)
                elif m.startswith('amo'):
                    self.access[a] = ('store', target, size)    # read-modify-write: a store and a load
                    self.access[(a, 'load')] = ('load', target, size)
                elif size:
                    self.access[a] = ('load', target, size)
            if dest is not None and m not in STORES:
                known.pop(dest, None)

    # -- facts about a range of code
    def loads_in(self, lo, hi):
        out = []
        for x in self.instructions(lo, hi):
            for key in (x.address, (x.address, 'load')):
                acc = self.access.get(key)
                if acc and acc[0] == 'load':
                    out.append((x.address, acc[1], acc[2]))
        return out

    def stores_in(self, lo, hi):
        return [(x.address, self.access[x.address][1], self.access[x.address][2])
                for x in self.instructions(lo, hi)
                if x.address in self.access and self.access[x.address][0] == 'store']


# ------------------------------------------------------------------------------------------------ names

class Names:
    """The spellings of every function of an image, and the test of a label's runs against them."""

    @staticmethod
    def norm(s):
        """A spelling: each run of underscores shortened to one, no leading or trailing underscore."""
        return re.sub(r'_+', '_', s).strip('_')

    @classmethod
    def plain_spellings(cls, f):
        """The spellings of a C name f: f, and f without a runtime prefix."""
        out = {cls.norm(f)}
        for p in RUNTIME_PREFIXES:
            if f.startswith(p) and len(f) > len(p):
                out.add(cls.norm(f[len(p):]))
        return out

    @classmethod
    def c_spellings(cls, name):
        """The spellings of a C function name, and for an interceptor, trampoline or wrapper P+f also the
        spellings of f, and icpt_ + those for an interceptor."""
        out = cls.plain_spellings(name)
        for p in ALIAS_PREFIXES:
            if name.startswith(p) and len(name) > len(p):
                fs = cls.plain_spellings(name[len(p):])
                out |= fs
                if p in ('___interceptor_', '__interceptor_'):
                    out |= {'icpt_' + x for x in fs}
                break
        return {x for x in out if x}

    def __init__(self, img):
        self.img = img
        self.spell = collections.defaultdict(set)     # spelling -> {('sym', addr), ('inline', name)}
        for s in img.funcs:
            if s['comps'] is not None:
                for k in range(1, len(s['comps']) + 1):
                    sp = self.norm('_'.join(s['comps'][-k:]))
                    if sp:
                        self.spell[sp].add(('sym', s['addr']))
            else:
                for sp in self.c_spellings(s['name']):
                    self.spell[sp].add(('sym', s['addr']))
        self.inline_spell = collections.defaultdict(set)   # spelling -> recorded inline names
        for n in img.inline_by_name:
            if not n.startswith('~'):
                for sp in self.c_spellings(n):
                    self.spell[sp].add(('inline', n))
                    self.inline_spell[sp].add(n)
        self.class_parts = {self.norm(c) for s in img.funcs if s['comps'] for c in s['comps'][:-1]}
        self.sorted_spellings = sorted(self.spell)

    def match(self, run, may_be_cut):
        """The targets a run names, or an empty set."""
        out = set(self.spell.get(run, ()))
        toks = run.split('_')
        for k in range(1, len(toks)):                   # K_n: a class or namespace part, then an inline name
            k_part, n_part = '_'.join(toks[:k]), '_'.join(toks[k:])
            if k_part in self.class_parts:
                out |= {('inline', n) for n in self.inline_spell.get(n_part, ())}
        if may_be_cut and len(run) >= 5:
            i = bisect.bisect_left(self.sorted_spellings, run)
            while i < len(self.sorted_spellings) and self.sorted_spellings[i].startswith(run):
                out |= self.spell[self.sorted_spellings[i]]
                i += 1
        return out

    def read_label(self, label):
        """(naming runs [(i, j, run, targets)], word tokens [(index, token)])"""
        toks = label.split('_')
        n = len(toks)
        cut = len(label) == 48
        runs = []
        for i in range(n):
            for j in range(i + 1, n + 1):
                run = '_'.join(toks[i:j])
                if not run:
                    continue
                targets = self.match(run, cut and j == n)
                if targets:
                    runs.append((i, j, run, targets))
        kept = [r for r in runs if not any(o[0] <= r[0] and r[1] <= o[1] and (o[0], o[1]) != (r[0], r[1])
                                           for o in runs)]
        covered = {t for i, j, _, _ in kept for t in range(i, j)}
        words = [(t, toks[t]) for t in range(n) if t not in covered]
        return kept, words


# ------------------------------------------------------------------------------------------------ the test

NUMBER = re.compile(r'^(0x[0-9a-fA-F]+|[0-9]+|(?=[0-9a-fA-F]*[0-9])[0-9a-fA-F]+)$')
SMALL = {'stub', 'tiny', 'shim', 'thunk', 'trampoline'}


class Test:
    def __init__(self, img):
        self.img = img
        self.names = Names(img)
        self._returned = {}

    # the functions a label names, found in the image
    def found(self, targets):
        syms, inl = set(), []
        for kind, v in sorted(targets):          # sorted: the order of evidence must not depend on the hash seed
            if kind == 'sym':
                syms.add(v)
            else:
                inl.extend(self.img.inline_by_name[v])
        return syms, inl

    def sym_range(self, addr):
        size = max(s['size'] for s in self.img.func_by_addr[addr])
        return addr, addr + max(size, 1)

    def label_name(self, addr):
        return self.img.name_of(self.img.func_by_addr[addr][0])

    def reads_first(self, start, reg):
        """Whether the function that starts at start reads reg before it writes it, in address order from its
        entry. A call or a tail jump before any write passes the register on, and counts as a read."""
        funcs = self.img.func_by_addr.get(start, [])
        end = start + max([s['size'] for s in funcs] + [0])
        for x in self.img.instructions(start, end):
            m, ops = x.mnemonic, x.operands
            if m == 'ret':
                return False
            if m in ('jal', 'jalr', 'jr', 'ecall'):
                return True
            if m == 'j':
                if not start <= x.address + ops[-1].imm < end:
                    return True
                continue
            regs = [o.reg for o in ops if o.type == 1]
            bases = [o.mem.base for o in ops if o.type == 3]
            if m in STORES or m in BRANCH:
                sources, dest = regs + bases, None
            elif regs:
                sources, dest = regs[1:] + bases, regs[0]
            else:
                sources, dest = bases, None
            if reg in sources:
                return True
            if reg == dest:
                return False
        return False

    # (d), second half: where the value a function returns goes in each caller
    def returned_to(self, producer):
        """[(caller site, caller, [(call site, target, argument registers that hold the value)], global stores)]"""
        if producer in self._returned:
            return self._returned[producer]
        out = []
        for site, kind in self.img.edges_to.get(producer, []):
            if kind != 'call':
                continue
            caller = self.img.function_at(site)
            if not caller:
                continue
            end = caller['addr'] + caller['size']
            tainted, slots, calls, stores = {A0}, set(), [], []
            for x in self.img.instructions(site + self.img.ins[site].size, end):
                m, ops = x.mnemonic, x.operands
                if m in ('ret', 'jr'):
                    break                                # the caller's next return, or a jump through a register
                if m in ('jal', 'jalr'):
                    target = self.img.calls_at.get(x.address)
                    if target is not None and tainted & ARG_REGS:
                        calls.append((x.address, target, tainted & ARG_REGS))
                    tainted = {r for r in tainted if r in KEEP_OVER_CALL}
                    continue
                if m == 'j':
                    if not caller['addr'] <= x.address + ops[-1].imm < end:
                        break                            # a tail jump out of the caller
                    continue
                if m in BRANCH or not ops:
                    continue
                dest = ops[0].reg if ops[0].type == 1 else None
                mem = [o for o in ops if o.type == 3]
                if m == 'mv' and len(ops) == 2 and ops[1].type == 1:
                    (tainted.add if ops[1].reg in tainted else tainted.discard)(dest)
                    continue
                if m in STORES and mem:
                    src = ops[0].reg
                    if mem[0].mem.base == SP:
                        (slots.add if src in tainted else slots.discard)(mem[0].mem.disp)
                    elif src in tainted and x.address in self.img.access:
                        stores.append((x.address,) + self.img.access[x.address][1:])
                    continue
                if m in LOADS and mem and mem[0].mem.base == SP:
                    (tainted.add if mem[0].mem.disp in slots else tainted.discard)(dest)
                    continue
                if dest is not None:
                    tainted.discard(dest)
            out.append((site, caller, calls, stores))
        self._returned[producer] = out
        return out

    def name_clauses(self, named_syms, named_inl, lo, hi, held, held_set, loads):
        """Clauses (a)-(d) for one name of the label: the evidence lists a, b, c, d."""
        img = self.img
        # (a) symbol
        a_hits = sorted(named_syms & held_set)
        # (b) inlined
        b_hits = []
        for r in named_inl:
            n = sum(max(0, min(y, hi) - max(x, lo)) for x, y in r['ranges'])
            if n:
                b_hits.append((r['name'], n))
        # (c) call
        c_hits = []
        for site, target, kind in img.edges:
            if lo <= site < hi and target in named_syms and target not in held_set:
                c_hits.append(f'{kind} {site:#x} to {self.label_name(target)}')
        for t in held:
            for site, kind in img.edges_to.get(t, []):
                if lo <= site < hi:
                    continue
                for p in sorted(named_syms - held_set):
                    plo, phi = self.sym_range(p)
                    if plo <= site < phi:
                        c_hits.append(f'{kind} {site:#x} from {self.label_name(p)}')
                for r in named_inl:
                    if any(x <= site < y for x, y in r['ranges']):
                        f = img.function_at(site)
                        c_hits.append(f"{kind} {site:#x} from inlined {r['name']} in {img.name_of(f) if f else '?'}")
                        break
        # (d) value

        def loaded(target, size):
            return [(s, t) for s, t, z in loads if t < target + size and target < t + z]

        d_hits = []
        producers = [self.sym_range(p) for p in sorted(named_syms - held_set)]
        producers += [(x, y) for r in named_inl for x, y in r['ranges'] if not (lo <= x < hi)]
        for plo, phi in producers:
            for site, target, size in img.stores_in(plo, phi):
                for lsite, ltarget in loaded(target, size):
                    d_hits.append(f'store {target:#x} at {site:#x}, load at {lsite:#x}')
        for p in sorted(named_syms - held_set):
            for site, caller, calls, stores in self.returned_to(p):
                for csite, ctarget, regs in calls:
                    read = sorted(REG[r] for r in regs if ctarget in held_set and self.reads_first(ctarget, r))
                    if read:
                        d_hits.append(f'a0 of {self.label_name(p)} (call {site:#x} in {img.name_of(caller)}) '
                                      f'passed in {",".join(read)} at call {csite:#x}, read by the held function')
                for ssite, target, size in stores:
                    for lsite, _ in loaded(target, size):
                        d_hits.append(f'a0 of {self.label_name(p)} (call {site:#x} in {img.name_of(caller)}) '
                                      f'stored to {target:#x} at {ssite:#x}, load at {lsite:#x}')
        return a_hits, b_hits, c_hits, d_hits

    def run(self, label, lo, hi):
        img = self.img
        held = [a for a in img.func_starts if lo <= a < hi]
        held_set = set(held)
        runs, words = self.names.read_label(label)
        loads = img.loads_in(lo, hi)
        a_hits, b_hits, c_hits, d_hits, per_name = [], [], [], [], []
        for _, _, run_text, targets in runs:
            syms, inl = self.found(targets)
            a, b, c, d = self.name_clauses(syms, inl, lo, hi, held, held_set, loads)
            shown = ''.join(k for k, v in (('a', a), ('b', b), ('c', c), ('d', d)) if v)
            per_name.append((run_text, shown))
            for out, new in ((a_hits, a), (b_hits, b), (c_hits, c), (d_hits, d)):
                out.extend(x for x in new if x not in out)
        # (e) words
        e_results = self.words(words, lo, hi, held)
        e_true = [w for w, v, why in e_results if v is True]
        e_false = [w for w, v, why in e_results if v is False]
        e_ok = bool(e_true) and not e_false
        # the verdict: a label that names a function stays only by (a)-(d) on a name it spells; words decide only
        # for a label that names no function
        if runs:
            kept = any(shown for _, shown in per_name)
            e_counts = False
        else:
            kept = e_ok
            e_counts = True
        # the name after the prefix: the longest leading run that spells a function symbol; with the value in a
        # different function and a suffix that states no relation, the label is false whatever (a)-(e) show
        toks = label.split('_')
        name, name_syms, suffix = None, [], []
        for j in range(len(toks), 0, -1):
            syms = sorted(v for kind, v in self.names.spell.get('_'.join(toks[:j]), ()) if kind == 'sym')
            if syms:
                name, name_syms, suffix = '_'.join(toks[:j]), syms, toks[j:]
                break
        at_value = img.function_at(lo)
        different = name is not None and (at_value is None or at_value['addr'] not in name_syms)
        states = any(len(t) >= 3 and not NUMBER.match(t) for t in suffix)
        name_false = different and not states
        if name_false:
            kept = False
        clauses = [c for c, ok in (('a', a_hits), ('b', b_hits), ('c', c_hits), ('d', d_hits),
                                   ('e', e_ok and e_counts)) if ok]
        return dict(held=held, runs=runs, a=a_hits, b=b_hits, c=c_hits, d=d_hits, e=e_results, e_ok=e_ok,
                    e_counts=e_counts, per_name=per_name, name=name, name_syms=name_syms, suffix=suffix,
                    at_value=at_value, different=different, states=states, name_false=name_false,
                    clauses=clauses, kept=kept)

    def words(self, words, lo, hi, held):
        img = self.img
        ins = list(img.instructions(lo, hi))
        stores = [x for x in ins if (x.mnemonic in STORES or x.mnemonic.split('.')[0] in ('sc',)
                                     or x.mnemonic.startswith('amo'))
                  and not any(o.type == 3 and o.mem.base == SP for o in x.operands)]
        calls = [x for x in ins if x.mnemonic == 'jal' or x.mnemonic == 'jalr']
        held_syms = [s for a in held for s in img.sym_by_addr[a] if s['type'] in ('STT_FUNC', 'STT_NOTYPE')]
        text = ' '.join(s['dem'] for s in held_syms).lower()
        files = ' '.join(sorted(img.files_of(held[0]))).lower() if held else ''
        toks = [t for _, t in words]
        idx = [i for i, _ in words]
        out, skip = [], set()
        for k, t in enumerate(toks):
            if k in skip:
                continue
            low = t.lower()
            pair = k + 1 < len(toks) and idx[k + 1] == idx[k] + 1     # the next token of the label is a word too
            if t.isdigit() and pair and toks[k + 1].lower() in ('insns', 'insn', 'ins'):
                skip.add(k + 1)
                n = int(t)
                out.append((f'{t}_{toks[k + 1]}', len(ins) == n, f'{len(ins)} instructions'))
                continue
            if low == 'no' and pair and toks[k + 1].lower() == 'op':
                skip.add(k + 1)
                ok = len(ins) <= 2 and not stores and not calls
                out.append(('no_op', ok, f'{len(ins)} instructions, {len(stores)} stores, {len(calls)} calls'))
                continue
            if len(t) < 3 or NUMBER.match(t):
                continue
            if low == 'ctor':
                ok = any(s['comps'] and len(s['comps']) >= 2 and s['comps'][-1] == s['comps'][-2] for s in held_syms) \
                    or any(img.array_entries.get(a, set()) & {'.init_array', '.preinit_array'} for a in held)
                out.append((t, ok, 'constructor or init_array entry' if ok else 'no constructor symbol, no init_array entry'))
            elif low == 'dtor':
                ok = any(s['comps'] and s['comps'][-1].startswith('~') for s in held_syms) \
                    or any('.fini_array' in img.array_entries.get(a, set()) for a in held)
                out.append((t, ok, 'destructor or fini_array entry' if ok else 'no destructor symbol, no fini_array entry'))
            elif low == 'weak':
                ok = any(s['bind'] == 'STB_WEAK' for s in held_syms)
                out.append((t, ok, 'weak symbol' if ok else 'no weak symbol'))
            elif low == 'ret':
                ok = bool(ins) and ins[-1].mnemonic == 'ret'
                out.append((t, ok, f'last instruction {ins[-1].mnemonic if ins else "none"}'))
            elif low == 'getter':
                ok = not stores and not calls
                out.append((t, ok, f'{len(stores)} stores, {len(calls)} calls'
                            + (f', first store {stores[0].address:#x}' if stores else '')))
            elif low in SMALL:
                out.append((t, len(ins) <= 4, f'{len(ins)} instructions'))
            elif low in text:
                out.append((t, True, 'in the held name'))
            elif low in files:
                out.append((t, True, 'in the file name'))
            else:
                out.append((t, None, 'not shown'))
        return out


# ------------------------------------------------------------------------------------------------ cells

CELL = re.compile(r'Definition tfib_([AE])_([A-Za-z0-9_]+) : Z := (0x[0-9a-fA-F]+|\d+)\.')


def cells_from(path, image_tag):
    """[(label, lo, hi)] from a Rocq file, or from a table.tsv printed by this script."""
    text = open(path, encoding='utf-8').read()
    if path.endswith('.tsv'):
        lines = text.splitlines()
        head = lines[0].split('\t')
        col = {c: i for i, c in enumerate(head)}
        out = []
        for line in lines[1:]:
            f = line.split('\t')
            if f[col['image']] == image_tag:
                out.append((f[col['label']], int(f[col['lo']], 16), int(f[col['hi']], 16)))
        return out
    vals, order = {}, []
    for m in CELL.finditer(text):
        kind, label, value = m.group(1), m.group(2), int(m.group(3), 0)
        if (kind, label) in vals:
            sys.exit(f'{path}: tfib_{kind}_{label} is defined twice')
        vals[(kind, label)] = value
        if kind == 'A':
            order.append(label)
    return [(l, vals[('A', l)], vals[('E', l)]) for l in order]


def labels_in(path):
    return {m.group(2) for m in CELL.finditer(open(path, encoding='utf-8').read()) if m.group(1) == 'A'}


def pins(unit):
    """The sha256 that harness.yaml records for the asan and asan-ubsan builds."""
    text = open(os.path.join(unit, 'harness.yaml'), encoding='utf-8').read()
    out = {}
    for m in re.finditer(r'\n  (\S+):\n    file: \S+\n    bytes: \d+\n    sha256: ([0-9a-f]{64})', text):
        out[m.group(1)] = m.group(2)
    return out


# ------------------------------------------------------------------------------------------------ table

COLUMNS = ['image', 'label', 'lo', 'hi', 'held', 'names', 'names_shown', 'a_symbol', 'b_inlined', 'c_call', 'd_value',
           'e_words', 'name_after_prefix', 'verdict', 'clauses', 'in_tree']


def cell(items, limit=3):
    items = list(items)
    if not items:
        return 'no'
    text = '; '.join(items[:limit])
    return text + (f'; and {len(items) - limit} more' if len(items) > limit else '')


def row(test, tag, label, lo, hi, in_tree):
    img = test.img
    r = test.run(label, lo, hi)
    held = '; '.join(f"{img.name_of(img.func_by_addr[a][0])} at {a:#x}, {max(s['size'] for s in img.func_by_addr[a])} B"
                     for a in r['held']) or 'none'
    names = []
    for _, _, run, targets in r['runs']:
        syms, inl = test.found(targets)
        parts = [f'{test.label_name(a)} at {a:#x}' for a in sorted(syms)[:3]]
        if len(syms) > 3:
            parts.append(f'{len(syms) - 3} more symbols')
        if inl:
            parts.append(f'{len(inl)} inline records')
        names.append(f"{run}: {', '.join(parts)}")
    a = cell(f'{test.label_name(x)} at {x:#x}' for x in r['a'])
    b = cell(f'{n} {k} B' for n, k in r['b'])
    words = '; '.join(f"{w} {'true' if v else 'false' if v is False else '-'} ({why})" for w, v, why in r['e'])
    if not r['e']:
        e = 'no words'
    elif not r['e_counts']:
        e = 'not counted, the label names a function: ' + words
    else:
        e = ('yes: ' if r['e_ok'] else 'no: ') + words
    shown = '; '.join(f"{run}: {s or 'none'}" for run, s in r['per_name']) or 'no names'
    if r['name'] is None:
        after = 'none: no leading run spells a function symbol'
    else:
        f = r['at_value']
        value = f"{img.name_of(f)} at {f['addr']:#x}" if f else 'no function symbol'
        syms = cell(f'{test.label_name(x)} at {x:#x}' for x in r['name_syms'])
        suffix = '_'.join(r['suffix'])
        if not r['different']:
            after = f"{r['name']}: {syms}; the value is in {value}, a function the name spells"
        elif r['states']:
            after = (f"{r['name']}: {syms}; the value is in {value}, a different function; the suffix {suffix} "
                     f"states a relation, decided by (a) to (e)")
        else:
            after = (f"false: {r['name']}: {syms}; the value is in {value}, a different function; "
                     + (f'the suffix {suffix} states no relation' if suffix else 'there is no suffix'))
    return [tag, label, f'{lo:#x}', f'{hi:#x}', held, '; '.join(names) or 'none', shown, a, b, cell(r['c']),
            cell(r['d']), e, after, 'kept' if r['kept'] else 'removed', ''.join(r['clauses']) or '-',
            'yes' if in_tree else 'no']


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('--unit', required=True, help='the unit root: the directory with harness.yaml and proofs/')
    ap.add_argument('--image-a', required=True)
    ap.add_argument('--debug-a', required=True)
    ap.add_argument('--image-b', required=True)
    ap.add_argument('--debug-b', required=True)
    ap.add_argument('--cells-a')
    ap.add_argument('--cells-b')
    args = ap.parse_args()
    files = {'A': os.path.join(args.unit, 'proofs', 'lib', 'A', 'AB1w.v'),
             'B': os.path.join(args.unit, 'proofs', 'lib', 'ReusableB', 'YB1w.v')}
    pinned = pins(args.unit)
    runs = [('A', 'asan', args.image_a, args.debug_a, args.cells_a), ('B', 'asan-ubsan', args.image_b, args.debug_b,
                                                                       args.cells_b)]
    out = ['\t'.join(COLUMNS)]
    for tag, build, image, debug, cells_path in runs:
        img = Image(tag, image, debug)
        if img.image_sha != pinned.get(build):
            sys.exit(f'image {tag}: sha256 {img.image_sha} is not the {build} pin in harness.yaml')
        ok, text = img.twin_check()
        print(f'image {tag}: {build} sha256 {img.image_sha}; debug twin sha256 {img.debug_sha}; {text}',
              file=sys.stderr)
        if not ok:
            sys.exit(f'image {tag}: the debug twin does not hold the image bytes')
        test = Test(img)
        cells = cells_from(cells_path or files[tag], tag)
        tree = labels_in(files[tag])
        counts = collections.Counter()
        for label, lo, hi in cells:
            r = row(test, tag, label, lo, hi, label in tree)
            counts[r[-3]] += 1
            out.append('\t'.join(x.replace('\t', ' ').replace('\n', ' ') for x in r))
        print(f'image {tag}: {len(cells)} labels tested from {cells_path or files[tag]}: '
              f"{counts['kept']} kept, {counts['removed']} removed", file=sys.stderr)
    sys.stdout.write('\n'.join(out) + '\n')


if __name__ == '__main__':
    main()
