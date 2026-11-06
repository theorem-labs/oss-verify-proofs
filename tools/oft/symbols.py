"""The symbol fact of a build (`oft symbols`): every function and data object of its unstripped twin, with the
SHA-256 of its bytes (a function's also with its address immediates masked) and the source lines a function's code
comes from, and every allocated section of the build, so that data no symbol names (a GOT slot) has a name too.

projects/<project>/<harness>/symbols/<build>.tsv is

    # oss-fuzz-theorems/symbols/1 sha256=<the sha256 of the stripped binary, which harness.yaml pins for the build>
    <name> TAB <kind> TAB <address, 0x...> TAB <size> TAB <exact> TAB <masked> TAB <lines>

with one row for each function (kind func) and each data object with a size (kind object) of the symbol table,
aliases each under its own name, and one for each allocated section (kind section, its name with its leading `.`), by
address and then name.  For a function, exact is the SHA-256 of its bytes, masked that of mask() of them, given the
build's Image (the functions of the symbol table that NORETURN names, and the bytes the program cannot write, which
hold its jump tables), and lines is `<file>:<first>-<last>` for each source file of its code, joined by `,`, or `-`
when the line table has none; a function of size 0 (musl's _start) has no bytes, so all three are `-`.  For a data
object and a section, exact is the SHA-256 of its bytes, or `-` for one with no file contents (.bss), and masked and
lines are `-`.

The addresses come from the unstripped twin's .symtab and the bytes from the stripped binary, so read() refuses a
stripped file that is not the pinned binary, and a pair whose .text, data objects' bytes or allocated sections differ
(but a note's bytes: each link writes its own build-id).  The line table is the text output of
`llvm-dwarfdump --debug-line` of the unstripped twin, run in the toolchain image of release.yaml, so neither this
module nor its tests need LLVM.

This module is not the checker (keys.NOT_THE_CHECKER): `oft check` never opens it, and facts.Harness.symbols imports
it only when it is called."""
import bisect
import collections
import hashlib
import os
import posixpath
import re
import struct
import sys

from . import elf, facts, layout, names, yamlio

HEADER = "# oss-fuzz-theorems/symbols/1 sha256=%s"
# the most bytes a symbol fact may hold: facts.MAX_BYTES, which facts.file_cap gives its path (no row of facts.CAPS
# names it); test_symbols holds the two equal
CAP = 5 << 20
_HEADER = re.compile(r"# oss-fuzz-theorems/symbols/1 sha256=([0-9a-f]{64})")
_SHA = re.compile(r"[0-9a-f]{64}")
_LINES = re.compile(r"-|[^\s,]+:[0-9]+-[0-9]+(?:,[^\s,]+:[0-9]+-[0-9]+)*")


# the kinds of a symbol fact's rows: a function and a data object (elf.KINDS), and an allocated section
KINDS = ("func", "object", "section")


class Sym(collections.namedtuple("Sym", "name kind address size exact masked lines")):
    """One row of a symbol fact: a function's, a data object's or an allocated section's name, its kind (KINDS),
    address and size, the SHA-256 of its bytes (exact; `-` for an object or section with no file contents and a
    function of size 0) and of mask() of them (masked; `-` but for a function with a size), and its source lines (`-`
    but for a function with a size)."""


# ------------------------------------------------------------------ masking
# Ported from s2_funcs.py mask_text (the bs-measure scripts), for one function at a time.

GP = 3
RA = 1
SP = 2
# ra, t0-t2, a0-a7 and t3-t6: the registers a callee may overwrite (the RISC-V calling convention)
CALLER_SAVED = (1, 5, 6, 7, 10, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31)
OP_LOAD = 0x03
OP_LOADFP = 0x07
OP_MISC_MEM = 0x0F
OP_IMM = 0x13
OP_AUIPC = 0x17
OP_STORE = 0x23
OP_STOREFP = 0x27
OP_AMO = 0x2F
OP_REG = 0x33
OP_LUI = 0x37
OP_BRANCH = 0x63
OP_JALR = 0x67
OP_JAL = 0x6F
OP_SYSTEM = 0x73
# the bits of an instruction that are not its immediate
KEEP_U = 0x00000FFF          # jal, auipc, lui: rd and the opcode
KEEP_B = 0x01FFF07F          # branch, store: rs2, rs1, funct3 and the opcode
KEEP_I = 0x000FFFFF          # addi, load, jalr: rs1, funct3, rd and the opcode

# The functions a call to which never returns, each a name pattern and why: the compiler places other code after
# such a call (it emits `unreachable` there), so mask() gives the call no path to the next instruction.  Only a global
# or weak function is one of them: the names are the C library's and the sanitizer runtimes', and a program's own
# local function of such a name (a static exit) is another function, which may return.
NORETURN = (
    (r"__asan_report_(?!.*_noabort$).*",
     "ASan's report entry points abort (ASan's ABI); only the *_noabort ones return"),
    (r"__ubsan_handle_.*_abort", "UBSan's *_abort handlers abort (UBSan's ABI); the others return"),
    (r"abort", "C: abort never returns"),
    (r"exit", "C: exit never returns"),
    (r"_Exit", "C: _Exit never returns"),
    (r"__assert_fail", "C (musl, glibc): the failure path of assert, which aborts"),
)
_NORETURN = re.compile("|".join("(?:%s)" % pattern for pattern, _why in NORETURN))
# The same for functions of a sanitizer runtime that a static link makes local, each a C++ name in the runtime's own
# namespace, which no program's static function has (a C static function's symbol is its plain name).
NORETURN_RUNTIME = (
    (r"_ZN11__sanitizer11CheckFailedEPKciS1_yy",
     "sanitizer_common: __sanitizer::CheckFailed is NORETURN (sanitizer_internal_defs.h), the failure path of CHECK, "
     "which ends in Die"),
)
_NORETURN_RUNTIME = re.compile("|".join("(?:%s)" % pattern for pattern, _why in NORETURN_RUNTIME))


def sx(v, bits):
    """v, a bits-wide two's complement number, as a Python int."""
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def jal_imm(w):
    """The displacement of a jal."""
    return sx(((w >> 31) & 1) << 20 | ((w >> 12) & 0xFF) << 12 | ((w >> 20) & 1) << 11 | ((w >> 21) & 0x3FF) << 1, 21)


def b_imm(w):
    """The displacement of a branch."""
    return sx(((w >> 31) & 1) << 12 | ((w >> 7) & 1) << 11 | ((w >> 25) & 0x3F) << 5 | ((w >> 8) & 0xF) << 1, 13)


def i_imm(w):
    """The 12-bit immediate of an I-type instruction (addi, a load, jalr)."""
    return sx((w >> 20) & 0xFFF, 12)


def s_imm(w):
    """The 12-bit immediate of a store."""
    return sx((w >> 25) << 5 | (w >> 7) & 0x1F, 12)


def u_imm(w):
    """The upper immediate of an auipc or a lui, shifted into place."""
    return sx(w & 0xFFFFF000, 32)


def noreturn_addresses(functions):
    """The addresses of the functions of [elf.Symbol] (elf.Elf.symbols) whose names NORETURN lists, global and weak
    ones only, or NORETURN_RUNTIME lists: the noreturn of mask()."""
    return frozenset(s.address for s in functions if s.kind == "func" and (
        (s.binding in ("global", "weak") and _NORETURN.fullmatch(s.name)) or _NORETURN_RUNTIME.fullmatch(s.name)))


# What mask() knows of the build a function is in: noreturn, the addresses of the functions a call to which never
# returns (noreturn_addresses); constant(address, size), the bytes there when the program cannot write them
# (elf.Elf.constant), or None; data(address, size), the bytes there in any allocated section with file contents, or
# None; sections, (start, end) of each allocated section with a size (the sections a symbol fact lists, which the
# lint's contract-literals also reads); stored, the code addresses the build keeps as data (code_addresses), or None
# when unknown; landing, [start, end) of the code of each function with landing pads (landing_ranges): ((0, 2^64))
# when unknown, in which case every function is treated as having landing pads and no low half is masked anywhere.
# build_image makes one.  NO_IMAGE is for tests of single functions: no call is known never to return, no
# jump table is proven, no lui forms an address, any jump through a register may be a computed goto, and no function
# has landing pads.
Image = collections.namedtuple("Image", "noreturn constant data sections stored landing")
NO_IMAGE = Image(frozenset(), lambda address, size: None, lambda address, size: None, (), None, ())
# the unwind tables, which hold offsets and function starts, never a label (a landing pad is an offset in the LSDA)
UNWIND = (".eh_frame", ".eh_frame_hdr", ".gcc_except_table")


def code_addresses(sections, lo, hi, skip=()):
    """The sorted 4-aligned addresses in [lo, hi) (.text) that sections (elf.Elf.sections) but the unwind tables
    (UNWIND) hold as 32-bit little-endian words at 4-aligned addresses, and, when hi passes 2^32, as 64-bit ones too
    (a 64-bit pointer below 2^32 at a 4-aligned address starts with such a 32-bit word): the code addresses the
    program keeps as data, such as the labels of a computed goto's table (Image.stored).  A word, or a 64-bit word,
    that starts inside a range [start, end) of skip, sorted (jump_table_words: the entries of relative jump tables,
    offsets that no code reads as an address), is left out."""
    starts_of_skip = [start for start, _end in skip]

    def skipped(address):
        k = bisect.bisect_right(starts_of_skip, address) - 1
        return k >= 0 and address < skip[k][1]
    found = set()
    for s in sections:
        if s.bytes is None or s.name in UNWIND:
            continue
        first = -s.address % 4
        for fmt, size, starts in (("<%dI", 4, (first,)), ("<%dQ", 8, (first, first + 4) if hi > 1 << 32 else ())):
            for start in starts:
                count = max(0, (len(s.bytes) - start) // size)
                for k, v in enumerate(struct.unpack_from(fmt % count, s.bytes, start)):
                    if lo <= v < hi and not v & 3 and not skipped(s.address + start + size * k):
                        found.add(v)
    return tuple(sorted(found))


def jump_table_words(text, text_addr, functions, constant, noreturn=frozenset()):
    """The sorted, disjoint [start, end) of the entries of the jump tables of each function of functions ((address,
    size) of each, in the bytes text at text_addr) whose every jump through a register has a table _tables proves
    (noreturn as mask's): 32-bit words in bytes the program cannot write (constant) that its code adds to the table's
    own address, so offsets, which code_addresses leaves out of Image.stored.  Such a word may look like an address
    of another function (LLVM's table of __sanitizer::VSNPrintf holds 0x46890, inside the asan runtime's wcrtomb of
    the libreac fuzz_ctrl build): a compiler emits each function's jump tables as its own data, so no other code reads
    one as a label."""
    out = []
    end = text_addr + len(text)
    for address, size in functions:
        if not (text_addr <= address and address + size <= end) or size < 4:
            continue
        code = text[address - text_addr:address - text_addr + size]
        words = struct.unpack_from("<%dI" % (len(code) // 4), code)
        succ, entered, body_calls = _edges(words, address, noreturn)
        jumps = _jumps(words, body_calls)
        spans = {}
        if jumps and _tables(words, address, constant, entered, jumps, succ, False, spans=spans):
            out += spans.values()
    merged = []
    for start, stop in sorted(out):
        if merged and start <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], stop))
        else:
            merged.append((start, stop))
    return tuple(merged)


def landing_ranges(sections, warn=None):
    """[start, end) of the code of each FDE of .eh_frame (in sections, elf.Elf.sections) whose CIE has an 'L'
    augmentation: an LSDA, whose landing pads the unwinder enters with the registers of the call that threw, sorted;
    ((0, 2^64),), every function, when _eh_frame cannot read .eh_frame (which disables low-half masking for the whole
    build; warn, when given, is called with the reason)."""
    out = []
    for s in sections:
        if s.name == ".eh_frame" and s.bytes is not None:
            try:
                out += _eh_frame(s.bytes, s.address)
            except (IndexError, ValueError, struct.error) as e:
                if warn:
                    warn(".eh_frame at 0x%x cannot be read (%s): low-half masking is disabled for this build"
                         % (s.address, e))
                return ((0, 1 << 64),)
    return tuple(sorted(out))


def _uleb(data, p):
    """(the unsigned LEB128 number at data[p], the position after it)."""
    value = shift = 0
    while True:
        byte = data[p]
        p += 1
        value |= (byte & 0x7F) << shift
        shift += 7
        if not byte & 0x80:
            return value, p


def _pointer(data, p, encoding, base):
    """(the value, the position after it) of a DWARF pointer of encoding (DW_EH_PE_*) at data[p], at address base + p:
    absolute, or relative to its own address (pcrel); ValueError for any other."""
    fmt = {0x00: "<Q", 0x02: "<H", 0x03: "<I", 0x04: "<Q", 0x0A: "<h", 0x0B: "<i", 0x0C: "<q"}.get(encoding & 0x0F)
    if encoding & 0x0F == 0x01:
        value, after = _uleb(data, p)
    elif encoding & 0x0F == 0x09:
        value, after = _uleb(data, p)
        value = sx(value, 7 * ((after - p)))
    elif fmt:
        value, after = struct.unpack_from(fmt, data, p)[0], p + struct.calcsize(fmt)
    else:
        raise ValueError("pointer encoding 0x%x" % encoding)
    if encoding & 0xF0 == 0x10:
        value += base + p
    elif encoding & 0xF0:
        raise ValueError("pointer encoding 0x%x" % encoding)
    return value & M64, after


def _eh_frame(data, base):
    """[start, end) of the code of each FDE of the .eh_frame bytes data at address base whose CIE's augmentation has
    an 'L'; IndexError, ValueError or struct.error when the walk cannot read every record to the end of data (a zero
    length ends it, followed by zero bytes only), a CIE is of a version other than 1, 3 or 4 (4 adds the address and
    segment selector sizes; 1 has a one-byte return address register, 3 and 4 a uleb128 one), or an 'L' CIE or one
    of its FDEs cannot be read within its record."""
    cies, out, pos = {}, [], 0
    while pos < len(data):
        length, start = struct.unpack_from("<I", data, pos)[0], pos + 4
        if not length:
            if any(data[start:]):
                raise ValueError("bytes after the terminator of .eh_frame")
            break
        if length == 0xFFFFFFFF:
            length, start = struct.unpack_from("<Q", data, start)[0], start + 8
        end = start + length
        if length < 4 or end > len(data):
            raise ValueError("a record of .eh_frame does not fit it")
        cie = struct.unpack_from("<I", data, start)[0]
        p = start + 4
        if not cie:
            version = data[p]
            nul = data.index(b"\0", p + 1, end)
            augmentation = data[p + 1:nul].decode("ascii")
            if version not in (1, 3, 4):
                raise ValueError("CIE version %d" % version)
            cies[pos] = None
            if "L" in augmentation:
                if not augmentation.startswith("z"):
                    raise ValueError("augmentation %r" % augmentation)
                p = nul + 1 + (2 if version == 4 else 0)               # the address and segment selector sizes
                p = _uleb(data, _uleb(data, p)[1])[1]                  # the code and data alignment factors
                p = p + 1 if version == 1 else _uleb(data, p)[1]       # the return address register
                p = _uleb(data, p)[1]                                  # the length of the augmentation data
                fde = 0x00
                for c in augmentation[1:]:
                    if c == "R":
                        fde, p = data[p], p + 1
                    elif c == "L":
                        p += 1
                    elif c == "P":   # the personality routine's pointer: only its size matters
                        p = _pointer(data, p + 1, data[p] & 0x0F, base)[1]
                    elif c not in "SB":
                        raise ValueError("augmentation %r" % augmentation)
                if p > end:
                    raise ValueError("a CIE of .eh_frame runs past its record")
                cies[pos] = fde
        else:
            if start - cie not in cies:
                raise ValueError("an FDE of .eh_frame names no CIE before it")
            fde = cies[start - cie]
            if fde is not None:
                begin, p = _pointer(data, p, fde, base)
                size, p = _pointer(data, p, fde & 0x0F, base)
                if p > end:
                    raise ValueError("an FDE of .eh_frame runs past its record")
                out.append((begin, begin + size))
        pos = end
    return out


def build_image(binary, sections, noreturn, warn=None, functions=()):
    """The Image of the build whose stripped binary is elf.Elf binary, sections its allocated sections
    (binary.sections()) and noreturn the addresses of its functions that never return (noreturn_addresses); the
    entries of the jump tables of functions ((address, size) of each) are not stored code addresses
    (jump_table_words).  warn, when given, is called with a diagnostic for each degradation (landing_ranges)."""
    def data(address, size):
        try:
            return binary.contents(address, size)
        except ValueError:
            return None
    lo, hi = binary.text_addr, binary.text_addr + len(binary.text)
    return Image(noreturn, binary.constant, data, tuple((s.address, s.address + s.size) for s in sections if s.size),
                 code_addresses(sections, lo, hi,
                                jump_table_words(binary.text, lo, functions, binary.constant, noreturn)),
                 landing_ranges(sections, warn=warn))


def mask(code, addr, image=NO_IMAGE):
    """code, the bytes of one function at addr, with its address immediates zeroed, so that the same function at
    another address masks equal:

      * a jal's or a branch's displacement when its target is outside the function (one inside is the function's
        own control flow, which a move leaves as it is, and a changed loop changes);
      * every auipc's upper immediate;
      * a lui's upper immediate, when every addi, load, store or jalr that takes its register as a base (below) forms
        with its 12-bit immediate an address inside a section of image.sections: the high half of an address (any
        other lui makes a number, as a lui and an addi that make sigaction flags do, and is kept);
      * the 12-bit immediate of an addi, load, store or jalr whose base register holds the high half of an address
        (an auipc's, or such a lui's) on every path to it, the low half, and of one relative to gp.

    Every other bit is kept.  A register holds an address high half at an instruction when it does on every path to
    it inside the function: from the entry, where no register holds one, to the next instruction (not after a jal
    or jalr that links x0: a jump, a return or a tail call, nor after a call to an address of image.noreturn: a call
    that never returns, after which the compiler places other code), to the target of a branch or a jal that is an
    instruction of the function, and from a jump through a register (a jalr that links x0 and is no return, jalr x0,
    0(ra)) to the targets of its jump table: the entries that are instructions of the function, when _tables proves
    every such table from the code and image.constant (an entry outside the function leaves it).  A jump through a
    register with no proven table is a tail call, which leaves the function, when its target is a loaded pointer or a
    number the code makes that is no label of the function (_tail_calls), and the program takes the address of no
    instruction of the function, its entry included, for more than to call it or to jump to its entry, and takes no
    value an auipc or a lui makes, at any distance, into arithmetic or memory (_labels_taken): a computed goto's
    target or anchor (labels as values, LLVM's indirectbr), biased or not, or an unproven jump table's.  When every
    such jump is a tail call through a pointer loaded with nothing added, the last rule is narrower
    (_loaded_tail_calls): only such a value, moved by arithmetic other than an immediate add, that the function hands
    on (stores, passes, returns) takes a label.  When a jump through a register is neither, or the function calls
    into its own body, by a jal or by a jalr to an address it forms (a return through ra may then come back into it),
    every jump through a register in it and every return may go to every instruction of it.  Code that no path from
    the entry reaches holds none where it starts.  A write to the register ends what it held, and a call (a jal or
    jalr that links a register) ends what the registers the callee may overwrite (CALLER_SAVED) held.  A call or tail
    call through a register goes to a function's entry (the calling convention) or to a label whose address the
    program takes, a return through ra goes back to the caller, and the function itself is entered only at its entry,
    but for a function with landing pads (image.landing), which the unwinder enters at other instructions with the
    registers of the call that threw: no register holds a high half anywhere in such a function.

    A frame slot (a base register and an offset) holds an auipc's high half after an sd of a register that holds
    one, through a base register that holds none and is not gp, and an ld from the slot puts it back in a register.
    A raw auipc result is never a C value (the compiler always completes it with its %pcrel_lo), so a slot that
    receives one is a compiler spill slot, which no C pointer may write: a call or a store through another register
    leaves it.  The slot ends when its base register is written (a call writes the caller-saved ones) or a store or
    an atomic through that register overlaps it.  A lui's value may be a C number kept in a variable, so no slot
    holds a lui's.  Every instruction is 32 bits (rv64g has no compressed ones); bytes after the last whole word are
    kept."""
    n = len(code) // 4
    words = struct.unpack_from("<%dI" % n, code)
    out = list(words)
    for i, w in enumerate(words):
        op = w & 0x7F
        if op in (OP_JAL, OP_BRANCH) and not 0 <= 4 * i + (jal_imm(w) if op == OP_JAL else b_imm(w)) < len(code):
            out[i] = w & (KEEP_U if op == OP_JAL else KEEP_B)
        elif op == OP_AUIPC:
            out[i] = w & KEEP_U
    succ, entered, body_calls = _edges(words, addr, image.noreturn)
    jumps = _jumps(words, body_calls)
    if jumps or any(w & 0x7F == OP_JALR and (w >> 7) & 0x1F for w in words):
        taken, inward = _labels_taken(words, addr, image, succ, set(jumps))
        if inward and not body_calls:
            body_calls = True
            jumps = _jumps(words, True)
        if jumps and taken and not body_calls and _loaded_tail_calls(words, addr, image, entered, jumps, succ):
            pass
        elif jumps and not _tables(words, addr, image.constant, entered, jumps, succ, not body_calls and not taken):
            everywhere = list(range(n))
            for i in jumps:
                succ[i] = everywhere
    # held[i]: register, or frame slot (base register, offset) -> the indices of the auipc and lui instructions whose
    # address high half it holds at i, for each that holds one on every path to i; none at all in a function with
    # landing pads (image.landing), which the unwinder enters from outside at instructions other than its entry
    if any(start < addr + len(code) and addr < end for start, end in image.landing):
        held = {i: {} for i in range(n)}
    else:
        held = _flow(n, succ, lambda i, state: _step(words, i, state),
                     lambda have, after: {r: have[r] | after[r] for r in have.keys() & after.keys()})
    uses = []   # (index, the auipc and lui instructions whose high half its base register holds)
    for i, w in enumerate(words):
        op, f3, rs1 = w & 0x7F, (w >> 12) & 7, (w >> 15) & 0x1F
        if (op == OP_IMM and f3 == 0) or op in (OP_LOAD, OP_LOADFP, OP_JALR, OP_STORE, OP_STOREFP):
            if rs1 in held[i]:
                uses.append((i, held[i][rs1]))
            elif rs1 == GP:
                out[i] = w & (KEEP_B if op in (OP_STORE, OP_STOREFP) else KEEP_I)
    numbers = set()
    for i, highs in uses:
        for high in highs:
            if words[high] & 0x7F == OP_LUI:
                value = (u_imm(words[high]) + _low(words[i])) & M64
                if not any(start <= value < end for start, end in image.sections):
                    numbers.add(high)
    for i, highs in uses:
        if not highs & numbers:
            out[i] = words[i] & (KEEP_B if words[i] & 0x7F in (OP_STORE, OP_STOREFP) else KEEP_I)
            for high in highs:
                if words[high] & 0x7F == OP_LUI:
                    out[high] = words[high] & KEEP_U
    return struct.pack("<%dI" % n, *out) + code[4 * n:]


def _edges(words, addr, noreturn):
    """(succ, entered, body_calls) of the function at addr, of words: the indices of the instructions each one may pass
    control to but by a jump through a register (the next one, not after a jal or jalr that links x0 nor after a call
    to an address of noreturn; the target of a branch or a jal that is an instruction of the function), the indices
    of those targets, and whether a jal calls into the function's body (not its entry, nor itself: LLD's call of an
    undefined weak function, which reaches no return)."""
    n = len(words)
    succ, entered, body_calls = [], set(), False
    for i, w in enumerate(words):
        op, rd = w & 0x7F, (w >> 7) & 0x1F
        to = [i + 1] if i + 1 < n and not (op in (OP_JAL, OP_JALR) and rd == 0) and not (
            op == OP_JAL and rd and addr + 4 * i + jal_imm(w) in noreturn) else []
        if op in (OP_JAL, OP_BRANCH):
            t = 4 * i + (jal_imm(w) if op == OP_JAL else b_imm(w))
            if 0 <= t < 4 * n and not t % 4:
                to.append(t // 4)
                entered.add(t // 4)
                body_calls |= op == OP_JAL and rd != 0 and t not in (0, 4 * i)
        succ.append(to)
    return succ, entered, body_calls


def _jumps(words, returns):
    """The indices of the jumps through a register of words: each jalr that links x0, but, unless returns, a return
    (jalr x0, 0(ra))."""
    return [i for i, w in enumerate(words) if w & 0x7F == OP_JALR and (w >> 7) & 0x1F == 0
            and (returns or (w >> 15) & 0x1F != RA or i_imm(w))]


def _flow(n, succ, step, meet, unreached=True):
    """{index: state} of a forward analysis of n instructions that holds on every path, to a fixed point: from the
    entry, where the state is empty ({}), then, with unreached, from each instruction no path reached (without, such
    an instruction has no state); succ[i] are the instructions instruction i may pass control to, step(i, state) is
    the state after it, and meet(a, b) what two states agree on."""
    at = {}
    for start in range(n) if unreached else range(min(n, 1)):
        if start in at:
            continue
        at[start] = {}
        work = [start]
        while work:
            i = work.pop()
            after = step(i, at[i])
            for j in succ[i]:
                have = at.get(j)
                joined = after if have is None else meet(have, after)
                if joined != have:
                    at[j] = joined
                    work.append(j)
    return at


M64 = (1 << 64) - 1


def _known(words, i, addr, state):
    """What state (register -> the number it holds) is after words[i] at addr + 4i: an auipc, a lui and an addi of a
    known register give a number, a call (a jal or jalr that links a register) ends what the registers the callee may
    overwrite (CALLER_SAVED) held, and any other write ends what its register held."""
    w = words[i]
    op, rd, f3, rs1 = w & 0x7F, (w >> 7) & 0x1F, (w >> 12) & 7, (w >> 15) & 0x1F
    if not rd or op in (OP_BRANCH, OP_STORE, OP_STOREFP, OP_MISC_MEM):
        return state
    state = dict(state)
    v = None
    if op == OP_AUIPC:
        v = (addr + 4 * i + u_imm(w)) & M64
    elif op == OP_LUI:
        v = u_imm(w) & M64
    elif op == OP_IMM and f3 == 0 and (rs1 == 0 or rs1 in state):
        v = (state.get(rs1, 0) + i_imm(w)) & M64
    elif op in (OP_JAL, OP_JALR):
        for r in CALLER_SAVED:
            state.pop(r, None)
    state.pop(rd, None)
    if v is not None:
        state[rd] = v
    return state


def _tables(words, addr, constant, entered, jumps, succ, leave, loads=False, spans=None):
    """True, with each jump of jumps given the targets of its jump table as its successors in succ, when _table proves
    the table of every jump a path from the entry reaches, with the numbers the registers hold on every such path
    (_known) while the jumps go only to those targets, and no target is inside the straight-line code of a jump (a
    jump no path reaches goes nowhere); with leave, a jump with no proven table may instead be a tail call by its
    target (_tail_calls, on the same paths, with loads only through a loaded pointer), which leaves the function and
    gets no successor; spans, when given, then gets the [start, end) of each proven table's entries, by jump.
    Otherwise False.  Such proofs hold of every run: the first jump of a run to go elsewhere would contradict its
    proof or its target's provenance, which held on the way there."""
    proven = {}
    for _round in range(MAX_ROUNDS):
        for i in jumps:
            succ[i] = list(proven.get(i, ()))
        known = _flow(len(words), succ, lambda i, state: _known(words, i, addr, state),
                      lambda a, b: {r: v for r, v in a.items() if b.get(r) == v}, unreached=False)
        tables = {i: _table(words, i, addr, constant, entered, known) if i in known else (i + 1, []) for i in jumps}
        unproven = [i for i, table in tables.items() if table is None]
        if unproven and not (leave and set(unproven) <= _tail_calls(words, addr, succ, unproven, loads)):
            return False
        found, guarded = {}, set()
        for i, table in tables.items():
            table = table or (i + 1, [])
            found[i] = table[1]
            guarded.update(range(table[0], i + 1))
        if any(guarded & set(targets) for targets in found.values()):
            return False
        if found == proven:
            if spans is not None:
                spans.update((i, table[2]) for i, table in tables.items() if table and len(table) == 3)
            return True
        proven = found
    return False


# a register's provenance (_provenance) that may be anything: an argument, a call's result, or arithmetic; a state
# holds no register whose provenance is UNKNOWN
UNKNOWN = frozenset(("unknown",))


def _tail_calls(words, addr, succ, jumps, loads=False):
    """The jumps of jumps (indices) that are tail calls by their target: on every path of succ (where the jumps go
    nowhere), the register they jump through holds a value loaded from memory with nothing added, nor the jump's
    immediate (a GOT or vtable pointer: a stored word, which code_addresses reads), or, but with loads, a number an
    auipc, lui or li and addi immediates make that, with the jump's immediate, is no address of an instruction of the
    function other than its entry (_provenance), as `tail f` makes.  Any other target, made by arithmetic, returned by
    a call or unknown, may be a label of the function."""
    lo, hi = addr + 1, addr + 4 * len(words)
    at = _flow(len(words), succ, lambda i, state: _provenance(words, i, addr, state), _join_provenance)
    out = set()
    for i in jumps:
        w = words[i]
        tags, imm = at[i].get((w >> 15) & 0x1F, UNKNOWN), i_imm(w)
        if all((t == "load" and not imm) or (not loads and t not in ("load", "unknown")
                                             and not lo <= (t[1] + imm) & M64 & ~1 < hi)
               for t in tags):
            out.add(i)
    return frozenset(out)


def _loaded_tail_calls(words, addr, image, entered, jumps, succ):
    """True, with succ given the control flow it proves, when each jump of jumps has a proven table or is a tail call
    through a pointer loaded with nothing added (_tables, loads) and, on that control flow, the program takes no label
    of the function (_labels_taken, with escapes): every rule of _labels_taken holds but the last, which only a value
    an auipc or a lui made that the function stores, or that arithmetic other than an immediate add moved and the
    function hands on, meets.  Otherwise False, and succ is as it was.

    Why the control flow may be the one this proves: such a tail call jumps to the word memory holds.  Take the first
    jump of a run to go to an instruction of the function other than its entry.  Until then every instruction of the
    function ran on this control flow, so the label it jumps to was put in memory on it: as a constant of the build
    (image.stored), or by a store of the function (of any value an auipc or a lui made: a label biased by any amount,
    as `&&start + 8192`, may be stored as it is and moved into the label by other code), or by other code it handed a
    moved value to (_escapes: arguments, returned values, a call's target).  The one way left is a value made by an
    auipc or a lui and immediate adds, outside the function, that the function passes to a callee or gives back to
    its caller, and that code then moves into a label and stores: the residual of Ruling 54, which _labels_taken
    leaves too."""
    trial = [list(to) for to in succ]
    if not _tables(words, addr, image.constant, entered, jumps, trial, True, loads=True):
        return False
    taken, inward = _labels_taken(words, addr, image, trial, (), escapes=True)
    if taken or inward:
        return False
    succ[:] = trial
    return True


def _join_provenance(a, b):
    """The provenance of each register on either of two paths: the union of its tags, UNKNOWN (left out) when either
    lacks it, when the union holds "unknown" or more than 8 numbers (so that a loop that steps a number ends)."""
    out = {}
    for r in a.keys() & b.keys():
        tags = a[r] | b[r]
        if "unknown" not in tags and len(tags) <= 8:
            out[r] = tags
    return out


def _provenance(words, i, addr, state):
    """What state (register -> its provenance, a set of tags: ("n", number), "load", or "unknown"; a register state
    lacks is unknown, as at the entry) is after words[i] at addr + 4i: an auipc, a lui and an addi of x0 make a
    number, an addi adds its immediate to each number (an addi of 0 copies), a load gives "load", a call (a jal or jalr
    that links a register) makes the registers the callee may overwrite (CALLER_SAVED) unknown, and any other write
    makes its register unknown."""
    w = words[i]
    op, rd, f3, rs1 = w & 0x7F, (w >> 7) & 0x1F, (w >> 12) & 7, (w >> 15) & 0x1F
    if not rd or op in (OP_BRANCH, OP_STORE, OP_STOREFP, OP_MISC_MEM):
        return state
    state = dict(state)
    tags = UNKNOWN
    if op == OP_AUIPC:
        tags = frozenset((("n", (addr + 4 * i + u_imm(w)) & M64),))
    elif op == OP_LUI:
        tags = frozenset((("n", u_imm(w) & M64),))
    elif op == OP_IMM and f3 == 0:
        source = frozenset((("n", 0),)) if not rs1 else state.get(rs1, UNKNOWN)
        if not i_imm(w):
            tags = source
        elif all(t != "unknown" and t != "load" for t in source):
            tags = frozenset(("n", (t[1] + i_imm(w)) & M64) for t in source)
    elif op == OP_LOAD:
        tags = frozenset(("load",))
    elif op in (OP_JAL, OP_JALR):
        for r in CALLER_SAVED:
            state.pop(r, None)
    state.pop(rd, None)
    if tags != UNKNOWN:
        state[rd] = tags
    return state


def _labels_taken(words, addr, image, succ, jumps, escapes=False):
    """(taken, inward) for the function at addr, of words, whose control flow is succ but each jump of jumps may go to
    every instruction.  taken: whether the program may take the address of an instruction of the function for more
    than to call it or to jump to its entry, so that a jump through a register may go there (a computed goto, LLVM's
    indirectbr, or an unproven jump table).  GNU C forms a label's address, and the anchor of label differences, only
    inside its function, so it is taken when image.stored holds an address of the function other than its entry (it
    is None when unknown); or, of the values an auipc or a lui made, moved by addi and addiw immediates, that the
    registers may hold (_derive):

      * an addi, load, store or jalr forms with one and its 12-bit immediate an address of the function, its entry
        included, but in a jalr that links a register (a call) or one that links x0 to the entry (a jump to it);
      * one forms the address of a 32-bit word (image.data) that, added to that address, gives one other than the
        entry (a jump table of relative entries);
      * an instruction reads one that is an address of the function otherwise (_reads: a branch, an argument, a
        returned value, arithmetic, a stored value);
      * an instruction takes one into other arithmetic or stores it (_arithmetic), whatever it is: a label biased by
        any amount, as `&&start + 8192`, comes back only through arithmetic, or through memory and arithmetic.  With
        escapes (_loaded_tail_calls) instead: the function stores one (_stored), or hands on (_escapes) one the
        analysis no longer follows, or a value arithmetic other than an immediate add made from one (_compute).

    inward: whether such a call goes to an instruction of the function other than its entry, a call into its own
    body."""
    lo, hi = addr + 1, addr + 4 * len(words)
    taken = image.stored is None
    if not taken:
        k = bisect.bisect_left(image.stored, lo)
        taken = k < len(image.stored) and image.stored[k] < hi
    everywhere = list(range(len(words)))
    flow = [everywhere if i in jumps else to for i, to in enumerate(succ)]
    may = _flow(len(words), flow, lambda i, state: _derive(words, i, addr, state), _join_derived)
    computed = {}
    if escapes:
        computed = _flow(len(words), flow, lambda i, state: _compute(words, i, may.get(i, {}), state), _join_computed)
    inward = False
    for i, w in enumerate(words):
        state = may.get(i) or {}
        if escapes:
            kinds = computed.get(i, {})
            leaves = w & 0x7F == OP_JAL and not 0 <= 4 * i + jal_imm(w) < 4 * len(words)
            moved = [r for r in _escapes(w, leaves)
                     if kinds.get(r) == "c" or any(v is None for _kind, v in state.get(r, ()))]
            if moved or any(r in state or kinds.get(r) == "sd" for r in _stored(w)):
                taken = True
        if not state:
            continue
        op, rd, f3, rs1 = w & 0x7F, (w >> 7) & 0x1F, (w >> 12) & 7, (w >> 15) & 0x1F
        if (op == OP_IMM and f3 == 0) or op in (OP_LOAD, OP_LOADFP, OP_JALR, OP_STORE, OP_STOREFP):
            for made in _values(state.get(rs1, ())):
                value = (made + _low(w)) & M64
                if addr <= value < hi:
                    if op == OP_JALR and rd:
                        inward |= value != addr
                    elif not (op == OP_JALR and value == addr):
                        taken = True
                word = image.data(value, 4)
                if word and lo <= (value + sx(int.from_bytes(word, "little"), 32)) & M64 < hi:
                    taken = True
        if (not escapes and any(r in state for r in _arithmetic(w))) or any(
                addr <= v < hi for r in _reads(w) for v in _values(state.get(r, ()))):
            taken = True
    return taken, inward


def _stored(w):
    """The integer registers whose value an instruction puts in memory, a CSR or an FP register: _arithmetic's, but
    for the operands of integer arithmetic."""
    return () if w & 0x7F in (OP_REG, OP_32, OP_IMM, OP_IMM_32) else _arithmetic(w)


def _escapes(w, leaves=False):
    """The integer registers whose value an instruction hands on to code other than the function's own arithmetic:
    those it stores (_stored), the arguments a call, a jump through a register, a jal that leaves the function
    (leaves: a tail call) or a system call passes, the values a return gives back (a0, a1), and the target of a call
    through a register."""
    op, rd, rs1 = w & 0x7F, (w >> 7) & 0x1F, (w >> 15) & 0x1F
    if op == OP_JAL:
        return ARGUMENTS if rd or leaves else ()
    if op == OP_JALR:
        return (10, 11) if not rd and rs1 == RA and not i_imm(w) else ARGUMENTS + ((rs1,) if rd else ())
    if w == 0x73:   # ecall
        return ARGUMENTS
    return _stored(w)


# the funct7 of the FP instructions that write an integer register: fcvt.w/l from single and double, feq/flt/fle,
# fmv.x and fclass
FP_TO_INTEGER = (0x50, 0x51, 0x60, 0x61, 0x70, 0x71)


def _compute(words, i, derived, state):
    """What state (register -> "c" when it may hold a value arithmetic other than an immediate add made from a value
    an auipc or a lui made (one that derived, the _derive state before words[i], holds) or from a "c" or "sd" one;
    "s" when it holds an address of the stack on every path, as sp does where it holds nothing else; "sd" when it may
    hold a stack address plus or minus a value an auipc or a lui made) is after words[i]: an addi or addiw of a "c"
    register makes "c", an addi of an "s" or "sd" one the same, and of one derived holds _derive follows; an add of an
    "s" register and one that holds nothing, or a sub of such a one from an "s" register, makes "s"; an add of an "s"
    and a derived register, or a sub of a derived one from an "s" one, makes "sd": a stack address plus a number is no
    label (a run's stack has no fixed distance to the code), but the stack taken away again gives the number back, so
    the function's store of an "sd" value takes labels (_labels_taken) and its arithmetic makes "c"; passed to a call
    or a tail call, or given back, it is in Ruling 54's residual (a callee's or a caller's stack is at a fixed
    distance from the function's).  slt, sltu, slti and
    sltiu make 0 or 1, no label; other integer arithmetic of a "c", "sd" or derived register, or of two "s" ones,
    makes "c"; any other write ends what its register held."""
    w = words[i]
    op, rd, f3, rs1, rs2 = w & 0x7F, (w >> 7) & 0x1F, (w >> 12) & 7, (w >> 15) & 0x1F, (w >> 20) & 0x1F
    if not rd or op in (OP_BRANCH, OP_STORE, OP_STOREFP, OP_MISC_MEM, OP_LOADFP) or (
            op == 0x53 and w >> 25 not in FP_TO_INTEGER):
        return state

    def held(r):
        return state.get(r) or ("d" if r in derived else "s" if r == SP else None)
    state = dict(state)
    kind = None
    if op in (OP_IMM, OP_IMM_32) and f3 == 0:
        source = held(rs1)
        if source == "c" or (source == "sd" and op == OP_IMM_32):
            kind = "c"
        elif source in ("s", "sd") and op == OP_IMM:
            kind = source
    elif op == OP_REG and f3 == 0 and w >> 25 == 0 and {held(rs1), held(rs2)} == {"s", None}:
        kind = "s"
    elif op == OP_REG and f3 == 0 and w >> 25 == 0x20 and held(rs1) == "s" and held(rs2) is None:
        kind = "s"
    elif op == OP_REG and f3 == 0 and (
            (w >> 25 == 0 and {held(rs1), held(rs2)} == {"s", "d"})
            or (w >> 25 == 0x20 and held(rs1) == "s" and held(rs2) == "d")):
        kind = "sd"
    elif op in (OP_REG, OP_32, OP_IMM, OP_IMM_32):
        compare = f3 in (2, 3) and (op == OP_IMM or (op == OP_REG and w >> 25 == 0))
        operands = [held(r) for r in _arithmetic(w)]
        if not compare and (any(k in ("c", "d", "sd") for k in operands) or operands.count("s") > 1):
            kind = "c"
    elif op not in (OP_LUI, OP_AUIPC, OP_JAL, OP_JALR, OP_LOAD, OP_AMO, 0x53, OP_SYSTEM) and any(
            held(r) in ("c", "d", "sd") for r in _arithmetic(w)):
        kind = "c"
    state.pop(rd, None)
    if kind:
        state[rd] = kind
    return state


def _join_computed(a, b):
    """What each register may hold (_compute) on either of two paths: "c" when either path gives it "c", else "sd"
    when either gives it "sd", and "s" when both give it "s"."""
    out = {}
    for r in a.keys() | b.keys():
        kinds = (a.get(r), b.get(r))
        kind = "c" if "c" in kinds else "sd" if "sd" in kinds else "s" if kinds == ("s", "s") else None
        if kind:
            out[r] = kind
    return out


def _high(words, i, addr):
    """The number the auipc or lui words[i] (at addr + 4i) puts in its register."""
    return ((addr + 4 * i if words[i] & 0x7F == OP_AUIPC else 0) + u_imm(words[i])) & M64


def _values(tags):
    """The numbers of the tags (_derive) whose number is known."""
    return [v for kind, v in tags if v is not None]


# the integer registers a call passes arguments in, a0-a7
ARGUMENTS = tuple(range(10, 18))
# the opcode of addiw and the other 32-bit immediate instructions, and of addw and the other 32-bit ones
OP_IMM_32 = 0x1B
OP_32 = 0x3B
# the opcodes of the instructions that write their rd, an integer register (an auipc and a lui aside); the others write
# none, or an FP register, or may write rd and are taken as not (fmv.x.d, fcvt.l.d, feq: OP-FP), which _derive may do
WRITES_RD = (OP_JAL, OP_JALR, OP_IMM, OP_IMM_32, OP_REG, OP_32, OP_LOAD, OP_AMO)


def _derive(words, i, addr, state):
    """What state (register -> the tags of the values an auipc or a lui made that it may hold: ("high", the number)
    for the value of an auipc or a lui, ("moved", the number) for one an addi or an addiw moved, ("moved", None) for
    one the analysis no longer follows) is after words[i] at addr + 4i: an auipc or a lui puts its value in its
    register, an addi or an addiw of such a register puts each value moved by its immediate in its own, and any other
    instruction that surely writes an integer register (WRITES_RD, a CSR instruction) ends what it held; a call ends
    nothing (a callee may return what it got).  A high tag is a single instruction's, so a loop keeps it exact."""
    w = words[i]
    op, rd, f3, rs1 = w & 0x7F, (w >> 7) & 0x1F, (w >> 12) & 7, (w >> 15) & 0x1F
    if not rd:
        return state
    if op in (OP_AUIPC, OP_LUI):
        made = frozenset((("high", _high(words, i, addr)),))
    elif op in (OP_IMM, OP_IMM_32) and f3 == 0 and rs1 in state:
        imm = i_imm(w)
        made = _capped(frozenset(
            ("moved", None if v is None else (v + imm) & M64 if op == OP_IMM else sx((v + imm) & 0xFFFFFFFF, 32) & M64)
            for _kind, v in state[rs1]))
    elif rd in state and (op in WRITES_RD or (op == OP_SYSTEM and f3)):
        state = dict(state)
        del state[rd]
        return state
    else:
        return state
    state = dict(state)
    state[rd] = made
    return state


def _capped(tags):
    """tags, with its moved values replaced by ("moved", None) when one is None or there are more than MAX_DERIVE (so
    that a loop that steps a pointer ends)."""
    moved = [t for t in tags if t[0] == "moved"]
    if len(moved) > MAX_DERIVE or ("moved", None) in tags:
        return frozenset(t for t in tags if t[0] == "high") | {("moved", None)}
    return tags


def _join_derived(a, b):
    """The tags (_derive) each register may hold on either of two paths: the union, _capped."""
    out = dict(a)
    for r, tags in b.items():
        out[r] = _capped(out.get(r, frozenset()) | tags)
    return out


def _arithmetic(w):
    """The integer registers whose value an instruction takes into arithmetic other than adding a 12-bit immediate
    (addi, addiw), or stores: the operands of the other integer instructions (add, sub, the shifts, the logic ones,
    slt, mul), an integer store's or an atomic's value, the value a CSR instruction writes and the integer an FP
    instruction reads (fmv to FP, fcvt from an integer); both of rs1 and rs2 of an instruction of another opcode."""
    op, f3, rs1, rs2 = w & 0x7F, (w >> 12) & 7, (w >> 15) & 0x1F, (w >> 20) & 0x1F
    if op in (OP_REG, OP_32):
        return (rs1, rs2)
    if op in (OP_STORE, OP_AMO):
        return (rs2,)
    if op in (OP_IMM, OP_IMM_32):
        return () if f3 == 0 else (rs1,)
    if op == OP_SYSTEM:
        return (rs1,) if 1 <= f3 <= 3 else ()
    if op == 0x53:
        return (rs1,) if w >> 25 in (0x68, 0x69, 0x78, 0x79) else ()
    if op in (OP_LUI, OP_AUIPC, OP_JAL, OP_JALR, OP_BRANCH, OP_LOAD, OP_LOADFP, OP_STOREFP, OP_MISC_MEM, 0x43, 0x47,
              0x4B, 0x4F):
        return ()
    return (rs1, rs2)


def _reads(w):
    """The integer registers an instruction reads other than as the base of an addi, a load, a store or a jalr: those
    of _arithmetic, a branch's, and the arguments a call, a jump through a register (a tail call) or a system call
    passes, or the values a return gives back (a0, a1)."""
    op, rs1, rs2 = w & 0x7F, (w >> 15) & 0x1F, (w >> 20) & 0x1F
    if op == OP_BRANCH:
        return (rs1, rs2)
    if op == OP_JAL:
        return ARGUMENTS if (w >> 7) & 0x1F else ()
    if op == OP_JALR:
        return (10, 11) if not (w >> 7) & 0x1F and rs1 == RA and not i_imm(w) else ARGUMENTS
    if w == 0x73:   # ecall
        return ARGUMENTS
    return _arithmetic(w)


# the most entries a jump table _table reads
MAX_TABLE = 1 << 12
# the most rounds _tables iterates to reach a fixed point
MAX_ROUNDS = 8
# the most moved values _join_derive keeps per register before widening to unknown
MAX_DERIVE = 8


def _table(words, j, addr, constant, entered, known):
    """(the index of the second instruction of the straight-line code that ends at the jump through a register
    words[j], the indices of its targets, [t, t + 4(N + 1)): the table's entries) when that code gives the jump's
    register t + the 32-bit entry at t + 4i, with t an address it computes (auipc, addi) and i in [0, N] (a bltu of a
    register it set to N, or a bgeu of one it set to N + 1, falls through), as LLVM's code for a jump table does,
    interleaved with other instructions:

        li n, N; bltu n, i, default; slli i, i, 2; auipc t, hi; addi t, t, lo; add i, i, t; lw x, 0(i); add x, x, t;
        jr x

    and the N + 1 entries are bytes the program cannot write (constant): the targets are the instructions of the
    function the entries lead to (one outside it leaves it).  The straight-line code runs back from the jump to the
    target of a branch or jal of the function (entered), or to the first instruction after a jump, call or system
    instruction; where it starts, a register holds the number known gives it there (known[start], _known), if any.
    None for any other jump, which may go anywhere."""
    s = j
    while s > 0 and s not in entered and j - s < 64 and words[s - 1] & 0x7F not in (OP_JAL, OP_JALR, OP_SYSTEM):
        s -= 1
    # the value of each register: ("c", c) the number c; ("b", N) a number in [0, N]; ("s", N) 4 times one; ("a", t, N)
    # t + 4i, i in [0, N]; ("e", t, N) the 32-bit entry at that address; ("t", t, N) t + that entry; None unknown
    val = {r: ("c", c) for r, c in known[s].items()}
    val[0] = ("c", 0)
    for k in range(s, j):
        w = words[k]
        op, rd, f3, rs1, rs2 = w & 0x7F, (w >> 7) & 0x1F, (w >> 12) & 7, (w >> 15) & 0x1F, (w >> 20) & 0x1F
        a, b, v = val.get(rs1), val.get(rs2), None
        if op == OP_BRANCH:
            # falling through a bltu N, i or a bgeu i, N + 1 leaves i in [0, N]
            if f3 == 6 and a and a[0] == "c" and 0 <= a[1] < MAX_TABLE and b is None:
                val[rs2] = ("b", a[1])
            elif f3 == 7 and b and b[0] == "c" and 0 < b[1] <= MAX_TABLE and a is None:
                val[rs1] = ("b", b[1] - 1)
            continue
        if op in (OP_STORE, OP_STOREFP, OP_MISC_MEM) or not rd:
            continue
        if op == OP_AUIPC:
            v = ("c", (addr + 4 * k + u_imm(w)) & M64)
        elif op == OP_LUI:
            v = ("c", u_imm(w) & M64)
        elif op == OP_IMM and f3 == 0:
            v = a if not i_imm(w) else ("c", (a[1] + i_imm(w)) & M64) if a and a[0] == "c" else None
        elif op == OP_IMM and f3 == 1 and w >> 20 == 2 and a and a[0] == "b":   # slli rd, rs1, 2
            v = ("s", a[1])
        elif op == OP_REG and w >> 25 == 0 and f3 == 0 and a and b:            # add
            pair = {a[0]: a, b[0]: b}
            if a[0] == b[0] == "c":
                v = ("c", (a[1] + b[1]) & M64)
            elif "c" in pair and "s" in pair:
                v = ("a", pair["c"][1], pair["s"][1])
            elif "c" in pair and "e" in pair and pair["e"][1] == pair["c"][1]:
                v = ("t",) + pair["e"][1:]
        elif op == OP_LOAD and f3 == 2 and w >> 20 == 0 and a and a[0] == "a":  # lw rd, 0(rs1)
            v = ("e",) + a[1:]
        val[rd] = v
    x = val.get((words[j] >> 15) & 0x1F)
    if not (x and x[0] == "t" and words[j] >> 20 == 0):
        return None
    _kind, table, last = x
    targets = set()
    for e in range(last + 1):
        entry = constant(table + 4 * e, 4)
        if entry is None:
            return None
        off = table + sx(int.from_bytes(entry, "little"), 32) - addr
        if 0 <= off < 4 * len(words):
            if off % 4:
                return None
            targets.add(off // 4)
    return s + 1, sorted(targets), (table, table + 4 * (last + 1))


def _low(w):
    """The 12-bit immediate of an addi, a load, a store or a jalr."""
    return s_imm(w) if w & 0x7F in (OP_STORE, OP_STOREFP) else i_imm(w)


def _step(words, i, held):
    """What held (register, or frame slot (base register, offset) -> the indices of the auipc and lui instructions
    whose high half it holds) is after words[i], when it is held before."""
    w = words[i]
    op, rd, f3, rs1 = w & 0x7F, (w >> 7) & 0x1F, (w >> 12) & 7, (w >> 15) & 0x1F
    held = dict(held)
    if op in (OP_AUIPC, OP_LUI):
        if rd:
            _forget(held, rd)
            held[rd] = frozenset((i,))
        return held
    if op in (OP_STORE, OP_STOREFP, OP_AMO):
        # the bytes a store or an atomic writes through rs1 end each slot of rs1 they overlap
        off = 0 if op == OP_AMO else s_imm(w)
        for slot in [k for k in held if isinstance(k, tuple) and k[0] == rs1 and off < k[1] + 8
                     and k[1] < off + (1 << f3)]:
            del held[slot]
    if op in (OP_STORE, OP_STOREFP):
        value = held.get((w >> 20) & 0x1F) if op == OP_STORE and f3 == 3 else None
        if value and rs1 not in held and rs1 != GP and all(words[high] & 0x7F == OP_AUIPC for high in value):
            held[(rs1, off)] = value
        return held
    loaded = held.get((rs1, i_imm(w))) if op == OP_LOAD and f3 == 3 else None
    if rd and op != OP_BRANCH:
        _forget(held, rd)
    if rd and op in (OP_JAL, OP_JALR):
        for r in CALLER_SAVED:
            _forget(held, r)
    if loaded and rd:
        held[rd] = loaded
    return held


def _forget(held, r):
    """End what register r held, and what each frame slot r is the base register of held."""
    held.pop(r, None)
    for slot in [k for k in held if isinstance(k, tuple) and k[0] == r]:
        del held[slot]


# --------------------------------------------------------------- line table

_VERSION = re.compile(r"version: ([0-9]+)$")
_DIRECTORY = re.compile(r'include_directories\[ *([0-9]+)\] = "(.*)"$')
_FILE = re.compile(r"file_names\[ *([0-9]+)\]:$")
_NAME = re.compile(r'name: "(.*)"$')
_DIR_INDEX = re.compile(r"dir_index: ([0-9]+)$")
_ROW = re.compile(r"0x([0-9a-f]+) +([0-9]+) +[0-9]+ +([0-9]+) ")   # address, line, column, file


def _source(version, dirs, name, dir_index, where):
    """A file entry's path: its name in its include directory (DWARF 4's directory 0, which it does not list, is the
    compilation directory), from DWARF 5's directory 0, the compilation directory, down when it is under it."""
    if not name.startswith("/") and (dir_index or version >= 5):
        if dir_index not in dirs:
            raise ValueError("%s: no include directory %d" % (where, dir_index))
        name = posixpath.join(dirs[dir_index], name)
    top = dirs.get(0, "").rstrip("/") if version >= 5 else ""
    if top and name.startswith(top + "/"):
        name = name[len(top) + 1:]
    return name


def line_table(text):
    """[(address, file, line)], by address, of each row of `llvm-dwarfdump --debug-line` output that places code on a
    line of a file: not an end_sequence row, whose address is the one after its sequence, nor a row of line 0, code of
    no line.  Each line table's own file entries name its rows' files (_source)."""
    rows = []
    version, dirs, entries, entry, names = 0, {}, {}, None, {}
    for no, line in enumerate(text.splitlines(), 1):
        line = line.strip()
        where = "line %d of the line table" % no
        if line.startswith("debug_line["):
            version, dirs, entries, entry, names = 0, {}, {}, None, {}
            continue
        m = _ROW.match(line)
        if m:
            if "end_sequence" in line.split() or m.group(2) == "0":
                continue
            index = int(m.group(3))
            if index not in names:
                if index not in entries or entries[index][0] is None:
                    raise ValueError("%s: no file %d" % (where, index))
                names[index] = _source(version, dirs, entries[index][0], entries[index][1], where)
            rows.append((int(m.group(1), 16), names[index], int(m.group(2))))
            continue
        for rx in (_VERSION, _DIRECTORY, _FILE, _NAME, _DIR_INDEX):
            m = rx.match(line)
            if m:
                break
        else:
            continue
        if rx is _VERSION:
            version = int(m.group(1))
        elif rx is _DIRECTORY:
            dirs[int(m.group(1))] = m.group(2)
        elif rx is _FILE:
            entry = int(m.group(1))
            entries[entry] = [None, 0]
        elif entry is not None and rx is _NAME:
            entries[entry][0] = m.group(1)
        elif entry is not None:
            entries[entry][1] = int(m.group(1))
    return sorted(rows, key=lambda r: r[0])


def source_lines(table, address, size):
    """`<file>:<first>-<last>` for each file with a row of table in [address, address + size), in the order of its
    first row, joined by `,`; `-` when there is none."""
    spans = {}
    for a, name, line in table[bisect.bisect_left(table, address, key=lambda r: r[0]):]:
        if a >= address + size:
            break
        first, last = spans.get(name, (line, line))
        spans[name] = (min(first, line), max(last, line))
    return ",".join("%s:%d-%d" % (name, first, last) for name, (first, last) in spans.items()) or "-"


# ------------------------------------------------------------------- facts

def _sha256(data):
    return hashlib.sha256(data).hexdigest()


def read(unstripped, stripped, lines_text, sha256):
    """[Sym] of every function and data object of the unstripped twin (elf.Elf.symbols) and every allocated section,
    by address and then name, its bytes taken from the stripped binary, which must be the one whose sha256 harness.yaml
    pins, sha256, and whose .text, data objects' bytes and allocated sections must be the twin's (a note aside: each
    link writes its own build-id); lines_text is `llvm-dwarfdump --debug-line` of the unstripped twin."""
    full, bare = elf.Elf(unstripped), elf.Elf(stripped)
    if bare.sha256 != sha256:
        raise ValueError("%s has sha256 %s, but the build's pinned sha256 is %s: it is not the published binary"
                         % (stripped, bare.sha256, sha256))
    if (full.text_addr, full.text) != (bare.text_addr, bare.text):
        raise ValueError("%s is not the stripped twin of %s: their .text differs (%d bytes at 0x%x, %d bytes at 0x%x)"
                         % (stripped, unstripped, len(bare.text), bare.text_addr, len(full.text), full.text_addr))
    table = line_table(lines_text)
    lo, hi = bare.text_addr, bare.text_addr + len(bare.text)
    out = []
    functions = full.symbols()
    sections = bare.sections()
    image = build_image(bare, sections, noreturn_addresses(functions),
                        warn=lambda msg: print("oft symbols: %s: %s" % (stripped, msg), file=sys.stderr),
                        functions=[(s.address, s.size) for s in functions if s.kind == "func"])
    for name, kind, address, size, _binding in functions:
        if kind == "object":
            data = bare.contents(address, size)
            if full.contents(address, size) != data:
                raise ValueError("%s is not the stripped twin of %s: the bytes of the object %s at 0x%x differ"
                                 % (stripped, unstripped, name, address))
            out.append(Sym(name, kind, address, size, "-" if data is None else _sha256(data), "-", "-"))
            continue
        if not (lo <= address and address + size <= hi):
            raise ValueError("%s: function %s at 0x%x (%d bytes) is outside .text (0x%x to 0x%x)"
                             % (unstripped, name, address, size, lo, hi))
        if size == 0:
            out.append(Sym(name, kind, address, 0, "-", "-", "-"))
            continue
        code = bare.text[address - lo:address - lo + size]
        out.append(Sym(name, kind, address, size, _sha256(code), _sha256(mask(code, address, image)),
                       source_lines(table, address, size)))
    twin = full.sections()
    if [s._replace(bytes=None) for s in sections] != [s._replace(bytes=None) for s in twin]:
        raise ValueError("%s is not the stripped twin of %s: their allocated sections differ" % (stripped, unstripped))
    for s, theirs in zip(sections, twin):
        if s.type != elf.SHT_NOTE and s.bytes != theirs.bytes:
            raise ValueError("%s is not the stripped twin of %s: the bytes of the section %s differ"
                             % (stripped, unstripped, s.name))
        out.append(Sym(s.name, "section", s.address, s.size, "-" if s.bytes is None else _sha256(s.bytes), "-", "-"))
    return sorted(out, key=lambda s: (s.address, s.name))


def _row(text, where):
    """The Sym of one row of a symbol fact."""
    fields = text.split("\t")
    if len(fields) != 7:
        raise ValueError("%s: %d fields, not 7" % (where, len(fields)))
    name, kind, address, size, exact, masked, lines = fields
    if not re.fullmatch(r"\S+", name):
        raise ValueError("%s: the name %r is empty or holds a space" % (where, name))
    if kind not in KINDS:
        raise ValueError("%s: the kind %r is neither %s" % (where, kind, " nor ".join(KINDS)))
    if not re.fullmatch(r"0x[0-9a-f]+", address):
        raise ValueError("%s: the address %r is not 0x and lower-case hexadecimal digits" % (where, address))
    if not re.fullmatch(r"0|[1-9][0-9]*", size):
        raise ValueError("%s: the size %r is not a number" % (where, size))
    if kind in ("object", "section"):
        if kind == "object" and size == "0":
            raise ValueError("%s: an object of size 0" % where)
        if exact != "-" and not _SHA.fullmatch(exact):
            raise ValueError("%s: the exact %r of the %s is neither a sha256 nor -" % (where, exact, kind))
        if (masked, lines) != ("-", "-"):
            raise ValueError("%s: the %s has no masked bytes and no lines, but %r and %r are not -"
                             % (where, kind, masked, lines))
    elif size == "0":
        if (exact, masked, lines) != ("-", "-", "-"):
            raise ValueError("%s: a function of size 0 has no bytes and no lines, but %r, %r and %r are not -"
                             % (where, exact, masked, lines))
    else:
        for what, value in (("exact", exact), ("masked", masked)):
            if not _SHA.fullmatch(value):
                raise ValueError("%s: %s %r is not a sha256" % (where, what, value))
        if not _LINES.fullmatch(lines):
            raise ValueError("%s: the lines %r are neither - nor <file>:<first>-<last>, joined by ," % (where, lines))
    return Sym(name, kind, int(address, 16), int(size), exact, masked, lines)


def write(path, syms, stripped_sha256):
    """Write the symbol fact of syms, read from the stripped binary whose sha256 is stripped_sha256, at path; a row
    that load would refuse is refused instead."""
    if not _SHA.fullmatch(stripped_sha256):
        raise ValueError("%r is not a sha256" % stripped_sha256)
    rows = [HEADER % stripped_sha256]
    for s in syms:
        row = "\t".join((s.name, s.kind, "0x%x" % s.address, str(s.size), s.exact, s.masked, s.lines))
        _row(row, "the row of %r" % s.name)
        rows.append(row)
    text = "\n".join(rows) + "\n"
    if len(text.encode("utf-8")) > CAP:
        raise ValueError("%d rows make a symbol fact over the %d-byte cap" % (len(syms), CAP))
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)


def load(path):
    """(stripped sha256, [Sym]) of the symbol fact at path; ValueError, naming the line, for one it cannot read.  It is
    read as lint reads a file: never through a symbolic link, and only a regular file of at most CAP bytes
    (facts.read_bounded raises facts.BoundedFileError for any other)."""
    return parse(facts.read_bounded(path, CAP).decode("utf-8"))


def parse(text):
    """(stripped sha256, [Sym]) of the text of a symbol fact; ValueError, naming the line, for one it cannot read."""
    if not text.endswith("\n"):
        raise ValueError("it does not end with a newline")
    lines = text[:-1].split("\n")
    m = _HEADER.fullmatch(lines[0])
    if not m:
        raise ValueError("line 1: not %r" % (HEADER % "<sha256>"))
    return m.group(1), [_row(line, "line %d" % no) for no, line in enumerate(lines[1:], 2)]


# ---------------------------------------------------------------- Symbols.v
# What Symbols.v defines (generate.symbols_v renders it, templates/Symbols.v.tmpl), read in one place by lint's
# contract-literals, contracts.py and prove.py: a module per build with a symbol fact (names.BUILD_MODULE), which
# defines s_<ident> and Size.s_<ident> for each function and data object, and, when the fact has sections, the same
# under Sec for each section, by the identifiers names.symbol_idents gives their names.

# the paths after Symbols.<Build> that name a module, not a definition: the build's module, Size, Sec and Sec.Size
MODULES = ("", "Size", "Sec", "Sec.Size")
# the build of each build's module
BUILD_OF = {m: b for b, m in names.BUILD_MODULE.items()}
# A name as Rocq reads one: an identifier, then fields, each a `.` and an identifier with nothing between them, with
# blanks allowed before each `.` (and comments, which rocq.strip blanks): rocq 9.2 reads `Symbols.Plain\n  .s_x`,
# `Symbols.Plain (* c *).s_x` and `Symbols .Plain .s_x` as Symbols.Plain.s_x.  A `.` before a blank ends a sentence.
ROCQ_NAME = re.compile(r"(?<![\w'.])[^\W\d][\w']*(?:\s*\.[^\W\d][\w']*)*")


class Table(collections.namedtuple("Table", "functions sections modules")):
    """What one build's module of Symbols.v defines (table): functions, {identifier: Sym} of its functions and data
    objects; sections, the same of its sections; modules, the paths of MODULES it has (Sec and Sec.Size only when the
    fact has a section)."""


def table(rows):
    """The Table of a build whose symbol fact is rows ([Sym]).  A name two or more rows share has no identifier
    (names.rocq_idents); ValueError as names.symbol_idents."""
    idents, sections = names.symbol_idents(rows)
    return Table({idents[r.name]: r for r in rows if r.kind != "section" and r.name in idents},
                 {sections[r.name]: r for r in rows if r.kind == "section" and r.name in sections},
                 frozenset(MODULES if any(r.kind == "section" for r in rows) else MODULES[:2]))


def paths(ident, section):
    """The two paths Symbols.v gives one identifier in its build's module: its address, then its size."""
    return ("Sec." + ident, "Sec.Size." + ident) if section else (ident, "Size." + ident)


def reference(name):
    """(the build's module, the path in it) of a name (ROCQ_NAME) that refers to Symbols.v, or None.  It is one
    written Symbols.<Build>.<path>, under the library's path or not, with any path; or <Build>.<path> (after `Require
    Import Symbols`) whose path starts with s_<name>, Size or Sec, since a fuzz target's image modules have the same
    names (Plain.M.loaded_segments) and none of those.  An empty path is the module itself."""
    fields = [f.strip() for f in name.split(".")]
    for i in range(len(fields) - 1):
        if fields[i] == "Symbols" and fields[i + 1] in BUILD_OF:
            return fields[i + 1], ".".join(fields[i + 2:])
    if fields[0] in BUILD_OF and len(fields) > 1 and (fields[1] in ("Size", "Sec") or fields[1].startswith("s_")):
        return fields[0], ".".join(fields[1:])
    return None


def resolve(tab, path):
    """(row, sized) of Symbols.<Build>.<path> in a build whose Table is tab (None for a build with no symbol fact):
    the row (a Sym) of the function, data object or section it names, None when it names none (a module, or a name
    the fact lacks or gives no identifier), and whether path names its size.  A path is never looked up as a symbol's
    name: an identifier is resolved through the table alone."""
    parts = path.split(".")
    section = parts[:1] == ["Sec"]
    if section:
        parts = parts[1:]
    sized = parts[:1] == ["Size"]
    if sized:
        parts = parts[1:]
    found = None if tab is None else tab.sections if section else tab.functions
    return (found.get(parts[0]) if found is not None and len(parts) == 1 else None), sized


def defines(tab, path):
    """Whether the build's module of Symbols.v whose Table is tab defines path: a definition resolve finds, or one of
    its modules."""
    return path in tab.modules or resolve(tab, path)[0] is not None



def run(root, unstripped, stripped, lines, harness, build, out):
    """`oft symbols`: write the build's symbol fact (layout.symbol_fact) from its unstripped twin, its stripped binary,
    which must be the one harness.yaml pins, and the `llvm-dwarfdump --debug-line` output of the twin; what it did, or
    why it refused, goes to out.  The exit status."""
    try:
        p, h = layout.split_unit(harness)
        rel = layout.symbol_fact(p, h, build)
        yml = os.path.join(root, layout.statement_dir(p, h), "harness.yaml")
        if not os.path.isfile(yml):
            raise ValueError("projects/%s has no harness.yaml" % harness)
        rec = ((yamlio.load_file(yml) or {}).get("builds") or {}).get(build) or {}
        pin = rec.get("sha256")
        if rec.get("withheld") or not pin:
            raise ValueError("projects/%s/harness.yaml publishes no build %s with a sha256" % (harness, build))
        with open(lines, encoding="utf-8") as f:
            text = f.read()
        syms = read(unstripped, stripped, text, pin)
        write(os.path.join(root, rel), syms, pin)
    except (OSError, ValueError) as e:
        print("FAIL oft symbols: %s" % e, file=out)
        return 1
    count = collections.Counter(s.kind for s in syms)
    print("%s: %d functions, %d data objects, %d sections" % (rel, count["func"], count["object"], count["section"]),
          file=out)
    return 0
