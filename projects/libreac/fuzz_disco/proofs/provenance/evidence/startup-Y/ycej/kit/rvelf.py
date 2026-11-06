"""Shared helpers for elf_symbols.py and numeral_map.py: a stdlib ELF64 reader and the
small RV64GC decoder both tools need (instruction lengths, PC-relative and
auipc-paired immediates, register writes).

Only what address alignment needs is decoded.  Full disassembly for humans is
left to capstone (optional, see disasm()).
"""

import hashlib
import struct

PT_LOAD = 1
PT_TLS = 7
SHT_PROGBITS = 1
SHT_NOBITS = 8
SHF_WRITE = 0x1
SHF_ALLOC = 0x2
SHF_EXECINSTR = 0x4
SHF_TLS = 0x400
PF_X = 1
PF_W = 2
PF_R = 4
PAGE = 0x1000


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


class Region:
    """An allocated address range: a section, or a PT_LOAD piece when the
    binary has no section headers."""

    __slots__ = ("name", "vaddr", "size", "offset", "kind", "flags")

    def __init__(self, name, vaddr, size, offset, kind, flags):
        self.name = name
        self.vaddr = vaddr
        self.size = size
        self.offset = offset  # file offset, None for NOBITS
        self.kind = kind      # exec | data | bss | tls
        self.flags = flags

    @property
    def end(self):
        return self.vaddr + self.size

    def to_json(self):
        return {"name": self.name, "vaddr": self.vaddr, "size": self.size, "kind": self.kind}


class Elf:
    def __init__(self, path):
        self.path = path
        with open(path, "rb") as f:
            self.data = f.read()
        d = self.data
        if d[:4] != b"\x7fELF" or d[4] != 2 or d[5] != 1:
            raise SystemExit(f"{path}: not a little-endian ELF64 file")
        (self.e_type, self.e_machine, _, self.entry, phoff, shoff, _, _, phentsize,
         phnum, shentsize, shnum, shstrndx) = struct.unpack_from("<HHIQQQIHHHHHH", d, 16)
        if self.e_machine != 243:
            raise SystemExit(f"{path}: e_machine {self.e_machine} is not RISC-V (243)")
        self.phdr_addr = None
        self.phnum = phnum
        self.phentsize = phentsize
        self.segments = []
        self.tls = None
        for i in range(phnum):
            p_type, p_flags, p_off, p_vaddr, _, p_filesz, p_memsz, p_align = struct.unpack_from(
                "<IIQQQQQQ", d, phoff + i * phentsize)
            if p_type == PT_LOAD:
                self.segments.append({"vaddr": p_vaddr, "filesz": p_filesz, "memsz": p_memsz,
                                      "offset": p_off, "flags": p_flags})
            elif p_type == 6:  # PT_PHDR
                self.phdr_addr = p_vaddr
            elif p_type == PT_TLS:
                self.tls = {"vaddr": p_vaddr, "filesz": p_filesz, "memsz": p_memsz, "align": p_align}
        self.sections = []
        if shoff and shnum:
            raw = [struct.unpack_from("<IIQQQQIIQQ", d, shoff + i * shentsize) for i in range(shnum)]
            stroff = raw[shstrndx][4]

            def name_at(o):
                e = d.index(b"\0", stroff + o)
                return d[stroff + o:e].decode()

            for (sh_name, sh_type, sh_flags, sh_addr, sh_offset, sh_size, *_rest) in raw:
                if not (sh_flags & SHF_ALLOC) or sh_size == 0:
                    continue
                if sh_flags & SHF_EXECINSTR:
                    kind = "exec"
                elif sh_flags & SHF_TLS:
                    kind = "tls"
                elif sh_type == SHT_NOBITS:
                    kind = "bss"
                else:
                    kind = "data"
                self.sections.append(Region(name_at(sh_name), sh_addr, sh_size,
                                            None if sh_type == SHT_NOBITS else sh_offset,
                                            kind, sh_flags))
        if not self.sections:
            # No section headers: one region per PT_LOAD file part, one per bss tail.
            for n, s in enumerate(self.segments):
                kind = "exec" if s["flags"] & PF_X else "data"
                if s["filesz"]:
                    self.sections.append(Region(f"load{n}", s["vaddr"], s["filesz"], s["offset"], kind, 0))
                if s["memsz"] > s["filesz"]:
                    self.sections.append(Region(f"load{n}.bss", s["vaddr"] + s["filesz"],
                                                s["memsz"] - s["filesz"], None, "bss", 0))
        self.sections.sort(key=lambda r: r.vaddr)

    # ----- image geometry (the elf-snapshot rule: page-rounded PT_LOADs) -----
    def image_segments(self):
        out = []
        for s in self.segments:
            lo = s["vaddr"] & ~(PAGE - 1)
            hi = (s["vaddr"] + s["memsz"] + PAGE - 1) & ~(PAGE - 1)
            perms = ("r" if s["flags"] & PF_R else "-") + ("w" if s["flags"] & PF_W else "-") + \
                    ("x" if s["flags"] & PF_X else "-")
            out.append({"base": lo, "size": hi - lo, "perms": perms})
        return out

    def read(self, vaddr, n):
        """Bytes at vaddr from the file image; None if not file-backed."""
        for s in self.segments:
            if s["vaddr"] <= vaddr and vaddr + n <= s["vaddr"] + s["filesz"]:
                o = s["offset"] + vaddr - s["vaddr"]
                return self.data[o:o + n]
        return None

    def region_bytes(self, r):
        return self.data[r.offset:r.offset + r.size]

    def hull(self):
        segs = self.image_segments()
        return min(s["base"] for s in segs), max(s["base"] + s["size"] for s in segs)


# --------------------------------------------------------------------------------------
# RV64GC decoding (subset)
# --------------------------------------------------------------------------------------

def sext(v, bits):
    m = 1 << (bits - 1)
    return (v & ((1 << bits) - 1) ^ m) - m


MASK_U = 0xFFFFF000          # U/J immediates: bits 31:12
MASK_I = 0xFFF00000          # I immediate: bits 31:20
MASK_SB = 0xFE000F80         # S/B immediates: bits 31:25, 11:7
MASK_CJ = 0x1FFC             # c.j immediate
MASK_CB = 0x1C7C             # c.beqz/c.bnez immediate

OP_LUI, OP_AUIPC, OP_JAL, OP_JALR, OP_BRANCH = 0x37, 0x17, 0x6F, 0x67, 0x63
OP_LOAD, OP_LOADFP, OP_STORE, OP_STOREFP, OP_IMM = 0x03, 0x07, 0x23, 0x27, 0x13

# Kinds returned by classify(): what makes an encoding move with addresses.
K_PLAIN, K_AUIPC, K_JAL, K_BRANCH, K_CJ, K_CB = 0, 1, 2, 3, 4, 5


def j_imm(w):
    return sext(((w >> 31) & 1) << 20 | ((w >> 12) & 0xFF) << 12 | ((w >> 20) & 1) << 11
                | ((w >> 21) & 0x3FF) << 1, 21)


def b_imm(w):
    return sext(((w >> 31) & 1) << 12 | ((w >> 7) & 1) << 11 | ((w >> 25) & 0x3F) << 5
                | ((w >> 8) & 0xF) << 1, 13)


def i_imm(w):
    return sext(w >> 20, 12)


def s_imm(w):
    return sext(((w >> 25) << 5) | ((w >> 7) & 0x1F), 12)


def cj_imm(h):
    v = (((h >> 12) & 1) << 11 | ((h >> 8) & 1) << 10 | ((h >> 9) & 3) << 8 | ((h >> 6) & 1) << 7
         | ((h >> 7) & 1) << 6 | ((h >> 2) & 1) << 5 | ((h >> 11) & 1) << 4 | ((h >> 3) & 7) << 1)
    return sext(v, 12)


def cb_imm(h):
    v = (((h >> 12) & 1) << 8 | ((h >> 5) & 3) << 6 | ((h >> 2) & 1) << 5 | ((h >> 10) & 3) << 3
         | ((h >> 3) & 3) << 1)
    return sext(v, 9)


def classify(raw, length):
    """(kind, rd_written or None, pcrel_offset or None) for one instruction."""
    if length == 4:
        op = raw & 0x7F
        rd = (raw >> 7) & 31
        if op == OP_AUIPC:
            return K_AUIPC, rd, sext(raw & MASK_U, 32)
        if op == OP_JAL:
            return K_JAL, rd, j_imm(raw)
        if op == OP_BRANCH:
            return K_BRANCH, None, b_imm(raw)
        if op in (OP_STORE, OP_STOREFP, OP_LOADFP, 0x0F):
            return K_PLAIN, None, None
        if op == 0x73 and ((raw >> 12) & 7) == 0:  # ecall/ebreak/...
            return K_PLAIN, None, None
        return K_PLAIN, rd, None  # conservative: any other opcode may write rd
    h = raw
    q = h & 3
    f3 = h >> 13
    if q == 1:
        if f3 == 5:
            return K_CJ, None, cj_imm(h)
        if f3 in (6, 7):
            return K_CB, None, cb_imm(h)
        if f3 == 4:
            return K_PLAIN, ((h >> 7) & 7) + 8, None
        return K_PLAIN, (h >> 7) & 31, None
    if q == 0:  # c.addi4spn / c.lw / c.ld write rd'; c.fld and the stores write no integer register
        return K_PLAIN, (((h >> 2) & 7) + 8 if f3 in (0, 2, 3) else None), None
    # q == 2
    if f3 == 4:
        rs1, rs2, b12 = (h >> 7) & 31, (h >> 2) & 31, (h >> 12) & 1
        if rs2 == 0:
            return K_PLAIN, (1 if b12 else None), None  # c.jalr writes ra; c.jr nothing
        return K_PLAIN, rs1, None  # c.mv / c.add
    if f3 in (0, 2, 3):
        return K_PLAIN, (h >> 7) & 31, None
    return K_PLAIN, None, None  # c.fldsp / stores


def lo12_user(raw, length, reg):
    """If this instruction consumes `reg` through a 12-bit immediate the way a
    %pcrel_lo partner does, return (mask, imm); else None."""
    if length != 4:
        return None
    op = raw & 0x7F
    rs1 = (raw >> 15) & 31
    if rs1 != reg:
        return None
    f3 = (raw >> 12) & 7
    if op in (OP_LOAD, OP_LOADFP, OP_JALR) or (op == OP_IMM and f3 == 0):
        return MASK_I, i_imm(raw)
    if op in (OP_STORE, OP_STOREFP):
        return MASK_SB, s_imm(raw)
    return None


PAIR_WINDOW = 64
CALLEE_SAVED = {2, 8, 9} | set(range(18, 28))  # sp, s0-s11
KIND_NAMES = {K_AUIPC: "auipc", K_JAL: "jal", K_BRANCH: "branch", K_CJ: "c.j", K_CB: "c.bxxz"}
KIND_MASK = {K_AUIPC: MASK_U, K_JAL: MASK_U, K_BRANCH: MASK_SB, K_CJ: MASK_CJ, K_CB: MASK_CB}


class Code:
    """Linear-sweep decode of one executable region.

    pcs[i], lens[i], raws[i]: the i-th instruction.
    tok[i]: encoding with every address-dependent immediate masked, so code
            that only moved compares equal.
    sens[i]: None, or (what, target) for address-dependent instructions:
             ("auipc"/"jal"/"branch"/"c.j"/"c.bxxz", pc-relative target) or
             ("lo12", target formed with its auipc partner at index j).
    """

    def __init__(self, blob, base):
        self.base = base
        pcs, lens, raws = [], [], []
        i, n = 0, len(blob)
        while i + 2 <= n:
            h = blob[i] | blob[i + 1] << 8
            if h & 3 == 3:
                if i + 4 > n:
                    break
                raws.append(h | (blob[i + 2] | blob[i + 3] << 8) << 16)
                lens.append(4)
            else:
                raws.append(h)
                lens.append(2)
            pcs.append(base + i)
            i += lens[-1]
        self.pcs, self.lens, self.raws = pcs, lens, raws
        N = len(raws)
        masks = [0xFFFFFFFF] * N
        sens = [None] * N
        partner = [None] * N
        for k in range(N):
            kind, rd, off = classify(raws[k], lens[k])
            if kind == K_PLAIN:
                continue
            masks[k] &= ~KIND_MASK[kind] & 0xFFFFFFFF
            tgt = (pcs[k] + off) & 0xFFFFFFFFFFFFFFFF
            sens[k] = (KIND_NAMES[kind], tgt)
            if kind == K_AUIPC and rd != 0:
                # Partners are found until rd is overwritten.  Code after an unconditional jump is
                # often still in rd's live range (`bltu ..; j slow; <fast path>`), so partners there
                # are masked too, but marked "lo12x": their target is not trusted as an anchor.
                after_jump = False
                for m in range(k + 1, min(N, k + 1 + PAIR_WINDOW)):
                    u = lo12_user(raws[m], lens[m], rd)
                    if u is not None:
                        masks[m] &= ~u[0] & 0xFFFFFFFF
                        if sens[m] is None:
                            sens[m] = ("lo12x" if after_jump else "lo12", (tgt + u[1]) & 0xFFFFFFFFFFFFFFFF)
                            partner[m] = k
                    mk, mrd, _ = classify(raws[m], lens[m])
                    if mrd == rd:
                        break
                    call = (mk == K_JAL and mrd == 1) or (lens[m] == 4 and raws[m] & 0x7F == OP_JALR and mrd == 1) \
                        or (lens[m] == 2 and raws[m] & 0xF07F == 0x9002 and raws[m] & 0x0F80)  # c.jalr
                    if call and rd not in CALLEE_SAVED:
                        break  # the callee may clobber a caller-saved rd
                    if mk == K_CJ or (mk == K_JAL and mrd == 0) or \
                            (lens[m] == 4 and raws[m] & 0x7F == OP_JALR and mrd == 0) or \
                            (lens[m] == 2 and raws[m] & 0xF07F == 0x8002):  # j / jr / ret / c.j / c.jr
                        after_jump = True
        self.masks = masks
        self.sens = sens
        self.partner = partner
        self.tok = [((raws[k] & masks[k]) << 2) | (lens[k] >> 1) | (0 if masks[k] == 0xFFFFFFFF else 1 << 40)
                    for k in range(N)]
        self._index = None

    def index_of(self, pc):
        """Instruction index starting exactly at pc, or None."""
        if self._index is None:
            self._index = {p: k for k, p in enumerate(self.pcs)}
        return self._index.get(pc)


def disasm(blob, base):
    """[(pc, hex, text)] via capstone, or None if capstone is not importable."""
    try:
        import capstone  # noqa: WPS433
    except ImportError:
        return None
    md = capstone.Cs(capstone.CS_ARCH_RISCV, capstone.CS_MODE_RISCV64 | capstone.CS_MODE_RISCVC)
    md.skipdata = True
    return [(a, blob[a - base:a - base + s].hex(), f"{m} {o}".strip())
            for (a, s, m, o) in md.disasm_lite(blob, base)]
