#!/usr/bin/env python3
"""ptree_emit.py: write the RStep.ptree Definition of one function of a RISC-V ELF image.

Input: the image (an ELF file), the start and end address of the function (end exclusive), the
Definition's name, the name of its base parameter, and the map from the external addresses the
function names (a jal target, or an auipc pair's address) to parameter names. Output: the text
`Definition NAME (BASE P1 ... Pn : Z) : RStep.ptree := TREE.` and a final newline, nothing else.

Decoding follows the 32-bit decoder of the RISC-V semantics (theories/Riscv/Decode.v): each word
becomes one constructor of Instr.v with its fields at their encoded widths (registers 5 bits, I/S
immediates 12, B 13, U 20, J 21, shift amounts 6 or 5, rounding mode 3). Each instruction is written
as the notation PJ_<constructor>_<arguments>_<operand kinds> of lib/CJ/RL/Reloc/RProgNotJ.v, as
`(PJ_... OFFSET OPERAND... 4`, the operands in Instr.v's order, each numeric operand as the unsigned
value of its field in decimal. Three operand kinds are written as terms instead:
  - jal to an address outside [start, end): (jimm21 (P - (BASE + OFFSET)));
  - auipc: (hi20 (P - (BASE + OFFSET))), where P is the address the auipc forms with its first partner;
  - the partner of an auipc (an instruction whose rs1 is the auipc's rd, the auipc being the last
    earlier instruction that writes that register): (lo12 (P - (BASE + AUIPC_OFFSET))).
At offset 0 the term is (P - BASE). P is the parameter the map gives for the address; each term is
checked to equal the field it stands for (RStep.v's hi20, lo12, jimm21) before it is written.

Layout: leaves of 10 consecutive instructions (the last one shorter); a list of leaves is one PLeaf
when it has one leaf, else PNode K (left) (right), the left part the first len // 2 leaves and K the
offset of the right part's first instruction. A node or leaf at depth d >= 1 is written at column
2d + 2 with a parenthesis; the root without one, at column --root-indent (default 2), which moves
the root's own line only; the instructions of a leaf at depth d at column 2d + 6.

It REFUSES (exit 2, and writes nothing) on: a word that the decoder does not decode, or that has
no PJ notation (a compressed or longer-than-32-bit encoding included); an external jal or auipc
address that the map does not name; an auipc without partner; an argument or output text that holds
a string listed in the --deny file (one string per line, `#` lines ignored; an empty list is refused);
a name that is not an identifier; and any malformed input.

Dependencies: Python 3 standard library and pyelftools. No network.
"""
import argparse
import os
import re
import sys

from elftools.elf.elffile import ELFFile

REFUSE = 2

# The names of RProgNotJ.v's 78 notations, without their "PJ_" prefix.
PJ_NOTATIONS = frozenset("""
    Auipc_nt Branch_BC_EQ_nnn Branch_BC_GEU_nnn Branch_BC_GE_nnn Branch_BC_LTU_nnn Branch_BC_LT_nnn
    Branch_BC_NE_nnn CsrI_CSR_RS_nnn Csr_CSR_RS_nnn Ecall_ FLoad_FMT_D_nnn FLoad_FMT_D_nnt FStore_FMT_D_nnn
    FStore_FMT_S_nnn Fari_F_MUL_FMT_D_nnnn Fari_F_MUL_FMT_S_nnnn Fcvt_FC_D_FC_W_nnn Fcvt_FC_S_FC_W_nnn
    Fmv_FMV_F_X_FMT_D_nn Fmv_FMV_F_X_FMT_S_nn Fmv_FMV_X_F_FMT_D_nn Fmv_FMV_X_F_FMT_S_nn Fsgnj_F_SGNJ_FMT_D_nnn
    Jal_nn Jal_nt Jalr_nnn Load_SZ1_false_nnn Load_SZ1_false_nnt Load_SZ1_true_nnn Load_SZ1_true_nnt
    Load_SZ2_false_nnn Load_SZ2_true_nnn Load_SZ4_false_nnn Load_SZ4_true_nnn Load_SZ8_true_nnn
    Load_SZ8_true_nnt Lr_AW_true_true_nn Lui_nn Mul32_M_DIVU_nnn Mul32_M_DIV_nnn Mul32_M_MUL_nnn
    Mul32_M_REMU_nnn Mul_M_DIVU_nnn Mul_M_MULHU_nnn Mul_M_MUL_nnn Op32_ALU_ADD_nnn Op32_ALU_SLL_nnn
    Op32_ALU_SRL_nnn Op32_ALU_SUB_nnn OpImm32_nnn OpImm_ALU_ADD_nnn OpImm_ALU_ADD_nnt OpImm_ALU_AND_nnn
    OpImm_ALU_OR_nnn OpImm_ALU_SLTU_nnn OpImm_ALU_SLT_nnn OpImm_ALU_XOR_nnn Op_ALU_ADD_nnn Op_ALU_AND_nnn
    Op_ALU_OR_nnn Op_ALU_SLL_nnn Op_ALU_SLTU_nnn Op_ALU_SLT_nnn Op_ALU_SRL_nnn Op_ALU_SUB_nnn Op_ALU_XOR_nnn
    Sc_AW_true_true_nnn ShiftImm32_ALU_SLL_nnn ShiftImm32_ALU_SRA_nnn ShiftImm32_ALU_SRL_nnn
    ShiftImm_ALU_SLL_nnn ShiftImm_ALU_SRA_nnn ShiftImm_ALU_SRL_nnn Store_SZ1_nnn Store_SZ1_nnt Store_SZ2_nnn
    Store_SZ4_nnn Store_SZ8_nnn
""".split())

LEAF = 10
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")


class Refusal(Exception):
    pass


def bits(w, lo, n):
    return (w >> lo) & ((1 << n) - 1)


class Ins:
    """One decoded word: Instr.v constructor, its enumeration arguments, and its operands.

    ops: list of [value, role]; role 'x' integer register, 'f' FP register, else an immediate
    field name.  wr: the integer register the instruction writes (None if none).  rs1: its rs1
    field when that is an integer base register of an I/S immediate (the lo12 partner position)."""

    def __init__(self, ctor, tags, ops, wr=None, rs1=None, lo_ix=None):
        self.ctor, self.tags, self.ops, self.wr, self.rs1, self.lo_ix = ctor, tags, ops, wr, rs1, lo_ix
        self.terms = {}  # operand index -> term text

    def notation(self):
        kinds = "".join("t" if i in self.terms else "n" for i in range(len(self.ops)))
        return "_".join([self.ctor] + self.tags) + "_" + kinds


def decode(w):
    """Decode.v's decode on one 32-bit word; None where it returns None."""
    opc, rd, f3, rs1, rs2, f7 = bits(w, 0, 7), bits(w, 7, 5), bits(w, 12, 3), bits(w, 15, 5), bits(w, 20, 5), bits(w, 25, 7)
    rm = f3
    imm_i = bits(w, 20, 12)
    imm_s = (bits(w, 25, 7) << 5) | bits(w, 7, 5)
    imm_b = (bits(w, 31, 1) << 12) | (bits(w, 7, 1) << 11) | (bits(w, 25, 6) << 5) | (bits(w, 8, 4) << 1)
    imm_u = bits(w, 12, 20)
    imm_j = (bits(w, 31, 1) << 20) | (bits(w, 12, 8) << 12) | (bits(w, 20, 1) << 11) | (bits(w, 21, 10) << 1)
    X, F = "x", "f"
    if opc == 0x37:
        return Ins("Lui", [], [[rd, X], [imm_u, "u20"]], wr=rd)
    if opc == 0x17:
        return Ins("Auipc", [], [[rd, X], [imm_u, "u20"]], wr=rd)
    if opc == 0x6F:
        return Ins("Jal", [], [[rd, X], [imm_j, "j21"]], wr=rd)
    if opc == 0x67:
        return Ins("Jalr", [], [[rd, X], [rs1, X], [imm_i, "i12"]], wr=rd) if f3 == 0 else None
    if opc == 0x63:
        c = {0: "BC_EQ", 1: "BC_NE", 4: "BC_LT", 5: "BC_GE", 6: "BC_LTU", 7: "BC_GEU"}.get(f3)
        return Ins("Branch", [c], [[rs1, X], [rs2, X], [imm_b, "b13"]]) if c else None
    if opc == 0x03:
        t = {0: ("SZ1", "true"), 1: ("SZ2", "true"), 2: ("SZ4", "true"), 3: ("SZ8", "true"),
             4: ("SZ1", "false"), 5: ("SZ2", "false"), 6: ("SZ4", "false")}.get(f3)
        return Ins("Load", list(t), [[rd, X], [rs1, X], [imm_i, "i12"]], wr=rd, rs1=rs1, lo_ix=2) if t else None
    if opc == 0x23:
        t = {0: "SZ1", 1: "SZ2", 2: "SZ4", 3: "SZ8"}.get(f3)
        return Ins("Store", [t], [[rs1, X], [rs2, X], [imm_s, "s12"]], rs1=rs1, lo_ix=2) if t else None
    if opc == 0x13:
        op = {0: "ALU_ADD", 2: "ALU_SLT", 3: "ALU_SLTU", 4: "ALU_XOR", 6: "ALU_OR", 7: "ALU_AND"}.get(f3)
        if op:
            return Ins("OpImm", [op], [[rd, X], [rs1, X], [imm_i, "i12"]], wr=rd, rs1=rs1, lo_ix=2)
        sh = bits(w, 20, 6)
        if f3 == 1:
            return Ins("ShiftImm", ["ALU_SLL"], [[rd, X], [rs1, X], [sh, "sh6"]], wr=rd) if bits(w, 26, 6) == 0 else None
        if f3 == 5:
            op = {0x00: "ALU_SRL", 0x10: "ALU_SRA"}.get(bits(w, 26, 6))
            return Ins("ShiftImm", [op], [[rd, X], [rs1, X], [sh, "sh6"]], wr=rd) if op else None
        return None
    if opc == 0x1B:
        sh5 = bits(w, 20, 5)
        if f3 == 0:
            return Ins("OpImm32", [], [[rd, X], [rs1, X], [imm_i, "i12"]], wr=rd)
        if f3 == 1:
            return Ins("ShiftImm32", ["ALU_SLL"], [[rd, X], [rs1, X], [sh5, "sh5"]], wr=rd) if f7 == 0 else None
        if f3 == 5:
            op = {0x00: "ALU_SRL", 0x20: "ALU_SRA"}.get(f7)
            return Ins("ShiftImm32", [op], [[rd, X], [rs1, X], [sh5, "sh5"]], wr=rd) if op else None
        return None
    if opc in (0x33, 0x3B):
        if opc == 0x33:
            ops = {(0x00, 0): "ALU_ADD", (0x20, 0): "ALU_SUB", (0x00, 1): "ALU_SLL", (0x00, 2): "ALU_SLT",
                   (0x00, 3): "ALU_SLTU", (0x00, 4): "ALU_XOR", (0x00, 5): "ALU_SRL", (0x20, 5): "ALU_SRA",
                   (0x00, 6): "ALU_OR", (0x00, 7): "ALU_AND"}
            mls = {0: "M_MUL", 1: "M_MULH", 2: "M_MULHSU", 3: "M_MULHU", 4: "M_DIV", 5: "M_DIVU", 6: "M_REM", 7: "M_REMU"}
            octor, mctor = "Op", "Mul"
        else:
            ops = {(0x00, 0): "ALU_ADD", (0x20, 0): "ALU_SUB", (0x00, 1): "ALU_SLL", (0x00, 5): "ALU_SRL",
                   (0x20, 5): "ALU_SRA"}
            mls = {0: "M_MUL", 4: "M_DIV", 5: "M_DIVU", 6: "M_REM", 7: "M_REMU"}
            octor, mctor = "Op32", "Mul32"
        rrr = [[rd, X], [rs1, X], [rs2, X]]
        if (f7, f3) in ops:
            return Ins(octor, [ops[(f7, f3)]], rrr, wr=rd)
        if f7 == 0x01 and f3 in mls:
            return Ins(mctor, [mls[f3]], rrr, wr=rd)
        return None
    if opc == 0x0F:
        if f3 == 0:
            ok = rd == 0 and rs1 == 0 and (bits(w, 28, 4) == 0 or bits(w, 20, 12) == 0x833)
            return Ins("Fence", [], [[bits(w, 28, 4), "fm4"], [bits(w, 24, 4), "p4"], [bits(w, 20, 4), "s4"], [rd, X], [rs1, X]]) if ok else None
        if f3 == 1:
            return Ins("FenceI", [], [[rd, X], [rs1, X], [imm_i, "i12"]]) if w == 0x0000100F else None
        return None
    if opc == 0x73:
        if f3 == 0:
            return {0x00000073: Ins("Ecall", [], []), 0x00100073: Ins("Ebreak", [], [])}.get(w)
        op = {1: "CSR_RW", 2: "CSR_RS", 3: "CSR_RC", 5: "CSR_RW", 6: "CSR_RS", 7: "CSR_RC"}.get(f3)
        if op is None:
            return None
        if f3 < 4:
            return Ins("Csr", [op], [[rd, X], [rs1, X], [bits(w, 20, 12), "csr12"]], wr=rd)
        return Ins("CsrI", [op], [[rd, X], [rs1, "uimm5"], [bits(w, 20, 12), "csr12"]], wr=rd)
    if opc == 0x2F:
        if f3 not in (2, 3):
            return None
        aw = "AW" if f3 == 2 else "AD"
        aq, rl = ("true" if bits(w, 26, 1) else "false"), ("true" if bits(w, 25, 1) else "false")
        f5 = bits(w, 27, 5)
        if f5 == 0x02:
            return Ins("Lr", [aw, aq, rl], [[rd, X], [rs1, X]], wr=rd) if rs2 == 0 else None
        if f5 == 0x03:
            return Ins("Sc", [aw, aq, rl], [[rd, X], [rs1, X], [rs2, X]], wr=rd)
        amo = {0x00: "AMO_ADD", 0x01: "AMO_SWAP", 0x04: "AMO_XOR", 0x08: "AMO_OR", 0x0C: "AMO_AND",
               0x10: "AMO_MIN", 0x14: "AMO_MAX", 0x18: "AMO_MINU", 0x1C: "AMO_MAXU"}.get(f5)
        return Ins("Amo", [amo, aw, aq, rl], [[rd, X], [rs1, X], [rs2, X]], wr=rd) if amo else None
    if opc == 0x07:
        fmt = {2: "FMT_S", 3: "FMT_D"}.get(f3)
        return Ins("FLoad", [fmt], [[rd, F], [rs1, X], [imm_i, "i12"]], rs1=rs1, lo_ix=2) if fmt else None
    if opc == 0x27:
        fmt = {2: "FMT_S", 3: "FMT_D"}.get(f3)
        return Ins("FStore", [fmt], [[rs1, X], [rs2, F], [imm_s, "s12"]], rs1=rs1, lo_ix=2) if fmt else None
    if opc in (0x43, 0x47, 0x4B, 0x4F):
        mo = {0x43: "F_MADD", 0x47: "F_MSUB", 0x4B: "F_NMSUB", 0x4F: "F_NMADD"}[opc]
        fmt = {0: "FMT_S", 1: "FMT_D"}.get(bits(w, 25, 2))
        return Ins("Fma", [mo, fmt], [[rd, F], [rs1, F], [rs2, F], [bits(w, 27, 5), F], [rm, "rm3"]]) if fmt else None
    if opc == 0x53:
        return decode_opfp(w, rd, f3, rs1, rs2, f7, rm)
    return None


def decode_opfp(w, rd, f3, rs1, rs2, f7, rm):
    X, F = "x", "f"
    cvt_int = {0: "FC_W", 1: "FC_WU", 2: "FC_L", 3: "FC_LU"}.get(rs2)
    ari = {0x00: ("F_ADD", "FMT_S"), 0x01: ("F_ADD", "FMT_D"), 0x04: ("F_SUB", "FMT_S"), 0x05: ("F_SUB", "FMT_D"),
           0x08: ("F_MUL", "FMT_S"), 0x09: ("F_MUL", "FMT_D"), 0x0C: ("F_DIV", "FMT_S"), 0x0D: ("F_DIV", "FMT_D")}
    if f7 in ari:
        return Ins("Fari", list(ari[f7]), [[rd, F], [rs1, F], [rs2, F], [rm, "rm3"]])
    if f7 in (0x2C, 0x2D):
        fmt = "FMT_S" if f7 == 0x2C else "FMT_D"
        return Ins("Fsqrt", [fmt], [[rd, F], [rs1, F], [rm, "rm3"]]) if rs2 == 0 else None
    if f7 in (0x10, 0x11):
        op = {0: "F_SGNJ", 1: "F_SGNJN", 2: "F_SGNJX"}.get(f3)
        fmt = "FMT_S" if f7 == 0x10 else "FMT_D"
        return Ins("Fsgnj", [op, fmt], [[rd, F], [rs1, F], [rs2, F]]) if op else None
    if f7 in (0x14, 0x15):
        op = {0: "F_MIN", 1: "F_MAX"}.get(f3)
        fmt = "FMT_S" if f7 == 0x14 else "FMT_D"
        return Ins("Fminmax", [op, fmt], [[rd, F], [rs1, F], [rs2, F]]) if op else None
    if f7 in (0x50, 0x51):
        op = {2: "F_EQ", 1: "F_LT", 0: "F_LE"}.get(f3)
        fmt = "FMT_S" if f7 == 0x50 else "FMT_D"
        return Ins("Fcmp", [op, fmt], [[rd, X], [rs1, F], [rs2, F]], wr=rd) if op else None
    if f7 in (0x60, 0x61):
        src = "FC_S" if f7 == 0x60 else "FC_D"
        return Ins("Fcvt", [cvt_int, src], [[rd, X], [rs1, F], [rm, "rm3"]], wr=rd) if cvt_int else None
    if f7 == 0x68:
        return Ins("Fcvt", ["FC_S", cvt_int], [[rd, F], [rs1, X], [rm, "rm3"]]) if cvt_int else None
    if f7 == 0x69:
        if cvt_int is None or (cvt_int in ("FC_W", "FC_WU") and f3 != 0):
            return None
        return Ins("Fcvt", ["FC_D", cvt_int], [[rd, F], [rs1, X], [rm, "rm3"]])
    if f7 == 0x20:
        return Ins("Fcvt", ["FC_S", "FC_D"], [[rd, F], [rs1, F], [rm, "rm3"]]) if rs2 == 1 else None
    if f7 == 0x21:
        return Ins("Fcvt", ["FC_D", "FC_S"], [[rd, F], [rs1, F], [rm, "rm3"]]) if rs2 == 0 and f3 == 0 else None
    if f7 in (0x70, 0x71):
        fmt = "FMT_S" if f7 == 0x70 else "FMT_D"
        if rs2 != 0:
            return None
        if f3 == 0:
            return Ins("Fmv", ["FMV_X_F", fmt], [[rd, X], [rs1, F]], wr=rd)
        if f3 == 1:
            return Ins("Fclass", [fmt], [[rd, X], [rs1, F]], wr=rd)
        return None
    if f7 in (0x78, 0x79):
        fmt = "FMT_S" if f7 == 0x78 else "FMT_D"
        return Ins("Fmv", ["FMV_F_X", fmt], [[rd, F], [rs1, X]]) if rs2 == 0 and f3 == 0 else None
    return None


def sx(v, n):
    return v - (1 << n) if v >> (n - 1) else v


def hi_q(d):
    return (d + 2048) // 4096  # Z division in RStep.v is floor division


def wrap(v, n):
    return v % (1 << n)


def read_code(path, start, end):
    try:
        f = open(path, "rb")
    except OSError as e:
        raise Refusal(f"cannot open image: {e.strerror}")
    with f:
        try:
            elf = ELFFile(f)
        except Exception as e:  # pyelftools raises several types on a non-ELF file
            raise Refusal(f"not an ELF file: {e}")
        if elf.header["e_machine"] != "EM_RISCV" or elf.elfclass != 64 or not elf.little_endian:
            raise Refusal("not a little-endian 64-bit RISC-V ELF file")
        for seg in elf.iter_segments():
            h = seg.header
            if h["p_type"] == "PT_LOAD" and h["p_vaddr"] <= start and end <= h["p_vaddr"] + h["p_filesz"]:
                f.seek(h["p_offset"] + start - h["p_vaddr"])
                data = f.read(end - start)
                if len(data) != end - start:
                    raise Refusal("short read from image")
                return data
    raise Refusal(f"[{start:#x}, {end:#x}) is not inside one PT_LOAD segment's file bytes")


def term_d(param, base, off):
    return f"{param} - {base}" if off == 0 else f"{param} - ({base} + {off})"


def emit(code, start, end, name, base, targets, root_indent=2):
    """Return the Definition text, or raise Refusal."""
    by_addr = {a: p for p, a in targets}
    ins, off = [], 0
    while off < len(code):
        if len(code) - off < 2:
            raise Refusal(f"offset {off}: truncated instruction")
        lo16 = int.from_bytes(code[off:off + 2], "little")
        if lo16 & 3 != 3:
            raise Refusal(f"offset {off}: compressed instruction {lo16:#06x}: no PJ notation")
        if (lo16 >> 2) & 7 == 7:
            raise Refusal(f"offset {off}: instruction longer than 32 bits: no PJ notation")
        if len(code) - off < 4:
            raise Refusal(f"offset {off}: truncated instruction")
        w = int.from_bytes(code[off:off + 4], "little")
        d = decode(w)
        if d is None:
            raise Refusal(f"offset {off}: word {w:#010x} does not decode")
        d.off, d.word = off, w
        ins.append(d)
        off += 4

    # auipc partners: the last earlier auipc that wrote rs1, with no write to rs1 between.
    live = {}  # register -> auipc Ins
    partners = {}  # id(auipc) -> [partner Ins]
    for d in ins:
        if d.lo_ix is not None and d.rs1 in live:
            d.partner = live[d.rs1]
            partners.setdefault(id(d.partner), []).append(d)
        if d.wr is not None:
            if d.ctor == "Auipc" and d.wr != 0:
                live[d.wr] = d
            else:
                live.pop(d.wr, None)

    for d in ins:
        pc = start + d.off
        if d.ctor == "Jal":
            tgt = pc + sx(d.ops[1][0], 21)
            if not (start <= tgt < end):
                p = by_addr.get(tgt)
                if p is None:
                    raise Refusal(f"offset {d.off}: jal to {tgt:#x}, which the map does not name")
                if wrap(tgt - pc, 21) != d.ops[1][0]:
                    raise Refusal(f"offset {d.off}: jimm21 check failed")
                d.terms[1] = f"(jimm21 ({term_d(p, base, d.off)}))"
        elif d.ctor == "Auipc":
            ps = partners.get(id(d))
            if not ps:
                raise Refusal(f"offset {d.off}: auipc without a partner: its address is unknown")
            q = ps[0]
            tgt = pc + sx(d.ops[1][0], 20) * 4096 + sx(q.ops[q.lo_ix][0], 12)
            p = by_addr.get(tgt)
            if p is None:
                raise Refusal(f"offset {d.off}: auipc pair (offset {q.off}) forms {tgt:#x}, which the map does not name")
            if wrap(hi_q(tgt - pc), 20) != d.ops[1][0]:
                raise Refusal(f"offset {d.off}: hi20 check failed")
            d.terms[1] = f"(hi20 ({term_d(p, base, d.off)}))"
    for d in ins:
        q = getattr(d, "partner", None)
        if q is None:
            continue
        apc = start + q.off
        tgt = apc + sx(q.ops[1][0], 20) * 4096 + sx(d.ops[d.lo_ix][0], 12)
        p = by_addr.get(tgt)
        if p is None:
            raise Refusal(f"offset {d.off}: partner of the auipc at {q.off} forms {tgt:#x}, which the map does not name")
        dd = tgt - apc
        if wrap(dd - hi_q(dd) * 4096, 12) != d.ops[d.lo_ix][0] or wrap(hi_q(dd), 20) != q.ops[1][0]:
            raise Refusal(f"offset {d.off}: lo12 check failed")
        d.terms[d.lo_ix] = f"(lo12 ({term_d(p, base, q.off)}))"

    rows = []
    for d in ins:
        nm = d.notation()
        if nm not in PJ_NOTATIONS:
            raise Refusal(f"offset {d.off}: word {d.word:#010x} is {d.ctor} {' '.join(d.tags)}: no notation PJ_{nm}")
        args = " ".join(d.terms.get(i, str(v)) for i, (v, _role) in enumerate(d.ops))
        rows.append(f"(PJ_{nm} {d.off} {args} 4")

    leaves = [rows[i:i + LEAF] for i in range(0, len(rows), LEAF)]
    offs = [ins[i].off for i in range(0, len(rows), LEAF)]
    out = []

    def put(lo, hi, depth, closers):
        root = depth == 0
        col = 2 * depth + 2
        head = " " * (root_indent if root else col) + ("" if root else "(")
        if hi - lo == 1:
            out.append(head + "PLeaf")
            leaf = leaves[lo]
            for r in leaf[:-1]:
                out.append(" " * (col + 4) + r)
            out.append(" " * (col + 4) + leaf[-1] + " nil" + ")" * len(leaf) + ("" if root else ")") + ")" * closers)
            return
        mid = lo + (hi - lo) // 2
        out.append(head + f"PNode {offs[mid]}%Z")
        put(lo, mid, depth + 1, 0)
        put(mid, hi, depth + 1, closers + (0 if root else 1))

    put(0, len(leaves), 0, 0)
    out[-1] += "."
    params = " ".join([base] + [p for p, _a in targets])
    return f"Definition {name} ({params} : Z) : RStep.ptree :=\n" + "\n".join(out) + "\n"


def parse_args(argv):
    ap = argparse.ArgumentParser(description="Write the RStep.ptree Definition of one function of a RISC-V ELF image.")
    ap.add_argument("--pin", required=True, help="the ELF image")
    ap.add_argument("--start", required=True, help="the function's first address")
    ap.add_argument("--end", required=True, help="the address after its last instruction")
    ap.add_argument("--name", required=True, help="the Definition's name")
    ap.add_argument("--base", required=True, help="the name of the base parameter (the function's address)")
    ap.add_argument("--target", action="append", default=[], metavar="NAME=ADDR",
                    help="an external address and its parameter name; the parameters follow --base in this order")
    ap.add_argument("--root-indent", type=int, default=2,
                    help="column of the root's line (default 2); every other line's column is set by its depth")
    ap.add_argument("--deny", required=True, help="file of strings that no argument and no output may hold")
    ap.add_argument("--out", required=True, help="the file to write")
    return ap.parse_args(argv)


def main(argv):
    a = parse_args(argv)
    try:
        try:
            with open(a.deny, encoding="utf-8") as f:
                deny = [s.strip() for s in f if s.strip() and not s.lstrip().startswith("#")]
        except OSError as e:
            raise Refusal(f"cannot read --deny file: {e.strerror}")
        if not deny:
            raise Refusal("the --deny file lists no string")

        def screen(text, what):
            for s in deny:
                if s in text:
                    raise Refusal(f"{what} holds a denied string (entry {deny.index(s) + 1} of the --deny file)")

        for i, s in enumerate(argv):
            screen(s, f"argument {i + 1}")
        try:
            start, end = int(a.start, 0), int(a.end, 0)
        except ValueError:
            raise Refusal("--start and --end must be integers")
        if not (0 <= start < end) or start % 2:
            raise Refusal("need 0 <= start < end, start even")
        if a.root_indent < 0:
            raise Refusal("--root-indent must be >= 0")
        for nm in [a.name, a.base]:
            if not IDENT.match(nm):
                raise Refusal(f"not an identifier: {nm!r}")
        targets, seen = [], set()
        for t in a.target:
            p, sep, v = t.partition("=")
            if not sep or not IDENT.match(p):
                raise Refusal(f"--target wants NAME=ADDR, got {t!r}")
            try:
                addr = int(v, 0)
            except ValueError:
                raise Refusal(f"--target address is not an integer: {t!r}")
            if p in seen or p in (a.base, a.name) or addr in {x for _q, x in targets}:
                raise Refusal(f"--target repeats a name or an address: {t!r}")
            seen.add(p)
            targets.append((p, addr))
        code = read_code(a.pin, start, end)
        text = emit(code, start, end, a.name, a.base, targets, a.root_indent)
        screen(text, "the output")
    except Refusal as e:
        print(f"ptree_emit: refused: {e}", file=sys.stderr)
        return REFUSE
    with open(a.out, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
