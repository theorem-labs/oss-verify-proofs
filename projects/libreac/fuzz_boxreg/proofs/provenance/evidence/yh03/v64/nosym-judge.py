#!/usr/bin/env python3
"""Judge the D cells of a YH03.v that yh03check reports NOSYM, against the unit's pinned image.

Usage, from the repository root:  nosym-judge.py SIDE YH03.v PINNED TWIN CHECK_ROWS REF
  SIDE        plain or ubsan; PINNED the pinned (stripped) binary of that build; TWIN its unstripped twin (symbols
              only: unit identity, the 4 PT_LOADs equal, is checked by yh03check); CHECK_ROWS yh03check's stdout on
              YH03.v; REF the commit whose .v files are searched for readers.
Bytes are read from PINNED through its PT_LOAD headers. Each NOSYM cell is judged by the rule its name gives:
  const_double_<X>   the 8 bytes at the value are the IEEE double X (`_` stands for `.` between digits, `_` before
                     an exponent's digits for `-`; a name of several doubles is judged on the first one)
  const_u64_0x<H>, const_HIGHS_0x<H>, const_ONES_0x<H>   the 8 bytes are the little-endian u64 H
  const_u64_<other>  no number in the name: judged by the code, TRUE only when an instruction pair of .text forms
                     the value (auipc + ld/fld/addi/lw)
  debruijn32         the 32 bytes are a 32-entry de Bruijn bit-position table (for the multiplier 0x077cb531, or
                     musl's 0x076be629): table[(2^k * m mod 2^32) >> 27] = k for every k < 32
  size_classes       the value is __malloc_size_classes
  jt_<fn>_<k>, jt_<fn>  the value is a .rodata address that an auipc + addi pair inside function <fn> forms
  got_<X>            the 8 bytes (a .got slot) are the address of one of X, __X, _X. An undefined weak symbol is 0,
                     so a slot holding 0 is TRUE by its bytes only; the functions that address the slot are listed
  <p>_<X>            (no rule above, and the image has a harness object oft_<X>, any one `_` of X standing for
                     `.`) that object is at the value. Such a cell is printed as src0_D_<p>_<X>: <p> is the harness
                     prefix of the cell names in YH03.v (the line number in YH03.v names the cell)
  atexit_<X>, stderr_buf, stdout_buf   the local symbol <X> / buf of atexit.c / stderr.c / stdout.c is at the value;
                     for the bufs also the FILE's buf field (offset 88) is the value + 8 (musl: .buf = buf+UNGET)
"Formed in .text by F": an auipc in F and a later addi / load / fld on its register, at most 32 bytes on and with
the register not written in between by a 4-byte instruction, give the value (corroboration, not a rule, except as
stated above).
Readers: `git grep -n -w <cell> REF` over the unit's .v files except the two YH03.v.
Prints one TSV row per cell: YH03.v line, cell, value, measured, verdict (TRUE / FALSE), why, readers.
"""
import re
import struct
import subprocess
import sys

from elftools.elf.elffile import ELFFile

UNIT = "proofs/libreac/fuzz_boxreg"
DEBRUIJN_MULTIPLIERS = (0x077CB531, 0x076BE629)


def load(path):
    f = open(path, "rb")
    return f, ELFFile(f)


def reader(f, elf):
    segs = [(s["p_vaddr"], s["p_filesz"], s["p_offset"]) for s in elf.iter_segments() if s["p_type"] == "PT_LOAD"]

    def rd(a, n):
        for va, sz, off in segs:
            if va <= a and a + n <= va + sz:
                f.seek(off + a - va)
                return f.read(n)
        return None
    return rd


def section_of(elf, a):
    for s in elf.iter_sections():
        if s["sh_addr"] <= a < s["sh_addr"] + s["sh_size"] and s["sh_addr"]:
            return s.name
    return "(no section)"


def symbols(elf):
    out, cur = [], None
    for s in elf.get_section_by_name(".symtab").iter_symbols():
        if s["st_info"]["type"] == "STT_FILE":
            cur = s.name
            continue
        if s.name:
            out.append((s.name, s["st_value"], s["st_size"], s["st_info"]["type"], s["st_info"]["bind"],
                        s["st_shndx"], cur if s["st_info"]["bind"] == "STB_LOCAL" else None))
    return out


def sext(v, bits):
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def formed(rd, lo, hi):
    """(pc, addr, kind) of each auipc + later (addi | load | fld) on its register in [lo, hi), at most 32 bytes on,
    the register not written in between by a 4-byte instruction: a linear sweep, RVC aware."""
    out, pc, regs = [], lo, {}
    while pc < hi:
        h = rd(pc, 2)
        if h is None:
            break
        if h[0] & 3 != 3:
            pc += 2
            continue
        i = struct.unpack("<I", rd(pc, 4))[0]
        op, rdreg, f3, rs1 = i & 0x7F, (i >> 7) & 31, (i >> 12) & 7, (i >> 15) & 31
        if op == 0x17:
            regs[rdreg] = (pc, sext(i & 0xFFFFF000, 32))
        else:
            if rs1 in regs and pc - regs[rs1][0] <= 32 and ((op == 0x13 and f3 == 0) or op == 0x03 or (op == 0x07 and f3 in (2, 3))):
                kind = {0x13: "addi", 0x03: "load", 0x07: "fld"}[op]
                out.append((regs[rs1][0], regs[rs1][0] + regs[rs1][1] + sext(i >> 20, 12), kind))
            if op not in (0x23, 0x27, 0x63, 0x0F, 0x73):
                regs.pop(rdreg, None)
        pc += 4
    return out


def number(tok):
    """const_double name token -> float, e.g. 0x1p28, 1_0, 0_5, 0x1p_969."""
    if tok.startswith("0x"):
        return float.fromhex(re.sub(r"p_(\d)", r"p-\1", tok))
    return float(tok.replace("_", "."))


def readers(ref, cell):
    out = subprocess.run(["git", "grep", "-n", "-w", "-e", cell, ref, "--", f"{UNIT}/*.v", f":!{UNIT}/lib/Reusable/YH03.v",
                          f":!{UNIT}/lib/U/Reusable/YH03.v"], capture_output=True, text=True).stdout
    return [l.split(":")[1] + ":" + l.split(":")[2] for l in out.splitlines() if l.strip()]


def main():
    side, yh03, pinned, twin, rows, ref = sys.argv[1:7]
    pf, pelf = load(pinned)
    rd = reader(pf, pelf)
    tf, telf = load(twin)
    syms = symbols(telf)
    by_name = {}
    for s in syms:
        by_name.setdefault(s[0], []).append(s)
    def harness(name):
        """The harness objects oft_<X> for a cell <p>_<X> (any one `_` of X may stand for `.`)."""
        x = name.split("_", 1)[1]
        alts = {"oft_" + x} | {"oft_" + x[:k] + "." + x[k + 1:] for k in range(len(x)) if x[k] == "_"}
        return [s for n in sorted(alts) for s in by_name.get(n, [])]

    text = telf.get_section_by_name(".text")
    all_formed = formed(rd, text["sh_addr"], text["sh_addr"] + text["sh_size"])
    formed_at = {}
    for pc, a, k in all_formed:
        formed_at.setdefault(a, []).append((pc, k))

    def fn_of(pc):
        best = None
        for n, v, z, t, b, sh, fl in syms:
            if t == "STT_FUNC" and v <= pc < v + max(z, 1):
                best = n
        return best

    vals = {m.group(1): int(m.group(2), 0) for m in re.finditer(r"Definition src0_(D_\w+) : Z := (0x[0-9a-fA-F]+|\d+)\.", open(yh03).read())}
    cells = [l.split("\t")[1] for l in open(rows) if len(l.split("\t")) > 2 and l.split("\t")[2] == "NOSYM"]
    lineno = {}
    for k, l in enumerate(open(yh03).read().split("\n"), 1):
        for m in re.finditer(r"Definition src0_(D_\w+) :", l):
            lineno[m.group(1)] = k
    print("\t".join(["line", "cell", "value", "measured", "verdict", "why", "readers"]))
    for c in cells:
        v = vals[c]
        name = c[2:]
        code = sorted({fn_of(pc) or "?" for pc, k in formed_at.get(v, [])})
        coderef = ("formed in .text by " + ", ".join(code)) if code else "formed by no auipc pair of .text"
        meas, verdict, why, shown = "", None, "", c
        if name.startswith("const_double_"):
            b = rd(v, 8)
            got = struct.unpack("<d", b)[0]
            want = number(name[len("const_double_"):].split("_0x")[0] if "_0x" in name[len("const_double_"):] else name[len("const_double_"):])
            meas = f"{b.hex(' ')} = {got!r}; {coderef}"
            verdict = got == want
            why = f"wants the double {want!r}"
        elif re.match(r"const_(u64|HIGHS|ONES)_0x[0-9a-fA-F]{16}$", name):
            b = rd(v, 8)
            want = int(name.split("_0x")[1], 16)
            got = struct.unpack("<Q", b)[0]
            meas = f"{b.hex(' ')} = 0x{got:016x}; {coderef}"
            verdict = got == want
            why = f"wants the u64 0x{want:016x}"
        elif name.startswith("const_u64_"):
            b = rd(v, 8)
            meas = f"{b.hex(' ')}; {coderef}"
            verdict = bool(code)
            why = "no number in the name: TRUE only when code forms the value"
        elif name == "debruijn32":
            b = rd(v, 32)
            ms = [m for m in DEBRUIJN_MULTIPLIERS if all(b[((1 << k) * m & 0xFFFFFFFF) >> 27] == k for k in range(32))]
            meas = f"{b.hex(' ')}; " + (f"the de Bruijn table of 0x{ms[0]:08x}" if ms else "no de Bruijn table") + f"; {coderef}"
            verdict = bool(ms)
            why = "wants a 32-entry de Bruijn bit-position table"
        elif name == "size_classes":
            s = by_name.get("__malloc_size_classes", [])
            meas = ", ".join(f"__malloc_size_classes at 0x{x[1]:x} size {x[2]}" for x in s)
            verdict = any(x[1] == v for x in s)
            why = "wants __malloc_size_classes"
        elif name.startswith("jt_"):
            m = re.match(r"jt_(.+?)(?:_(\d+))?$", name)
            fn = m.group(1)
            f = [x for x in by_name.get(fn, []) if x[3] == "STT_FUNC"]
            tables = sorted({a for x in f for pc, a, k in formed(rd, x[1], x[1] + x[2]) if k == "addi" and section_of(telf, a) == ".rodata"})
            meas = f"value in {section_of(telf, v)}; .rodata addresses {fn} forms by auipc + addi: " + (", ".join(f"0x{a:x}" for a in tables) or "none")
            verdict = v in tables
            why = f"wants a jump table that {fn} forms"
        elif name.startswith("got_"):
            x = name[4:]
            cand = [s for n in (x, "__" + x, "_" + x) for s in by_name.get(n, [])]
            want = sorted({s[1] for s in cand})
            b = rd(v, 8)
            got = struct.unpack("<Q", b)[0] if b else None
            slot = section_of(telf, v)
            meas = f"{slot} slot holds 0x{got:x}; " + ", ".join(f"{s[0]} = 0x{s[1]:x} ({s[4][4:].lower()}{', undefined' if s[5] == 'SHN_UNDEF' else ''})" for s in cand)
            hit = sorted({s[0] for s in cand if s[1] == got})
            meas += f"; {coderef}"
            verdict = slot == ".got" and bool(hit)
            why = "wants a .got slot holding the address of " + "/".join(sorted({s[0] for s in cand}) or [x]) + \
                (f"; it holds {'/'.join(hit)}" if hit else "") + ("; 0 = undefined weak, TRUE by its bytes only" if hit and got == 0 else "")
        elif name.startswith("atexit_") or name in ("stderr_buf", "stdout_buf"):
            src, local = (("atexit.c", name[7:]) if name.startswith("atexit_") else (name.split("_")[0] + ".c", "buf"))
            cand = [s for s in by_name.get(local, []) if s[6] == src]
            meas = ", ".join(f"{src} {local} at 0x{s[1]:x} size {s[2]}" for s in cand)
            ok = any(s[1] == v for s in cand)
            if local == "buf":
                fs = [s for s in by_name.get("__" + name.split("_")[0] + "_FILE", [])]
                w = struct.unpack("<Q", rd(fs[0][1] + 88, 8))[0] if fs else None
                meas += f"; __{name.split('_')[0]}_FILE.buf = 0x{w:x}" if w is not None else "; no FILE symbol"
                ok = ok and w == v + 8
            verdict = ok
            why = f"wants {src}'s {local}" + (" and FILE.buf = value + 8" if local == "buf" else "")
        elif re.match(r"[a-z]+_.", name) and harness(name):
            p_, x = name.split("_", 1)
            cand = harness(name)
            inside = [f"{n}+0x{v - sv:x}" for n, sv, z, t, bnd, sh, fl in syms if t == "STT_OBJECT" and sv <= v < sv + z]
            meas = ", ".join(f"{s[0]} at 0x{s[1]:x} size {s[2]}" for s in cand) + "; the value is in " + (", ".join(inside) or "no object")
            verdict = any(s[1] == v for s in cand)
            why = f"wants the harness object {cand[0][0]}"
            shown = f"D_<p>_{x}"
        else:
            meas, verdict, why = "no rule", None, "not judged"
        rds = readers(ref, "src0_" + c)
        print("\t".join([str(lineno[c]), f"src0_{shown}", f"0x{v:x}", meas, {True: "TRUE", False: "FALSE", None: "NOT JUDGED"}[verdict], why,
                         "; ".join(rds) if rds else "0"]))


if __name__ == "__main__":
    main()
