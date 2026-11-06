#!/usr/bin/env python3
"""mklisting.py -- the position-abstract listing of a target's program code.

It reads one ELF (RV64, 4-byte instructions only) and the program-code range, and writes
  - the `pinstr` table (cgif's lib/YP0b.v form: PW / PCall / PTail / PHi / PAddHi / PLdHi),
  - the symbol list (one constructor per call target outside the range, plus the call
    targets inside the range that get their own contract),
  - the hi-value table (one entry per distinct auipc result) and the object table
    (one entry per distinct address an auipc+lo12 pair builds),
  - a JSON side file with the same data for the checks.

Usage: mklisting.py IMAGE NM LO HI --out DIR [--call NAME[,NAME...]]
  LO/HI hex addresses of the program code; --call names the functions inside the range
  that are reached by a call slot (PCall) instead of being walked through.
"""
import argparse
import json
import os
import struct
import sys


def read_elf(path):
    d = open(path, "rb").read()
    assert d[:4] == b"\x7fELF" and d[4] == 2
    (_t, _m, _v, _entry, phoff, _shoff, _f, _ehs, phes, phn, *_r) = struct.unpack_from(
        "<HHIQQQIHHHHHH", d, 16)
    segs = []
    for i in range(phn):
        p_type, _fl, p_off, p_vaddr, _pa, p_filesz, p_memsz, _al = struct.unpack_from(
            "<IIQQQQQQ", d, phoff + i * phes)
        if p_type == 1:
            segs.append((p_vaddr, p_off, p_filesz, p_memsz))
    return d, segs


def rd_at(d, segs, addr, n):
    for vaddr, off, filesz, _memsz in segs:
        if vaddr <= addr and addr + n <= vaddr + filesz:
            return d[off + addr - vaddr: off + addr - vaddr + n]
    return None


def sx(v, bits):
    return v - (1 << bits) if v >> (bits - 1) else v


def decode(w):
    """Returns (kind, fields) for the instruction classes the listing names."""
    op = w & 0x7F
    rd = (w >> 7) & 0x1F
    rs1 = (w >> 15) & 0x1F
    f3 = (w >> 12) & 7
    if op == 0x17:                                  # auipc
        return ("auipc", rd, sx(w >> 12, 20))
    if op == 0x6F:                                  # jal
        imm = (((w >> 31) & 1) << 20) | (((w >> 12) & 0xFF) << 12) | \
              (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3FF) << 1)
        return ("jal", rd, sx(imm, 21))
    if op == 0x13 and f3 == 0:                      # addi
        return ("addi", rd, rs1, sx(w >> 20, 12))
    if op == 0x03:                                  # load
        return ("load", rd, rs1, sx(w >> 20, 12), f3)
    return ("plain",)


LOADS = {0: ("SZ1", "true"), 1: ("SZ2", "true"), 2: ("SZ4", "true"), 3: ("SZ8", "true"),
         4: ("SZ1", "false"), 5: ("SZ2", "false"), 6: ("SZ4", "false")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("image")
    ap.add_argument("nm")
    ap.add_argument("lo")
    ap.add_argument("hi")
    ap.add_argument("--out", required=True)
    ap.add_argument("--call", default="")
    ap.add_argument("--prefix", default="grant")
    args = ap.parse_args()
    lo, hi = int(args.lo, 16), int(args.hi, 16)
    d, segs = read_elf(args.image)
    syms = {}
    byaddr = {}
    # nm -S: addr size type name
    for line in open(args.nm):
        f = line.split()
        if len(f) == 4:
            a, t, nm_ = int(f[0], 16), f[2], f[3]
        elif len(f) == 3:
            a, t, nm_ = int(f[0], 16), f[1], f[2]
        else:
            continue
        if t in "tTwW":
            syms.setdefault(nm_, a)
            byaddr.setdefault(a, nm_)
    for line in open(args.nm):
        f = line.split()
        if len(f) == 4:
            byaddr.setdefault(int(f[0], 16), f[3])
        elif len(f) == 3:
            byaddr.setdefault(int(f[0], 16), f[2])
    callset = set(x for x in args.call.split(",") if x)

    n = (hi - lo) // 4
    words = [struct.unpack_from("<I", rd_at(d, segs, lo + 4 * i, 4))[0] for i in range(n)]

    # pass 1: hi values held per register, to pair lo12 with its auipc
    his = []           # list of absolute hi values
    hi_index = {}
    objs = []          # list of absolute object addresses
    obj_index = {}
    symlist = []       # list of (symbol name, target address)
    sym_index = {}

    def hidx(v):
        if v not in hi_index:
            hi_index[v] = len(his)
            his.append(v)
        return hi_index[v]

    def oidx(v):
        if v not in obj_index:
            obj_index[v] = len(objs)
            objs.append(v)
        return obj_index[v]

    def sidx(name, tgt):
        if name not in sym_index:
            sym_index[name] = len(symlist)
            symlist.append((name, tgt))
        return sym_index[name]

    slots = [None] * n
    held = {}          # reg -> (hi value, slot index of the auipc)
    fstarts = set(a for a in syms.values() if lo <= a < hi)
    for i, w in enumerate(words):
        pc = lo + 4 * i
        if pc in fstarts:
            held.clear()
        dec = decode(w)
        k = dec[0]
        if k == "auipc":
            _, rd, imm = dec
            val = (pc + (imm << 12)) & ((1 << 64) - 1)
            held[rd] = val
            slots[i] = ("PHi", rd, val)
            continue
        if k == "jal":
            _, rd, imm = dec
            tgt = pc + imm
            name = byaddr.get(tgt)
            if lo <= tgt < hi and (name is None or name not in callset):
                slots[i] = ("PW", w)        # a jump inside the listing
            else:
                if name is None:
                    name = "addr_%x" % tgt
                if rd == 0:
                    slots[i] = ("PTail", name, tgt)
                else:
                    slots[i] = ("PCall", name, rd, tgt)
                sidx(name, tgt)
            held.pop(rd, None)
            continue
        if k == "addi":
            _, rd, rs1, imm = dec
            if rs1 in held:
                tgt = (held[rs1] + imm) & ((1 << 64) - 1)
                slots[i] = ("PAddHi", rd, rs1, held[rs1], tgt)
                if rd != rs1:
                    held.pop(rd, None)
                else:
                    held.pop(rd, None)
                continue
            held.pop(rd, None)
            slots[i] = ("PW", w)
            continue
        if k == "load":
            _, rd, rs1, imm, f3 = dec
            if rs1 in held and f3 in LOADS:
                tgt = (held[rs1] + imm) & ((1 << 64) - 1)
                slots[i] = ("PLdHi", rd, rs1, held[rs1], tgt, f3)
                held.pop(rd, None)
                continue
            held.pop(rd, None)
            slots[i] = ("PW", w)
            continue
        # any other instruction: it may write rd, so drop what rd held
        rd = (w >> 7) & 0x1F
        op = w & 0x7F
        if op not in (0x63, 0x23):          # branches and stores write no register
            held.pop(rd, None)
        slots[i] = ("PW", w)

    # pass 2: number the hi values and objects in listing order
    out = []
    for i, s in enumerate(slots):
        if s[0] == "PW":
            out.append("PW 0x%x;" % s[1])
        elif s[0] == "PCall":
            out.append("PCall %s_%s (%d%%bv : reg);" % (args.prefix.upper()[0] + "S", s[1], s[2]))
        elif s[0] == "PTail":
            out.append("PTail %s_%s;" % (args.prefix.upper()[0] + "S", s[1]))
        elif s[0] == "PHi":
            out.append("PHi (%d%%bv : reg) %d;" % (s[1], hidx(s[2])))
        elif s[0] == "PAddHi":
            out.append("PAddHi (%d%%bv : reg) (%d%%bv : reg) %d (A_OBJ %d) 0x%x;"
                       % (s[1], s[2], hidx(s[3]), oidx(s[4]), 0))
        elif s[0] == "PLdHi":
            szs, sg = LOADS[s[5]]
            out.append("PLdHi (%d%%bv : reg) (%d%%bv : reg) %d (A_OBJ %d) 0x%x %s %s;"
                       % (s[1], s[2], hidx(s[3]), oidx(s[4]), 0, szs, sg))
    os.makedirs(args.out, exist_ok=True)
    meta = {"lo": lo, "hi": hi, "nslots": n,
            "his": his, "objs": objs,
            "syms": symlist,
            "funcs": {name: a - lo for name, a in syms.items() if lo <= a < hi}}
    json.dump(meta, open(os.path.join(args.out, "listing.json"), "w"), indent=1)
    open(os.path.join(args.out, "listing.body"), "w").write("\n".join(out) + "\n")
    print("slots %d  his %d  objs %d  syms %d" % (n, len(his), len(objs), len(symlist)))
    for nm_, a in symlist:
        print("  sym %-40s 0x%x" % (nm_, a))


if __name__ == "__main__":
    main()
