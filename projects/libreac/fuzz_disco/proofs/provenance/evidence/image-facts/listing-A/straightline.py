#!/usr/bin/env python3
"""straightline.py -- check that every auipc pairing of mklisting.py is on one straight-line path.

For every PLdHi / PAddHi slot the generator makes (same pairing rule as mklisting.py pass 1),
report it when
  (a) an instruction strictly between the auipc and the use is a branch, jal or jalr, or
  (b) some control transfer can land in (auipc, use]: a branch / jal target in the image's
      executable segments, a jump-table entry (label-minus-base int32 tables reached from the
      listing's own objects), or an 8-byte data word that points into the listing range.
Usage: straightline.py IMAGE NM LO HI [--json OUT]
Exit 1 when any slot is reported.
"""
import argparse
import json
import struct
import sys

sys.path.insert(0, __import__("os").path.dirname(__file__))
from mklisting import read_elf, rd_at, sx, decode, LOADS  # noqa: E402


def btarget(w, pc):
    op = w & 0x7F
    if op == 0x63:
        imm = (((w >> 31) & 1) << 12) | (((w >> 7) & 1) << 11) | \
              (((w >> 25) & 0x3F) << 5) | (((w >> 8) & 0xF) << 1)
        return pc + sx(imm, 13)
    if op == 0x6F:
        return pc + decode(w)[2]
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("image")
    ap.add_argument("nm")
    ap.add_argument("lo")
    ap.add_argument("hi")
    ap.add_argument("--json")
    a = ap.parse_args()
    lo, hi = int(a.lo, 16), int(a.hi, 16)
    d, segs = read_elf(a.image)
    syms = {}
    for line in open(a.nm):
        f = line.split()
        if len(f) == 4 and f[2] in "tTwW":
            syms.setdefault(f[3], int(f[0], 16))
        elif len(f) == 3 and f[1] in "tTwW":
            syms.setdefault(f[2], int(f[0], 16))
    fstarts = set(v for v in syms.values() if lo <= v < hi)
    n = (hi - lo) // 4
    words = [struct.unpack_from("<I", rd_at(d, segs, lo + 4 * i, 4))[0] for i in range(n)]

    # pairings, exactly as mklisting.py pass 1, with the auipc slot recorded
    held = {}
    pairs = []
    for i, w in enumerate(words):
        pc = lo + 4 * i
        if pc in fstarts:
            held.clear()
        dec = decode(w)
        k = dec[0]
        if k == "auipc":
            held[dec[1]] = ((pc + (dec[2] << 12)) & ((1 << 64) - 1), i)
            continue
        if k == "jal":
            held.pop(dec[1], None)
            continue
        if k == "addi":
            _, rd, rs1, imm = dec
            if rs1 in held:
                pairs.append((held[rs1][1], i, "PAddHi", (held[rs1][0] + imm) & ((1 << 64) - 1)))
            held.pop(rd, None)
            continue
        if k == "load":
            _, rd, rs1, imm, f3 = dec
            if rs1 in held and f3 in LOADS:
                pairs.append((held[rs1][1], i, "PLdHi", (held[rs1][0] + imm) & ((1 << 64) - 1)))
            held.pop(rd, None)
            continue
        op = w & 0x7F
        if op not in (0x63, 0x23):
            held.pop((w >> 7) & 0x1F, None)

    # every control-transfer target into [lo, hi)
    targets = {}
    _raw, phs = d, []
    phoff = struct.unpack_from("<Q", d, 0x20)[0]
    phes, phn = struct.unpack_from("<HH", d, 0x36)
    for j in range(phn):
        t, fl, off, va, _pa, fs, ms, _al = struct.unpack_from("<IIQQQQQQ", d, phoff + j * phes)
        if t == 1:
            phs.append((va, off, fs, fl))
    for va, off, fs, fl in phs:
        if not fl & 1:
            continue
        for k in range(0, fs - 3, 2):          # 2-byte steps: the rest of the image may use RVC
            w = struct.unpack_from("<I", d, off + k)[0]
            if w & 3 != 3:
                continue
            t = btarget(w, va + k)
            if t is not None and lo <= t < hi:
                targets.setdefault(t, set()).add("branch/jal@0x%x" % (va + k))
    # jump tables: int32 label-minus-base entries at the listing's own PAddHi objects
    for (_ai, ui, kind, obj) in pairs:
        if kind != "PAddHi":
            continue
        fn_lo = max([s for s in fstarts if s <= lo + 4 * ui], default=lo)
        fn_hi = min([s for s in fstarts if s > lo + 4 * ui], default=hi)
        e = 0
        while True:
            b = rd_at(d, [(va, off, fs, 0) for va, off, fs, fl in phs], obj + 4 * e, 4)
            if b is None:
                break
            t = obj + struct.unpack_from("<i", b)[0]
            if not (fn_lo <= t < fn_hi and t % 4 == 0):
                break
            targets.setdefault(t, set()).add("jumptable@0x%x[%d]" % (obj, e))
            e += 1
    # 8-byte data words pointing into the listing (function pointers, absolute tables)
    for va, off, fs, fl in phs:
        if fl & 1:
            continue
        for k in range(0, fs - 7, 8):
            v = struct.unpack_from("<Q", d, off + k)[0]
            if lo <= v < hi:
                targets.setdefault(v, set()).add("dataptr@0x%x" % (va + k))

    bad = []
    for (ai, ui, kind, obj) in pairs:
        why = []
        for j in range(ai + 1, ui):
            w = words[j]
            if w & 0x7F in (0x63, 0x6F, 0x67):
                why.append("ctl@0x%x(0x%08x)" % (lo + 4 * j, w))
        for j in range(ai + 1, ui + 1):
            pc = lo + 4 * j
            if pc in targets:
                why.append("target 0x%x <- %s" % (pc, ",".join(sorted(targets[pc]))))
        if why:
            bad.append({"auipc": hex(lo + 4 * ai), "use": hex(lo + 4 * ui), "slot": ui,
                        "kind": kind, "obj": hex(obj), "why": why})
    print("pairings %d, jump targets into range %d, reported %d" % (len(pairs), len(targets), len(bad)))
    for b in bad:
        print("  slot %d %s auipc %s use %s obj %s: %s" % (b["slot"], b["kind"], b["auipc"], b["use"],
                                                         b["obj"], "; ".join(b["why"])))
    if a.json:
        json.dump({"pairs": len(pairs), "bad": bad}, open(a.json, "w"), indent=1)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
