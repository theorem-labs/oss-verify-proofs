#!/usr/bin/env python3
"""heldcheck.py -- the held-map check of a mklisting.py listing (an auditor's request: each auipc pairing must be sound).

Replays mklisting.py's pass 1 over [LO, HI) of ELF and records, for every PAddHi / PLdHi slot, the auipc slot it was
paired with. A pair is SOUND only if the path auipc -> use is straight-line: no branch / jal / jalr strictly between
them, and no control-flow target (direct branch or jal target anywhere in the listing range, plus every entry of the
given jump tables) in (auipc, use]. Prints every unsound pair and a count.

usage: heldcheck.py ELF NM LO HI [--table ADDR:N:BASE ...]   (BASE: 'abs' or a hex address the entries are added to)
  It decodes through the listing generator's own decoder (../listing-A/mklisting.py of this directory tree).
"""
import argparse
import os
import struct
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "listing-A"))
import mklisting as M  # noqa: E402

ap = argparse.ArgumentParser()
ap.add_argument("elf"); ap.add_argument("nm"); ap.add_argument("lo"); ap.add_argument("hi")
ap.add_argument("--table", action="append", default=[])
a = ap.parse_args()
lo, hi = int(a.lo, 16), int(a.hi, 16)
d, segs = M.read_elf(a.elf)
n = (hi - lo) // 4
words = [struct.unpack("<I", M.rd_at(d, segs, lo + 4 * i, 4))[0] for i in range(n)]
syms = {}
for line in open(a.nm):
    f = line.split()
    if len(f) >= 4 and f[2] in ("t", "T"):
        syms[f[3]] = int(f[0], 16)
fstarts = set(v for v in syms.values() if lo <= v < hi)


def sx(v, b):
    return v - (1 << b) if (v >> (b - 1)) & 1 else v


targets = set()
cf = [False] * n
for i, w in enumerate(words):
    pc = lo + 4 * i
    op = w & 0x7F
    if op == 0x63:
        imm = sx(((w >> 31) & 1) << 12 | ((w >> 7) & 1) << 11 | ((w >> 25) & 0x3F) << 5 | ((w >> 8) & 0xF) << 1, 13)
        targets.add(pc + imm); cf[i] = True
    elif op == 0x6F:
        imm = sx(((w >> 31) & 1) << 20 | ((w >> 12) & 0xFF) << 12 | ((w >> 20) & 1) << 11 | ((w >> 21) & 0x3FF) << 1, 21)
        targets.add(pc + imm); cf[i] = True
    elif op == 0x67:
        cf[i] = True
for t in a.table:
    addr, cnt, base = t.split(":")
    addr, cnt = int(addr, 16), int(cnt)
    for k in range(cnt):
        e = struct.unpack("<i", M.rd_at(d, segs, addr + 4 * k, 4))[0]
        targets.add(e if base == "abs" else (int(base, 16) + e) & ((1 << 64) - 1))

held = {}
pairs = []
for i, w in enumerate(words):
    pc = lo + 4 * i
    if pc in fstarts:
        held.clear()
    dec = M.decode(w)
    k = dec[0]
    if k == "auipc":
        held[dec[1]] = i
        continue
    if k == "jal":
        held.pop(dec[1], None)
        continue
    if k in ("addi", "load"):
        rd, rs1 = dec[1], dec[2]
        if rs1 in held and (k == "addi" or dec[4] in M.LOADS):
            pairs.append((held[rs1], i, k))
        held.pop(rd, None)
        continue
    rd = (w >> 7) & 0x1F
    if (w & 0x7F) not in (0x63, 0x23):
        held.pop(rd, None)

bad = []
for ia, iu, k in pairs:
    why = []
    if any(cf[j] for j in range(ia + 1, iu)):
        why.append("control flow between")
    tg = [t for t in targets if lo + 4 * ia < t <= lo + 4 * iu]
    if tg:
        why.append("target(s) %s inside" % ",".join(hex(t) for t in sorted(tg)))
    if why:
        bad.append((ia, iu, k, why))
for ia, iu, k, why in bad:
    print("UNSOUND %s slot %d pc %#x <- auipc slot %d pc %#x: %s" % (k, iu, lo + 4 * iu, ia, lo + 4 * ia, "; ".join(why)))
print("pairs %d, unsound %d, control-flow targets %d" % (len(pairs), len(bad), len(targets)))
