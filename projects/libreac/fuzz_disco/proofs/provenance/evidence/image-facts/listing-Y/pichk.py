#!/usr/bin/env python3
"""pichk.py -- re-checks a mklisting.py output (listing.json + listing.body) against the ELF, slot by slot, the way
PaTable.v's pi_slot_check does (pc = lo + 4k; PW: word; PCall/PTail: jal target = sigma; PHi: auipc value = hi[j];
PAddHi/PLdHi: hi[j] + imm12 = obj[i] + off). Prints the first failing slots.

usage: pichk.py GEN ELF
  It reads the ELF through the listing generator's own reader (../listing-A/mklisting.py of this directory tree).
"""
import json
import os
import struct
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "listing-A"))
import mklisting as M  # noqa: E402

gen, elf = sys.argv[1], sys.argv[2]
m = json.load(open(gen + "/listing.json"))
body = [s.strip() for s in open(gen + "/listing.body").read().split(";") if s.strip()]
d, segs = M.read_elf(elf)
sigma = {n: a for n, a in m["syms"]}
objs, his, lo = m["objs"], m["his"], m["lo"]


def sx(v, b):
    return v - (1 << b) if v >> (b - 1) else v


bad = 0
for k, s in enumerate(body):
    pc = lo + 4 * k
    w = struct.unpack("<I", M.rd_at(d, segs, pc, 4))[0]
    f = s.replace("(", " ").replace(")", " ").replace("%bv", "").replace(":", " ").split()
    op = f[0]
    ok = True
    why = ""
    if op == "PW":
        ok = int(f[1], 16) == w
    elif op in ("PCall", "PTail"):
        imm = sx(((w >> 31) & 1) << 20 | ((w >> 12) & 0xff) << 12 | ((w >> 20) & 1) << 11 | ((w >> 21) & 0x3ff) << 1, 21)
        name = f[1][3:]
        ok = (w & 0x7f) == 0x6f and pc + imm == sigma.get(name)
        why = "jal->%x sigma %s=%s" % (pc + imm, name, hex(sigma.get(name, -1)))
    elif op == "PHi":
        j = int(f[-1])
        val = (pc + sx(w & 0xfffff000, 32)) & ((1 << 64) - 1)
        ok = (w & 0x7f) == 0x17 and val == his[j]
        why = "auipc %x vs hi[%d]=%x" % (val, j, his[j])
    elif op in ("PAddHi", "PLdHi"):
        j = int(f[5])
        i = int(f[7])
        off = int(f[8], 16)
        imm = sx(w >> 20, 12)
        ok = his[j] + imm == objs[i] + off
        why = "hi[%d]=%x + %d vs obj[%d]=%x + %d" % (j, his[j], imm, i, objs[i], off)
    if not ok:
        bad += 1
        if bad <= 12:
            print("slot %d pc %x: %s  word %08x  %s" % (k, pc, s, w, why))
print("bad slots:", bad, "of", len(body))
