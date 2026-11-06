#!/usr/bin/env python3
"""repin.py -- puts given addresses at given object numbers in a mklisting.py output (listing.json + listing.body),
renumbering the body's (A_OBJ n) consistently. For each INDEX=ADDR: if ADDR is already an object, the two numbers
swap; if not, ADDR is appended and then swapped in (the object that held INDEX moves to ADDR's old number).
(Written because mklisting.py --pin, 19:5xZ version, swaps the table but leaves the body's numbers stale.)

usage: repin.py SRC DST INDEX=ADDR[,...]
"""
import json
import os
import re
import sys

src, dst, spec = sys.argv[1], sys.argv[2], sys.argv[3]
m = json.load(open(os.path.join(src, "listing.json")))
body = open(os.path.join(src, "listing.body")).read()
objs = list(m["objs"])
perm = list(range(len(objs)))            # perm[old] = new
pos = {a: i for i, a in enumerate(objs)}  # address -> current number
for part in spec.split(","):
    k, v = part.split("=")
    idx, addr = int(k, 0), int(v, 16)
    while len(objs) <= idx:
        objs.append(None)
    if addr not in pos:
        objs.append(addr)
        pos[addr] = len(objs) - 1
    p = pos[addr]
    if p == idx:
        continue
    a_idx = objs[idx]
    objs[idx], objs[p] = addr, a_idx
    pos[addr] = idx
    if a_idx is not None:
        pos[a_idx] = p
    for o in range(len(perm)):
        if perm[o] == idx:
            perm[o] = p
        elif perm[o] == p:
            perm[o] = idx
assert None not in objs
body = re.sub(r"\(A_OBJ (\d+)\)", lambda mm: "(A_OBJ %d)" % perm[int(mm.group(1))], body)
m["objs"] = objs
os.makedirs(dst, exist_ok=True)
json.dump(m, open(os.path.join(dst, "listing.json"), "w"))
open(os.path.join(dst, "listing.body"), "w").write(body)
print("objs %d; pinned %s" % (len(objs), spec))
