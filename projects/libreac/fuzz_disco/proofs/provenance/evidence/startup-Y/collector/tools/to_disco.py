#!/usr/bin/env python3
"""to_disco.py -- turns the collector's donor-namespace outputs into fuzz_disco's lib/Reusable files (S6b):
module path cgif_file_fuzzer.lib -> libreac.fuzz_disco.lib.Reusable, plus one Modified line saying how the file was
made. The donor's licence lines and its own Modified line stay (these files are the donor's text with generated data).

usage: to_disco.py SRC OUT NOTE
"""
import sys

src, out, note = sys.argv[1], sys.argv[2], sys.argv[3]
CGM = "OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib"
DIM = "OssFuzzTheorems.Proofs.libreac.fuzz_disco.lib.Reusable"
t = open(src).read()
assert CGM in t
t = t.replace(CGM + ".", DIM + ".").replace(CGM + " ", DIM + " ")
assert "cgif_file_fuzzer.lib" not in t, "unrewritten module path"
lines = t.split("\n")
k = 0
while k < len(lines) and lines[k].startswith("(*"):
    k += 1
lines = lines[:k] + ["(* Modified by Theorem Labs, 2026-10: %s *)" % note] + lines[k:]
open(out, "w").write("\n".join(lines))
print("wrote", out)
