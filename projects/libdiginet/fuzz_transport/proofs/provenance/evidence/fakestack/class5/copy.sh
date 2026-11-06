#!/bin/sh
# Copy image-free donor modules into this unit with their module paths only (class1/run.sh's COPY step, with the donor
# and its ref as arguments): the files class 5 (FCiface.v) and class 4 / FCiface.v (YF0v.v) Require that the image-A core
# lacks.
#   copy.sh WT HUB ELF SRC REF FILE...
#     WT    this unit's worktree (files are written under proofs/libdiginet/fuzz_transport/lib/)
#     HUB   the git hub holding REF
#     ELF   the target image (unstripped twin) whose address range a copied file must not name
#     SRC   the donor P/H (e.g. plugin-hostd/fuzz_command)
#     REF   the donor commit (layout proofs/<P>/<H>/lib)
#     FILE  paths under the donor's lib/ (e.g. Reusable/FCiface.v)
# Image numerals: every numeral >= 0x10000 (hex or decimal) of a FILE is listed; one that lies in the image's span (from
# the lowest PT_LOAD start to the highest PT_LOAD end of ELF) refuses the file (nothing written, exit code 1); one above
# that span is not an address of the image (e.g. an ASan shadow-layout constant) and is listed as such. The donor's
# leading comment block is kept byte for byte, one notice line is added before the first From / Require line, and
# OssFuzzTheorems.Proofs.<SRC>.lib becomes OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib.
set -eu
WT=$1 HUB=$2 ELF=$3 SRC=$4 REF=$5; shift 5
rc=0
for f in "$@"; do
  dst="$WT/proofs/libdiginet/fuzz_transport/lib/$f"
  mkdir -p "$(dirname "$dst")"
  git -C "$HUB" show "$REF:proofs/$SRC/lib/$f" | python3 -c '
import re, sys
from elftools.elf.elffile import ELFFile
dst, src, ref, elf, f, blob = sys.argv[1:]
text = sys.stdin.read()
loads = [s for s in ELFFile(open(elf, "rb")).iter_segments() if s["p_type"] == "PT_LOAD"]
lo, hi = min(s["p_vaddr"] for s in loads), max(s["p_vaddr"] + s["p_memsz"] for s in loads)
bad = []
for k, l in enumerate(text.split("\n"), 1):
    for t in re.findall(r"\b(0x[0-9a-fA-F]+|[0-9]+)\b", l):
        v = int(t, 0) if t.startswith("0x") else int(t)
        if v >= 0x10000:
            inside = lo <= v < hi
            print("copy %s:%d %s = 0x%x: %s" % (f, k, t, v, "IN the image span [0x%x, 0x%x)" % (lo, hi) if inside
                                               else "above the image span [0x%x, 0x%x), not an image address" % (lo, hi)))
            bad += [t] if inside else []
if bad:
    print("copy %s: %d image numerals, not copied" % (f, len(bad))); sys.exit(1)
print("copy %s: image-free (no numeral in [0x%x, 0x%x)); blob %s" % (f, lo, hi, blob))
d = text.split("\n")
hd = next(k for k, l in enumerate(d) if l.startswith(("From ", "Require ")))
old = "OssFuzzTheorems.Proofs.%s.lib" % src.replace("-", "_").replace("/", ".")
body = [l.replace(old, "OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib") for l in d[hd:]]
note = ("(* Modified by Theorem Labs, 2026-10: copied from %s at %s for libdiginet/fuzz_transport by this unit\x27s "
        "provenance/evidence/class5/copy.sh (image-free: module paths only). *)" % (src, ref))
open(dst, "w").write("\n".join(d[:hd] + [note] + body))
print("%s: copied, header %d lines kept, %d module paths renamed" % (f, hd, sum(l.count(old) for l in d[hd:])))
' "$dst" "$SRC" "$REF" "$ELF" "$f" "$(git -C "$HUB" rev-parse "$REF:proofs/$SRC/lib/$f" | cut -c1-12)" || rc=1
done
exit $rc
