# provenance/evidence/pack-checks: the checks of the fuzz_uci ASan pack before its release check

This record covers the tree that this slice's commit is added to (its parent commit is named in `checker.txt`). Every
file named below is in this directory.

## 1. Evidence index (provenance/evidence/MANIFEST)

- `checker.txt`: evidence_manifest_check.py (sha256 in the file) on the parent commit: every file named, every naming
  line's sha256 equal, rc 0.
- `sha256sum-c.txt`: `sha256sum -c` of field 3 of every MANIFEST line, run from the evidence directory of the parent
  commit's tree: rc 0, every line OK.
- Planted controls, each on a scratch copy of the same tree:
  - `control-checker-line.txt`: one MANIFEST line deleted; the checker gives rc 1 and names the file.
  - `control-checker-sha.txt`: one sha256 field zeroed; the checker gives rc 1 and names both hashes.
  - `control-sha256.txt`: one byte appended to one file; `sha256sum -c` gives rc 1 and names the file.
- The index is written only by mk_top_manifest.py a0ba0eb66d66 (commit 1d2d6eab3320,
  tools/mk_top_manifest/a0ba0eb66d66/mk_top_manifest.py), run unmodified at every merge; no MANIFEST line is written by
  hand.

## 2. Plain and UBSan files equal the merged plain PR

The parent commit merges the plain / UBSan PR's merge commit e10f488c53fc, whose fuzz_uci files are the tree that PR's
release check passed (4617ea9f0b7b). Against e10f488c53fc nothing outside proofs/reac-repacer/fuzz_uci/ differs. In the
unit, the only changed file outside lib/A, lib/B, lib/AZ, provenance/ and the four ASan statement directories is
lib/Theorems.v (the four new entries); the other differences are 131 added files and no deleted file.

## 3. Build and assumptions

- The lib and the seven statement directories of the parent commit are byte-identical to those of 4cf8a03f103;
  theories/ and toolchain/ are unchanged, and under projects/reac-repacer/ only README.md files differ.
- Build of 4cf8a03f103 (cb, dune cache allowed): rc 0, wall 2540 s, 15 targets compiled, 2187 restored from the
  cache, 0 failed; the four binaries are the pins (4 PINNED, 0 MISMATCH, 0 MISSING).
- Print Assumptions of the seven lib/Theorems.v entries (plain_halts, ubsan_halts, ubsan_agrees, asan_halts,
  asan_agrees, asan_ubsan_halts, asan_ubsan_agrees), from a scratch file in the same build, deleted after: seven blocks,
  each exactly PrimInt63.{sub, ltb, lsr, lsl, lor, leb, land, int, eqb}, PrimString.{string, length, get},
  PrimArray.array, FunctionalExtensionality.functional_extensionality_dep, Classical_Prop.classic. No Section variable
  or hypothesis is left.

## 4. Name scan (binscan of record 807be47c4034)

Scope: lib/, provenance/evidence/ and the seven statement directories of the parent commit (the directories the PR
takes). Result: 0 blocking rows in provenance/evidence/. In lib/, 32 blocking rows on 14 lines; every one of those
lines is byte-identical to a line of a released file at ossv/recipes 2fceb489f4aa (`binscan-lines.tsv`: file, line,
the released file that has the same line). No blocking row is in a line written for this unit.

## 5. Comparison records and the comparison kit 86da41d3ef68

`kitscan-table.md` lists, per record of this evidence directory, the image pair, the functions the record compared, the
luiscan 9ae61e4a0e01 and ambiscan 9f61b4cee422 results, and a hand trace of every lui instruction of every compared
function (uses followed through addi, add, sub, sh1add / sh2add / sh3add, and / or / xor and their immediate forms, ld /
sd and jalr, up to the register's next write; every load / store / jump base built from a lui value compared as
symbol + offset in both images). Result: no lui-built address differs in any record. The table scans each record as
it was on the comparison kit 4bbd3a74be89. Records whose rows luiscan or ambiscan expose are re-run on 86da41d3ef68 by
their writers: stackmalloc1-A, stackmalloc1-B and uci-b-memcpy are already re-run in this tree (uci-b-memcpy with its
fresh reviews REVIEW-4bbd.md and REVIEW-86da.md, both CONFIRM).

uci-b-alloc's 96 ambiscan AMBIG rows (all `MemToShadow`, in the current paircl outputs) are settled per row in
`ambig-settle-uci-b-alloc.tsv`: in each row both images' addresses are the same-source copy that the paired callers
call at the same offset (96 MATCH, 0 MISMATCH). The record's verdict files cite none of its earlier/ outputs
(`ambig-settle-uci-b-alloc.md`).

## 6. The relocation script's step K3 (second donors)

For this unit K3 copied nothing: every run of record prints `K3 plain strlen: not linked by the unit, skipped` and the
same for ubsan strlen, plain memmove and ubsan memmove, and k2/k2-values.tsv has no row made by K3. No value or file of
this unit comes from K3.
