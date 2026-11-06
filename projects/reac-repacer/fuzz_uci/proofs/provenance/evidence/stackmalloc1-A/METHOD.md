# Image-A class-1 stack_malloc contract for fuzz_uci: the route

The image-B record's route (../stackmalloc1-B/METHOD.md) with image B -> image A: core-A's route (../core-A/run.sh) for
three files; only the file list and two patches differ from core-A.

## Donor

fuzz_grant's RELEASED files at recipes 4f87de75d67 (PR #401; the three blobs are the same at 25e3d17bdb50, core-A's
donor commit): lib/A/Rt/AF0r.v (the code table, the symbolic runs, the probe loop; CID 1, FS_ENTRY 0x3cf18),
lib/A/Rt/AF0s.v (tfib_stack_malloc_at and the corollary stack_malloc1_contract, line 513) and lib/Reusable/YF0v.v
(own_free_frame / own_free_frame_shadow, which AF0s.v uses). The released-proof lookup found no fuzz_uci class-1
contract (released or in flight), so the grant-A proof is ported. `mkdon-sm1.sh 4f87de75d67` normalises the donor by
core-A's rule (lib/Reusable/* -> root).

## Bodies first

Before the relocation every body the two proofs step through was compared instruction by instruction with fuzz_grant's
(bytecmp.py, BYTECMP.md): the code table's rows and every callee of the class-1 code, 13 bodies, all equal up to
relocation. The tool is the image-B record's fixed tool (its data-place rules and p_filesz reader), which needed one
rule for these twins (an `addi rd, rs, 0` low half of an auipc pair, printed `mv`), measured and controlled in
BYTECMP.md. fuzz_grant's table also covers __asan_stack_malloc_0 / _2 / _4,
which fuzz_uci does not link (sites.py, keyset classes).

## Tool and inputs

`run.sh`: port_core 0e4e065eab9f with core-A's flags (`--old-syms` core-reloc/A/fuzz_grant.asan.syms.txt,
`--old-prog 806b0:857dc`, the rename set `GrantB=UciB GrantSyms=UciSyms GrantB_syms=UciB_syms GrantB_ok=UciB_ok`, the
`--no-stage` start-up list, `--known-elf` fuzz_uci.asan-ubsan, `--reusable-dir Reusable --kernel-dir Reusable`);
`--files files-sm1.txt`. Target lib = this branch's lib (image A's core and start-up layer): every module the three
files Require is KEPT from it except YF0v, which the unit's lib/Reusable lacks and which the run stages once, into
lib/Reusable (it states no image value). Run result: staged 3, kept 0, required.tsv empty, 0 override values, 2 / 2
patches applied, decode check 7 / 7 ok, symbol gate PASS.

## Values no rule decides, and the structural changes

- No `--override`. The image-B record's one override (the low-shadow bound, grant B's exact kLowShadowBeg + IMG_TOP / 8)
  has no image-A counterpart: grant A's AF0s.v:253 states a smaller constant, 2148213760, which port_core leaves; it is
  at most kLowShadowBeg + IMG_TOP / 8 on both images (fuzz_grant.asan 2148230144, fuzz_uci.asan 2148227072:
  `measure-sm1.py`, `measure-sm1.out`), so the same lia step proves it on fuzz_uci.asan (the build).
- port_core's review rows `FAIL data-symbol` on AF0r.v FS_FROFF 0x109000 (lines 36, 355, 364 of the stage): the value is
  the model's fake-frame offset of class 1, kFakeFramesOff + (1 << kStackSizeLog) = 0x9000 + 0x100000 (frame_addr_cid,
  Qed), not an address; it stays (the by-value check declares it, GATES.md 2c).
- `A-fs-ranges.patch`: AF0r.v's code table without fuzz_grant's __asan_stack_malloc_0 / _2 / _4 rows, which port_core
  refuses (code-no-counterpart): fuzz_uci links class 1 only, and the class-1 code calls none of them.
- `YF0v-lia.patch`: YF0v.v shadow_apart's last step `nia` -> `lia`. The text rules forbid nia; the goal is linear once
  the divisions by 8 are rewritten, and the build proves it. The image-B record's lib/Reusable/YF0v.v (git blob
  3bd99830db8a) keeps `nia`, so the two branches' YF0v.v differ in that step and in the header line this run writes.

## Apply and headers

`apply-sm1.sh` copies the stage-out by --apply's rule (nothing overwritten; applied.txt), because of core-A's known FAIL
row `rename-new-undeclared UciSyms` (its Record is in the start-up file lib/A/AF0m.v, never staged). `header-sm1.py
LIB DON` (comments only; code bytes checked unchanged): every inherited header line (Copyright, SPDX, each donor
Modified line) stays the donor blob's byte for byte, the one donor line port_core's rename reached gets its own words
back (`TfibSyms renamed GrantSyms`), and port_core's line is replaced by one `(* Modified by Theorem Labs, 2026-10: ...
*)` notice naming the donor file at its release commit, the donor image, the target image and what changed.

## Gates

GATES.md: bytecmp, the flag gate (port_addr_check efa19b81e92b of record, e165063a0081 beside it, two planted
pointers), codeptr, keyset and the range-table check in place of atable, the by-value check, v10, yh03check (N/A) and the
build, each with a planted control (`gates/run-gates.sh`, records in records/ by `gates/records-sm1.py`), Print
Assumptions, and the consumer's hypothesis type closed by `exact`.
