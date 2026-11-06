# fuzz_wire image A: the fake-stack contracts of classes 0 and 1

fuzz_wire.asan (sha256 2f8f8697cd4f, unstripped twin d2f662a22962) calls `__asan_stack_malloc_0` (0x3c544) and
`__asan_stack_malloc_1` (0x3c6b8). The contracts of both are fuzz_grant's released proofs, relocated onto this image:

| file (lib/) | donor (release commit 98c99a85e4; the same blob at 4f87de75d67, under proofs/libreac/fuzz_grant/lib/) |
|---|---|
| A/Rt/StackMalloc0.v | projects/libreac/fuzz_grant/proofs/lib/A/Rt/StackMalloc0.v |
| A/Rt/StackMalloc0Tbl.v | projects/libreac/fuzz_grant/proofs/lib/A/Rt/StackMalloc0Tbl.v |
| A/Rt/AF0r.v | projects/libreac/fuzz_grant/proofs/lib/A/Rt/AF0r.v |
| A/Rt/AF0s.v | projects/libreac/fuzz_grant/proofs/lib/A/Rt/AF0s.v |
| Reusable/YF0v.v | projects/libreac/fuzz_grant/proofs/lib/Reusable/YF0v.v (a kernel file StackMalloc0.v and AF0s.v Require, which the unit lacked) |

Each file keeps its donor's header lines (lines 1-4: Copyright, SPDX and the two `Modified by` lines) byte for byte, as
copied (the unit owner's ruling, 2026-10-31 18:12Z); licence-lines (C) rewrites them through the unit's path-map row.
Commit 9031801b53fd had left them out; records/header-restore.txt is the comment-only restore (token streams and
statements unchanged).

The contracts (records/print-assumptions.txt):

    A/Rt/StackMalloc0.v:513  Corollary stack_malloc0_contract : forall B, AR_laws tfibsegs B -> WireSyms B -> astack_malloc_realizes tfibsegs B 0.
    A/Rt/AF0s.v:513          Corollary stack_malloc1_contract : forall B, AR_laws tfibsegs B -> WireSyms B -> astack_malloc_realizes tfibsegs B 1.

Both are in `Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.`, so `About` prints
`forall {fx : FPState} {rc : RunCeil} (B : YG0f.asyms), ...`. Print Assumptions of each contract, and of each at WireB
(`@astack_malloc_realizes fx rc tfibsegs WireB <class>` for every fx and rc, closed by `exact` with AR_laws_ok and
WireB_syms): 14 axioms, every one in toolchain/allowed-axioms.txt.

## 1. The relocation (run.sh, sm_apply.py)

`run.sh <work>` is port_core 0e4e065eab9f with the flags of image A's core run: `--old-syms fuzz_grant.asan.syms.txt`,
`--old-prog 806b0:857dc`, the --no-stage list not-relocated-startup-layer.txt, the renames GrantB / GrantSyms /
GrantB_syms / GrantB_ok -> Wire*, `--known-elf` fuzz_wire.asan-ubsan, `--reusable-dir Reusable --kernel-dir Reusable`,
`--files files.txt`, and one patch: A-fs-ranges.patch, AF0r.v's code table without fuzz_grant's `__asan_stack_malloc_2`
/ `_4` rows (port_core refuses them, code-no-counterpart: fuzz_wire.asan links classes 0 and 1 only). Every input is
pinned by sha256 in the script. Result: staged 5, 0 kept, required.tsv empty, 0 override values, 1 / 1 patch, decode
check 14 / 14 ok, symbol gate PASS. port_core's FAIL rows: `rename-new-undeclared WireSyms` (its Record is in the
start-up file lib/A/AF0m.v, never staged) and `data-symbol` on AF0r.v's FS_FROFF 0x109000, three times (the model's
class-1 frame offset, kFakeFramesOff + 2^kStackSizeLog, not an address: role table). A re-run on the base lib
(a3f9509d24de) gives a byte-equal stage-out.

`sm_apply.py <work> <lib> <donor lib> <list>` copies the stage-out by port_core --apply's rule for new files (nothing
overwritten), with the donor's header lines in place of the stage-out's (the donor's lib in repository layout at
98c99a85e4, unnormalised). After module paths, the rename and numerals are normalised, each file equals its donor apart
from that one code-table line. run.sh, sm_apply.py and the two depot_apply.py runs of section 2 reproduce the five
files byte for byte.

## 2. The SZ step on the empty-depot kernel (takes.tsv)

The unit's kernel is the empty-depot form (lib/Reusable/DepotCfg.v:16 `depot_has_trace := false`): owned_extents
(lib/Reusable/YG0f.v:375-383) holds `if (ly_NB ly =? 0) then (4096, 0) else ...` and the same for ly_SB, which
fuzz_grant's kernel does not have, so the SZ step's `cbn [snd]; ... lia` failed in both files (records/build.txt, the
build of 9031801b53fd). fuzz_knock's released lib/A/AF0s.v:74 (release commit 88154566652a) is that step on this
kernel. The fix is one line in each file, every statement byte-equal (stmt_diff.py; records/stmt-diff-*.out):

- A/Rt/AF0s.v:69, the consumer route. knock/run-knock.sh (the knock run's flags, knock-files.txt = A/AF0s.v)
  relocates knock's AF0s.v onto fuzz_wire.asan. depot_classify.py --consumer (lib's provenance/evidence/depot/) classes
  the 18 hunks against this relocation's AF0s.v (records/consumer-classes-AF0s-full.tsv): 2 depot, 16 other. The SZ
  hunk is taken alone (records/consumer-classes-AF0s.tsv, depot-AF0s.patch). The other depot hunk re-wraps two Require
  statements (whitespace only) and is not taken, so the statements stay byte-equal (the unit owner's ruling,
  2026-10-31 17:36Z, condition 1).
- A/Rt/StackMalloc0.v:69, the glue (the unit owner's ruling, 2026-10-31 17:36Z). No released knock file has a class-0 SZ
  step on this kernel; StackMalloc0.v's SZ line is byte-equal to AF0s.v's. sm0_glue_twin.py writes the class-0 twin
  (StackMalloc0.v with knock's line) and refuses unless those lines are byte-equal; depot_classify.py --consumer gives
  1 hunk, depot (records/consumer-classes-StackMalloc0.tsv); depot_apply.py --consumer takes it (depot-StackMalloc0.patch).

The same two `sm0_glue_twin.py` / `depot_classify.py` / `depot_apply.py` commands give AF0s.v's line from knock's own
file. A non-writer read of the two hunks against the donor lines and the ruling found every item true.

## 3. The checks

- Bodies (records/rows-strictcmp3.out, bodies-strictcmp3.out): strictcmp3 65688e94214a of cmpkit 86da41d3ef68.
  `rows_cmp.py <kit> <grant twin> <wire twin> <plant>` compares the 10 rows of AF0r.v's code table word by word: 10 of
  10 EQUAL / EQUAL-mod-pcrel, each row the same function and offset in both images (MemToShadow's 28-word row cuts an
  auipc pair; its whole function is EQUAL-mod-pcrel). Control: one word of `__asan_stack_malloc_1` flipped in a copy
  of the twin gives that row DIFFERENT and no other change (CAUGHT). `strictcmp3.py cmp` on the 13 functions the code
  table holds or the class-0 / class-1 code calls: 12 EQUAL; RegisterCommonFlags differs only at +0x1218, outside the
  2 words the table holds (+0x358), which are EQUAL.
- Every numeral by role (records/roles.tsv, roles.out): `sm_roles.py <work> <grant twin> <wire twin> <out>`, each
  numeral that the relocation changed or that lies in an address range, measured on fuzz_wire.asan: 105 of 105 RIGHT
  (pc 24, thread 24, data 8, got 8, got-word 6, insn-word 8, img-top 14, model-constant 11, pc-decimal 2). The lines
  are the stage-out's (1 more than the files'). The SZ fix adds the two `0` literals of `=? 0` per file, no image value.
- The low-shadow bound 2148213760 (StackMalloc0.v / AF0s.v :253), unchanged: `sm_measure.py` (records/low-shadow-bound.out):
  at most kLowShadowBeg + IMG_TOP / 8 on both images (0x800b6400, 0x800b5a00).
- Size check (records/size-moves*.tsv): size_moves.py and size_moves_classify.py, 10 moves, 10 RIGHT (image.top).
- port_addr_check 45b78aaa48c3 (`pac_sm.sh`; records/pac-45b78aaa48c3-rows.tsv without the tool's note header, and
  .summary): 10 flag rows, each read: UNPAIRED-SOURCE 4 (the two code-table rows A-fs-ranges.patch drops),
  UNPAIRED-PORTED 4 (the `0` literals of the SZ line, two per file), UNRESOLVED 2 (the low-shadow bound above).
- Crossed pairs (records/ab1w-swaps.*): `ab1w_swaps.py` on lib/A/AB1w.v, which this relocation does not change: 0. The
  FS_* pc cells of the four files are each the same function and offset in both images (role table).
- Builds (records/build.txt): cb build --fresh of 9031801b53fd, rc 1 at the SZ step; of 8a2b472e9c3e, rc 0.

The scripts read elftools from PYTHONPATH and every input from an argument or the environment; they read and write
only the paths they are given.
