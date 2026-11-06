# fuzz_transport fake-stack classes 0, 1, 2, 4, 5 on image A: the write and the build

Proves no function (kind: merge). Image A = fuzz_transport.asan e89be137db17 (unstripped twin 86efc3a80314). Core of
record: the image-A core 9f022aeb9a21 (merged into this branch; record TransportSyms, lib/A/AF0m.v:3120).

## The write (commit 37b85428a20b)

Each class's script with --write, image A only, RECORD_A=TransportSyms, in the order 0, 1, 2, 4, 5; outputs in each
class's out-port2-write/ (run-write-A.log there). WT = this worktree, HUB = the hub, AL =
<ALRELOC_DIR>/alreloc.py.frozen-a5c53bb2bed4ad03 (sha256 a5c53bb2bed4ad03...), T = a directory
of links bin/ and unstripped/fuzz_transport/ to the port2 pins. The scripts as shipped also need KIT, the cmpkit
86da41d3ef68 directory (../README.md); paths below are relative to the slice directory (fakestack/).

    OUT=out-port2-write RECORD_A=TransportSyms sh class0/smrun.sh WT HUB DONORS/libreac T AL class0/class0-A.conf --write
    IMAGES=A OUT=class1/out-port2-write RECORD_A=TransportSyms sh class1/run.sh WT HUB DONOR_CTRL T AL --write
    IMAGES=A OUT=class2/out-port2-write RECORD_A=TransportSyms sh class2/run.sh WT HUB DONOR_CTRL T AL --write
    OUT=out-port2-write RECORD_A=TransportSyms sh class0/smrun.sh WT HUB DONORS/libreac T AL class4/class4.conf --write
    IMAGES=A OUT=class5/out-port2-write RECORD_A=TransportSyms sh class5/run.sh WT HUB DONORS/plugin-hostd T AL --write
    OUT=class5/out-port2-write/RtSM1T RECORD=TransportSyms sh class5/run-c1.sh WT HUB DONORS/plugin-hostd T AL --write
    sh class5/copy.sh WT HUB <unstripped fuzz_transport.asan> plugin-hostd/fuzz_command 781f46bc05cd Reusable/FCiface.v
    sh class5/copy.sh WT HUB <unstripped fuzz_transport.asan> libreac/fuzz_grant 4f87de75d67 Reusable/YF0v.v

Script changes: class1/run.sh and class5/run.sh read IMAGES (default "A B"). With IMAGES unset the loop is the old
`for I in A B`; the dry run of both images, repeated with the changed scripts (regress-dry-class1.log,
regress-dry-class5.log), writes resolve-{A,B}.txt, class{1,5}-{A,B}.tsv and checkrep-{A,B}.txt byte for byte as
class1/out-port2/ and class5/out-port2/; alreloc's outputs differ only in path strings (worktree, target directory) and,
for fuzz_command B, in alreloc's note on whether a built donor image exists elsewhere. class5/copy.sh is new: the copy
step of class1/run.sh with the donor as arguments; it refuses a numeral in the image span (lowest PT_LOAD start to
highest PT_LOAD end, [0x10000, 0x6153d0) for this image) and lists every other numeral >= 0x10000.

| file (lib/) | written by | donor at ref | alreloc (symbol / derived / resolved; KEPT-ADDR, UNMAPPED) | checkrep of the run | own .vo real s (counted build) |
|---|---|---|---|---|---|
| A/Rt/StackMalloc0Tbl.v | class0/smrun.sh class0-A.conf | libreac/fuzz_ctrl e10f488c53fc | 15 / 0 / 10; 0, 0 | 0 wrong rows | 9.08 |
| A/Rt/StackMalloc0.v | class0/smrun.sh class0-A.conf | libreac/fuzz_ctrl e10f488c53fc | 0 / 0 / 3; 0, 0 | 0 wrong rows | 60.94 |
| A/Rt/StackRawKept.v | class0/smrun.sh (and class1/run.sh, same body) | libreac/fuzz_ctrl, blob 0127a5ae165b | 0 / 0 / 0; 0, 0 | 0 wrong rows | 0.83 |
| A/Rt/StackMalloc1Tbl.v | class1/run.sh | libreac/fuzz_ctrl 2fceb489f4aa | 15 / 0 / 15; 0, 0 | 0 wrong rows | 8.95 |
| A/Rt/StackMalloc1.v | class1/run.sh | libreac/fuzz_ctrl 2fceb489f4aa | 0 / 0 / 5; 0, 0 | 0 wrong rows | 61.55 |
| A/Rt/StackMalloc2Tbl.v | class2/run.sh | libreac/fuzz_ctrl 2fceb489f4aa | 15 / 0 / 17; 0, 0 | 0 wrong rows | 8.98 |
| A/Rt/StackMalloc2.v | class2/run.sh | libreac/fuzz_ctrl 2fceb489f4aa | 0 / 0 / 4; 0, 0 | 0 wrong rows | 61.34 |
| A/Rt/StackMalloc4Tbl.v | class0/smrun.sh class4.conf | libreac/fuzz_grant e10f488c53fc | 20 / 0 / 9; 0, 0 | 0 wrong rows | 4.46 |
| A/Rt/StackMalloc4.v | class0/smrun.sh class4.conf | libreac/fuzz_grant e10f488c53fc | 6 / 7 / 7; 0, 0 | 0 wrong rows | 38.41 |
| A/Rt/AF0r.v | class0/smrun.sh class4.conf | libreac/fuzz_grant e10f488c53fc | 31 / 0 / 9; 0, 0 | 0 wrong rows | 8.49 |
| A/Rt/RtSM5T.v | class5/run.sh | plugin-hostd/fuzz_command 781f46bc05cd | 18 / 0 / 11; 0, 0 | 0 wrong rows | 8.38 |
| A/Rt/RtSM5.v | class5/run.sh | plugin-hostd/fuzz_command 781f46bc05cd | 0 / 0 / 10; 0, 0 | 0 wrong rows | 578.83 |
| A/Rt/RtSF5.v | class5/run.sh | plugin-hostd/fuzz_command 781f46bc05cd | 15 / 6 / 9; 0, 0 | 0 wrong rows | 6.72 |
| A/Rt/RtSMxA.v | class5/run.sh | plugin-hostd/fuzz_command 781f46bc05cd | 0 / 0 / 3; 0, 0 | 0 wrong rows | 1.01 |
| A/Rt/RtStack.v | class5/run.sh | plugin-hostd/fuzz_command 781f46bc05cd | 0 / 0 / 9; 0, 0 | 0 wrong rows | 0.80 |
| A/Rt/RtSM1T.v | class5/run-c1.sh | plugin-hostd/fuzz_command 781f46bc05cd | 32 / 0 / 11; 0, 0 | 0 wrong rows | 8.84 |
| Rt/StackMallocRawDef.v | class1/run.sh (copy) | libreac/fuzz_ctrl 2fceb489f4aa | copied: 0 numerals >= 0x10000 | - | 0.82 |
| Reusable/StackFreeDef.v | class1/run.sh (copy) | libreac/fuzz_ctrl 2fceb489f4aa | copied: 0 numerals >= 0x10000 | - | 0.78 |
| Reusable/StackFreeRaw.v | class1/run.sh (copy) | libreac/fuzz_ctrl 2fceb489f4aa | copied: 0 numerals >= 0x10000 | - | 0.78 |
| Reusable/FCiface.v | class5/copy.sh | plugin-hostd/fuzz_command 781f46bc05cd | copied: 0 numerals >= 0x10000 | - | 1.20 |
| Reusable/YF0v.v | class5/copy.sh | libreac/fuzz_grant 4f87de75d67 | copied: 0 in the image span; 2 above it | - | 1.81 |

Every write run: the compare PASS, control self PASS with 0 values moved, the planted word caught (1 FAIL line),
alreloc 0 UNMAPPED and 0 KEPT-ADDR, checkrep 0 wrong rows. Values moved inside a symbol (checkrep lists them; all
addresses, the same symbol + offset on both sides): common_flags_dont_use + 0x89 (StackMalloc4Tbl.v:68, AF0r.v:72,
RtSM5T.v:102, RtSM1T.v:76) and builtin_tls + 0xc8 / 0xe8 / 0xf0 / 0x8c8 / 0x800 / 0x8dc (the static TLS cells:
StackMalloc4Tbl.v, StackMalloc4.v, AF0r.v, RtSM1T.v), as in the dry runs.

- StackRawKept.v: classes 0 and 1 write it from one donor blob (0127a5ae165b at e10f488c53fc and 2fceb489f4aa); their
  outputs (class0/ and class1/out-port2-write/StackRawKept.v.written) differ only in the notice line (which run wrote
  it); the tree keeps class 0's. Class 2 does not write it.
- AF0r.v lands at lib/A/Rt/AF0r.v (grant's path; class4.conf FILES_A). No other class writes that path; the core has no
  lib/A/AF0r.v and no lib/A/Rt/.
- RtSM1T.v: fs_ranges drops __asan_stack_malloc_3 (0x3fc0c) and __asan_stack_malloc_7 (0x40244), which this image
  does not link.
- YF0v.v:93 holds 17594333495296 (0x10007fff8000, kHighMemBeg) and 2199291686912 (its / 8): ASan shadow-layout
  constants above the image span, not image addresses.
- Copyright / SPDX: every relocated or copied file keeps the donor's leading lines byte for byte and has one notice of
  this unit. The donors of StackRawKept.v, Rt/StackMallocRawDef.v and Reusable/StackFreeRaw.v have no leading comment
  (their first line is a Require), so these files start with the notice.
- Module names: every Require of the written files names a module of transport's core (lib/A AB1v AB1w AE34 AF0l AF0m
  AF0x AE2y; lib/Reusable YZ00 YK.. YP.. YN3v YN32 YI04 YG.. YA0i-YA0q YCe5 YK04 YK0j YM05) or a written file. No
  module name of the written files exists elsewhere in the unit.

## The build (from commit 37b85428a20b; clone <WT>, VM <VM>)

    cb clone libdiginet/fuzz_transport <CLONE> 37b85428a20b                                   (cb-clone.log)
    CACHE=dune VM=<VM> MEM=24g cb build <CLONE> $(cat targets.txt)               (cb-build-dune-1.log)
    CACHE=none VM=<VM> MEM=24g cb build --fresh <CLONE> $(cat targets.txt)       (cb-build-none-1.log)

- dune: build-20261031T081743Z.log, rc=0 wall=595, 21 targets compiled, 0 failed, vo check 0 failed; 4 PINNED.
- counted, CACHE=none (--fresh: the workspace re-made from base f6acfcb0c1b8, so make compiles every target and every
  core file it needs that differs from the base): counted-build-lines.txt (the log's pin, vo check, `.vo (real` and rc
  lines; the whole log is build-20261031T082914Z.log (sha256 7e89a35a0bbd; internal record)), rc=0 wall=720, 80 files compiled
  (the 21 targets and 59 core files), 0 failed; vo check before and after make 0 failed; 4 PINNED (facts f6acfcb0c1b8).
  Each target's own `.vo (real` line is in the last column of the table above.

No relocation fix was needed: every file compiled as written. No core gap was found.

## Print Assumptions (PrintAssumptionsFakeStackA.v)

Compiled after the counted build in the checker image (sha256:cc9ae43a9f4b...) against the workspace's _CoqProject, in
a directory of the workspace <VM_WS> (rc=0, empty log); each Redirect file is pa-<name>.out here. The first run used the
probe with the six contracts below (sha256 ae3c007319aa...); the probe now also prints stack_free5_realizes (sha256
560c0da4000b..., next section), and its run on be55a2f7f0ae wrote the six outputs below again byte for byte.

| contract | file | axioms |
|---|---|---|
| ctrl_stack_malloc0 | A/Rt/StackMalloc0.v:535 | 14 |
| ctrl_stack_malloc1 | A/Rt/StackMalloc1.v:536 | 14 |
| ctrl_stack_malloc2 | A/Rt/StackMalloc2.v:536 | 14 |
| stack_malloc4_contract | A/Rt/StackMalloc4.v:514 | 14 |
| cmd_stack_malloc5_contract | A/Rt/RtSM5.v:534 | 14 |
| cmd_stack_free5_contract | A/Rt/RtSF5.v:388 | 14 |
| stack_free5_realizes | A/Rt/RtSF5Cg.v:33 | 14 |

The 14 are the same for each: PrimInt63 sub ltb lsr lsl lor leb land int eqb, PrimString string length get,
PrimArray.array, FunctionalExtensionality.functional_extensionality_dep. Each is the suffix of one entry of the base's
allowed-axioms.txt (sha256 in allowed-axioms.sha256); no Section hypothesis is left open.

## The class-5 release bridge (commit be55a2f7f0ae)

be55a2f7f0ae adds two files to lib/: A/Prog/TransportRtCg.v (taken by path, byte for byte, from the image-A core's
lib/A/Prog/TransportRtCg.v (sha256 bb6bd5b4d88b): the callee texts aset_shadow_realizes and astack_free_cls_realizes that the image-A program-walk
statements assume) and A/Rt/RtSF5Cg.v (Theorem stack_free5_realizes : forall B, AR_laws tfibsegs B -> TransportSyms B ->
TransportRtCg.astack_free_cls_realizes tfibsegs B 0x3df10 5, proved by RtSF5.cmd_stack_free5_contract). The Definition
text of astack_free_cls_realizes in TransportRtCg.v:51 is the text of RtStack.v:78 character for character (1065
bytes), in the same Section shape (Context fx rc; Variables segs B), so the proof is the same term.

    CACHE=dune VM=<VM> MEM=24g cb build <CLONE> lib/A/Prog/TransportRtCg.vo lib/A/Rt/RtSF5Cg.vo          (cb-build-dune-cg.log)
    CACHE=none VM=<VM> MEM=24g cb build --fresh <CLONE> $(cat targets-cg.txt)                              (cb-build-none-cg.log)
    CACHE=none VM=<VM> MEM=24g cb build <CLONE> $(cat targets.txt) lib/A/Prog/TransportRtCg.vo lib/A/Rt/RtSF5Cg.vo  (cb-build-none-pa.log)

(target paths in full: proofs/libdiginet/fuzz_transport/lib/...). The clone was fast-forwarded to be55a2f7f0ae.

- dune: build-20261031T093542Z.log, rc=0 wall=6, 2 targets compiled, 0 failed, vo check 0 failed; 4 PINNED.
- counted, CACHE=none --fresh (workspace re-made from base f6acfcb0c1b8), targets TransportRtCg.vo, RtSF5Cg.vo and
  RtSF5.vo: counted-build-lines-cg.txt (the log's header, every `.vo (real` line, the vo check after make, rc; the whole
  log is build-20261031T093618Z.log (sha256 dd98e6edd049; internal record)), rc=0 wall=156, 64 files compiled, 0 failed;
  vo check before and after make 0 failed;
  4 PINNED (facts f6acfcb0c1b8). Own `.vo (real` lines:

      proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportRtCg.vo (real: 0.78, user: 0.51, sys: 0.26, mem: 512584 ko)
      proofs/libdiginet/fuzz_transport/lib/A/Rt/RtSF5.vo (real: 6.76, user: 6.37, sys: 0.38, mem: 679380 ko)
      proofs/libdiginet/fuzz_transport/lib/A/Rt/RtSF5Cg.vo (real: 0.93, user: 0.67, sys: 0.26, mem: 579532 ko)

- for the probe, CACHE=none without --fresh on the same workspace, every image-A target (the 21 of targets.txt and the
  two new files): pa-build-lines.txt (the whole log is build-20261031T093936Z.log (sha256 a146da89c781; internal
  record)), rc=0 wall=592, 18 files compiled (the targets the counted build did not need),
  the three counted targets up to date, 0 failed, vo check after make 0 failed; 4 PINNED. Then the probe above.

No relocation fix: both files compiled as committed; TransportRtCg.v is unchanged. Print Assumptions of
stack_free5_realizes (pa-stack_free5_realizes.out): the same 14 axioms as the six contracts above, each the suffix of
one entry of the base's allowed-axioms.txt.
