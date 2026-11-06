# fuzz_transport fake-stack classes 0, 1, 2, 3, 5 on image B: the write and the build

Proves no function (kind: merge). Image B = fuzz_transport.asan-ubsan 41113a03c82f (unstripped twin e217cb0a84f1).

Core of record: the image-B core a83315552115, merged into this branch at b4662df8e81 (no conflict). It holds the
image-B start-up 9cbb0cb6647 (row T4r) on the new pins, and the merge leaves the 19 start-up files as they were (among
them lib/B/YF0m.v, sha256 35d10c8cbfc1, and lib/B/YB1v.v, sha256 00ba4a17bb4a). Record TransportSyms (lib/B/YF0m.v:3126;
asyms value YD2l.TransportB), segments tfibsegs. The 15 files were written (f9158444652) and first built on the interim
image-B core 57e14e8205e with the same start-up (the last section); the merge of the core of record changes none of
them. The build of record below is on the core of record. The image-B integration line b40685a42a62 (core run of
record r16) was merged after it (98fec74a3b5); it changes none of these files, and the counted build on it is the
section "The image-B line b40685a42a62 merged".

## The write (commit f9158444652)

Each class's script with --write, image B only, RECORD_B=TransportSyms. The outputs are in each class's
out-port2-write-B/: run-write-B.log, and run-c1-write-B.log for RtSM1T. WT = this worktree, HUB = the hub, AL =
<ALRELOC_DIR>/alreloc.py.frozen-a5c53bb2bed4ad03, T = <WORK>/target (links to the port2 pins), KIT = the cmpkit
86da41d3ef68 directory (../README.md). Paths are relative to the slice directory (fakestack/). Every OUT was an absolute
path: alreloc runs from its own directory.

    OUT=out-port2-write-B RECORD_B=TransportSyms sh class0/smrun.sh WT HUB DONORS/libreac T AL class0/class0-B.conf --write
    IMAGES=B OUT=class1/out-port2-write-B RECORD_B=TransportSyms sh class1/run.sh WT HUB DONORS/libreac T AL --write
    IMAGES=B OUT=class2/out-port2-write-B RECORD_B=TransportSyms sh class2/run.sh WT HUB DONORS/libreac T AL --write
    OUT=class3/out-port2-write-B RECORD_B=TransportSyms sh class3/run.sh WT HUB <AGENTS> T AL --write
    IMAGES=B OUT=class5/out-port2-write-B RECORD_B=TransportSyms sh class5/run.sh WT HUB DONORS/plugin-hostd T AL --write
    IMAGES=B OUT=class5/out-port2-write-B/RtSM1T RECORD=TransportSyms sh class5/run-c1.sh WT HUB DONORS/plugin-hostd T AL --write
    python3 class0/bpaths.py WT HUB libreac/fuzz_ctrl e10f488c53fc B/Rt/StackMalloc0Tbl.v B/Rt/StackMalloc0.v B/Rt/StackRawKept.v
    python3 class0/bpaths.py WT HUB libreac/fuzz_ctrl 2fceb489f4aa B/Rt/StackMalloc1Tbl.v B/Rt/StackMalloc1.v
    python3 class0/bpaths.py WT HUB libreac/fuzz_ctrl 2fceb489f4aa B/Rt/StackMalloc2Tbl.v B/Rt/StackMalloc2.v

(DONORS/libreac/{bin,unstripped}/fuzz_ctrl/ link to <LIBREAC_V190>/s/fuzz_ctrl/ and x/unstripped/fuzz_ctrl/;
DONORS/plugin-hostd/{bin,unstripped}/fuzz_command/ to <AGENTS>/pau-pipeline/plugin-hostd/.) bpaths.py's output is
bpaths-B.log in the out-port2-write-B/ of classes 0, 1 and 2.

| file (lib/) | written by | donor at ref | alreloc (symbol / derived / resolved; KEPT-ADDR, UNMAPPED) | checkrep of the run | own .vo real s (counted build of record) |
|---|---|---|---|---|---|
| B/Rt/StackMalloc0Tbl.v | class0/smrun.sh class0-B.conf | libreac/fuzz_ctrl e10f488c53fc | 15 / 0 / 12; 0, 0 | 0 wrong rows | 11.04 |
| B/Rt/StackMalloc0.v | class0/smrun.sh class0-B.conf | libreac/fuzz_ctrl e10f488c53fc | 0 / 0 / 3; 0, 0 | 0 wrong rows | 70.39 |
| B/Rt/StackRawKept.v | class0/smrun.sh (and class1/run.sh, same body) | libreac/fuzz_ctrl, blob 0127a5ae165b | 0 / 0 / 0; 0, 0 | 0 wrong rows | 1.28 |
| B/Rt/StackMalloc1Tbl.v | class1/run.sh | libreac/fuzz_ctrl 2fceb489f4aa | 15 / 0 / 16; 0, 0 | 0 wrong rows | 12.20 |
| B/Rt/StackMalloc1.v | class1/run.sh | libreac/fuzz_ctrl 2fceb489f4aa | 0 / 0 / 5; 0, 0 | 0 wrong rows | 76.03 |
| B/Rt/StackMalloc2Tbl.v | class2/run.sh | libreac/fuzz_ctrl 2fceb489f4aa | 15 / 0 / 18; 0, 0 | 0 wrong rows | 12.20 |
| B/Rt/StackMalloc2.v | class2/run.sh | libreac/fuzz_ctrl 2fceb489f4aa | 0 / 0 / 4; 0, 0 | 0 wrong rows | 76.22 |
| B/Rt/RtSM3T.v | class3/run.sh | plugin-hostd/fuzz_command 781f46bc05cd | 26 / 0 / 44; 0, 0 | 0 wrong rows | 10.00 |
| B/Rt/RtSM3.v | class3/run.sh | plugin-hostd/fuzz_command 781f46bc05cd | 6 / 0 / 10; 0, 0 | 0 wrong rows | 51.81 |
| B/Rt/RtSM5T.v | class5/run.sh | plugin-hostd/fuzz_command 781f46bc05cd | 18 / 0 / 33; 0, 0 | 0 wrong rows | 10.38 |
| B/Rt/RtSM5.v | class5/run.sh | plugin-hostd/fuzz_command 781f46bc05cd | 0 / 0 / 11; 0, 0 | 0 wrong rows | 619.50 |
| B/Rt/RtSF5.v | class5/run.sh | plugin-hostd/fuzz_command 781f46bc05cd | 16 / 6 / 16; 0, 0 | 0 wrong rows | 8.62 |
| B/Rt/RtSMxA.v | class5/run.sh | plugin-hostd/fuzz_command 781f46bc05cd | 0 / 0 / 3; 0, 0 | 0 wrong rows | 1.41 |
| B/Rt/RtStack.v | class5/run.sh | plugin-hostd/fuzz_command 781f46bc05cd | 0 / 0 / 9; 0, 0 | 0 wrong rows | 1.24 |
| B/Rt/RtSM1T.v | class5/run-c1.sh | plugin-hostd/fuzz_command 781f46bc05cd | 30 / 0 / 51; 0, 0 | 0 wrong rows | 10.85 |

Every write run: the compare PASS, control self PASS with 0 values moved, the planted word caught (1 FAIL line),
alreloc 0 UNMAPPED and 0 KEPT-ADDR, checkrep 0 wrong rows. Each class's compare table, compare summary, resolve lines
and checkrep output (class{0,1,2,3,5}-B.tsv / .txt, resolve-B.txt, checkrep-B.txt) are byte for byte the same files
in the class's out-port2/ (the dry run). twins-B.txt and plant-B.txt are byte for byte the same too. The
alreloc per-file counts are the dry run's. Class 3 ran its rule-24 compare of the six donors again: all six PASS, with
the same closeness lines. Values moved inside a symbol: each one is an address, with the same symbol + offset on both
sides (checkrep lists them). They are common_flags_dont_use + 0x89 (RtSM3T.v:74, RtSM5T.v:103, RtSM1T.v:77) and the
static TLS cells builtin_tls + 0xc8 / 0xe8 / 0xf0 / 0x8c8 / 0x800 / 0x8dc (RtSM3T.v, RtSM3.v, RtSM1T.v), as in the dry
runs. The written files state TP and TSD as 0x5f3770 and 0x614b18 (RtSM3T.v, RtSM1T.v). These are the start-up's
TFIB_TP and TFIB_TSD (lib/B/YF0m.v:15).

- No image-free file was written twice. class1/run.sh copies lib/Rt/StackMallocRawDef.v, lib/Reusable/StackFreeDef.v
  and StackFreeRaw.v again, and those copies are byte for byte the committed ones. lib/Reusable/FCiface.v and YF0v.v
  (class 5 / 3) are the committed image-A copies; copy.sh did not run.
- StackRawKept.v: classes 0 and 1 write it from one donor blob (0127a5ae165b at e10f488c53fc and 2fceb489f4aa, the
  same blob as image A's). The two outputs (StackRawKept.v.written of each class) differ only in the notice line. The
  tree keeps class 0's.
- RtSM1T.v: fs_ranges drops __asan_stack_malloc_4 (0x3fe04) and __asan_stack_malloc_7 (0x40290). This image does not
  link them (RtSM1T/absent-B.txt).
- Module paths. libreac/fuzz_ctrl keeps its image-B core under lib/Reusable; transport keeps it under lib/B.
  class0/bpaths.py reads the donor's core from the donor: the lib/Reusable modules that have an A twin in its lib/A
  (369 at both refs). In each of the six StackMalloc{0,1,2}{,Tbl}.v files, one line (:19) Requires YB1v YE34 YF0l YF0m
  YF0x YE2y. The script moves that line from lib.Reusable to lib.B and adds one sentence to the file's one notice line.
  Each of the six modules is in transport's lib/B and none of them is in its lib/Reusable. StackRawKept.v Requires no
  core module. The donor's shared lib/Reusable modules (YCe5, YG0q, ...) stay lib/Reusable. fuzz_command's files
  Require lib.B already. Every module that a written file Requires under the unit's prefix is a file of the unit:
  lib/B YB1v YB1w YE34 YF0l YF0m YF0x YE2y, lib/B/Rt (the files written here), lib/Rt StackMallocRawDef, and
  lib/Reusable (YZ00, YK.., YP.., YN3v, YN32, YI04, YG.., YA0i-YA0q, YCe5, YK04, YK0j, YM05, StackFreeDef,
  StackFreeRaw, FCiface).
- Copyright / SPDX: every relocated file keeps the donor's leading lines byte for byte and has one notice of this unit.
  The donor of StackRawKept.v has no leading comment, so that file starts with the notice.

Script changes:

- class5/run-c1.sh reads IMAGES, one image, default A. regress-c1-A-images.log is the dry image-A run with the changed
  script. It writes resolve-A.txt, class1-A.tsv, class1-A.txt, checkrep-A.txt, absent-A.txt and the two controls'
  resolve-A.txt byte for byte as class5/out-port2-write/RtSM1T/, with the same alreloc counts.
- class5/class1cmp.py has class3/class3cmp.py's decimal code-point rule. Without the rule, alreloc does not write
  B/Rt/RtSM1T.v: `AMBIGUOUS-MODEL-CONSTANT B/Rt/RtSM1T.v:33 0x3fbd4 -> 0x3d974 (Definition FS_FOUND: its decimal twin
  261076 stays in the file)`. The donor's leading notice (:5) names FS_FOUND in hex and in decimal, and those header
  numerals are kept. With the rule, the hex (:33) and the decimal (:279) both come from the paired function:
  __asan_stack_malloc_1 + 0x10c, 0x3d974 = 252276. regress-c1-A-decimal.log is the image-A run with --write and the
  changed script. Its resolve-A.txt has two more lines, A/Rt/RtSM1T.v:32 0x3fb88 0x3d918 and :278 261000 252184,
  which are the values alreloc's same-code-function rule gave before. The rule also moves 2 of alreloc's 32 symbol
  rows to resolved rows. The file it writes, lib/A/Rt/RtSM1T.v, is byte for byte the committed file.
- class0/bpaths.py is new (above).

## The build of record (from commit 56be9351a30; clone <CLONE>, VM <VM>)

    the clone fast-forwarded to 56be9351a30 (the core of record merged, and the bridge below)
    CACHE=dune VM=<VM> MEM=24g cb build <CLONE> $(cat targets-rec.txt)                                  (cb-build-dune-rec.log)
    CACHE=none VM=<VM> MEM=24g cb build --fresh <CLONE> $(cat targets-rec.txt)                          (cb-build-none-rec.log)

(targets-rec.txt: the 15 files of the table and lib/B/Rt/RtSF5CgB.vo, paths in full.) The VM's load average before
the builds was 25.0 (88 cores).

- dune: build-20261031T121305Z.log, rc=0 wall=721, 16 targets compiled, 0 restored from the cache, 0 failed, 0
  warnings, vo check 0 failed; 4 PINNED.
- counted, CACHE=none --fresh: the workspace was made again from base f6acfcb0c1b8, so make compiles every target and
  every file it needs that differs from the base. counted-build-lines-rec.txt has the log's header to .Makefile.d,
  every `.vo (real` line, the summary line of the vo check after make, and rc. The whole log is
  build-20261031T122545Z.log (sha256 39e259d6606b; internal record). rc=0 wall=799, 100 files compiled, 0 failed:
  the 16 targets and 84 more (lib/B YB1q YB1v YB1w YE20 YE2y YE34 YF0l YF0m YF0x YImgTop, 72 lib/Reusable files,
  lib/Rt/StackMallocRawDef, lib/A/Prog/TransportRtCg). 4 PINNED (facts f6acfcb0c1b8). vo check before make: 0
  failed. vo check after make: 374 .vo failed (all inconsistent), and 0 of them are this build's targets or what they
  Require. They are base .vo outside this closure (43 under lib/, 2 under lib/Prog, 325 under lib/Reusable, 4 under
  lib/U) that were compiled against lib/Reusable files the core of record changes and this build compiled again. cb
  removes them from the workspace, so a later build compiles them. The last column of the table above has each
  target's own `.vo (real` line, and RtSF5CgB.vo's is 1.19 s.

No relocation fix was needed in the .v files: every file compiled as written, on both cores. No gap was found in the
core or the start-up within the closure of these files.

## The class-5 release bridge (lib/B/Rt/RtSF5CgB.v, commit 56be9351a30)

lib/B/Rt/RtSF5CgB.v is the image-B twin of lib/A/Rt/RtSF5Cg.v (build-A/BUILD-A.md, "The class-5 release bridge"):

    Theorem stack_free5_realizes_B : forall (B : asyms), AR_laws tfibsegs B -> TransportSyms B ->
      TransportRtCg.astack_free_cls_realizes tfibsegs B 0x3df4c 5.
    Proof. intros B LAWS TB. exact (RtSF5.cmd_stack_free5_contract B LAWS TB). Qed.

0x3df4c is __asan_stack_free_5 of this image, as RtSF5.v states it (SF_ENTRY, :42; cmd_stack_free5_contract, :389)
and as lib/B/Prog/DgnTransportBAddr.v:79 maps TB___asan_stack_free_5. The import block is RtSF5.v's own (lines 7-30)
byte for byte, then lib.B.Rt RtSF5 and lib.A.Prog TransportRtCg. TransportRtCg.v is image-free (it Requires only
lib/Reusable modules) and both images share it. The image-B walk lib/B/Prog/diginet_session_tick_cg.v Requires the
same file (:522), so no twin is made. Its Definition text of astack_free_cls_realizes (TransportRtCg.v:50) and the
one in lib/B/Rt/RtStack.v:79 are the same 1064 bytes, in the same Section shape (Context fx rc; Variables segs B). So
the proof is the same term. The malloc contracts need no bridge: they state lib/Reusable/YG0d.v's
astack_malloc_realizes (:286), as on image A.

## Print Assumptions (PrintAssumptionsFakeStackB.v, sha256 221481cdaae6...)

The probe was compiled after the counted build of record, in the checker image (sha256:cc9ae43a9f4b...), against the
workspace's _CoqProject, in a directory of the workspace <VM_WS> (rc=0, empty log). Each Redirect file is
pa-<name>.out here.

| contract | file | axioms |
|---|---|---|
| ctrl_stack_malloc0 | B/Rt/StackMalloc0.v:536 | 14 |
| ctrl_stack_malloc1 | B/Rt/StackMalloc1.v:536 | 14 |
| ctrl_stack_malloc2 | B/Rt/StackMalloc2.v:536 | 14 |
| cmd_stack_malloc3_contract | B/Rt/RtSM3.v:518 | 14 |
| cmd_stack_malloc5_contract | B/Rt/RtSM5.v:535 | 14 |
| cmd_stack_free5_contract | B/Rt/RtSF5.v:389 | 14 |
| stack_free5_realizes_B | B/Rt/RtSF5CgB.v:34 | 14 |

Each of the seven outputs is byte for byte the image-A outputs (build-A/pa-*.out, sha256 465973b74e8f...). On the
interim core the probe without the bridge (sha256 b8035966df26...) wrote the six contracts' outputs byte for byte the
same. The 14 axioms are PrimInt63 sub ltb lsr lsl lor leb land int eqb, PrimString string length get,
PrimArray.array, and FunctionalExtensionality.functional_extensionality_dep. Each is the suffix of one entry of the
base's allowed-axioms.txt. Its sha256 is in allowed-axioms.sha256, and it is the same file as image A's. No Section
hypothesis is left open.

## The image-B line b40685a42a62 merged, and the build again (commit 98fec74a3b5)

98fec74a3b5 merges b40685a42a62 into this branch (merge base a83315552115, no conflict). b40685a42a62 is the head of the
image-B integration line. It holds the image-B core run of record r16 (allocator-model tags in the seven image-B twins,
EV_LIB 2048 in lib/B/YCfn.v and YCfl.v), the image-B statements, and the image-A line f26449c3a90d.

- The merge changes no file of lib/A/Rt, lib/B/Rt or lib/Rt, none of the image-free copies, and no file of fakestack/.
  Those files are byte for byte the files of fa865159b4af. Of the files this slice ships, the merge changes only
  lib/A/Prog/TransportRtCg.v, and only in two comments (0060946d62f): line 14 and lines 48-49 name the source of
  astack_free_cls_realizes without a work-item name. Its Definition text (:50) is still the same 1064 bytes as
  lib/B/Rt/RtStack.v:79.
- Of the 100 files the counted build compiles, five are changed by the merge: lib/Reusable/YG00.v (the allocator-model
  tags, numerals of mcheck and spin), YG03.v, YG06.v, lib/B/YB1w.v (function-table cells removed, a comment) and
  TransportRtCg.v (the comments above). lib/B/YCfn.v and YCfl.v are not in the closure of these files.
- provenance/evidence/MANIFEST and MANIFEST.md (the evidence index above the slices) are written again by
  mkmanifest.py and then mk_top_manifest.py 9921cc76eaf9, the two commands that wrote them on the integration line (its
  copy of record, with its SHA256SUMS checked), after this commit's files were written. Control: on b40685a42a62's
  evidence the two commands write its MANIFEST and MANIFEST.md again byte for byte. On this branch MANIFEST.md lists
  fakestack/'s files as this MANIFEST names them. mk_top_manifest.py kept MANIFEST and added one line, the root file
  untime-removed.tsv (in no slice).

    the clone fast-forwarded to 98fec74a3b5
    CACHE=none VM=<VM> MEM=24g cb build --fresh <CLONE> $(cat targets-rec.txt)                  (cb-build-none-merge.log)
    CACHE=dune VM=<VM> MEM=24g cb build <CLONE> $(cat ../build-A/targets.txt) lib/A/Prog/TransportRtCg.vo lib/A/Rt/RtSF5Cg.vo
                                                                                                 (cb-build-dune-A-merge.log)

- counted, CACHE=none --fresh, the 16 image-B targets: counted-build-lines-merge.txt (the header to .Makefile.d,
  every `.vo (real` line, the summary line of the vo check after make, rc). The whole log is
  build-20261031T150032Z.log (sha256 0689cac49dfa; internal record). rc=0 wall=795, 100 files compiled (the same 100
  as the build of record), 0 failed, 4 PINNED (facts f6acfcb0c1b8). vo check before make: 0 failed. vo check after
  make: 374 .vo failed (all inconsistent), as in the build of record, and 0 of them are this build's targets or what
  they Require. Own `.vo (real` lines, in s:

  | target (lib/B/Rt/) | s | target (lib/B/Rt/) | s |
  |---|---|---|---|
  | StackMalloc0Tbl | 11.99 | RtSM3T | 9.45 |
  | StackMalloc0 | 70.68 | RtSM3 | 45.71 |
  | StackRawKept | 1.11 | RtSM5T | 11.22 |
  | StackMalloc1Tbl | 10.47 | RtSM5 | 628.37 |
  | StackMalloc1 | 70.81 | RtSF5 | 9.01 |
  | StackMalloc2Tbl | 10.54 | RtSMxA | 1.45 |
  | StackMalloc2 | 69.57 | RtStack | 1.01 |
  | RtSM1T | 11.73 | RtSF5CgB | 1.25 |

- Print Assumptions: the probe (sha256 221481cdaae6...) was compiled again after this counted build, in the checker
  image against the workspace's _CoqProject (rc=0, empty log). Its seven outputs are byte for byte the pa-*.out files
  here (sha256 465973b74e8f...), so they are not shipped again.
- image A, dune: build-20261031T151529Z.log, rc=0 wall=6. All 23 targets (the 21 of build-A/targets.txt,
  TransportRtCg.vo and RtSF5Cg.vo) were restored from dune's shared cache: a dune build compiled earlier each target's
  rule with the same inputs. 0 compiled, 0 failed, vo check 0 failed (164 .vo read), 4 PINNED. This is not a counted
  build of image A.

No relocation fix was needed and no finding was made: the core changes break no file of this slice.

## Before the core of record: the interim image-B core

This branch first merged 9cbb0cb6647 (the 19 start-up files), then the interim image-B core 57e14e8205e (388 more lib/B
files), into the image-A row branch (f179db1ca46). The two touch no common file, so neither merge had a conflict.

### The B side before the write (cb-build-dune-core.log, core-build-lines.txt)

    cb clone libdiginet/fuzz_transport <CLONE> f179db1ca46                                                (cb-clone.log)
    CACHE=dune VM=<VM> MEM=24g cb build <CLONE> lib/B/{TransportDriverB,YA07,YA0b,YD1j,YD1l,YD2l,YD2m,YE2q,YE2r,YE2s,YF0q,YF0w,YF0m}.vo

The 12 lib/B files that no other file Requires, and the start-up's YF0m.v. rc=1 wall=1438: 9 targets compiled (YF0m.vo
among them), 4 not built; 6 compiles failed (2 with an error, 4 with exit -7); vo check 0 failed; 4 PINNED.
core-build-lines.txt holds the log's selected lines; the whole log is build-20261031T102911Z.log (sha256 4295cb37b71e;
internal record). Findings for the core / start-up owners. None of them is in the Require closure of the files below
(lib/B YB1v YB1w YE34 YF0l YF0m YF0x YE2y and what they Require: 119 modules, 10 of them under lib/B):

1. lib/B/YD25.v:536 (rs_zero_shadow, :531): `tauto` finds no case. The lemma states the zero-shadow range (0xa8fc0,
   0x5ded38 - 0xa8fc0) (:532); the start-up's Tfib_zero_shadow (lib/B/YF0m.v:3112) has (0xa8fa0, 0x5ded38 - 0xa8fa0).
2. lib/B/YD1o.v:102 (bss_shadow_facts, :89): `lia` fails (`No applicable tactic`) on the .bss zero-shadow range
   (0x5f2e60, 0x616000 - 0x5f2e60). That range is in Tfib_zero_shadow.
3. lib/B/TransportDriverB.v:19 Requires lib.B YK09 YA0c YA0e YA01 YA02. Those modules are only in lib/Reusable, so rocq
   dep warns 5 times in each build of this unit since the merge (also in build-20261031T111520Z.log and
   counted-build-lines.txt), and the file cannot compile as it is.
4. After 1 and 2 failed, 4 more compiles (YFgk, YFf8, YFj6, YFh0) ended with `exit -7` (a signal), and YD1j, YF0q,
   YF0w and TransportDriverB were not built. This build does not show whether these files compile.

On the core of record: YD25.v:532 states the range from 0xa8fa0 (changed by 4d8cde586af); YD1o.v (bss_shadow_facts,
:89) bounds its consumer by 0x5f2e80, and TransportDriverB.v Requires those five modules from lib.Reusable (:20), so
rocq dep warns no more (the builds of record above show none of these warnings). The message of 2d48500794d describes
these two changes.

### The interim build (from commit f9158444652; clone <CLONE>, VM <VM>)

    cb clone libdiginet/fuzz_transport <CLONE> f179db1ca46; the clone fast-forwarded to f9158444652     (cb-clone.log)
    CACHE=dune VM=<VM> MEM=24g cb build <CLONE> $(cat targets.txt)                                      (cb-build-dune-1.log)
    CACHE=none VM=<VM> MEM=24g cb build --fresh <CLONE> $(cat targets.txt)                              (cb-build-none-1.log)

(target paths in full: proofs/libdiginet/fuzz_transport/lib/B/Rt/...; the 15 files of the table.) The VM's load
average before the builds was 3.8 (88 cores).

- dune: build-20261031T111520Z.log, rc=0 wall=623, 15 targets compiled, 0 restored from the cache, 0 failed, vo check
  0 failed; 4 PINNED.
- counted, CACHE=none --fresh: the workspace was made again from base f6acfcb0c1b8, so make compiles every target and
  every core file it needs that differs from the base. counted-build-lines.txt has the log's header to .Makefile.d,
  every `.vo (real` line, the vo check after make, and rc. The whole log is build-20261031T112618Z.log (sha256
  b36a5ca3016d; internal record). rc=0 wall=768, 80 files compiled, 0 failed: the 15 targets and 65 core files
  (lib/B YB1q YB1v YB1w YE20 YE2y YE34 YF0l YF0m YF0x YImgTop, 54 lib/Reusable files, lib/Rt/StackMallocRawDef). vo
  check before and after make: 0 failed. 4 PINNED (facts f6acfcb0c1b8). Each target's own `.vo (real` line is in
  counted-build-lines.txt.

No relocation fix was needed in the .v files: every file compiled as written. The one fix was in the write tools
(class1cmp.py, above). It was found before the build, by alreloc's refusal. No gap was found in the core or the
start-up within the closure of these files. The four findings above are outside that closure.
