# fuzz_transport fake-stack classes 0-5, both images, on the port2 pins: the relocation records and the image-A and image-B builds

Proves no function (kind: measurement). Each class is a relocation of a released donor's contract. Each class directory
holds its own scripts, the rule-24 lookup, BYTECMP-port2.md, out-port2/ (the dry run), out-port2-write/ (the image-A
write of record, for the image-A classes) and out-port2-write-B/ (the image-B write, for the image-B classes). build-A/
holds the image-A build (BUILD-A.md), build-B/ the image-B build (BUILD-B.md). MANIFEST names every file of this
directory with its sha256 and its role.

Pins: fuzz_transport.asan e89be137db17 (twin 86efc3a80314), fuzz_transport.asan-ubsan 41113a03c82f (twin e217cb0a84f1).

| class | image(s) | donor (released) | donor files | dir |
|---|---|---|---|---|
| 0 | A, B | libreac/fuzz_ctrl | Rt/StackMalloc0Tbl.v, StackMalloc0.v, StackRawKept.v | class0/ |
| 1 | A, B | libreac/fuzz_ctrl | Rt/StackMalloc1Tbl.v, StackMalloc1.v, StackRawKept.v | class1/ |
| 2 | A, B | libreac/fuzz_ctrl | Rt/StackMalloc2Tbl.v, StackMalloc2.v | class2/ |
| 3 | B | plugin-hostd/fuzz_command | B/Rt/RtSM3T.v, RtSM3.v | class3/ |
| 4 | A | libreac/fuzz_grant | A/Rt/StackMalloc4Tbl.v, StackMalloc4.v, A/AF0r.v (its code table) | class4/ |
| 5 | A, B | plugin-hostd/fuzz_command | Rt/RtSM5T.v, RtSM5.v, RtSF5.v, RtSMxA.v, RtStack.v | class5/ |

Image A uses classes 0, 1, 2, 4, 5; image B uses 0, 1, 2, 3, 5.

Every (class, image) pair: every walked range paired and compared with strictcmp3 (EQUAL or EQUAL-mod-pcrel; 0 real, 0
differing targets in the walked words), the donor-against-itself control moves 0 values, one planted word is caught, alreloc
a5c53bb2bed4 --dry reports 0 UNMAPPED and 0 KEPT-ADDR, and checkrep finds 0 wrong rows. The resolve lines that move a value
(the MemToShadow copy and the .got / TLS cells) agree across donors.

## Image A: written and built on the image-A core of record (build-A/BUILD-A.md)

On the image-A core 9f022aeb9a21 (merged; record TransportSyms), classes 0, 1, 2, 4, 5 were written for image A by
their own scripts (--write, IMAGES=A where the script runs both images; outputs in each class's out-port2-write/), with
RtSM1T.v (class5/run-c1.sh; outputs in class5/out-port2-write/RtSM1T/) and the image-free copies
lib/Rt/StackMallocRawDef.v, lib/Reusable/StackFreeDef.v, StackFreeRaw.v (class1/run.sh), FCiface.v and YF0v.v
(class5/copy.sh): 21 files under lib/. Every write: 0 UNMAPPED, 0 KEPT-ADDR, 0 wrong rows. cb build from the write
commit 37b85428a20b: dune rc=0 (21 compiled) and the counted CACHE=none build rc=0 (80 files compiled, 4 PINNED); no
relocation fix and no core gap. Print Assumptions of the six contracts (ctrl_stack_malloc0 / 1 / 2,
stack_malloc4_contract, cmd_stack_malloc5_contract, cmd_stack_free5_contract): Rocq primitives and
functional_extensionality_dep only. be55a2f7f0ae adds lib/A/Prog/TransportRtCg.v and the bridge lib/A/Rt/RtSF5Cg.v
(stack_free5_realizes, from cmd_stack_free5_contract): dune rc=0 and the counted CACHE=none build rc=0 (4 PINNED), the
same axioms (build-A/BUILD-A.md, "The class-5 release bridge").

## Image B: written and built on the image-B core of record (build-B/BUILD-B.md)

Classes 0, 1, 2, 3, 5 were written for image B by their own scripts (--write, IMAGES=B where the script runs both
images, RECORD_B=TransportSyms; outputs in each class's out-port2-write-B/), with RtSM1T.v (class5/run-c1.sh,
IMAGES=B; outputs in class5/out-port2-write-B/RtSM1T/): 15 files under lib/B/Rt/, written (f9158444652) on the
interim image-B core 57e14e8205e and the image-B start-up 9cbb0cb6647 on the new pins (record TransportSyms,
lib/B/YF0m.v). They use the image-free files that image A copied; no image-free file was written again.
class0/bpaths.py Requires fuzz_ctrl's image-B core modules from this unit's lib/B. Every write: 0 UNMAPPED, 0
KEPT-ADDR, 0 wrong rows, and the compare, resolve and checkrep files are the dry runs'. lib/B/Rt/RtSF5CgB.v
(stack_free5_realizes_B) bridges the class-5 release contract to the callee text the image-B walks assume, as
lib/A/Rt/RtSF5Cg.v does on image A. On the image-B core of record a83315552115 (merged; the start-up files unchanged)
the cb build from 56be9351a30 of the 15 files and the bridge: dune rc=0 (16 compiled) and the counted CACHE=none
--fresh build rc=0 (100 files compiled, 4 PINNED); no relocation fix in a .v file and no gap in the files' Require
closure. Print Assumptions of the six contracts (ctrl_stack_malloc0 / 1 / 2, cmd_stack_malloc3_contract,
cmd_stack_malloc5_contract, cmd_stack_free5_contract) and of stack_free5_realizes_B: Rocq primitives and
functional_extensionality_dep only, the image-A outputs byte for byte. The image-B integration line b40685a42a62 (core
run of record r16) was merged after (98fec74a3b5): it changes none of these files, the counted build of the 16 files on
it has rc=0 (100 files compiled, 4 PINNED), and the seven outputs are the same. The first build, on the interim core,
and its core findings are the last section of BUILD-B.md.

## For the write and the build

- Record names: image A TransportSyms; image B TransportSyms (asyms value YD2l.TransportB).
- Files that carry no image numeral and are copied with module paths only: lib/Rt/StackMallocRawDef.v,
  lib/Reusable/StackFreeDef.v, lib/Reusable/StackFreeRaw.v (classes 0-2), lib/Reusable/FCiface.v and lib/Reusable/YF0v.v
  (class 5 / 3).
- Donor layouts differ: fuzz_ctrl keeps its image-B core under lib/Reusable (YB1v ...), fuzz_command under lib/B; module paths
  are mapped to transport's core layout at write time (image B: class0/bpaths.py moves the Require of fuzz_ctrl's six core
  modules to lib/B). RtSF5.v Requires the donor's class-1 walk RtSM1T for three lemmas; class5/run-c1.sh relocates it
  with the two absent class bodies removed from its table (image A: 3, 7; image B: 4, 7).

## Running the scripts, and the rerun of class 3

Every script takes the comparison kit directory as KIT (cmpkit 86da41d3ef68; inputs/cmpkit-86da41d3ef68/ of the
internal record below) and checks its SHA256SUMS and its kit id before anything else. The other arguments are the ones
each script's header and its class's BYTECMP-port2.md name (WT, HUB, the donor image directory, TARGET_DIR, ALRELOC);
class1/rule24/screen.py reads HUB, AGENTS, LIBREAC_V190, CGIF_BIN, CGIF_TWINS and PINS from the environment.

The dry run of class 3 was run again from this directory, on the run of record's target directory:

    KIT=<kit> OUT=<out> sh class3/run.sh <WT> <HUB> <AGENTS> <WORK>/target <ALRELOC_DIR>/alreloc.py.frozen-a5c53bb2bed4ad03

rc=0. Of its 45 output files, 42 are byte for byte the files of class3/out-port2/ (resolve-B.txt, class3-B.tsv,
class3-B.txt, checkrep-B.txt, every cmp-*/ and ctl-*/ file, the twins and control logs), and 3 (alreloc-B.out and the two
report/ tables, which name the images, the worktree and OUT) are equal after the token map below; its stdout is
class3/out-port2/run.log after the token map. The rerun's outputs, its command and the compare script are
runs/rerun-class3/ of the internal record (its result: compare.txt (sha256 573fe7ce96fb; internal record)).

## Tokens

The records here name host paths, workspace and VM names and work-item names by these tokens (98 files); every other
byte is as the run wrote it. The internal record holds each file as committed at 5b9b619a45c5, and the map
(tokenise-f753d40c619d.py, sha256 f753d40c619d; internal record); the build outputs of be55a2f7f0ae (build-A/*-cg.*,
cb-build-none-pa.log, pa-build-lines.txt, build-20261031T093542Z.log) were tokenised by that map, and their originals
are in the internal record too (README.md (sha256 b4ae41d8bec5; internal record), "Added for the class-5 release
bridge build").

The image-B outputs (each class's out-port2-write-B/ and build-B/) were tokenised by the same map with this row's
image-B worktree, clone and scratch directory added to it (tokenise.py, sha256 09de84b09ff4; internal record). On the
image-A originals that map gives each of the 78 tokens-only shipped files byte for byte. The originals of the
image-B files it changed are in the internal record (README.md, "Added for the image-B write and build").

| token | what it stands for |
|---|---|
| `<WT>` | the unit worktree of the run (WT) |
| `<OUT>` | the run's output directory (OUT) |
| `<WORK>` | the run's scratch directory; TARGET_DIR is `<WORK>/target` (links bin/ and unstripped/fuzz_transport/ to the port2 pins) |
| `<AGENTS>` | the root of the pipeline image stores: `<AGENTS>/<pipeline>/<project>/bin/<unit>/` and `unstripped/<unit>/` |
| `<LIBREAC_V190>` | the image store of libreac v1.9.0 (fuzz_ctrl, fuzz_pcap) |
| `<CGIF_BIN>`, `<CGIF_TWINS>` | the cgif pins and their unstripped twins |
| `<PINS>` | fuzz_transport's port2 pins and their unstripped twins |
| `<ALRELOC_DIR>` | the directory of alreloc.py.frozen-a5c53bb2bed4ad03 and its align/keep-numerals.txt |
| `<HUB>` | the git hub |
| `<OWS>`, `<WS_CACHE>`, `<VM_TOOL>`, `ws-cache`, `vm-tool` | the build kit's workspace script, workspace cache and VM tool |
| `<VM>` | the build VM |
| `<VM_WS>`, `<VM_DCO>`, `<VM_DCO_LOGS>`, `<VM_DUNE_CACHE>`, `<VM_OLD>` | on the VM: the cb workspace, the dune checkout, its logs, the dune cache, the directory of old workspaces |
| `<CLONE>`, `<CLONE_BRANCH>`, `<CLONE_LOGS>` | the cb clone of the write commit, its branch and its local log directory |
| `<WS_BUCKET>` | the storage bucket of the base workspaces |
| `<CHECKER_IMAGE>` | the checker image (its sha256 is kept) |
| `<COQLIB>` | the Rocq library directory of the checker image |
| `<internal branch>`, `<internal path>`, `<worker>` | an internal branch, an internal path and a work-item name, in text the records quote (donor notices, git grep lines) |

## Changes from the files as run

- The slice moved here from provenance/evidence/class0/ ... class5/ and the build directory (now build-A/); this file was
  the index beside them.
- The comparison kit copies (tools/cmpkit-86da41d3ef68/ of classes 0, 1, 3 and 5; tools/cmpkit-4bbd3a74be89/ of class 5)
  are not shipped: their files name host paths and work items, and a kit's id is the sha256 of its SHA256SUMS, so they
  cannot be rewritten. Every script takes the kit directory as KIT (it was the copy beside the script) and makes the same
  checks. The BYTECMP records still say where the run read its copy.
- class5/run-c1.sh and class5/class1cmp.py, the RtSM1T step of the write, moved here from the class-5 scratch directory;
  KIT replaces C5DIR for the kit, and run-c1.sh uses the checkrep.py beside it.
- class1/rule24/screen.py reads the hub and the image stores from the environment (they were host path constants).
- build-A/counted-build-lines.txt holds the selected lines of the counted build's log: its header, every `.vo (real` line,
  the vo check after make, and rc. build-A/PrintAssumptionsFakeStackA.v and class5/strictcmp*-oldpins.out were renamed
  (their old names named a work item).
- Not shipped: the class-5 scratch directory but the RtSM1T step (an interim image-A write and build of class 5 on an
  interim core, not the build of record).
- The tokens above.
- Image B: the write outputs were tokenised before their commit (f9158444652), so no commit holds their originals; the
  internal record does. build-B/counted-build-lines.txt, counted-build-lines-rec.txt, counted-build-lines-merge.txt
  and core-build-lines.txt hold selected lines of four build logs (BUILD-B.md); the whole logs are in the internal
  record. build-B/regress-c1-A-*.log are the stdout of two image-A runs of class5/run-c1.sh made to check its changes
  (their outputs are in the internal record).

## Internal record

The internal records ref libdiginet-fuzz_transport-fakestack. Its index files: SHA256SUMS (sha256 e3e508d23920; internal
record), which lists every other file of the record with its sha256; README.md (sha256 b4ae41d8bec5; internal record);
FILEMAP.tsv (sha256 236f174000d9; internal record), each file of this slice as committed at 5b9b619a45c5, each
original of the bridge build outputs and each original of an image-B file shipped here in another form: its path here,
or not shipped, and its change; PRESERVED-COMMITS.tsv (sha256 19c32a06098f; internal record), the commits this slice
names that the released history does not hold, each reachable from the ref's tip. It also holds evidence-5b9b619a45c5/
(every file of this slice as committed at 5b9b619a45c5, verbatim), the originals of the bridge build outputs,
evidence-image-B/ (the originals of the image-B files), the kits (inputs/cmpkit-86da41d3ef68/: SHA256SUMS (sha256
86da41d3ef68; internal record) and the nine files it lists; inputs/cmpkit-4bbd3a74be89/: SHA256SUMS (sha256
4bbd3a74be89; internal record)), tokenise.py, runs/rerun-class3/ and the two image-A run-c1.sh runs
(runs/regress-c1-A-images/, runs/regress-c1-A-decimal/).
