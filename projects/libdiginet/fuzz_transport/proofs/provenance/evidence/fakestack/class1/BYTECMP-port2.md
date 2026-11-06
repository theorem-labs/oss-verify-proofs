# fuzz_transport fake-stack class 1 on the port2 pins: the walked code compared with the donor's, by cmpkit 86da41d3ef68

Proves no function (kind: measurement). The method is class5/'s (BYTECMP-port2.md there), made class- and
donor-generic: run.sh, clscmp.py (class5cmp.py with the donor, its tables, its files and its model constants as
arguments) and checkrep.py (class5/checkrep.py unchanged, sha256 20aee082fef7ac1d...). class2/ runs the same three
files with its own donor.conf and model.txt.

Pins: fuzz_transport.asan e89be137db17b720 (unstripped twin 86efc3a803149811), fuzz_transport.asan-ubsan
41113a03c82fde82 (twin e217cb0a84f1e181), as projects/libdiginet/fuzz_transport/harness.yaml pins them on this branch.

Donor: libreac/fuzz_ctrl at origin/ossv/recipes 2fceb489f4aa (the last recipes commit with the proofs/<P>/<U>/lib
layout alreloc reads; every file used has the same blob at the recipes tip 9b0ac6f0e678). Images: fuzz_ctrl.asan
aac16e1fe728 (twin 78efaeda1de5), fuzz_ctrl.asan-ubsan 12136677c5cf (twin ee07e2c38d94), the pins of
2fceb489f4aa:projects/libreac/fuzz_ctrl/harness.yaml (= the tip's). The contract: `ctrl_stack_malloc1 : forall fq B,
AR_laws tfibsegs B -> CtrlTSyms B -> astack_malloc_realizes (fx := fq) tfibsegs B 1` (lib/A/Rt/StackMalloc1.v:535,
lib/B/Rt/StackMalloc1.v:535).

Files (donor.conf): per image I, lib/I/Rt/StackMalloc1Tbl.v (the code table fs_ranges and every image value),
lib/I/Rt/StackMalloc1.v (0 body numerals >= 0x10000; header only), lib/I/Rt/StackRawKept.v (0 numerals; it is the same
blob 0127a5ae165b on both images); and three image-free files they Require, copied with module paths only:
lib/Rt/StackMallocRawDef.v, lib/Reusable/StackFreeDef.v, lib/Reusable/StackFreeRaw.v (run.sh checks each holds no
numeral >= 0x10000: 0 / 0 / 0). Class 2 Requires StackRawKept.v and the three copies too; they are relocated here only.

## Donor (rule 24: look up, compare, then choose)

Lookup (rule24/lookup.sh, outputs beside it): the released set origin/ossv/recipes 9b0ac6f0e678, path-scoped per unit
(projects/<P>/<U>/proofs, 89 units), one git grep at a time: grep-stmt.txt (a statement `astack_malloc_realizes <segs>
<B> 1|2` or a `stack_malloc{1,2}_contract`), grep-decl.txt (every Theorem / Lemma / Corollary named for class 1 / 2,
which also finds statements split over lines, e.g. fuzz_ctrl's), files-sm12.txt (StackMalloc1/2, SM1/2 files).
Units that state `astack_malloc_realizes` at class 1 (the predicate the transport walks take): cgif_file_fuzzer,
cgif_rgb_fuzzer, fuzz_ctrl, fuzz_disco, fuzz_grant, fuzz_knock, fuzz_pcap, fuzz_scene, fuzz_command, fuzz_pin, fuzz_uci;
the other hits state other predicates (`stack_malloc_contract RTA 1`, `astack_malloc_realizes_x`, `astack_mallocA_stmt`,
`smU_stmt`, ...) and are not donors of this statement.

Compare (rule24/screen.py, screen.out, one directory per candidate under rule24/screen/): every candidate's table at the
same recipes commit, whose pinned image is on this box (all but cgif_rgb_fuzzer: no file of its pins 0d102754e9d2 /
ed3b5ad58f4b in the pipeline stores, <internal path> or its delivery directories), compared range by range and whole function
by whole function with clscmp.py against fuzz_transport's image of the same build. Counts are differing words; in every
PASS they are pc-relative only (0 real, 0 unmeasured). "common" counts the 8 functions every candidate walks (the class
body and its 7 helpers).

| candidate (table) | image | verdict | all walked: range / whole fn | common 8: range / whole fn |
|---|---|---|---|---|
| fuzz_ctrl A/Rt/StackMalloc1Tbl.v | A | PASS | **38 / 55** | 38 / 55 |
| fuzz_disco A/AF0r.v | A | PASS | 46 / 289 | 38 / 52 |
| fuzz_grant A/Rt/AF0r.v | A | PASS | 62 / 416 | 38 / 59 |
| fuzz_knock A/AF0r.v | A | PASS | 44 / 438 | 44 / 68 |
| fuzz_pcap A/AF0r.v | A | PASS | 49 / 388 | 41 / 64 |
| fuzz_scene A/AF0r.v | A | PASS | 50 / 443 | 41 / 64 |
| cgif_file_fuzzer A/AF0r.v | A | PASS | 51 / 421 | 42 / 65 |
| fuzz_pin A/AF0r.v | A | PASS | 41 / 386 | 41 / 64 |
| fuzz_uci A/Rt/AF0r.v | A | PASS | 44 / 438 | 44 / 68 |
| fuzz_command A/Rt/RtSM1T.v | A | FAIL: lists __asan_stack_malloc_3, _7 (absent in transport A) | 87 / 504 | 36 / 60 |
| fuzz_ctrl B/Rt/StackMalloc1Tbl.v | B | PASS | **40 / 54** | 40 / 54 |
| fuzz_disco Reusable/YF0r.v | B | PASS | 48 / 281 | 40 / 53 |
| fuzz_knock AU/YF0r.v | B | PASS | 44 / 438 | 44 / 68 |
| fuzz_pin AU/YF0r.v | B | PASS | 43 / 390 | 43 / 66 |
| fuzz_uci B/Rt/YF0r.v | B | PASS | 44 / 438 | 44 / 68 |
| fuzz_scene AU/YF0r.v | B | PASS | 50 / 443 | 41 / 64 |
| fuzz_pcap Reusable/YF0r.v | B | PASS | 51 / 387 | 43 / 66 |
| cgif_file_fuzzer YF0r.v | B | PASS | 53 / 423 | 44 / 67 |
| fuzz_grant B/Rt/YF0r.v | B | FAIL: lists __asan_stack_malloc_4 (absent in transport B) | 56 / 364 | 40 / 59 |
| fuzz_command B/Rt/RtSM1T.v | B | FAIL: lists __asan_stack_malloc_4, _7 (absent in transport B) | 84 / 501 | 34 / 58 |

Choice: fuzz_ctrl on both images. Of the candidates that relocate whole, it has the fewest differing words over the
code its walk steps through (A 38, B 40) and over the whole functions holding it (A 55, B 54); on the 8 common
functions it ties for the fewest walked differing words (fuzz_disco and fuzz_grant also 38 on A; fuzz_disco 40 on B).
fuzz_disco's 3 / 1 fewer whole-function words on the common set lie outside the walked words, while every other
candidate also walks 2 words of RegisterCommonFlags, a function whose whole compare has 220-370 differing words and 1
differing target (it passes only on the 2 walked words): fuzz_ctrl walks no such function, so every function it walks
is clean as a whole function. On image B fuzz_ctrl's __asan_stack_malloc_1 is at the address of transport's (0x3d868),
so the probe points do not move. Its files are at lib/A/Rt and lib/B/Rt, where transport's layout keeps runtime walks.

## Command

    run.sh WT HUB DONOR_DIR TARGET_DIR alreloc.py.frozen-a5c53bb2bed4ad03      (out-port2/run.log)

DONOR_DIR / TARGET_DIR: directories of symlinks bin/<u>/<u>.<build> and unstripped/<u>/<u>.<build> to
<LIBREAC_V190>/{s,x/unstripped}/fuzz_ctrl/ and
<PINS>/{stripped,unstripped}/; run.sh checks every image against its
pin and the kit copy against its SHA256SUMS (9 files OK, kit id 86da41d3ef68).

Result, both images: twins proved (2 pairs each); 8 ranges paired and compared, PASS; control self PASS with 0 values
moved; the planted `or` caught (A and B: the `and` at __asan_stack_malloc_1 + 0x94, word 0x00e678b3 -> 0x00e668b3;
1 FAIL line, `range DIFFERENT (8, 1, 0)`); alreloc --dry on 3 files: 0 UNMAPPED, 0 KEPT-ADDR (A 41, B 42 numerals);
checkrep 0 wrong rows. No value is moved by its offset inside a symbol (0 `symbol` rows).

## Every range (out-port2/class1-A.tsv, class1-B.tsv)

Every range starts at its function's entry (offset +0x0). Columns: walked words; range verdict (pcrel, real,
unmeasured, differing targets); whole function verdict (pcrel, real, unmeasured) differing targets.

| function | words | donor A -> transport A | range A | whole fn A | donor B -> transport B | range B | whole fn B |
|---|---|---|---|---|---|---|---|
| __asan_stack_malloc_1 | 100 | 0x3d72c -> 0x3d80c | EQUAL-mod-pcrel (8, 0, 0, 0) | EQUAL-mod-pcrel (8, 0, 0) 0 | 0x3d868 -> 0x3d868 | EQUAL-mod-pcrel (8, 0, 0, 0) | EQUAL-mod-pcrel (8, 0, 0) 0 |
| __interceptor___tls_get_addr | 31 | 0x472d8 -> 0x47660 | EQUAL-mod-pcrel (2, 0, 0, 0) | EQUAL-mod-pcrel (2, 0, 0) 0 | 0x47414 -> 0x4769c | EQUAL-mod-pcrel (2, 0, 0, 0) | EQUAL-mod-pcrel (2, 0, 0) 0 |
| __tls_get_addr | 9 | 0x98800 -> 0x9de04 | EQUAL | EQUAL 0 | 0x99624 -> 0x9da60 | EQUAL | EQUAL 0 |
| __asan::GetCurrentThread | 8 | 0x5c838 -> 0x5cbc0 | EQUAL | EQUAL 0 | 0x5c974 -> 0x5cbfc | EQUAL | EQUAL 0 |
| __asan::AsanTSDGet | 6 | 0x55384 -> 0x5570c | EQUAL-mod-pcrel (3, 0, 0, 0) | EQUAL-mod-pcrel (6, 0, 0) 0 | 0x554c0 -> 0x55748 | EQUAL-mod-pcrel (3, 0, 0, 0) | EQUAL-mod-pcrel (6, 0, 0) 0 |
| __pthread_getspecific (tss_get) | 7 | 0x998b4 -> 0x9eeb8 | EQUAL | EQUAL 0 | 0x9a6d8 -> 0x9eb14 | EQUAL | EQUAL 0 |
| __sanitizer::DTLS_on_tls_get_addr | 140 | 0x69f4c -> 0x6a2d4 | EQUAL-mod-pcrel (16, 0, 0, 0) | EQUAL-mod-pcrel (27, 0, 0) 0 | 0x6a088 -> 0x6a310 | EQUAL-mod-pcrel (18, 0, 0, 0) | EQUAL-mod-pcrel (26, 0, 0) 0 |
| __asan::MemToShadow (the copy the body calls) | 28 | 0x3dc3c -> 0x3dfc4 | 1 unmeasured: the auipc at + 0x6c is consumed after the 28 words | EQUAL-mod-pcrel (12, 0, 0) 0 | 0x3dd78 -> 0x3e000 | the same | EQUAL-mod-pcrel (12, 0, 0) 0 |

MemToShadow has several copies; it is paired by the `jal` at the same word of __asan_stack_malloc_1 on both sides
(paired_by `call`); every other range by its function's name. strictcmp3 reports no lui-built target in any of these
functions.

## Resolve lines (out-port2/resolve-A.txt, resolve-B.txt)

Moved, each taken from the paired instruction of a compared function (alreloc's `gap` rule maps a .got cell by its
offset in .got, and its symbol rule cannot place a local static with several copies):

- A: 0x3dc3c -> 0x3dfc4 (MemToShadow's copy, StackMalloc1Tbl.v:61); the .got / TLS cells 0x9fac0 -> 0xa4080 (:90, :91),
  0x9fb20 -> 0xa40e0 (:91), 0xa07b0 -> 0xa4d70 (:90), 0xa07c0 -> 0xa4d80 (:92).
- B: 0x3dd78 -> 0x3e000 (:61); 0xa08e0 -> 0xa3ce0 (:90, :91), 0xa0940 -> 0xa3d40 (:91), 0xa15d0 -> 0xa49d0 (:90),
  0xa15e0 -> 0xa49e0 (:92).

These are the values class5/'s resolve lines take for the same cells and the same MemToShadow copy on these pins
(class5/BYTECMP-port2.md), found here independently from a different donor.

Kept: the model constants of model.txt, 0x109000 (FS_FROFF, StackMalloc1Tbl.v:38), 1085440 (:375, :384), 1048576
(1 << kStackSizeLog, :463), which lie in the image range (internal_alloc_placeholder + 0x5f580 / + 0x56580 of the donor)
and alreloc would otherwise move as addresses; and every numeral >= 0x10000 of the inherited header lines
(StackMalloc1Tbl.v:4, :6; StackMalloc1.v:4-6), which run.sh --write restores byte for byte.

## alreloc and checkrep (out-port2/alreloc-*.out, checkrep-*.txt, report/)

Per image: StackMalloc1Tbl.v 15 symbol + 15 / 16 resolved, StackMalloc1.v 5 resolved, StackRawKept.v nothing; 0 gap,
0 KEPT-ADDR, 0 UNMAPPED. checkrep rows by rule: A resolve 20, FUNC entry 8, same-code function 5, OBJECT start 2,
not an address 4, SIZES_KEEP 2 (B: resolve 21, the rest the same); PASS: 0 wrong rows. The kept values that lie in a
donor symbol are the instruction words 0x0007c283 and 0x00160613 (:227-228, :233-234; `not an address`).

Values moved inside a symbol (each checked by checkrep: the same symbol + offset on both sides), all addresses:
- FUNC entries: the 8 range starts (:61) and FS_ENTRY (:29);
- same-code function (interior pcs of __asan_stack_malloc_1, whose code is compared above): FS_LOOP + 0x94, FS_FOUND
  + 0x10c, FS_SDFF + 0x138, FS_SDSH + 0x154 (:30-33) and FS_FOUND's bit-vector literal (decimal, :294; A 251960 ->
  252184, B 252276 unchanged), the probe points of the walk;
- OBJECT starts: __interception::real___tls_get_addr (A 0xa1870 -> 0xa5e30, B 0xa2690 -> 0xa5a90) and
  __asan::tsd_key_inited (A 0xa80e0 -> 0xac260, B 0xa8f20 -> 0xabee0) (:90, :92), cells the walk reads.
On image B the stack_malloc_1 entry and its interior pcs keep their value (identity: the same address in both images).

## The --write path (out-port2/write-test.log, write-test.diff)

Run on a scratch worktree (only projects/libdiginet/fuzz_transport/harness.yaml and an empty lib/) with RECORD_A =
TestASyms, RECORD_B = TestBSyms: alreloc wrote the 6 files, run.sh restored the headers (6 lines; StackRawKept.v has
none), renamed CtrlTSyms (4 in each StackMalloc1.v) and added one notice line per file, and copied the 3 image-free
files (5 / 5 / 6 module paths). write-test.diff is every written file against the donor: module paths, the record name,
the notice line and the numerals above; no other line differs.

## What the relocated files Require (for --write and the build)

- The record of each image's core: RECORD_A / RECORD_B replace CtrlTSyms (`Hypothesis TB`, and the three theorems'
  premise).
- lib.A (image A core): AB1v AE34 AF0l AF0m AF0x AE2y.
- lib.Reusable (the ASan engine): YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0q YG0t YG0v YCe5 YK04 YK18 YK0j YA0i YA0n YA0o
  YA0p YA0q (none on this branch's lib/Reusable yet), and YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0s YK0n YP0n YK1d
  YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01 YN3v YN32 YI04 YM05 YZ00 (modules of these names are in
  this branch's lib/Reusable; their text is not compared here).
- Image B's core modules YB1v YE34 YF0l YF0m YF0x YE2y are Required from lib.Reusable, where fuzz_ctrl keeps them; where
  transport's image-B core puts them (the decode precedent: lib/B, with YCe5) their module path is renamed at --write.
- Copied here: lib/Rt/StackMallocRawDef.v, lib/Reusable/StackFreeDef.v, lib/Reusable/StackFreeRaw.v; relocated here:
  lib/{A,B}/Rt/StackRawKept.v.

## What is not done here

The relocated files are not written on this branch: `RECORD_A=... RECORD_B=... run.sh ... --write` writes them once
this unit's image cores (their record names and module paths above) exist on these pins; then cb builds them.
