# fuzz_transport fake-stack class 2 on the port2 pins: the walked code compared with the donor's, by cmpkit 86da41d3ef68

Proves no function (kind: measurement). The method is class5/'s, made class- and donor-generic in ../class1/ (run.sh,
clscmp.py, checkrep.py, the kit copy tools/cmpkit-86da41d3ef68/); this directory holds class 2's donor.conf, model.txt,
a run.sh that runs ../class1/run.sh with them, and the outputs (out-port2/).

Pins: fuzz_transport.asan e89be137db17b720 (unstripped twin 86efc3a803149811), fuzz_transport.asan-ubsan
41113a03c82fde82 (twin e217cb0a84f1e181), as projects/libdiginet/fuzz_transport/harness.yaml pins them on this branch.

Donor: libreac/fuzz_ctrl at origin/ossv/recipes 2fceb489f4aa (every file used has the same blob at the recipes tip
9b0ac6f0e678). Images: fuzz_ctrl.asan aac16e1fe728 (twin 78efaeda1de5), fuzz_ctrl.asan-ubsan 12136677c5cf (twin
ee07e2c38d94). The contract: `ctrl_stack_malloc2 : forall fq B, AR_laws tfibsegs B -> CtrlTSyms B ->
astack_malloc_realizes (fx := fq) tfibsegs B 2` (lib/A/Rt/StackMalloc2.v:535, lib/B/Rt/StackMalloc2.v:535).

Files (donor.conf): per image I, lib/I/Rt/StackMalloc2Tbl.v (the code table fs_ranges and every image value) and
lib/I/Rt/StackMalloc2.v (0 body numerals >= 0x10000; header only). StackMalloc2.v also Requires lib/I/Rt/StackRawKept.v
and the image-free lib/Rt/StackMallocRawDef.v (StackRawKept.v Requires lib/Reusable/StackFreeDef.v and StackFreeRaw.v):
class 1 relocates and copies those (../class1/BYTECMP-port2.md), so they are not handled twice.

## Donor (rule 24)

The lookup and the compare are class 1's (../class1/rule24/: lookup.sh and its outputs, screen.py, screen.out, one
directory per candidate under screen/). Units that state `astack_malloc_realizes` at class 2: cgif_file_fuzzer,
cgif_rgb_fuzzer, fuzz_ctrl, fuzz_disco, fuzz_grant, fuzz_scene (grep-stmt.txt, grep-decl.txt). Each class-2 contract
walks the code table of its own unit: fuzz_ctrl StackMalloc2Tbl.v; AF0u.v / YF0u.v through AF0t.v / YF0t.v, whose
table is AF0r.v / YF0r.v's tbl_fs. cgif_rgb_fuzzer is not screened: no file of its pins on this box.

| candidate (table) | image | verdict | all walked: range / whole fn | common 8: range / whole fn |
|---|---|---|---|---|
| fuzz_ctrl A/Rt/StackMalloc2Tbl.v | A | PASS | **38 / 55** | 38 / 55 |
| fuzz_disco A/AF0r.v | A | PASS | 46 / 289 | 38 / 52 |
| fuzz_grant A/Rt/AF0r.v | A | PASS | 62 / 416 | 38 / 59 |
| fuzz_scene A/AF0r.v | A | PASS | 50 / 443 | 41 / 64 |
| cgif_file_fuzzer A/AF0r.v | A | PASS | 51 / 421 | 42 / 65 |
| fuzz_ctrl B/Rt/StackMalloc2Tbl.v | B | PASS | **40 / 54** | 40 / 54 |
| fuzz_disco Reusable/YF0r.v | B | PASS | 48 / 281 | 40 / 53 |
| fuzz_scene AU/YF0r.v | B | PASS | 50 / 443 | 41 / 64 |
| cgif_file_fuzzer YF0r.v | B | PASS | 53 / 423 | 44 / 67 |
| fuzz_grant B/Rt/YF0r.v | B | FAIL: lists __asan_stack_malloc_4 (absent in transport B) | 56 / 364 | 40 / 59 |

Choice: fuzz_ctrl on both images, for class 1's reasons (../class1/BYTECMP-port2.md, "Donor"): the fewest differing
words over the walked code and over its whole functions, a tie for the fewest walked words on the common 8, and no walk
into RegisterCommonFlags (whose whole function differs by 220-370 pc-relative words and 1 target in every other
candidate). On image B, fuzz_ctrl's __asan_stack_malloc_2 is at transport's address (0x3d9f8).

## Command

    run.sh WT HUB DONOR_DIR TARGET_DIR alreloc.py.frozen-a5c53bb2bed4ad03      (out-port2/run.log)

(the same DONOR_DIR / TARGET_DIR as class 1). Result, both images: twins proved (2 pairs each); 8 ranges paired and
compared, PASS; control self PASS with 0 values moved; the planted `or` caught (A and B: the `and` at
__asan_stack_malloc_2 + 0x94, word 0x00e678b3 -> 0x00e668b3; 1 FAIL line, `range DIFFERENT (8, 1, 0)`); alreloc --dry
on 2 files: 0 UNMAPPED, 0 KEPT-ADDR (A 42, B 43 numerals); checkrep 0 wrong rows. No value is moved by its offset
inside a symbol (0 `symbol` rows).

## Every range (out-port2/class2-A.tsv, class2-B.tsv)

Every range starts at its function's entry. Range verdict (pcrel, real, unmeasured, differing targets); whole function
verdict (pcrel, real, unmeasured) differing targets.

| function | words | donor A -> transport A | range A | whole fn A | donor B -> transport B | range B | whole fn B |
|---|---|---|---|---|---|---|---|
| __asan_stack_malloc_2 | 103 | 0x3d8bc -> 0x3d99c | EQUAL-mod-pcrel (8, 0, 0, 0) | EQUAL-mod-pcrel (8, 0, 0) 0 | 0x3d9f8 -> 0x3d9f8 | EQUAL-mod-pcrel (8, 0, 0, 0) | EQUAL-mod-pcrel (8, 0, 0) 0 |
| __interceptor___tls_get_addr | 31 | 0x472d8 -> 0x47660 | EQUAL-mod-pcrel (2, 0, 0, 0) | EQUAL-mod-pcrel (2, 0, 0) 0 | 0x47414 -> 0x4769c | EQUAL-mod-pcrel (2, 0, 0, 0) | EQUAL-mod-pcrel (2, 0, 0) 0 |
| __tls_get_addr | 9 | 0x98800 -> 0x9de04 | EQUAL | EQUAL 0 | 0x99624 -> 0x9da60 | EQUAL | EQUAL 0 |
| __asan::GetCurrentThread | 8 | 0x5c838 -> 0x5cbc0 | EQUAL | EQUAL 0 | 0x5c974 -> 0x5cbfc | EQUAL | EQUAL 0 |
| __asan::AsanTSDGet | 6 | 0x55384 -> 0x5570c | EQUAL-mod-pcrel (3, 0, 0, 0) | EQUAL-mod-pcrel (6, 0, 0) 0 | 0x554c0 -> 0x55748 | EQUAL-mod-pcrel (3, 0, 0, 0) | EQUAL-mod-pcrel (6, 0, 0) 0 |
| __pthread_getspecific (tss_get) | 7 | 0x998b4 -> 0x9eeb8 | EQUAL | EQUAL 0 | 0x9a6d8 -> 0x9eb14 | EQUAL | EQUAL 0 |
| __sanitizer::DTLS_on_tls_get_addr | 140 | 0x69f4c -> 0x6a2d4 | EQUAL-mod-pcrel (16, 0, 0, 0) | EQUAL-mod-pcrel (27, 0, 0) 0 | 0x6a088 -> 0x6a310 | EQUAL-mod-pcrel (18, 0, 0, 0) | EQUAL-mod-pcrel (26, 0, 0) 0 |
| __asan::MemToShadow (the copy the body calls) | 28 | 0x3dc3c -> 0x3dfc4 | 1 unmeasured: the auipc at + 0x6c is consumed after the 28 words | EQUAL-mod-pcrel (12, 0, 0) 0 | 0x3dd78 -> 0x3e000 | the same | EQUAL-mod-pcrel (12, 0, 0) 0 |

MemToShadow is paired by the `jal` at the same word of __asan_stack_malloc_2 on both sides; every other range by its
function's name. strictcmp3 reports no lui-built target in any of these functions.

## Resolve lines (out-port2/resolve-A.txt, resolve-B.txt)

Moved, each from the paired instruction of a compared function:

- A: 0x3dc3c -> 0x3dfc4 (MemToShadow's copy, StackMalloc2Tbl.v:61); 0x9fac0 -> 0xa4080 (:90, :91), 0x9fb20 -> 0xa40e0
  (:91), 0xa07b0 -> 0xa4d70 (:90), 0xa07c0 -> 0xa4d80 (:92).
- B: 0x3dd78 -> 0x3e000 (:61); 0xa08e0 -> 0xa3ce0 (:90, :91), 0xa0940 -> 0xa3d40 (:91), 0xa15d0 -> 0xa49d0 (:90),
  0xa15e0 -> 0xa49e0 (:92).

The same cells and MemToShadow copy as class 1's and class5/'s resolve lines on these pins.

Kept: the model constants of model.txt, 0x209000 (FS_FROFF of class 2, StackMalloc2Tbl.v:38), 2134016 (:375, :384),
1048576 (:463); and every numeral >= 0x10000 of the inherited header lines (StackMalloc2Tbl.v:4, :6; StackMalloc2.v:4-6),
restored byte for byte by run.sh --write.

## alreloc and checkrep (out-port2/alreloc-*.out, checkrep-*.txt, report/)

Per image: StackMalloc2Tbl.v 15 symbol + 17 / 18 resolved, StackMalloc2.v 4 resolved; 0 gap, 0 KEPT-ADDR, 0 UNMAPPED.
checkrep rows by rule: A resolve 21, FUNC entry 8, same-code function 5, OBJECT start 2, not an address 4, SIZES_KEEP 2
(B: resolve 22, the rest the same); PASS: 0 wrong rows. The kept values that lie in a donor symbol are the instruction
words 0x0007c283 and 0x00160613 (:227-228, :233-234; `not an address`).

Values moved inside a symbol (each checked by checkrep: the same symbol + offset on both sides), all addresses: the 8
range starts and FS_ENTRY (FUNC entries); FS_LOOP + 0x94, FS_FOUND + 0x10c, FS_SDFF + 0x13c, FS_SDSH + 0x158 of
__asan_stack_malloc_2 (:30-33) and FS_FOUND's bit-vector literal (:294; A 252360 -> 252584, B 252676 unchanged), the
walk's probe points; the cells __interception::real___tls_get_addr (A 0xa1870 -> 0xa5e30, B 0xa2690 -> 0xa5a90) and
__asan::tsd_key_inited (A 0xa80e0 -> 0xac260, B 0xa8f20 -> 0xabee0) (:90, :92). On image B the stack_malloc_2 entry and
its interior pcs keep their value (the same address in both images).

## The --write path (out-port2/write-test.log, write-test.diff)

On a scratch worktree with RECORD_A = TestASyms, RECORD_B = TestBSyms: alreloc wrote the 4 files, run.sh restored the
headers (6 lines), renamed CtrlTSyms (4 in each StackMalloc2.v) and added one notice line per file. write-test.diff is
every written file against the donor: module paths, the record name, the notice line and the numerals above.

## What the relocated files Require (for --write and the build)

- RECORD_A / RECORD_B in place of CtrlTSyms.
- lib/I/Rt/StackMalloc2Tbl.v (relocated here), lib/I/Rt/StackRawKept.v and lib/Rt/StackMallocRawDef.v (class 1's).
- lib.A: AB1v AE34 AF0l AF0m AF0x AE2y (image A); image B takes YB1v YE34 YF0l YF0m YF0x YE2y from lib.Reusable, where
  fuzz_ctrl keeps them (renamed at --write to where transport's image-B core puts them; the decode precedent: lib/B).
- lib.Reusable: YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0q YG0t YG0v YCe5 YK04 YK18 YA0i YA0n YA0o YA0p YA0q (none on this
  branch's lib/Reusable yet), and YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0k YK0s YK0n YP0n YK1d YP0m YP0e YP09 YP02 YP0l
  YP0k YP06 YP08 YP03 YP04 YP0g YP01 YN3v YN32 YI04 YM05 YZ00 (modules of these names are in this branch's lib/Reusable;
  their text is not compared here).

## What is not done here

The relocated files are not written on this branch: `RECORD_A=... RECORD_B=... run.sh ... --write` writes them once
this unit's image cores exist on these pins; then cb builds them.
