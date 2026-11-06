# fuzz_transport fake-stack class 0 on the port2 pins: donor chosen by rule 24, walked code compared, dry relocation

Proves no function (kind: measurement). Method of record: class5/ (run.sh, class5cmp.py, checkrep.py, BYTECMP-port2.md),
generalized here; nothing is written under lib/.

Pins (projects/libdiginet/fuzz_transport/harness.yaml of this branch): fuzz_transport.asan e89be137db17b720 (unstripped
twin 86efc3a803149811), fuzz_transport.asan-ubsan 41113a03c82fde82 (twin e217cb0a84f1e181).

Kit: cmpkit 86da41d3ef68 (copy in tools/cmpkit-86da41d3ef68/, SHA256SUMS checked by every script, kit id = first 12 hex
of sha256(SHA256SUMS)); strictcmp3 is the one compare, drvcmp proves the twins. alreloc of record a5c53bb2bed4
(alreloc.py.frozen-a5c53bb2bed4ad03).

Scripts (this directory; class4/ uses the same ones):
- smcmp.py: class5cmp.py with the donor, class, code tables, relocated files and model constants as arguments; same
  steps, kit and resolve rules. Regression: given class 5's arguments (fuzz_command at 781f46bc05cd, image A) it writes
  class5/out-port2/resolve-A.txt line for line and class5-A.tsv's columns 2-16 unchanged.
- smrun.sh: class5/run.sh driven by a configuration (class0-A.conf, class0-B.conf, ../class4/class4.conf): pins,
  twins, smcmp, the two controls, alreloc (--dry unless --write), checkrep, and with --write the header / record /
  notice step. Changes from run.sh: the planted copies are written beside the target images, not in the worktree; the
  plant takes an `and` with funct7 0 only; OUT from the environment overrides the configuration's.
- checkrep.py: class5/checkrep.py, reading every report .tsv under <IMG>/ (not only <IMG>/Rt/).
- cands.sh + closeness.py: the rule-24 compare of every released donor (below).

## Rule 24: every released donor of class 0, compared before the choice

Lookup (rule24-grep.txt): origin/ossv/recipes 9b0ac6f0e678, one path-scoped `git grep -lE
'__asan_stack_malloc_(0|4)\b|Definition CID : Z := (0|4)\.'` per released unit with an ASan proof tree (36 units),
one at a time. Files that state `astack_malloc_realizes tfibsegs B 0` (the statement fuzz_transport takes):
libreac/fuzz_{decode,ctrl,grant,identity,pcap} A and B, fuzz_disco A, plugin-hostd/fuzz_command A and B (RtSM0),
reac-pw/fuzz_pin A and AU. Not candidates: omx-clap-core/fuzz_{state,preset} FCm0s.v state
`astack_malloc_realizes_x ... ARx 0` over fs_iface (another statement); fuzz_ctrl B Prog/asan_stack_malloc_0F.v is a
footprint contract. The libdiginet frame trunk is not released (no projects/libdiginet/*/proofs/lib/{A,B}).

Every file is read at e10f488c53fc, the last origin/ossv/recipes commit with proofs/<P/H>/lib (the next first-parent
commit, 4c4e829bbe9c, moves proofs to projects/<P/H>/proofs/lib; alreloc reads only the old layout); each file read
there has the same blob at the tip (column `layout move` of rule24-0.tsv). fuzz_pin was released after the move: read
at the tip (compared only; alreloc a5c53bb2bed4 could not read it).

`cands.sh 0 HUB DONORS TARGET out-port2/rule24` (out-port2/rule24/rule24-0.tsv, cands.log; one directory and log per
candidate):

| img | donor | code table | verdict | ranges | pc-rel words walked / whole fns | resolve moves |
|---|---|---|---|---|---|---|
| A | libreac/fuzz_decode | own fs_ranges | PASS | 9 of 9 | 44 / 439 | 5 |
| A | libreac/fuzz_disco | own fs_ranges | PASS | 9 of 9 | 38 / 281 | 5 |
| A | libreac/fuzz_ctrl | own fs_ranges | PASS | 8 of 8 | 38 / 55 | 6 |
| A | libreac/fuzz_grant | A/Rt/AF0r.v (classes 0 1 2 4) | PASS | 12 of 12 | 62 / 416 | 9 |
| A | libreac/fuzz_identity | A/Rt/StackMallocTbl.v | FAIL: __asan_stack_malloc_3 not in transport A | 10 of 11 | 47 / 403 | 5 |
| A | libreac/fuzz_pcap | A/AF0r.v | PASS | 10 of 10 | 49 / 388 | 9 |
| A | plugin-hostd/fuzz_command | A/Rt/RtSM1T.v | FAIL: __asan_stack_malloc_3, _7 not in transport A | 13 of 15 | 87 / 504 | 9 |
| A | reac-pw/fuzz_pin (tip) | A/Rt/StackMallocTbl.v | PASS | 9 of 9 | 41 / 386 | 5 |
| B | libreac/fuzz_decode | own fs_ranges | PASS | 9 of 9 | 44 / 439 | 5 |
| B | libreac/fuzz_ctrl | own fs_ranges | PASS | 8 of 8 | 40 / 54 | 6 |
| B | libreac/fuzz_grant | B/Rt/YF0r.v | FAIL: __asan_stack_malloc_4 not in transport B | 11 of 12 | 56 / 364 | 9 |
| B | libreac/fuzz_identity | B/Rt/StackMallocTbl.v | FAIL: __asan_stack_malloc_4 not in transport B | 10 of 11 | 49 / 403 | 5 |
| B | libreac/fuzz_pcap | Reusable/YF0r.v | PASS | 10 of 10 | 51 / 387 | 9 |
| B | plugin-hostd/fuzz_command | B/Rt/RtSM1T.v | FAIL: __asan_stack_malloc_4, _7 not in transport B | 13 of 15 | 84 / 501 | 9 |
| B | reac-pw/fuzz_pin (tip) | AU/Rt/StackMallocTbl.v | PASS | 9 of 9 | 43 / 390 | 5 |

A FAIL is a table that lists the body of a class the transport image does not link (transport A links classes 0 1 2 4
5, B 0 1 2 3 5): it cannot be relocated whole; every range those candidates could pair compares clean. Every passing
candidate's code is the same instructions as transport's but for pc-relative offsets, so the closeness measure
(closeness.py, rule24-0-closeness.txt) is taken over what each relocation carries, the donor's own code table: the walked
words that differ by a pc-relative offset; ties broken by the whole functions those ranges lie in, first their
differing targets, then their pc-relative words.

- Image A: ctrl 38 walked, whole 0 differing targets / 55; disco 38, whole 1 / 281 (its table walks 2 words of
  RegisterCommonFlags, whose whole compare has a differing target at + 0x1218, data-differs); fuzz_pin 41; decode 44;
  pcap 49; grant 62. Chosen: **libreac/fuzz_ctrl** lib/A/Rt/StackMalloc0Tbl.v + StackMalloc0.v + StackRawKept.v at
  e10f488c53fc (last changed by 75ff9552daad; image asan aac16e1fe728 in libreac-v190 s/, twin 78efaeda1de5 in
  x/unstripped/).
- Image B: ctrl 40, whole 0 / 54; fuzz_pin 43; decode 44; pcap 51. Chosen: **libreac/fuzz_ctrl** lib/B/Rt/
  StackMalloc0Tbl.v + StackMalloc0.v + StackRawKept.v at e10f488c53fc (87c5184fb26e, 41bbb1385d8a; image asan-ubsan
  12136677c5cf in s/, twin ee07e2c38d94 in x/unstripped/; its __asan_stack_malloc_0 is at 0x3d6f4 as transport B's).

The result is the same donor on both images (ctrl's B files are its A files relocated, per their own notices); the
class-1/2 lane of this row reported (2026-10-31) the same donor, fuzz_ctrl, for classes 1 and 2 on both images.

## Command and result (out-port2/run-A.log, run-B.log)

    smrun.sh WT HUB DONORS/libreac TARGET alreloc.py.frozen-a5c53bb2bed4ad03 class0-A.conf
    smrun.sh WT HUB DONORS/libreac TARGET alreloc.py.frozen-a5c53bb2bed4ad03 class0-B.conf

TARGET holds bin/fuzz_transport/ and unstripped/fuzz_transport/ (links to the port2 pins); DONORS/libreac/{bin,
unstripped}/fuzz_ctrl/ link to libreac-v190's s/fuzz_ctrl/ and x/unstripped/fuzz_ctrl/.

| | image A (ctrl -> transport A) | image B (ctrl -> transport B) |
|---|---|---|
| twins (drvcmp) | proved, 2 pairs | proved, 2 pairs |
| ranges paired and compared | 8, PASS (0 real, 0 differing targets) | 8, PASS (0 real, 0 differing targets) |
| control self | PASS, 0 values moved | PASS, 0 values moved |
| control plant (`and` -> `or` at __asan_stack_malloc_0 + 0x84, 0x00d67833 -> 0x00d66833) | caught, 1 FAIL line | caught, 1 FAIL line |
| alreloc --dry | 0 UNMAPPED, 0 KEPT-ADDR (3 files) | 0 UNMAPPED, 0 KEPT-ADDR (3 files) |
| checkrep | 0 wrong rows; 0 values moved inside a symbol | 0 wrong rows; 0 values moved inside a symbol |

write-test-A.log / write-test-B.log: the same runs with --write into a scratch copy of the unit tree (not this
worktree), record names TransportASyms / TransportBSyms as placeholders: alreloc writes the 3 files per image with the
module paths moved to libdiginet.fuzz_transport, the header blocks come back from the donor (5 lines on A, 6 on B; none
in StackRawKept.v), CtrlTSyms is renamed 4 times in StackMalloc0.v, one notice line is added per file.

## Every range (out-port2/class0-A.tsv, class0-B.tsv)

Image A (fuzz_ctrl -> fuzz_transport.asan):

| donor range | words | function | paired by | transport | range: verdict (pc-rel) | whole function |
|---|---|---|---|---|---|---|
| 0x3d5b8 | 93 | __asan_stack_malloc_0 | name | 0x3d698 | EQUAL-mod-pcrel (8) | same, clean |
| 0x472d8 | 31 | __interceptor___tls_get_addr | name | 0x47660 | EQUAL-mod-pcrel (2) | same, clean |
| 0x98800 | 9 | __tls_get_addr | name | 0x9de04 | EQUAL | clean |
| 0x5c838 | 8 | __asan::GetCurrentThread | name | 0x5cbc0 | EQUAL | clean |
| 0x55384 | 6 | __asan::AsanTSDGet | name | 0x5570c | EQUAL-mod-pcrel (3) | EQUAL-mod-pcrel (6), clean |
| 0x998b4 | 7 | __pthread_getspecific | name | 0x9eeb8 | EQUAL | clean |
| 0x69f4c | 140 | __sanitizer::DTLS_on_tls_get_addr | name | 0x6a2d4 | EQUAL-mod-pcrel (16) | EQUAL-mod-pcrel (27), clean |
| 0x3dc3c | 28 | __asan::MemToShadow (the copy __asan_stack_malloc_0 calls) | call | 0x3dfc4 | EQUAL-mod-pcrel (9), 1 unmeasured (the auipc at + 0x6c is consumed after the 28 words) | EQUAL-mod-pcrel (12), clean |

Image B (fuzz_ctrl -> fuzz_transport.asan-ubsan):

| donor range | words | function | paired by | transport | range: verdict (pc-rel) | whole function |
|---|---|---|---|---|---|---|
| 0x3d6f4 | 93 | __asan_stack_malloc_0 | name | 0x3d6f4 | EQUAL-mod-pcrel (8) | same, clean |
| 0x47414 | 31 | __interceptor___tls_get_addr | name | 0x4769c | EQUAL-mod-pcrel (2) | same, clean |
| 0x99624 | 9 | __tls_get_addr | name | 0x9da60 | EQUAL | clean |
| 0x5c974 | 8 | __asan::GetCurrentThread | name | 0x5cbfc | EQUAL | clean |
| 0x554c0 | 6 | __asan::AsanTSDGet | name | 0x55748 | EQUAL-mod-pcrel (3) | EQUAL-mod-pcrel (6), clean |
| 0x9a6d8 | 7 | __pthread_getspecific | name | 0x9eb14 | EQUAL | clean |
| 0x6a088 | 140 | __sanitizer::DTLS_on_tls_get_addr | name | 0x6a310 | EQUAL-mod-pcrel (18) | EQUAL-mod-pcrel (26), clean |
| 0x3dd78 | 28 | __asan::MemToShadow (the copy __asan_stack_malloc_0 calls) | call | 0x3e000 | EQUAL-mod-pcrel (9), 1 unmeasured (+ 0x6c, as on A) | EQUAL-mod-pcrel (12), clean |

strictcmp3 reports no lui-built target in these functions.

## Resolve lines (out-port2/resolve-A.txt, resolve-B.txt) and why each exists

- The MemToShadow copy (a name with several copies; alreloc's symbol rule cannot place it): A StackMalloc0Tbl.v:60
  0x3dc3c -> 0x3dfc4, B StackMalloc0Tbl.v:61 0x3dd78 -> 0x3e000, each the target of the paired `jal` in
  __asan_stack_malloc_0 (the copy class 5 pairs too: A 0x3dfc4, B 0x3e000).
- .got cells the walk reads (pc-relative data targets with no symbol home; alreloc's `gap` rule maps a cell by its .got
  offset, wrong across these .got layouts), in fsA_rodata's cell_region rows: A StackMalloc0Tbl.v:89-91 0x9fac0 ->
  0xa4080, 0x9fb20 -> 0xa40e0 (the cells holding &common_flags_dont_use and &current_verbosity), 0xa07b0 -> 0xa4d70,
  0xa07c0 -> 0xa4d80 (the TLS pair holding 1 / -0x800 and 8); B StackMalloc0Tbl.v:90-92 0xa08e0 -> 0xa3ce0, 0xa0940 ->
  0xa3d40, 0xa15d0 -> 0xa49d0, 0xa15e0 -> 0xa49e0. Each value is the paired instruction's target; they are class 5's
  cells (A 0xa4080 / 0xa40e0 / 0xa4d70 / 0xa4d80, B 0xa3ce0 / 0xa3d40 / 0xa49d0 / 0xa49e0).
- Kept: the header numerals (A: StackMalloc0{,Tbl}.v:4-5; B: StackMalloc0.v:4-5, StackMalloc0Tbl.v:4-6; 0x3cda4,
  0x3d5b8, 0x3d6f4, inherited notices, byte for byte). No model constant needs a keep line: ctrl's files name the class
  constants and take TP, TSD and the thread-object cells from the core (TFIB_TP, TFIB_TSD, tfib_cell).

## Values moved inside a symbol (checkrep)

None on either image. Every moved value is a FUNC entry, a same-code function offset, an OBJECT start (real___tls_get_addr
A 0xa1870 -> 0xa5e30, B 0xa2690 -> 0xa5a90; tsd_key_inited A 0xa80e0 -> 0xac260, B 0xa8f20 -> 0xabee0), each checked
by checkrep, or a resolve line. Kept values inside a donor symbol: the probe-loop instruction words 0x0007c883 and
0x00160613 (fetch_word facts; the compare shows the same words in transport), SIZES_KEEP 1048576.

## What the relocated files Require (for the later --write and build)

Per image I (A, B): lib/I/Rt/StackMalloc0Tbl.v, lib/I/Rt/StackMalloc0.v, lib/I/Rt/StackRawKept.v (relocated;
StackRawKept has no numeral), plus three files with no image numeral, carried by module path only:
lib/Rt/StackMallocRawDef.v, lib/Reusable/StackFreeDef.v, lib/Reusable/StackFreeRaw.v (shared with classes 1 and 2
when they come from fuzz_ctrl too).
- Core, image A: lib/A AB1v AE34 AF0l AF0m AF0x AE2y. Core, image B: the image-B twins in lib/Reusable YB1v YE34 YF0l
  YF0m YF0x YE2y. Both: lib/Reusable YZ00 YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YK0j YP0n YK1d YP0m
  YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01 YN3v YI04 YG0v YK04 YA0i YA0n YA0o YA0p YA0q YG00 YG0a YG01
  YG0f YG0n YG0d YG0s YG0q YG0t YCe5 YN32 YM05.
- Record: CtrlTSyms (the premise of ctrl_stack_malloc0, which gives astack_malloc_realizes through _hid_plain and _raw),
  renamed to RECORD_A / RECORD_B by --write.
- The core must give TFIB_TP, TFIB_TSD and Tfib_const rows for every cell StackMalloc0Tbl.v reads through tfib_cell:
  A: the relocated .got cells 0xa4d70 (16 bytes), 0xa4080, 0xa40e0, 0xa4d80, real___tls_get_addr 0xa5e30, *(0xa4080) +
  0x89, *(0xa40e0), tsd_key_inited 0xac260; B: 0xa49d0 (16 bytes), 0xa3ce0, 0xa3d40, 0xa49e0, 0xa5a90, *(0xa3ce0) +
  0x89, *(0xa3d40), 0xabee0; both: TP - 88, TP - 8, *(TP - 8) + 8, and the AT 48 / AT 56 cells.

## What is not done here

The relocated .v files are not written in this worktree (smrun.sh --write needs RECORD_A / RECORD_B, the record names of
this unit's image cores) and not built. With the cores: `RECORD_A=... smrun.sh ... class0-A.conf --write`,
`RECORD_B=... smrun.sh ... class0-B.conf --write`, copy the three numeral-free files with their module paths changed,
then cb build.
