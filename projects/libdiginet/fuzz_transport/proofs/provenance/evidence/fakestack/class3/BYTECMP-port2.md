# fuzz_transport fake-stack class 3 on the port2 pins: the walked code compared with the donors', by cmpkit 86da41d3ef68

Proves no function (kind: measurement). Image B (asan-ubsan) only: image A calls no `__asan_stack_malloc_3` (its
on_announce takes class 4). The method is ../class5's (run.sh, class5cmp.py, checkrep.py), generalized here to class 3.

Pin: fuzz_transport.asan-ubsan 41113a03c82fde82 (unstripped twin e217cb0a84f1e181), the value this worktree's
projects/libdiginet/fuzz_transport/harness.yaml pins. Chosen donor: plugin-hostd/fuzz_command at origin/ossv/recipes
781f46bc05cd (the class-5 donor and ref), asan-ubsan bbe55d24d096 / 658cefbe806b, files lib/B/Rt/RtSM3T.v (the walk
tables) and lib/B/Rt/RtSM3.v (the contract `cmd_stack_malloc3_contract : forall B, AR_laws tfibsegs B -> CmdBSyms B ->
astack_malloc_realizes tfibsegs B 3`, and its `_x` form over fs_iface).

Kit: cmpkit 86da41d3ef68 (copy in tools/cmpkit-86da41d3ef68/, the class-5 copy; run.sh checks its SHA256SUMS: 9 files
OK, kit id = the first 12 hex of sha256(SHA256SUMS)). strictcmp3 65688e94214a is the one compare; drvcmp 4d70e90bc1fa
proves the twins. alreloc of record: alreloc.py.frozen-a5c53bb2bed4ad03 (align/keep-numerals.txt 3a58c0617633beca).

Command (out-port2/, made by run.sh with OUT=out-port2; out-port2/run.log is its output):

    OUT=out-port2 run.sh WT HUB <AGENTS> <dir with bin/ and unstripped/ fuzz_transport.asan-ubsan> \
      alreloc.py.frozen-a5c53bb2bed4ad03

Result: rule 24 lookup found six released image-B class-3 donors of this unit's form; all six compare PASS; the chosen
donor's 9 ranges paired and compared, PASS; control self PASS with 0 values moved; the planted `or` in
`__asan_stack_malloc_3` caught; alreloc --dry 0 UNMAPPED, 0 KEPT-ADDR (2 files); checkrep 0 wrong rows.

## Rule 24: lookup, compare, choice

RULE24-LOOKUP.txt holds the lookup: one path-scoped git grep per unit on origin/ossv/recipes 9b0ac6f0e678, for the
statement `astack_malloc_realizes <segs> <B> 3` (and `_x`), then for `stack_malloc_?3` in every released unit. Six units
state this unit's class-3 contract on their asan-ubsan image; every other class-3 walk on recipes states another
framework's predicate (stack_malloc_contract RTA 3, N5_stack_malloc3, ...), so it is not a donor of this hypothesis.
Each donor is read at its release ref (the last commit before the move 48907dc7e8ca, where proofs/<unit>/lib exists and
projects/<unit>/harness.yaml pins the image); each image's sha256 was checked against that pin and its twin proved.

| donor | ref | asan-ubsan pin | walk files | ranges | walked words that differ (pc-relative) per range | sum | whole functions |
|---|---|---|---|---|---|---|---|
| **plugin-hostd/fuzz_command** | 781f46bc05cd | bbe55d24d096 | B/Rt/RtSM3T.v, RtSM3.v | 9, PASS | 7, 0, 5, 0, 0, 2, 0, 18, 4 | **36** | 430 |
| omx-clap-core/fuzz_preset | 4cda83dac850 | d663f82d7f48 | AU/FCimgB.v, FCm3r.v, FCm3s.v | 9, PASS | 9, 0, 5, 0, 0, 3, 0, 14, 9 | 40 | 278 |
| libreac/fuzz_disco | b5cf457a8820 | cee6f04ad3d4 | Y/Rt/StackMalloc3Tbl.v, StackMalloc3.v | 9, PASS | 8, 0, 2, 0, 0, 3, 0, 18, 9 | 40 | 273 |
| libreac/fuzz_boxreg | ee71d1fd3fcf | 7620eb05e0ad | B/Rt/StackMalloc3Tbl.v, StackMalloc3.v | 9, PASS | 9, 0, 2, 0, 0, 3, 0, 18, 9 | 41 | 435 |
| libreac/fuzz_identity | cffeac4df63e | baf1a4d065e0 | B/Rt/StackMalloc3Tbl.v, StackMalloc3.v | 9, PASS | 9, 0, 2, 0, 0, 3, 0, 18, 9 | 41 | 395 |
| omx-clap-core/fuzz_state | d0e2eea9a341 | 5ac5ce0954f8 | B/FCimg.v, FCm3r.v, FCm3s.v | 9, PASS | 9, 0, 5, 0, 0, 3, 0, 18, 9 | 44 | 288 |

The ranges, in order: `__asan_stack_malloc_3` (107 words), RegisterCommonFlags + 0x358 (2), `__interceptor___tls_get_addr`
(31), `__tls_get_addr` (9), GetCurrentThread (8), AsanTSDGet (6), `__pthread_getspecific` (7), DTLS_on_tls_get_addr (140),
the MemToShadow copy the body calls (28): 338 walked words. In every donor the same 4 ranges are EQUAL byte for byte and
none has a real, unmeasured or differing-target word (out-port2/cmp-<unit>/class3-B.tsv; image pipelines: pau-pipeline,
and pau-preset-102 for fuzz_preset, whose port pin pau-pipeline does not hold).

Choice: plugin-hostd/fuzz_command. (1) Its walked code is the closest to the target's: 36 of the 338 walked words differ
(all pc-relative), against 40 to 44 for the others (the body: 7 against 8 or 9; MemToShadow: 4 against 9). (2) It is the
class-5 donor at the same ref, so classes 3 and 5 need one image core: RtSM3.v Requires the class-5 files' core (lib/B
YB1v YE34 YF0l YF0m YF0x YE2y, lib/Reusable FCiface) and B/Rt/RtSMxA.v, which the class-5 relocation already carries, and
names the same record CmdBSyms; its resolve values for the shared cells are class 5's B values (0x3e000, 0xa3ce0,
0xa3d40, 0xa49d0, 0xa49e0). The others need a second core layout: boxreg Requires lib.B AB1v AE34 AF0l AF0m AF0x AE2y
(A-named modules), identity lib.ReusableB Y*, disco its lib/Y (no alreloc build directory; disco releases no asan_ubsan
theorem), and the omx-clap-core pair a generated lib/B/FCimg.v (a generator run, not an alreloc relocation). Between the
two donors this row first named, boxreg and identity tie on the walked words (41); identity is closer in the whole
functions (395 against 435).

## Every range of the chosen donor (out-port2/class3-B.tsv)

| donor range | function | transport | paired by | range | whole function |
|---|---|---|---|---|---|
| 0x3fc58 (107) | `__asan_stack_malloc_3` | 0x3db94 | name | EQUAL-mod-pcrel (7), clean | the same (428 B) |
| 0x67b4c (2) | RegisterCommonFlags + 0x358 | 0x628bc | name | EQUAL, clean | EQUAL-mod-pcrel (370), 1 differing target at + 0x1218 (data-differs, a .rodata region), outside the 2 walked words |
| 0x4b08c (31) | `__interceptor___tls_get_addr` | 0x4769c | name | EQUAL-mod-pcrel (5), clean | the same (124 B) |
| 0x9f714 (9) | `__tls_get_addr` | 0x9da60 | name | EQUAL, clean | the same |
| 0x61e8c (8) | `__asan::GetCurrentThread` | 0x5cbfc | name | EQUAL, clean | the same |
| 0x5a9d8 (6) | `__asan::AsanTSDGet` | 0x55748 | name | EQUAL-mod-pcrel (2), clean | EQUAL-mod-pcrel (6), clean |
| 0xa07c8 (7) | `__pthread_getspecific` | 0x9eb14 | name | EQUAL, clean | the same |
| 0x6f5a0 (140) | `__sanitizer::DTLS_on_tls_get_addr` | 0x6a310 | name | EQUAL-mod-pcrel (18), clean | EQUAL-mod-pcrel (32), clean |
| 0x4045c (28) | `__asan::MemToShadow` (one of 5 copies) | 0x3e000 | the body's call | EQUAL-mod-pcrel (4); 1 unmeasured (the auipc at + 0x6c is consumed after the 28 words) | EQUAL-mod-pcrel (10), clean |

The verdicts are class 5's for the 8 shared callee ranges (../class5/BYTECMP-port2.md, image B); strictcmp3 reports no
lui-built target in any of these functions.

## Resolve lines (out-port2/resolve-B.txt): 54, of which 7 move a value

Each moving line takes the value from the paired instruction or function, and each value was read back in both ELFs:

- RtSM3T.v:31 `0x3fd64 -> 0x3dca0` and :276 `261476 -> 253088`: FS_FOUND, `__asan_stack_malloc_3 + 0x10c` on both sides
  (the body's whole-function compare passed, so the same offset is the same instruction). The decimal is the walk's
  `replace (Z_to_bv 64 FS_FOUND) with (261476%bv : bv 64)`, so it must move with the hex; class3cmp.py gives it from the
  pairing rather than leave a decimal code point to alreloc's rules. The hex line exists because a first run with only
  the decimal line (not kept) stopped on `AMBIGUOUS-MODEL-CONSTANT B/Rt/RtSM3T.v:31 0x3fd64 -> 0x3dca0 (Definition
  FS_FOUND: its decimal twin 261476 stays in the file; ...)`: alreloc does not see that a resolve line moves the twin.
- RtSM3T.v:44 `0x4045c -> 0x3e000`: the MemToShadow copy, a local static with 5 copies in each image; the body's `jal` at
  the same word names 0x3e000.
- RtSM3T.v:73 `0xa5f40 -> 0xa3ce0`, :74 `0xa5fa0 -> 0xa3d40`, :73 `0xa6c50 -> 0xa49d0`, :74 `0xa6c60 -> 0xa49e0`: .got cells
  (no symbol home) that the walked functions load pc-relative; the target's word at the same instruction names the cell.
  Read back: 0xa3ce0 holds common_flags_dont_use (0x13e1a8, donor 0x142768), 0xa3d40 holds current_verbosity (0x13c118,
  donor 0x1406d8), 0xa49d0 holds the TLS index (1, -0x800) as the donor's, 0xa49e0 holds 8 as the donor's. alreloc's
  `gap` rule would map these by their .got offset.

The other 47 keep their value: every numeral >= 0x10000 of the two files' leading comment blocks (RtSM3T.v:4-6,
RtSM3.v:4-6: the inherited header and notice lines name other images' addresses) and the model constants 0x309000
(FS_FROFF), 3182592 (its decimal) and 1441792 ((kFakeStackSize - kFakeFramesOff) / 8), which lie in the image hull.

## Controls

- self: the donor against itself, PASS, 0 values moved (out-port2/ctl-self-B.log).
- planted word: `and a7, a2, a4` at `__asan_stack_malloc_3 + 0x94` of a copy of the target (0x00e678b3 -> 0x00e668b3, `or`):
  caught, 1 FAIL line (range and whole function DIFFERENT, 1 real word; out-port2/ctl-plant-B.log).

## alreloc --dry (out-port2/alreloc-B.out)

RtSM3T.v: 26 symbol, 44 resolved, 0 KEPT-ADDR, 0 UNMAPPED; RtSM3.v: 6 symbol, 10 resolved, 0 KEPT-ADDR, 0 UNMAPPED. 94
numerals reported (out-port2/report/). Nothing was written.

## checkrep (out-port2/checkrep-B.txt): 0 wrong rows

Rows by rule: resolve 54, FUNC entry 9, same-code function 4, OBJECT start 6, symbol 13, SIZES_KEEP 4, not an address 4.
TSD 0x6054c0 -> 0x614b18 is the OBJECT start of `__pthread_tsd_main` on both sides. The 13 values moved by their offset
inside a symbol, each judged an address:

- RtSM3T.v:74 `0x1427f1 -> 0x13e231`, common_flags_dont_use + 0x89: the flag byte the walk loads through the .got cell
  0xa3ce0 (base + 0x89); class 5 moves the same value the same way.
- RtSM3T.v:40 TP `0x5e4118 -> 0x5f3770` (builtin_tls + 0xc8); :75 `0x5e4138 -> 0x5f3790` (+ 0xe8, the value of TP - 8),
  `0x5e4140 -> 0x5f3798` (+ 0xf0, the cell (TP - 8) + 8) and `0x5e4918 -> 0x5f3f70` (+ 0x8c8, its value); :83 and
  RtSM3.v:121-124, 189-190 the thread-object words `0x5e4850 -> 0x5f3ea8` (+ 0x800) and `0x5e492c -> 0x5f3f84` (+ 0x8dc):
  pointers into musl's static TLS area. They are the same offsets on both images because both have the same PT_TLS
  (memsz 20, align 8) and the same builtin_tls size (131280), from which musl places the thread at start-up.

Kept values that lie in a donor symbol: the instruction words 0x0007c283 / 0x00160613 (fetch_word / decode_any facts,
`not an address`, the twin holds the same word) and 1048576 (SIZES_KEEP); no model constant was moved.

## For the later --write and build

`RECORD_B=<the core's image-B record> run.sh ... --write` writes lib/B/Rt/RtSM3T.v and lib/B/Rt/RtSM3.v (CmdBSyms
becomes RECORD_B outside the restored header). The written files Require, under this unit's prefix:

- lib/Reusable: YZ00; YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d; YP0m YP0e YP09 YP02 YP0l YP0k
  YP06 YP08 YP03 YP04 YP0g YP01; YN3v YI04; YG0v; YK04 YA0i YA0n YA0o YA0p YA0q; YG00 YG0a YG01 YG0f YG0n YG0d YG0t YCe5
  (RtSM3T.v) and YG0s FCiface (RtSM3.v); YN32; YM05.
- lib/B: YB1v YE34 YF0l YF0m YF0x YE2y; lib/B/Rt: RtSMxA (class 5's relocation) and RtSM3T.
- the record (CmdBSyms in the donor) with fields ts_code, ts_tp, ts_tsd, ts_const, and Tfib_const rows for the cells of
  RtSM3T.v fsA_rodata, TP - 88, TP - 8, (TP - 8) + 8 and the AT 48 / AT 56 cells. RtSM3T.v states TP and TSD as literals
  (0x5f3770, 0x614b18 after relocation) where class 5's RtSM5T.v reads TFIB_TP / TFIB_TSD: the core's YF0m must state
  those two values.

This worktree's lib has none of lib/B and, of lib/Reusable, lacks YK18, YG0v, YK04, YA0i YA0n YA0o YA0p YA0q, YG00
YG0a YG01 YG0f YG0n YG0d YG0t YG0s, YCe5 and FCiface (the image core is not on these pins yet); the build waits on it.
