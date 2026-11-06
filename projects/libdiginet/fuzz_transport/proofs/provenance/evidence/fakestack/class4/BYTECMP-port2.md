# fuzz_transport fake-stack class 4 on the port2 pins: donor chosen by rule 24, walked code compared, dry relocation

Proves no function (kind: measurement). Method of record: class5/, generalized in ../class0/ (smcmp.py, smrun.sh,
checkrep.py, cands.sh, closeness.py; see ../class0/BYTECMP-port2.md for what each changes from class5/); this
directory holds class 4's configuration (class4.conf, model.txt) and outputs. Nothing is written under lib/.

Only image A: fuzz_transport.asan-ubsan has no __asan_stack_malloc_4 (no FUNC symbol of that name; the class-0
candidates whose tables list it fail on image B for that reason, ../class0/out-port2/rule24/). Pin: fuzz_transport.asan
e89be137db17b720 (unstripped twin 86efc3a803149811). Kit cmpkit 86da41d3ef68 (../class0/tools/), alreloc of record
a5c53bb2bed4.

## Rule 24: every released donor of class 4, compared before the choice

Lookup: ../class0/rule24-grep.txt (origin/ossv/recipes 9b0ac6f0e678, one path-scoped git grep per released unit with
an ASan proof tree, 36 units). Files that state `astack_malloc_realizes tfibsegs B 4`: libreac/fuzz_grant A and B
(Rt/StackMalloc4{,Tbl}.v), libreac/fuzz_identity A and B (Rt/StackMalloc4{,Tbl}.v), plugin-hostd/fuzz_command A and B
(Rt/RtSM4{,T}.v). Each read at e10f488c53fc (the last recipes commit with proofs/<P/H>/lib, the layout alreloc reads;
every file read there has the same blob at the tip).

`cands.sh 4 HUB DONORS TARGET out-port2/rule24` (out-port2/rule24/rule24-4.tsv, rule24-4-closeness.txt):

| img | donor | code table | verdict | ranges | pc-rel words walked / whole fns | resolve moves |
|---|---|---|---|---|---|---|
| A | libreac/fuzz_grant | A/Rt/AF0r.v (classes 0 1 2 4 and callees) | PASS | 12 of 12 | 62 / 416 | 9 |
| A | libreac/fuzz_identity | A/Rt/StackMallocTbl.v | FAIL: __asan_stack_malloc_3 not in transport A | 10 of 11 | 47 / 403 | 5 |
| A | plugin-hostd/fuzz_command | A/Rt/RtSM1T.v | FAIL: __asan_stack_malloc_3, _7 not in transport A | 13 of 15 | 87 / 504 | 9 |

Every class-4 walk takes its code table from a shared table file; only grant's lists bodies transport A links (its
classes 0, 1, 2, 4), so only grant's relocates whole. The closeness measure (../class0/closeness.py, over what each
relocation carries, the donor's own table: walked words differing by a pc-relative offset, then the whole functions'
differing targets and pc-relative words): grant 62 walked; whole functions 1 differing target (RegisterCommonFlags +
0x1218, data-differs, outside the 2 walked words) and 416 words; the failing ones, not ranked: identity 47 / 1 / 403,
fuzz_command 87 / 1 / 504. Chosen: **libreac/fuzz_grant** lib/A/Rt/StackMalloc4Tbl.v + StackMalloc4.v + AF0r.v (the
table StackMalloc4Tbl.v takes tbl_fs from) at e10f488c53fc (last changed by d2e4b664b21d; image asan c2c7559b29bd,
twin 57c26f993615).

AF0r.v is grant's class-1 walk file; classes 1 and 2 of this row come from another donor (reported 2026-10-31), so
AF0r.v is relocated here for class 4's table only.

## Command and result (out-port2/run.log)

    smrun.sh WT HUB <pau-pipeline>/libreac TARGET alreloc.py.frozen-a5c53bb2bed4ad03 class4/class4.conf

Twins proved (2 pairs); 12 ranges paired and compared, PASS (0 real, 0 differing targets); control self PASS, 0 values
moved; control plant (`and` -> `or` at __asan_stack_malloc_4 + 0x94, 0x00e678b3 -> 0x00e668b3) caught, 1 FAIL line;
alreloc --dry 0 UNMAPPED, 0 KEPT-ADDR (3 files); checkrep 0 wrong rows.

write-test-A.log: the same run with --write into a scratch copy of the unit tree (not this worktree), record name
TransportASyms as a placeholder: alreloc writes the 3 files with the module paths moved to libdiginet.fuzz_transport,
each header block (4 lines) comes back from the donor, GrantSyms is renamed twice in StackMalloc4.v, one notice line
is added per file.

## Every range (out-port2/class4-A.tsv)

| donor range | words | function | paired by | transport | range: verdict (pc-rel) | whole function |
|---|---|---|---|---|---|---|
| 0x3cda4 | 93 | __asan_stack_malloc_0 | name | 0x3d698 | EQUAL-mod-pcrel (8) | same, clean |
| 0x3cf18 | 100 | __asan_stack_malloc_1 | name | 0x3d80c | EQUAL-mod-pcrel (8) | same, clean |
| 0x3d0a8 | 103 | __asan_stack_malloc_2 | name | 0x3d99c | EQUAL-mod-pcrel (8) | same, clean |
| 0x3d244 | 115 | __asan_stack_malloc_4 | name | 0x3db38 | EQUAL-mod-pcrel (8) | same, clean |
| 0x61ccc | 2 | RegisterCommonFlags + 0x358 | name | 0x62880 | EQUAL | EQUAL-mod-pcrel (333); 1 differing target at + 0x1218 (data-differs), outside the 2 walked words |
| 0x46aac | 31 | __interceptor___tls_get_addr | name | 0x47660 | EQUAL-mod-pcrel (2) | same, clean |
| 0x96620 | 9 | __tls_get_addr | name | 0x9de04 | EQUAL | clean |
| 0x5c00c | 8 | __asan::GetCurrentThread | name | 0x5cbc0 | EQUAL | clean |
| 0x54b58 | 6 | __asan::AsanTSDGet | name | 0x5570c | EQUAL-mod-pcrel (3) | EQUAL-mod-pcrel (7), clean |
| 0x976d4 | 7 | __pthread_getspecific | name | 0x9eeb8 | EQUAL | clean |
| 0x69720 | 140 | __sanitizer::DTLS_on_tls_get_addr | name | 0x6a2d4 | EQUAL-mod-pcrel (16) | EQUAL-mod-pcrel (29), clean |
| 0x3d410 | 28 | __asan::MemToShadow (the copy the class bodies call) | call | 0x3dfc4 | EQUAL-mod-pcrel (9), 1 unmeasured (the auipc at + 0x6c is consumed after the 28 words) | EQUAL-mod-pcrel (13), clean |

strictcmp3 reports no lui-built target in these functions.

## Resolve lines (out-port2/resolve-A.txt) and why each exists

- The MemToShadow copy (several copies of the name): AF0r.v:42 0x3d410 -> 0x3dfc4, the target of the paired `jal` (the
  copy class 0 and class 5 pair on image A too).
- .got cells the walk reads (no symbol home; alreloc's `gap` rule would map them by .got offset): AF0r.v:71-72 and
  StackMalloc4Tbl.v:67-68 0x9c860 -> 0xa4080, 0x9c8c0 -> 0xa40e0 (the cells holding &common_flags_dont_use and
  &current_verbosity), 0x9d550 -> 0xa4d70, 0x9d560 -> 0xa4d80 (the TLS pair): each the paired instruction's target, the
  same cells as classes 0 and 5 on image A.
- Kept: the header numerals (AF0r.v:4 0x3cf18; StackMalloc4{,Tbl}.v:4 0x3d244 and 0x409000) and the model constants of
  model.txt: FS_FROFF 0x409000 (StackMalloc4Tbl.v:37) and its decimal 4231168 (Tbl :351, :360; StackMalloc4.v:239, :244),
  4231168 / 64 = 66112 (StackMalloc4.v:244), 1441792 (StackMalloc4.v:277, :279), class 1's FS_FROFF 0x109000 (AF0r.v:36)
  and 1085440 (AF0r.v:355, :364). Without them alreloc moves 0x409000 to theDepot + 0x2825e8 and 0x109000 to
  internal_alloc_placeholder + 0x632c0 (AMBIGUOUS-MODEL-CONSTANT, TWIN-MISMATCH) and reports the decimals UNMAPPED
  (the first dry run, before model.txt).

## Values moved inside a symbol (checkrep), each judged

- common_flags_dont_use + 0x89 (AF0r.v:72, StackMalloc4Tbl.v:68; 0x1366f1 -> 0x13e5b1): the flag byte the walk reads; an
  address.
- builtin_tls + 0xc8 (TP: AF0r.v:38, StackMalloc4Tbl.v:39), + 0xe8, + 0xf0, + 0x8c8 (the dtv pointer, dtv[1]'s cell
  and value: AF0r.v:73, StackMalloc4Tbl.v:69), + 0x800 and + 0x8dc (T + 48 / T + 56: AF0r.v:81, StackMalloc4Tbl.v:77,
  StackMalloc4.v:116-119, :184-185): addresses in musl's static TLS block, whose layout is the same in both images
  (PT_TLS filesz 0, memsz 0x14, align 8; builtin_tls 131280 bytes; (builtin_tls + 200) mod 8 = 0 in both, so TP =
  builtin_tls + 0xc8 in both). Addresses; the symbol + offset map is right.
- Kept values inside a donor symbol: the probe-loop instruction words 0x0007c283 and 0x00160613 (fetch_word facts, the
  same words in transport by the compare), SIZES_KEEP 1048576, and the model constants above.

## What the relocated files Require (for the later --write and build)

A/Rt/StackMalloc4Tbl.v, A/Rt/StackMalloc4.v, A/Rt/AF0r.v. Core: lib/A AB1v AE34 AF0l AF0m AF0x AE2y; lib/Reusable YZ00
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g
YP01 YN3v YI04 YG0v YK04 YA0i YA0n YA0o YA0p YA0q YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0t YCe5 YN32 YG0q YF0v YM05.
Record: GrantSyms (premise of stack_malloc4_contract), renamed to RECORD_A by --write.

## What is not done here

The relocated .v files are not written (smrun.sh --write needs RECORD_A, the record name of this unit's image-A core)
and not built. With the core: `RECORD_A=... smrun.sh ... class4/class4.conf --write`, then cb build.
