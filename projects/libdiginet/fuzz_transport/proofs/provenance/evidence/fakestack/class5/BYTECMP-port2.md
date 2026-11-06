# fuzz_transport fake-stack class 5 on the port2 pins: the walked code compared with the donor's, by cmpkit 86da41d3ef68

Proves no function (kind: measurement). Supersedes BYTECMP-cmpkit.md (old pins, cmpkit 4bbd3a74be89) for the new pins.

Pins (the re-pin to the port commit 835f336c + c47f6290): fuzz_transport.asan e89be137db17b720 (unstripped twin
86efc3a803149811), fuzz_transport.asan-ubsan 41113a03c82fde82 (twin e217cb0a84f1e181). The donor is unchanged:
plugin-hostd/fuzz_command at origin/ossv/recipes 781f46bc05cd, asan c0661b96b5bd / 68db792d5fa7, asan-ubsan
bbe55d24d096 / 658cefbe806b.

Kit: cmpkit 86da41d3ef68 (kit id = the first 12 hex of sha256(SHA256SUMS); its SHA256SUMS sha256
86da41d3ef68abf071a843e599786e5eb0a6ed77c4a6b6eb645e7498bffbee60; copy in tools/cmpkit-86da41d3ef68/, its SHA256SUMS
checked by run.sh: 9 files OK). strictcmp3 65688e94214a is the one compare (it adds lui-built addresses as targets, rule 8);
drvcmp 4d70e90bc1fa proves the twins. class5cmp.py loads strictcmp3 from that copy; nothing else in it changed.

Command (out-port2/, made by run.sh with OUT=out-port2): the unit's harness.yaml still pins the old images, so for this
run its two asan pins were replaced in the worktree by e89be137db17 / 41113a03c82f and restored after (that file, sha256
73986b3d9d0b6582..., is the old one with only those two values changed); run.sh and alreloc check every image against it.

    OUT=out-port2 run.sh WT HUB pau-pipeline/plugin-hostd <dir with bin/ and unstripped/ fuzz_transport.{asan,asan-ubsan}> \
      alreloc.py.frozen-a5c53bb2bed4ad03

Result, both images: twins proved (2 pairs each); 11 ranges paired and compared, PASS; control self PASS with 0 values
moved; the planted `or` in __asan_stack_malloc_5 caught; alreloc 0 UNMAPPED, 0 KEPT-ADDR; checkrep 0 wrong rows. The one
value moved inside a symbol is common_flags_dont_use + 0x89 (A 0x142c71 -> 0x13e5b1, B 0x1427f1 -> 0x13e231), as on the
old pins.

## Every range (out-port2/class5-A.tsv, class5-B.tsv)

Same verdicts as on the old pins with the old kit (out/class5-*.tsv), range by range; only the transport addresses move.

| donor range A / B | function | transport A old -> new | transport B old -> new | range, whole function |
|---|---|---|---|---|
| 0x3ff84 / 0x3ffd0 | __asan_stack_malloc_5 | 0x3dcfc -> 0x3dd04 | 0x3dd40 (same) | EQUAL-mod-pcrel (7), clean |
| 0x67b00 / 0x67b4c | RegisterCommonFlags + 0x358 | 0x62878 -> 0x62880 | 0x628bc (same) | EQUAL; whole function 1 differing target at + 0x1218 (data-differs, a .rodata region), outside the 2 walked words |
| 0x4b040 / 0x4b08c | __interceptor___tls_get_addr | 0x47658 -> 0x47660 | 0x4769c (same) | EQUAL-mod-pcrel (5), clean |
| 0x9fbb8 / 0x9f714 | __tls_get_addr | 0x9de04 (same) | 0x9da7c -> 0x9da60 | EQUAL, clean |
| 0x61e40 / 0x61e8c | __asan::GetCurrentThread | 0x5cbb8 -> 0x5cbc0 | 0x5cbfc (same) | EQUAL, clean |
| 0x5a98c / 0x5a9d8 | __asan::AsanTSDGet | 0x55704 -> 0x5570c | 0x55748 (same) | EQUAL-mod-pcrel (3 / 2), clean |
| 0xa0c6c / 0xa07c8 | pthread_getspecific | 0x9eeb8 (same) | 0x9eb30 -> 0x9eb14 | EQUAL, clean |
| 0x6f554 / 0x6f5a0 | __sanitizer::DTLS_on_tls_get_addr | 0x6a2cc -> 0x6a2d4 | 0x6a310 (same) | EQUAL-mod-pcrel (18), clean |
| 0x40410 / 0x4045c | __asan::MemToShadow (the copy the class-5 bodies call) | 0x3dfbc -> 0x3dfc4 | 0x3e000 (same) | range: 1 unmeasured (the auipc at + 0x6c is consumed after the 28 words); whole function clean |
| 0x40190 / 0x401dc | __asan_stack_free_5 | 0x3df08 -> 0x3df10 | 0x3df4c (same) | EQUAL-mod-pcrel (3), clean |

strictcmp3 reports no lui-built target in any of these functions (0 lui rows in either table).

## Resolve lines (out-port2/resolve-A.txt, resolve-B.txt) against the old pins' (out/)

- A: only MemToShadow's copy moves, 0x3dfbc -> 0x3dfc4 (RtSF5.v:33, :46; RtSM5T.v:68, :71); every other resolve value is
  the old one (the .got cells 0xa4d70 / 0xa4d80, the anonymous .rodata 0x10338, the TLS cells 0xa4080-0xa40e0).
- B: the .got / TLS cells move by -0x20 (0xa3d00 -> 0xa3ce0, 0xa3d08 -> 0xa3ce8, 0xa3d10 -> 0xa3cf0, 0xa3d60 -> 0xa3d40,
  0xa49f0 -> 0xa49d0, 0xa4a00 -> 0xa49e0; RtSF5.v:34, :53; RtSM5T.v:103, :104), each taken from the paired instruction.

## What is not done here

The relocated .v files are not written (run.sh --write needs RECORD_A / RECORD_B, the record names of this unit's image
core) and so not built: the donor's files Require the unit's image-A / image-B core, which is not on these pins yet. With
the core's sha and record names, `RECORD_A=... RECORD_B=... run.sh ... --write` writes them, then cb builds them.
