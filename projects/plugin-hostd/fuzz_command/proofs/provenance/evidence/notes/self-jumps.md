# Self-jumps of fuzz_command's ASan images, and the stops_more of lib/A/AB12.v and lib/B/YB12.v

Written by hand; not generated from `PROVENANCE.yaml`. Recorded 2026-10-29: a measurement; no proof reads it.

## Decision

`stops_more` (lib/A/AB12.v:18, lib/B/YB12.v:18) is the start-up runner's list of block ends:
`STOPS := [x_imemset; x_imemcpy; x_memset; x_memcpy; x_memiszero; x_envscan; x_pnscan] ++ stops_more`
(lib/Reusable/YK09.v:2707-2708). Its only readers are the start-up checker's block runs
(lib/Reusable/YA0c.v:149 and :348-357); their soundness (lib/Reusable/YA0e.v, e.g. :3196, :4252) holds for any list.
A missing self-jump can only make a start-up check fail, never pass falsely; an extra one changes no theorem.
So the tables keep the address-table generator's 12 entries per image (the merged tables, whose certificate check
passes), and a site is added only when a start-up plan needs a block end there (decision of the tools owner,
16:09Z, relayed by this port).

## Measurement: 25 self-jumps per image

Method 1: linear RVC-aware decode of `.text` of each pinned image (projects/plugin-hostd/bin/fuzz_command/,
sha256 as in index/binaries.tsv), counting 4-byte words with `(w & 0xfffff07f) == 0x6f` (`jal rd, 0`, any rd);
no `c.j 0` and no `beq rX, rX, 0` found. Method 2: the self-loop scanner 774544b67990 (counts `jal zero, 0` only):
13 per image, equal to method 1's rd = zero subset. Method 3: the frame relocation's scan for fuzz_command
(`jal rd, 0` with rd != 0): the same 12 per image as method 1's rd = ra subset. Method 4: another scan, of self-jumps
with any rd (both forms, both images): the same 25 per image. Method 5: a scan of fuzz_command's self-jumps (its
record's sha256 5980e11a83bd...; 13 x0-form + 12 jal ra, 0 per image): the same 25 per image. Method 6: the
self-loop scanner 306164615bf6 (counts `jal rd, 0` for any rd), on both pinned images with their unstripped twins:
total 25 per image, the same 25 sites.

| A (fuzz_command.asan) | B (fuzz_command.asan-ubsan) | rd | site | in the generated stops_more |
|---|---|---|---|---|
| 0x333e4 | 0x33430 | ra | __do_init+0x5c | no |
| 0x33474 | 0x334c0 | ra | __do_fini+0x78 | no |
| 0x373a0 | 0x373ec | zero | __sanitizer::SealedHangOnAllocationFailure+0x24 | yes |
| 0x389c4 | 0x38a10 | zero | QuarantineCache<QuarantineCallback>::Enqueue+0x190 | yes |
| 0x59cc8 | 0x59d14 | zero | __asan::PoisonShadow+0x4a4 | yes |
| 0x60080 | 0x600cc | zero | __asan::SealedReserveShadow+0x1b0 | yes |
| 0x60094 | 0x600e0 | zero | __asan::SealedReserveShadow+0x1c4 | yes |
| 0x600a8 | 0x600f4 | zero | __asan::SealedReserveShadow+0x1d8 | yes |
| 0x65a38 | 0x65a84 | zero | __sanitizer::ReportMmapFailureAndDie+0x30 | yes |
| 0x65b08 | 0x65b54 | zero | __sanitizer::ReportMunmapFailureAndDie+0x28 | yes |
| 0x73034 | 0x73080 | zero | __sanitizer::MapDynamicShadow+0x158 | yes |
| 0x73f40 | 0x73f8c | zero | __sanitizer::MmapFixedNoReserve+0xc4 | yes |
| 0x740d0 | 0x7411c | zero | __sanitizer::ReservedAddressRange::Init+0xc4 | yes |
| 0x74240 | 0x7428c | zero | __sanitizer::SealedRepairReservation+0xc0 (reached only after Map's mmap failure) | no |
| 0x7d5a4 | 0x7d5f0 | ra | Symbolizer::PlatformDemangle+0x78 | no |
| 0x7d668 | 0x7d6b4 | ra | Symbolizer::PlatformInit+0x9c | no |
| 0x7d674 | 0x7d6c0 | ra | Symbolizer::PlatformInit+0xa8 | no |
| 0x7dd14 | 0x7dd60 | ra | InternalSymbolizer::SymbolizePC+0x30 | no |
| 0x7dd80 | 0x7ddcc | ra | InternalSymbolizer::SymbolizeData+0x38 | no |
| 0x7ddf8 | 0x7de44 | ra | InternalSymbolizer::SymbolizeFrame+0x2c | no |
| 0x7de28 | 0x7de74 | zero | InternalSymbolizer::Flush | yes |
| 0x7de48 | 0x7de94 | ra | InternalSymbolizer::Demangle+0x1c | no |
| 0x8050c | 0x80558 | ra | __lsan::LeakSuppressionContext::Suppress+0x68 | no |
| 0x81180 | 0x811cc | ra | __lsan::CheckForLeaks+0x120 | no |
| 0x86464 | 0x864b0 | ra | target_run+0x150 | no |

The 12 `jal ra, 0` sites per image are NOT measured unreachable (an earlier reason, a GOT-word-0 plus beqz guard at
7 of them, was a window pattern match, not a decode of the register the guard tests, and was withdrawn by its
author); any stops list is sound, since it is the start-up runner's block-end list (decision of the tools owner,
16:09Z). The certificate's start-up plan reaches none of the 13 sites outside the generated list: its check passes
with the 12-entry list (the merged tables), and a start-up run that reached a self-jump that is not a stop would spin
until its fuel and fail the check.

## Gates

- On the merged 12-entry tables (lib/A/AB12.v): plugin-hostd/fuzz_reply's start-up key-set builder 542a382c38fb
  (with the pin bundle that the README of fuzz_reply's start-up tools pairs with AB12 / YB12),
  run with --twin: PASS (image fields 3 rows; x_* fields 11 rows; stops_more 12 rows = the image's 13
  `j .` sites minus SealedRepairReservation+0xc0, which that version excludes by name as not a start-up stop).
- The start-up key-set builder 5e82deff7134 (with its own pin bundle) is not used: its owner re-freezes it.
