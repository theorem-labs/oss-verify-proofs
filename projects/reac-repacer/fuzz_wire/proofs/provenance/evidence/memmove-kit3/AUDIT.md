# Audit of memmove-kit3 (commit 97ab13e41f99): the by-hand acceptances

Reviewer: a fresh read-only reviewer (no function proved). Date: 2026-10-30.

Record: `proofs/reac-repacer/fuzz_wire/provenance/evidence/memmove-kit3/README.md` at 97ab13e41f99, with `records/` and `tools/`. Kit: cmpkit 4bbd3a74be89
(the kit directory, SHA256SUMS hash 4bbd3a74be89...). Images: X = fuzz_wire.asan.unstripped
d2f662a22962 (A) and fuzz_wire.asan-ubsan.unstripped 51eb4bef2425 (B); Y = fuzz_pcap.asan 36da3052c383 (A) and fuzz_pcap.asan-ubsan
c969d83cdd59 (B), the unstripped twins. The stripped pins differ from the twins only in the ELF header and .note.gnu.build-id
(records/twins-pcap-*.txt), and no target in this audit lies there.

## Method

- Disassembly: capstone RV64GC, the same decoder as `rvdis.py`, with auipc+addi / auipc+load targets resolved. Every address below
  is a function offset (`FUNC+0xNN`) or an image address.
- Consumer use: a register dataflow walk from the lo12 word that sets the target register. It follows `mv` copies and both
  sides of each branch, and it stops when the register is overwritten. It records each call that gets the target in an
  argument register (with the format string when a0 is a constant), each store, each load from the target, each pointer
  arithmetic, and each return in a0. I ran it on X-A, X-B, Y-A and Y-B. Then I read the disassembly by hand at every
  store, spill, return, table or unusual site (the notes in the tables below).
- Recount: I ran the kit itself again, read-only (`PYTHONDONTWRITEBYTECODE=1`): `closure_strict2.py` and `paircl.py` on
  both images. I also called the kit's own `strictcmp2.tcmp` on every reported function to get its full target list.
- Reproduction: the closure outputs I made are byte-identical to records/closure-*.txt. The paircl outputs differ from
  records/paircl-*.txt only in the header line, because I gave the twin path as Y_ELF. `tools/settle.py` on the four
  record inputs and `tools/byhand.py` on the ten targets give the records/settle-* and records/byhand-asan.txt output
  byte for byte.

Record line references: `C:n` = records/settle-closure-asan.txt line n, `P:n` = records/settle-paircl-asan.txt line n. The
-asan-ubsan files have the same row on the same line, with the same X/Y target addresses (checked for all 144 CSTR rows).

## 1. CSTR rows

All 72 distinct CSTR targets (function + word offset) in records/settle-*, on both images: 144 rows. This is every
'other-use' (28) and 'redefined' (29) target, all 14 'arg' targets and the 1 'lbu0' target. There is no 'wide-load' row
in any record. 46 of the targets are the empty string X 0x13e67 / Y 0x13e7d, and I checked all of them. For each target I
also checked the bytes myself: up to the first NUL they are equal on both sides, NUL included (144 of 144). The dataflow
result is identical on X-A, X-B, Y-A and Y-B for all 72 targets.

String key: `\e` = ESC (0x1b). 0x17781 `\e[1m\e[31m` (Warning, red), 0x17717 `\e[1m\e[32m` (green), 0x1f9bd `\e[1m\e[34m`
(blue), 0x18dc0 `\e[1m\e[0m` (Default), 0x13e67 `""`. "Printf(a1, fmt '%s')" means `__sanitizer::Printf("%s", target)`.

| target | record lines | X/Y | string | settle kind | consumer use (X-A) | result |
|---|---|---|---|---|---|---|
| HeapAddressDescription::Print+0x68 | C:7,P:15 | 0x13e67/0x13e7d | '' | redefined | +0xc4 Append(a1) | CONFIRMED |
| StackAddressDescription::Print+0x4c | C:9,P:17 | 0x13e67/0x13e7d | '' | redefined | +0x64 Printf(a1, fmt '%s') | CONFIRMED |
| StackAddressDescription::Print+0x58 | C:10,P:18 | 0x17717/0x17754 | '\e[1m\e[32m' | redefined | +0x64 Printf(a1, fmt '%s') | CONFIRMED |
| GlobalAddressDescription::Print+0x80 | C:11,P:19 | 0x13e67/0x13e7d | '' | other-use | spilled to 0x38(sp); reloaded +0x164 and +0x20c into a1 for InternalScopedString::Append (C string) | CONFIRMED |
| GlobalAddressDescription::Print+0x88 | C:12,P:20 | 0x17717/0x17754 | '\e[1m\e[32m' | other-use | spilled to 0x30(sp); reloaded +0x15c into a1 for Append | CONFIRMED |
| ErrorDoubleFree::Print+0x34 | C:13,P:52 | 0x13e67/0x13e7d | '' | other-use | +0x58,+0xa0 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorDoubleFree::Print+0x48 | C:14,P:53 | 0x17781/0x177be | '\e[1m\e[31m' | redefined | +0x58 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorNewDeleteTypeMismatch::Print+0x30 | C:15,P:54 | 0x13e67/0x13e7d | '' | other-use | +0x50 Printf(a1, fmt '%s'); +0x98 Printf(a1, fmt '%s  object passed to delete has wrong ty') | CONFIRMED |
| ErrorNewDeleteTypeMismatch::Print+0x44 | C:16,P:55 | 0x17781/0x177be | '\e[1m\e[31m' | redefined | +0x50 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorFreeNotMalloced::Print+0x2c | C:17,P:64 | 0x13e67/0x13e7d | '' | redefined | +0x44 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorFreeNotMalloced::Print+0x38 | C:18,P:65 | 0x17781/0x177be | '\e[1m\e[31m' | redefined | +0x44 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorAllocTypeMismatch::Print+0x38 | C:20,P:60 | 0x13e67/0x13e7d | '' | redefined | +0x50 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorAllocTypeMismatch::Print+0x44 | C:21,P:61 | 0x17781/0x177be | '\e[1m\e[31m' | redefined | +0x50 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorMallocUsableSizeNotOwned::Print+0x28 | C:22,P:66 | 0x13e67/0x13e7d | '' | redefined | +0x40 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorMallocUsableSizeNotOwned::Print+0x34 | C:23,P:67 | 0x17781/0x177be | '\e[1m\e[31m' | redefined | +0x40 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorSanitizerGetAllocatedSizeNotOwned::Print+0x28 | C:24,P:70 | 0x13e67/0x13e7d | '' | redefined | +0x40 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorSanitizerGetAllocatedSizeNotOwned::Print+0x34 | C:25,P:71 | 0x17781/0x177be | '\e[1m\e[31m' | redefined | +0x40 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorCallocOverflow::Print+0x30 | C:26,P:56 | 0x13e67/0x13e7d | '' | other-use | +0x54,+0x98 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorCallocOverflow::Print+0x44 | C:27,P:57 | 0x17781/0x177be | '\e[1m\e[31m' | redefined | +0x54 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorReallocArrayOverflow::Print+0x30 | C:28,P:62 | 0x13e67/0x13e7d | '' | other-use | +0x54,+0x98 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorReallocArrayOverflow::Print+0x44 | C:29,P:63 | 0x17781/0x177be | '\e[1m\e[31m' | redefined | +0x54 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorPvallocOverflow::Print+0x30 | C:30,P:48 | 0x13e67/0x13e7d | '' | redefined | +0x48 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorPvallocOverflow::Print+0x3c | C:31,P:49 | 0x17781/0x177be | '\e[1m\e[31m' | other-use | +0x48 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorInvalidAllocationAlignment::Print+0x2c | C:32,P:50 | 0x13e67/0x13e7d | '' | other-use | +0x50,+0x8c Printf(a1, fmt '%s') | CONFIRMED |
| ErrorInvalidAllocationAlignment::Print+0x40 | C:33,P:51 | 0x17781/0x177be | '\e[1m\e[31m' | redefined | +0x50 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorInvalidAlignedAllocAlignment::Print+0x30 | C:34,P:84 | 0x13e67/0x13e7d | '' | other-use | +0x54,+0x98 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorInvalidAlignedAllocAlignment::Print+0x44 | C:35,P:85 | 0x17781/0x177be | '\e[1m\e[31m' | redefined | +0x54 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorInvalidPosixMemalignAlignment::Print+0x2c | C:36,P:74 | 0x13e67/0x13e7d | '' | other-use | +0x50,+0x90 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorInvalidPosixMemalignAlignment::Print+0x40 | C:37,P:75 | 0x17781/0x177be | '\e[1m\e[31m' | redefined | +0x50 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorAllocationSizeTooBig::Print+0x34 | C:38,P:76 | 0x13e67/0x13e7d | '' | other-use | +0x58,+0xa4 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorAllocationSizeTooBig::Print+0x48 | C:39,P:77 | 0x17781/0x177be | '\e[1m\e[31m' | redefined | +0x58 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorRssLimitExceeded::Print+0x28 | C:40,P:46 | 0x13e67/0x13e7d | '' | other-use | +0x4c,+0x7c Printf(a1, fmt '%s') | CONFIRMED |
| ErrorRssLimitExceeded::Print+0x3c | C:41,P:47 | 0x17781/0x177be | '\e[1m\e[31m' | other-use | +0x4c Printf(a1, fmt '%s') | CONFIRMED |
| ErrorOutOfMemory::Print+0x28 | C:42,P:58 | 0x13e67/0x13e7d | '' | other-use | +0x4c,+0x80 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorOutOfMemory::Print+0x3c | C:43,P:59 | 0x17781/0x177be | '\e[1m\e[31m' | other-use | +0x4c Printf(a1, fmt '%s') | CONFIRMED |
| ErrorStringFunctionMemoryRangesOverlap::Print+0x50 | C:44,P:44 | 0x13e67/0x13e7d | '' | redefined | +0x68 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorStringFunctionMemoryRangesOverlap::Print+0x5c | C:45,P:45 | 0x17781/0x177be | '\e[1m\e[31m' | redefined | +0x68 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorStringFunctionSizeOverflow::Print+0x2c | C:46,P:72 | 0x13e67/0x13e7d | '' | other-use | +0x50,+0x80 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorStringFunctionSizeOverflow::Print+0x40 | C:47,P:73 | 0x17781/0x177be | '\e[1m\e[31m' | arg | +0x50 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorODRViolation::Print+0x2c | C:48,P:68 | 0x13e67/0x13e7d | '' | other-use | +0x50,+0x80 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorODRViolation::Print+0x40 | C:49,P:69 | 0x17781/0x177be | '\e[1m\e[31m' | arg | +0x50 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorInvalidPointerPair::Print+0x34 | C:50,P:41 | 0x13e67/0x13e7d | '' | redefined | +0x4c Printf(a1, fmt '%s') | CONFIRMED |
| ErrorInvalidPointerPair::Print+0x40 | C:51,P:42 | 0x17781/0x177be | '\e[1m\e[31m' | redefined | +0x4c Printf(a1, fmt '%s') | CONFIRMED |
| ErrorGeneric::Print+0x50 | C:53,P:78 | 0x13e67/0x13e7d | '' | redefined | +0x68 Printf(a1, fmt '%s') | CONFIRMED |
| ErrorGeneric::Print+0x5c | C:54,P:79 | 0x17781/0x177be | '\e[1m\e[31m' | redefined | +0x68 Printf(a1, fmt '%s') | CONFIRMED |
| __asan::InitializeFlags+0x104 | C:55,P:31 | 0x13e67/0x13e7d | '' | other-use | stored to asan_flags_dont_use_directly+0x68 (= flag "suppressions", FlagHandler<const char*> vtable 0x982d8, registered +0xae4) and to 0x120(sp), reloaded +0xc94 as a1 of FlagParser::ParseString | CONFIRMED |
| Decorator::ShadowByte+0x28 | C:59,P:83 | 0x17781/0x177be | '\e[1m\e[31m' | redefined | jump-table dispatch with a1 = red; every arm returns a1 or "" in a0 (+0x84); caller PrintMemoryByte passes it as a3 to AppendF "%s%s%x%x%s%s" | CONFIRMED |
| __asan_describe_address+0x114 | C:60,P:14 | 0x13e67/0x13e7d | '' | arg | a2 = bug_type of PrintAddressDescription | CONFIRMED |
| __asan_default_suppressions+0x4 | C:63,P:6 | 0x13e67/0x13e7d | '' | arg | returned as the const char* result | CONFIRMED |
| LoadedModule::addAddressRange+0x70 | C:64,P:4 | 0x13e67/0x13e7d | '' | other-use | internal_strncpy(name, "", 16) (stops at NUL) | CONFIRMED |
| CommonFlags::SetDefaults+0x48 | C:65,P:38 | 0x13e67/0x13e7d | '' | arg | stored to CommonFlags +24/+200/+208 = strip_path_prefix, cov_8bit_counters_out, cov_pcs_out (all FlagHandler<const char*> in RegisterCommonFlags) | CONFIRMED |
| RegisterCommonFlags+0x1218 | C:66,P:37 | 0x13e67/0x13e7d | '' | other-use | stored to FlagHandlerInclude+0x18 (original_path_) for "include" and "include_if_exists"; FlagHandlerInclude::Format (0x624b0) passes it to internal_snprintf "%s" | CONFIRMED |
| FlagParser::PrintFlagDescriptions+0x70 | C:67,P:32 | 0x13e67/0x13e7d | '' | arg | s5 -> a3 = third %s of "\t%s\n\t\t- %s (Current Value%s: %s)\n" (Printf +0x94) | CONFIRMED |
| OpenFile+0x60 | C:69,P:1 | 0x209a0/0x209f4 | '' | other-use | NOT a C string: int32 table, see item 2 | see item 2 |
| Symbolizer::PlatformInit+0x18c | C:72,P:5 | 0x13e67/0x13e7d | '' | arg | binary_name "" -> internal_strncmp(.., "llvm-symbolizer", 15), internal_strcmp(.., "atos"/"addr2line") | CONFIRMED |
| ReportDeadlySignal+0x90 | C:73,P:86 | 0x13e67/0x13e7d | '' | other-use | +0x200,+0x240 Printf(a1, fmt '%s') | CONFIRMED |
| ReportDeadlySignal+0xb8 | C:74,P:87 | 0x13e67/0x13e7d | '' | other-use | +0x2ac,+0x338 Printf(a1, fmt '%s') | CONFIRMED |
| __lsan::Flags::SetDefaults+0xc | C:75,P:36 | 0x13e67/0x13e7d | '' | other-use | stored to __lsan::Flags+32 = "suppressions" (FlagHandler<const char*>) | CONFIRMED |
| __lsan_default_options+0x4 | C:76,P:33 | 0x13e67/0x13e7d | '' | arg | returned as the const char* result | CONFIRMED |
| __ubsan::Flags::SetDefaults+0x4 | C:77,P:35 | 0x13e67/0x13e7d | '' | other-use | stored to __ubsan::Flags+8 = "suppressions" (FlagHandler<const char*>) | CONFIRMED |
| __ubsan_default_options+0x4 | C:78,P:34 | 0x13e67/0x13e7d | '' | arg | returned as the const char* result | CONFIRMED |
| __fstat+0xc | C:85,P:30 | 0x13e67/0x13e7d | '' | arg | tail call __fstatat(fd, "", st, AT_EMPTY_PATH=0x1000): path C string | CONFIRMED |
| __nl_langinfo_l+0x5c | C:87,P:27 | 0x13e67/0x13e7d | '' | arg | default return value "" (+0x118 ret) | CONFIRMED |
| __nl_langinfo_l+0xf8 | C:88,P:28 | 0x13e67/0x13e7d | '' | lbu0 | LC_MONETARY path: idx!=0 returns it at +0x118; idx==0 reads only byte 0 (lbu +0x100, the NUL) and returns; the skip loop +0xd4 is not on this path | CONFIRMED |
| __tm_to_tzname+0x74 | C:89,P:29 | 0x13e67/0x13e7d | '' | redefined | returned (zone name) to __strftime_fmt_1 +0x438 -> +0x50c strlen | CONFIRMED |
| __strftime_fmt_1+0x530 | C:91,P:26 | 0x13e67/0x13e7d | '' | arg | +0x528 sd zero,0(s0) (*l = 0) then return ""; __strftime_l +0x1cc..+0x24c reads t[0] only, copies k = 0 bytes | CONFIRMED |
| __lsan::CheckForLeaks+0x2c0 | P:7 | 0x13e67/0x13e7d | '' | other-use | +0x630,+0x654 Printf(a1, fmt '%s') | CONFIRMED |
| __lsan::CheckForLeaks+0x318 | P:8 | 0x13e67/0x13e7d | '' | other-use | +0x594,+0x5b8 Printf(a1, fmt '%s') | CONFIRMED |
| LeakReport::PrintReportForLeak+0x34 | P:9 | 0x13e67/0x13e7d | '' | redefined | +0x4c Printf(a1, fmt '%s') | CONFIRMED |
| LeakReport::PrintReportForLeak+0x40 | P:10 | 0x1f9bd/0x1fa0b | '\e[1m\e[34m' | arg | +0x4c Printf(a1, fmt '%s') | CONFIRMED |
| __lsan::PrintResults+0x74 | P:11 | 0x13e67/0x13e7d | '' | other-use | +0xa0,+0xc4 Printf(a1, fmt '%s') | CONFIRMED |
| __lsan::PrintResults+0x90 | P:12 | 0x17781/0x177be | '\e[1m\e[31m' | arg | +0xa0 Printf(a1, fmt '%s') | CONFIRMED |

Notes on the by-hand readings above:
- `__nl_langinfo_l` +0xf4..+0x118 (X-A 0x94a40): `addi a0,..=0x13e67; bnez a3,+0x118 (ret); lbu a3,0(a0); beqz a3,+0x118`. The
  string is read at byte 0 only. The idx-skip loop at +0xd4..+0xe4 is reached only from the LC_NUMERIC/LC_TIME/LC_MESSAGES
  paths (+0x84, +0xb4, +0xcc).
- `__strftime_fmt_1` +0x528..+0x534 and +0x544..+0x550: `sd zero,0(s0)` with s0 = the `l` argument (+0x20 `mv s0,a1`), then
  return "". The only callers (`__strftime_l` / `strftime_l` +0x1bc) read `t[0]`, compare it with '+', '-' and '0'
  (+0x1cc..+0x21c), count digits from `t[0]` (+0x23c loop) and copy k = 0 bytes. No byte after the NUL is read.
- InitializeFlags field +0x68: `addi a0,s3,0x68` (+0x294) goes to 0xf8(sp), then into a FlagHandler at +0xae4..+0xae8 with
  vtable 0x982d8 = `_ZTVN11__sanitizer11FlagHandlerIPKcEE`, name "suppressions" (0x1ba57).
- CommonFlags field offsets: from the 88 RegisterHandler calls in RegisterCommonFlags (vtable + field pointer per handler),
  +24 = strip_path_prefix, +200 = cov_8bit_counters_out, +208 = cov_pcs_out. All three are FlagHandler<const char*>.
  __lsan::Flags +32 and __ubsan::Flags +8 are "suppressions" (RegisterLsanFlags / RegisterUbsanFlags, FlagHandler<const char*>).

Result: CONFIRMED for all 71 C-string targets: each is used as a C string. OpenFile +0x60 is not a C string (item 2). No
target is used as non-string data whose bytes after the NUL matter.

## 2. TABLE rows (9 + OpenFile)

| row | record lines | X/Y | consumer (X-A) | index bound / entry width | bytes compared | result |
|---|---|---|---|---|---|---|
| Allocator::Deallocate +0x20c | C:1, P:94 | 0x103e8/0x103e0 | +0x1f8..+0x214 `neg; and; mul (0x103b8 const); srli a3,a3,0x3a; add; lbu a3,0(a3)` | 6-bit index (srli 58): 64 entries x 1 byte | 64 (equal prefix 4096) | CONFIRMED |
| Allocator::Allocate +0xdc | C:2, P:95 | 0x10428/0x10420 | +0xc8..+0xe4 same pattern, `lbu a1,0(a1)` | 64 x 1 byte | 64 | CONFIRMED |
| SizeClassAllocator64::MaybeReleaseToOS +0x140 | C:3, P:21 | 0x10468/0x10460 | +0x128..+0x148 same, `srli a3,a3,0x3a; lbu` | 64 x 1 byte | 64 | CONFIRMED |
| SizeClassAllocator64::ReleaseFreeMemoryToOS +0x128 | C:4, P:22 | 0x104a8/0x104a0 | +0x114..+0x130 same, `srli a1,a1,0x3a; lbu` | 64 x 1 byte | 64 | CONFIRMED |
| SizeClassAllocator64::PackedCounterArray ctor +0x190 | C:5, P:23 | 0x104e8/0x104e0 | +0x170..+0x19c same, `srli a2,a2,0x3a; lbu` | 64 x 1 byte | 64 | CONFIRMED |
| RZSize2Log +0x44 | C:6, P:96 | 0x10528/0x10520 | +0x30..+0x54 same, `srli a1,a1,0x3a; lbu a2,0(a1)` | 64 x 1 byte | 64 | CONFIRMED |
| HeapAddressDescription::Print +0xbc | C:8, P:16 | 0x17717/0x17754 | +0xb8 `addi a1,..=0x17717; addi a0,sp,0x10; jal InternalScopedString::Append` | NO index: settle.py took the bound from `srli a0,a0,0x3e` at +0xd4 (a chunk-state bit field read by the next statement) | 4 as a "table"; equal prefix 4096 covers the 9 bytes + NUL | FINDING F3 (a C string, equal) |
| PrintMemoryByte +0x70 | C:56, P:80 | 0x13e67/0x13e7d | +0x70 `addi a3,..=0x13e67` -> a3 of AppendF "%s%s%x%x%s%s" (+0xc4) | NO index: bound from `andi a1,a1,1` at +0x54 (the Decorator colour bool) | 2; equal prefix 462 covers the NUL | FINDING F3 (a C string, equal) |
| PrintMemoryByte +0x88 | C:57, P:81 | 0x18dc0/0x18dec | +0x88 `addi a6,..=0x18dc0` -> a6 of the same AppendF (+0xc4) | NO index: bound from `andi a1,a1,1` at +0x78 | 2; equal prefix 4049 covers the 8 bytes + NUL | FINDING F3 (a C string, equal) |
| OpenFile +0x60 (by hand) | C:69, P:1 (settle: CSTR) | 0x209a0/0x209f4 | +0x50..+0x68 `addi a1,zero,2; bltu a1,s1,+0x70; slli s1,s1,2; addi a1,..=0x209a0; add; lw a1,0(a1)` | index <= 2: 3 entries x 4 bytes (int32) | 12: `00000000 41020000 42000000` = 0, 0x241, 0x42 on X-A, X-B, Y-A, Y-B (byte 12 differs: 0xcd / 0xb1, the next table) | CONFIRMED |

The six De Bruijn tables are each a permutation of 0..63, the same on both sides in both images (checked: 64 bytes equal).
Image B has the same consumer instructions and the same table addresses.

## 3. The four by-hand functions

- **Decorator::ShadowByte** (X-A 0x54938, size 160). +0x0..+0x2c: `addi a1,a1,-0xac; addi a2,zero,0x52; bltu a2,a1,+0x8c;
  slli a1,a1,2; table 0x2066c; lw; add; addi a1,..=0x17781; jr a2`. The 83 table entries go to six arms: +0x30 (4 entries),
  +0x44 (3), +0x58 (2), +0x6c (1), +0x74 (6, red), +0x8c (67, default). Each arm loads one colour into a1: +0x34 0x1f9bd
  `\e[1m\e[34m`, +0x48 0x1d71c `\e[1m\e[35m`, +0x5c 0x201ab `\e[1m\e[33m`, +0x70 0x1090b `\e[1m\e[36m`, +0x90 0x18dc0
  `\e[1m\e[0m`. Then `lbu a0,0(a0)` reads `this->ansi_`, and if it is 0, a1 = +0x80 0x13e67 `""`. Return at +0x84
  `mv a0,a1; ret`. Byte check: the six strings are equal with their NUL on both sides in both images, and they are the
  strings that the README names. The only caller, PrintMemoryByte +0x44, passes the result as a3 of AppendF
  "%s%s%x%x%s%s" (0x1d8a4). The C-string reading is CONFIRMED. The README's evidence sentence is wrong: see FINDING F4.
  The kit rule needs printable bytes (strictcmp2.py:58 `PRINTABLE = range(32,127) | {9,10,13}`; :145 needs k > 0), so ESC
  and "" are not measured. CONFIRMED.
- **CFI_Parser::parseCIE +0x23c** (X-A 0x823f4). +0x234 `addi s5,zero,0x2e`; +0x23c table s6 = 0x20c94 (Y 0x20d74);
  +0x254 `addi a1,a0,-0x4c; bltu s5,a1,+0x2f0; slli a1,a1,2; add a1,a1,s6; lw a0,0(a1); add a0,a0,s6; jr a0`. Relative
  32-bit jump table, index = c - 'L', bound 46 -> 47 entries ('L'..'z'). My measurement: entries 0..46 give the same
  function offsets on both sides (6 distinct arms +0x248, +0x24c, +0x270, +0x28c, +0x298, +0x2b4). Entry 47 leaves the
  function on both sides (X-A 0x83c1c / Y-A 0x84254; X-B 0x83cb0 / Y-B 0x84120). The bound and table code are the same in
  X-B, Y-A and Y-B. Matches records/byhand-*.txt:15 (`47 entries ... bound constants [255, 122, 46]`). CONFIRMED.
- **SignalContext::Describe +0x1c** (X-A 0x65ea0, size 60). `lw a0,0(a0); addiw a0,a0,-4; addi a1,zero,7; bltu a1,a0,+0x30;
  slli a0,a0,2; table 0x209ac; add; lw a0,0(a0); add a0,a1,a0; ret`. Eight relative 32-bit entries (sig - 4, bound 7)
  that point to strings. My measurement on both images: ILL, TRAP, ABRT, BUS, FPE, UNKNOWN SIGNAL, UNKNOWN SIGNAL, SEGV,
  equal with NUL on both sides. Entry 8 is not a string (X-A 0x6629c). The claim is CONFIRMED, but records/byhand-* does
  not contain this measurement: see FINDING F5.
- **__strftime_fmt_1 +0x530 / +0x54c**: both are `addi a0,..=0x13e67` after `sd zero,0(s0)` (*l = 0), then return. They are
  the empty string at X 0x13e67 / Y 0x13e7d, equal with NUL in both images. The caller reads only t[0] (item 1 notes).
  CONFIRMED.

## 4. Recount

| README number | record evidence | my recount | result |
|---|---|---|---|
| closure A: 785, EQUAL 173, mod-pcrel 550, other 62 | closure-asan.txt:1 | same (kit re-run, byte-identical output) | CONFIRMED |
| closure B: 785, EQUAL 171, mod-pcrel 552, other 62 | closure-asan-ubsan.txt:1 | same | CONFIRMED |
| paircl A: 944, EQUAL 214, mod-pcrel 663, other 67, 0 conflicts | paircl-asan.txt:2 | same | CONFIRMED |
| paircl B: 944, EQUAL 212, mod-pcrel 665, other 67, 0 conflicts | paircl-asan-ubsan.txt:2 | same | CONFIRMED |
| closure "(91 targets)" per image | 91 targets printed in 62 rows | the kit reports **162** differing targets per image (161 data-differs, 1 cstr-differs) | FINDING F1 |
| paircl "(97 targets)" per image | 100 printed in 67 rows (96 data, 1 cstr, 3 unmeasured) | the kit reports **178** per image (sum of `target-diff N`; 174 data-differs, 1 cstr-differs, 3 unmeasured) | FINDING F1, F2 |
| TABLE 9 / 9 | settle-*: TABLE 9 | 9 rows, but 3 of them are C strings | FINDING F3 |
| OpenFile 1 / 1 | settle C:69, P:1 | 1 | CONFIRMED |
| CSTR 65 / 71; empty string 42 / 46 | settle CSTR 66 / 72 minus OpenFile | 65 / 71; 42 / 46 at 0x13e67 | CONFIRMED (68 / 74 with the F3 rows) |
| jtcheck-settled 16 / 16 (15 functions) | settle OPEN 16; jtcheck-open-*.txt | 11 functions with differs 0, unmeasured 0, unpaired 0 (lines 1, 3, 23, 46, 61, 63, 171, 179, 206, 234, 236), 4 open (ShadowByte 6 unmeasured, parseCIE 1 differs, Describe 1 unmeasured, strftime 2 unmeasured) | CONFIRMED |

## FINDINGS

**F1. The record settles only the first two differing targets of each function.** `closure_strict2.py:88` prints
`(diff or [])[:2]` and `paircl.py:67` keeps `diff[:2]`. tools/settle.py reads only the printed targets. The kit's own
`strictcmp2.tcmp` on the 62 closure rows gives 162 differing targets per image; the record shows 91. On the 67 paircl rows
it gives 178 (the rows' own `target-diff N` adds up to 178); the record shows 100. So 71 closure targets and 78 paircl
targets per image (78 distinct, 7 of them only in paircl) were never measured by the record. The README sentence "Every row
that the kit leaves unsettled ... Each one is settled below" is false as written. The target counts 91 / 97 are counts of
printed targets. My measurement of the 78 (table below): each is an ANSI colour string or "", equal with its NUL on both
sides in both images, and used as a C string. 7 of them (ShadowByte +0x34, +0x48, +0x5c, +0x70, +0x80, +0x90 and
__strftime_fmt_1 +0x54c) are the README's jtcheck by-hand targets. The other 71 (64 in closure, 71 in paircl) are outside
every record measurement. So the code verdict holds, but the record does not show it.

| unprinted target | in run | X/Y | string | equal with NUL (A and B) | consumer use (X-A) |
|---|---|---|---|---|---|
| ReportDeadlySignal+0xcc | closure+paircl | 0x17781/0x177be | '\e[1m\e[31m' | yes | +0x200 Printf(a1, fmt '%s') |
| ReportDeadlySignal+0xd0 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x240 Printf(a1, fmt '%s') |
| ReportDeadlySignal+0xe0 | closure+paircl | 0x17781/0x177be | '\e[1m\e[31m' | yes | +0x2ac Printf(a1, fmt '%s') |
| ReportDeadlySignal+0xe4 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x338 Printf(a1, fmt '%s') |
| ReportDeadlySignal+0x15c | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0x200,+0x240 Printf(a1, fmt '%s') |
| ReportDeadlySignal+0x1d8 | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0x2ac,+0x338 Printf(a1, fmt '%s') |
| ReportDeadlySignal+0x1ec | closure+paircl | 0x17781/0x177be | '\e[1m\e[31m' | yes | +0x200 Printf(a1, fmt '%s') |
| ReportDeadlySignal+0x1f0 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x240 Printf(a1, fmt '%s') |
| ReportDeadlySignal+0x29c | closure+paircl | 0x17781/0x177be | '\e[1m\e[31m' | yes | +0x2ac Printf(a1, fmt '%s') |
| ReportDeadlySignal+0x2a0 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x338 Printf(a1, fmt '%s') |
| ReportDeadlySignal+0x6b0 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | spilled to 0x10(sp), reloaded +0x6dc into a6 = last %s of AppendF "%s%s%x%x%s " (0x13c43) at +0x6f4 |
| ReportDeadlySignal+0x6b8 | closure+paircl | 0x1d71c/0x1d754 | '\e[1m\e[35m' | yes | s11 -> a3 = 2nd %s of AppendF "%s%s%x%x%s " at +0x6f4 |
| ReportDeadlySignal+0x6c0 | closure+paircl | 0x13e67/0x13e7d | '' | yes | s7 -> a2 = 1st %s of AppendF "%s%s%x%x%s " (+0x6f4), and a3/a6 when colour is off; the a6 copy live at ReopenIfNecessary +0x780 / LockSlow +0x7a8 is not read by those callees (tracer artefact) |
| ErrorGeneric::Print+0xa0 | closure+paircl | 0x13e67/0x13e7d | '' | yes | Printf "%s" (+0xc4); a1 = 1st %s and a6 = 6th %s of "%s%s of size %zu at %p thread %s%s\n" (+0x13c) |
| ErrorGeneric::Print+0xb4 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | Printf "%s" (+0xc4); a6 = last %s of "%s%s of size %zu at %p thread %s%s\n" (+0x13c) |
| ErrorGeneric::Print+0xd0 | closure+paircl | 0x1f9bd/0x1fa0b | '\e[1m\e[34m' | yes | a1 = 1st %s of "%s%s of size %zu at %p thread %s%s\n" (+0x13c) |
| ErrorGeneric::Print+0x34c | closure+paircl | 0x13e67/0x13e7d | '' | yes | "before" (a1) / "after" (a4) of PrintMemoryByte at 15 call sites +0x378..+0x7f4; PrintMemoryByte passes them as a2 / a7 = 1st / 6th %s of AppendF "%s%s%x%x%s%s" |
| ErrorGeneric::Print+0x898 | closure+paircl | 0x13e67/0x13e7d | '' | yes | "before" (a1) of PrintMemoryByte at 7 call sites +0x8ac..+0x954 (AppendF %s) |
| ErrorDoubleFree::Print+0x90 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0xa0 Printf(a1, fmt "%s" held in an s-register, 0x16f7d) |
| PrintMemoryByte+0x94 | closure+paircl | 0x1d71c/0x1d754 | '\e[1m\e[35m' | yes | a3 = 2nd %s of AppendF "%s%s%x%x%s%s" (+0xc4) |
| PrintMemoryByte+0xac | closure+paircl | 0x13e67/0x13e7d | '' | yes | a6 = 5th %s of AppendF "%s%s%x%x%s%s" (+0xc4) |
| ErrorOutOfMemory::Print+0x74 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x80 Printf(a1, fmt "%s" held in an s-register, 0x16f7d) |
| ErrorODRViolation::Print+0x74 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x80 Printf(a1, fmt "%s" held in an s-register, 0x16f7d) |
| ErrorCallocOverflow::Print+0x8c | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x98 Printf(a1, fmt "%s" held in an s-register, 0x16f7d) |
| ErrorFreeNotMalloced::Print+0x80 | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0x98 Printf(a1, fmt '%s') |
| ErrorFreeNotMalloced::Print+0x8c | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x98 Printf(a1, fmt '%s') |
| ErrorPvallocOverflow::Print+0x98 | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0xb0 Printf(a1, fmt '%s') |
| ErrorPvallocOverflow::Print+0xa4 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0xb0 Printf(a1, fmt '%s') |
| ErrorRssLimitExceeded::Print+0x70 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x7c Printf(a1, fmt "%s" held in an s-register, 0x16f7d) |
| ErrorAllocTypeMismatch::Print+0xb8 | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0xd0 Printf(a1, fmt '%s') |
| ErrorAllocTypeMismatch::Print+0xc4 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0xd0 Printf(a1, fmt '%s') |
| ErrorInvalidPointerPair::Print+0x90 | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0xa8 Printf(a1, fmt '%s') |
| ErrorInvalidPointerPair::Print+0x9c | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0xa8 Printf(a1, fmt '%s') |
| ErrorAllocationSizeTooBig::Print+0x98 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0xa4 Printf(a1, fmt "%s" held in an s-register, 0x16f7d) |
| ErrorReallocArrayOverflow::Print+0x8c | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x98 Printf(a1, fmt "%s" held in an s-register, 0x16f7d) |
| ErrorNewDeleteTypeMismatch::Print+0x88 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x98 Printf(a1, fmt '%s  object passed to delete has wrong ty') |
| ErrorMallocUsableSizeNotOwned::Print+0x6c | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0x84 Printf(a1, fmt '%s') |
| ErrorMallocUsableSizeNotOwned::Print+0x78 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x84 Printf(a1, fmt '%s') |
| ErrorInvalidAllocationAlignment::Print+0x80 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x8c Printf(a1, fmt "%s" held in an s-register, 0x16f7d) |
| ErrorStringFunctionSizeOverflow::Print+0x74 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x80 Printf(a1, fmt "%s" held in an s-register, 0x16f7d) |
| ErrorInvalidAlignedAllocAlignment::Print+0x8c | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x98 Printf(a1, fmt "%s" held in an s-register, 0x16f7d) |
| ErrorInvalidPosixMemalignAlignment::Print+0x84 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x90 Printf(a1, fmt "%s" held in an s-register, 0x16f7d) |
| ErrorSanitizerGetAllocatedSizeNotOwned::Print+0x6c | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0x84 Printf(a1, fmt '%s') |
| ErrorSanitizerGetAllocatedSizeNotOwned::Print+0x78 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x84 Printf(a1, fmt '%s') |
| ErrorStringFunctionMemoryRangesOverlap::Print+0xb0 | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0xd0 Printf(a1, fmt '%s') |
| ErrorStringFunctionMemoryRangesOverlap::Print+0xbc | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0xd0 Printf(a1, fmt '%s') |
| Decorator::ShadowByte+0x34 | closure+paircl | 0x1f9bd/0x1fa0b | '\e[1m\e[34m' | yes | returned in a0 (+0x84/+0x88) to PrintMemoryByte +0x44 -> a3 of AppendF "%s%s%x%x%s%s" |
| Decorator::ShadowByte+0x48 | closure+paircl | 0x1d71c/0x1d754 | '\e[1m\e[35m' | yes | returned in a0 (+0x84/+0x88) to PrintMemoryByte +0x44 -> a3 of AppendF "%s%s%x%x%s%s" |
| Decorator::ShadowByte+0x5c | closure+paircl | 0x201ab/0x201fd | '\e[1m\e[33m' | yes | returned in a0 (+0x84/+0x88) to PrintMemoryByte +0x44 -> a3 of AppendF "%s%s%x%x%s%s" |
| Decorator::ShadowByte+0x70 | closure+paircl | 0x1090b/0x10903 | '\e[1m\e[36m' | yes | returned in a0 (+0x84/+0x88) to PrintMemoryByte +0x44 -> a3 of AppendF "%s%s%x%x%s%s" |
| Decorator::ShadowByte+0x80 | closure+paircl | 0x13e67/0x13e7d | '' | yes | returned in a0 (+0x84/+0x88) to PrintMemoryByte +0x44 -> a3 of AppendF "%s%s%x%x%s%s" |
| Decorator::ShadowByte+0x90 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | returned in a0 (+0x84/+0x88) to PrintMemoryByte +0x44 -> a3 of AppendF "%s%s%x%x%s%s" |
| LeakReport::PrintReportForLeak+0x9c | paircl | 0x13e67/0x13e7d | '' | yes | +0xb4 Printf(a1, fmt '%s') |
| LeakReport::PrintReportForLeak+0xa8 | paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0xb4 Printf(a1, fmt '%s') |
| __lsan::PrintResults+0xb8 | paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0xc4 Printf(a1, fmt "%s" held in an s-register, 0x16f7d) |
| __lsan::CheckForLeaks+0x584 | paircl | 0x17781/0x177be | '\e[1m\e[31m' | yes | +0x594 Printf(a1, fmt '%s') |
| __lsan::CheckForLeaks+0x5ac | paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x5b8 Printf(a1, fmt "%s" held in an s-register, 0x16f7d) |
| __lsan::CheckForLeaks+0x620 | paircl | 0x17781/0x177be | '\e[1m\e[31m' | yes | +0x630 Printf(a1, fmt '%s') |
| __lsan::CheckForLeaks+0x648 | paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x654 Printf(a1, fmt "%s" held in an s-register, 0x16f7d) |
| HeapAddressDescription::Print+0x154 | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0x168 Append(a1) |
| HeapAddressDescription::Print+0x160 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x168 Append(a1) |
| HeapAddressDescription::Print+0x1e4 | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0x30c Printf(a1, fmt '%sallocated by thread %s here:%s\\n') |
| HeapAddressDescription::Print+0x248 | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0x30c Printf(a3, fmt '%sallocated by thread %s here:%s\\n') |
| HeapAddressDescription::Print+0x264 | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0x3a8 Printf(a1, fmt '%sfreed by thread %s here:%s\\n'); +0x450 Printf(a1, fmt '%spreviously allocated by thread %s here') |
| HeapAddressDescription::Print+0x2c8 | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0x3a8 Printf(a3, fmt '%sfreed by thread %s here:%s\\n'); +0x450 Printf(a3, fmt '%spreviously allocated by thread %s here') |
| HeapAddressDescription::Print+0x2d4 | closure+paircl | 0x1d71c/0x1d754 | '\e[1m\e[35m' | yes | +0x30c Printf(a1, fmt '%sallocated by thread %s here:%s\\n') |
| HeapAddressDescription::Print+0x2f8 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x30c Printf(a3, fmt '%sallocated by thread %s here:%s\\n') |
| HeapAddressDescription::Print+0x36c | closure+paircl | 0x1d71c/0x1d754 | '\e[1m\e[35m' | yes | +0x3a8 Printf(a1, fmt '%sfreed by thread %s here:%s\\n'); +0x450 Printf(a1, fmt '%spreviously allocated by thread %s here') |
| HeapAddressDescription::Print+0x390 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x3a8 Printf(a3, fmt '%sfreed by thread %s here:%s\\n'); +0x450 Printf(a3, fmt '%spreviously allocated by thread %s here') |
| StackAddressDescription::Print+0xa0 | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0xcc Printf(a2, fmt ' at offset %zu in frame%s\\n'); +0xdc Printf(a1, fmt '%s') |
| StackAddressDescription::Print+0xb0 | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0x458 Printf(a1, fmt '%s\\n') |
| StackAddressDescription::Print+0xbc | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0xcc Printf(a2, fmt ' at offset %zu in frame%s\\n'); +0xdc Printf(a1, fmt '%s') |
| StackAddressDescription::Print+0x18c | closure+paircl | 0x13e67/0x13e7d | '' | yes | spilled to 0x18(sp), reloaded +0x3c0 into a2 and a5 = 1st / last %s of AppendF "%s <== Memory access at offset %zd %s this variable%s\n" (+0x3f4) |
| StackAddressDescription::Print+0x3d4 | closure+paircl | 0x17717/0x17754 | '\e[1m\e[32m' | yes | a2 = 1st %s of AppendF "%s <== Memory access at offset %zd %s this variable%s\n" (+0x3f4) |
| StackAddressDescription::Print+0x3d8 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | a5 = last %s of the same AppendF (+0x3f4) |
| StackAddressDescription::Print+0x44c | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x458 Printf(a1, fmt '%s\\n') |
| GlobalAddressDescription::Print+0xa4 | closure+paircl | 0x18dc0/0x18dec | '\e[1m\e[0m' | yes | +0x214 Append(a1) |
| __strftime_fmt_1+0x54c | closure+paircl | 0x13e67/0x13e7d | '' | yes | +0x544 sd zero,0(s0) (*l = 0), return "" (+0x614); caller reads t[0] only |

**F2. Three 'unmeasured' targets in paircl are not settled or named.** paircl-asan.txt and -asan-ubsan.txt row
`_ZN6__lsanL21CheckForLeaksCallback...` (targets +0x484, +0x48c) and row `__sanitizer_dump_coverage` (+0x118) carry
`'I/S-type word on an auipc register, not a compared target', 'unmeasured'`. settle.py keeps only data-differs /
cstr-differs targets, the README's 97 leaves them out, and the README says every other row's targets are
data-differs / cstr-differs. My measurement: CheckForLeaksCallback +0x484 `addi a1,a3,1` and +0x48c `slli a3,a3,3` start
at +0x480. The only way to reach +0x480 is a branch (`j` at +0x47c is the instruction before it). The branches are at
+0x808 and +0x828, after `ld a3,0x140(sp)` (vector size). dump_coverage +0x118 `addi a0,a0,-1` is reached only from
+0x170, +0x1a0 and +0x1c8 (`j` at +0x114 is the instruction before it), with a0 as the heap-sort counter. The words are
byte-identical in X and Y on both images. They are integer operations, not pc-relative uses, so they are not a
difference. But the record does not settle them.

**F3. Three TABLE rows are C strings.** HeapAddressDescription::Print +0xbc, PrintMemoryByte +0x70 and +0x88 (item 2).
settle.py's `index_bound` (tools/settle.py:52-62) takes any `andi` / `srli >= 56` within 8 words, and here those
instructions are not related to the target. The README's "2- and 4-entry tables in PrintMemoryByte and
HeapAddressDescription::Print" is false. As C strings they are equal with their NUL (equal prefixes 4096 / 462 / 4049), so
there is no code difference. The correct counts are TABLE 6 / 6 and CSTR 68 / 74.

**F4. The README's ShadowByte evidence sentence is wrong.** README.md:42 says "The consumer reads them byte by byte
(`lbu a0, 0(a1)` loop)". ShadowByte has no such loop. Its `lbu a0,0(a0)` (+0x38, +0x4c, +0x60, +0x74, +0x94) reads the
Decorator's colour flag. The strings are returned (`mv a0,a1; ret`, +0x84) to PrintMemoryByte, which prints them with
AppendF "%s". The conclusion (C strings) is correct.

**F5. The Describe claim has no measurement in the record.** README.md:48-50 (8 relative entries, bound 7, the 8 equal
signal names) cites records/byhand-*. But byhand-*.txt:16-17 has only `CSTR-ANY DIFFER`. byhand.py prints a JT32 line
only when entry 0 lands inside the function (tools/byhand.py:66-75), and these entries point to .rodata strings. My
measurement (item 3) confirms the claim.

**F6. README.md:36 "the rest are messages, flag names and the ANSI colour strings".** The 23 (closure) / 25 (paircl)
non-empty CSTR targets are all ANSI colour strings (0x17781 x21 / x22, 0x17717 x2, 0x1f9bd x0 / x1). There is no message or
flag name among them. This is a documentation error only.

## Extra check (outside the brief): the kit's own CSTR acceptances

The pool owner's ruling covers the kit's printable C-string acceptances too: the CSTR lines in closure-*, paircl-* and
jtcheck-open-*, 3533 distinct (function, offset) per image. I ran the same dataflow walk on all of them in both images.
It flagged 6 for a closer look, and I read each one: VSNPrintf +0x21c "<null>" (a byte-by-byte loop up to the NUL),
__vsyslog +0x13c / +0x140 "[" / "]" (`"[" + !pid`, which reads at most the NUL), do_tzset +0x5c "/etc/localtime" (strcmp /
strlen / memcpy of strlen+1; s[1] is read only after s[0] == ':'), StackAddressDescription +0x2cc "overflows" (a
branchless pointer select), ReportFile::SetReportPath +0x188 "\n" (the flagged store is on the path after the noreturn
`Die()`). None of them is used as non-string data. This is an automated pass plus these 6 readings, not a by-hand reading
of all 3533.

## Verdict

Items checked: 72 CSTR targets (144 rows), 10 TABLE rows, 4 by-hand functions (10 targets), 10 recount lines. Also 78
unprinted targets and 3 unmeasured words (F1, F2), and an automated pass over 3533 kit CSTR acceptances. FINDINGS: F1-F6.

- "No code difference": STANDS on my measurements. Every differing target of every reported function on both runs and both
  images, including the ones the record never saw, is an equal C string used as a C string, an equal bounded table, an
  equal relative jump table or string table, or (F2) an integer word that the kit linked to an auipc by mistake.
- "Every unsettled row settled": DOES NOT STAND as written. The record never measured 71 distinct targets per image (F1) or the 3
  unmeasured words (F2), its target counts 91 / 97 are counts of printed targets, and its TABLE count includes 3 C strings
  (F3). To make the record complete, settle the full `tcmp` target list (not the printed `[:2]`), include `unmeasured`
  targets, and fix the README text for F3-F6.

## Re-check of v2

Record: the record's working commit 6ec81ea98d60 (v2 = 833c5da53b35 plus the README paragraph at lines 25-29), same
directory. Read-only, same images and kit as above. Record line references in this section: `S2:n` =
records/settle2-asan.txt line n, `CS:n` = records/closure-settlement-asan.txt line n, `JO:n` = records/jtcheck-open-asan.txt,
`JM:n` = records/jtcheck-members-asan.txt, `BH:n` = records/byhand-asan.txt. The -asan-ubsan files have the same rows on
the same lines (checked for settle2, closure-settlement and byhand).

Reproduction (kit directory, `PYTHONDONTWRITEBYTECODE=1`): `tools/settle2.py` on both images, `tools/byhand.py` on the
ten targets on both images, and the kit's `jtcheck.py` on the 15 jtcheck-open names give records/settle2-*,
records/byhand-* and records/jtcheck-open-* byte for byte. `jtcheck.py` on the 173 names of records/jtcheck-members-*
gives that file byte for byte except its first line `\tSKIP None None`, which comes from an empty name in the original
name list (jtcheck.py:200).

### Item 1. settle2's full-list counts and its CSTR set: CONFIRMED

- I called the kit's own `strictcmp2.tcmp` myself: closure rows against the pcap twin, paircl rows against the
  stripped pin, with paircl.py's PT_LOAD layout check. Per image this gives 178 targets keyed by (X address, offset):
  162 closure + 16 paircl-only, with 174 data-differs, 1 cstr-differs and 3 unmeasured. Each paircl row's printed
  `target-diff N` equals its list length. settle2's 178 rows are the same 178 keys, with the same closure / paircl tags.
  The classes are TABLE 7, CSTR 152, WORD-EQUAL 3 and OPEN 16 (S2:179), the same on A and B by name + offset. Keyed by
  name, the list has 179 entries, because ErrorGeneric's constructor has two names at one address (C2 and C1). settle2
  keys by address, which is correct.
- settle2's CSTR set equals my 71 + 78 + 3 exactly, on both images. 71 = the v1 CSTR rows (97ab13e41f99
  records/settle-*) minus OpenFile. 78 = the full list minus the targets that closure_strict2 / paircl print. 3 = F3
  (HeapAddressDescription::Print +0xbc, PrintMemoryByte +0x70, +0x88). The three sets are disjoint and their union is
  152. My own byte check of all 152 (target addresses from `targets()`, equal to settle2's): equal up to and including
  the NUL. The strings are `""` x72 and ESC colour strings x80 (`\e[1m\e[31m` 28, `\e[1m\e[0m` 38, `\e[1m\e[35m` 5,
  `\e[1m\e[32m` 4, `\e[1m\e[34m` 3, `\e[1m\e[33m` 1, `\e[1m\e[36m` 1). Their consumers are the ones read in items 1
  and 2 and in F1 above.
- The 3 WORD-EQUAL words (S2:176-178) are F2's words, byte-equal in X and Y.

### Item 2. The 7 TABLE rows by settle2's `table_reading`: CONFIRMED

I executed tools/settle2.py:60-103 (`W` and `table_reading`) on every one of the 178 targets on both images. It gives
a reading for 19 targets: the 7 TABLE rows (S2:1-6 and S2:126) and 12 OPEN tables whose bytes differ (jump
or pointer tables, Describe's string table). It gives None for all 152 CSTR rows, the three F3 targets among them.
The 7 are the six De Bruijn tables, 64 entries x 1 byte (index from `srli 58`), and OpenFile +0x60, 3 x 4 bytes
(`addi a1,zero,2; bltu a1,s1` with `slli s1,s1,2`, `lw`). I checked that the first k*w bytes are equal on both sides.
Two notes on the rule, neither of which affects these 7. A `bgeu rI, rK` bound is counted as K+1 entries where K is
correct, which over-counts, so it fails closed. The backward walk for the index definition goes by address and does
not follow paths.

### Item 3. Coverage of the 16 OPEN targets: CONFIRMED

- **12 targets in the 11 jtcheck-SETTLED functions.** JO:1, 3, 23, 46, 61, 63, 171, 179, 206, 234 and 236 each read
  `target differs 0, target unmeasured 0, unpaired 0`, and each has an ACCEPT at the OPEN offset (getEncodedP at
  +0x28 and +0x1a8). My own measurement, on A and B:
  - Relative jump tables. Every entry has the same function offset in X and Y over the bound: AddressDescription::Print
    +0x14 (5), ErrorGeneric ctor +0x224 (82), ErrorDescription::Print +0x1c (25), force_interface_symbols +0x20 (52),
    getEncodedP +0x28 (13) and +0x1a8 (6), getTableEntrySize +0x24 (12), sysconf +0xdc (13), VSNPrintf +0x1c0 (33:
    `addi s0,zero,0x20` at +0x68, `bltu s0,a7` at +0x1b4), parseFDEInstructions +0x140 (48: `addi s1,zero,0x2f` at
    +0xd0, `bltu s1,s9` at +0x134).
  - GetHandleSignalMode +0x24. Bound `addi a1,zero,7; bltu a1,a0` gives 8 absolute .data.rel.ro pointers. Each names
    the same `common_flags_dont_use+off` on both sides.
  - __synccall +0x54. `addi a2,zero,0x98; jal __wrap_memcpy` copies a 152-byte .data.rel.ro initializer. 18 words are
    raw-equal, and word 0 is `handler+0` on both sides.
- **ShadowByte +0x14 and __strftime_fmt_1 +0x44.** JO:52 and JO:210 read `target differs 0`. JO:59 is `ACCEPT table
  +0x14 rel4-jump 83 entries` and JO:213 is `ACCEPT table +0x44 rel4-jump 86 entries`. My relative-table compare
  agrees: 83 and 86 entries with the same function offsets on A and B. Their unmeasured items are CSTR rows: S2:111-116
  (ShadowByte +0x34 ... +0x90) and S2:161-162 (strftime +0x530, +0x54c).
- **parseCIE +0x23c.** BH:15 is JT32-rel with 47 entries, and my measurement (above, item 3) agrees.
- **SignalContext::Describe +0x1c.** BH:18 reads `STRTAB32-rel 8 entries are equal C strings (NUL included): ILL, TRAP,
  ABRT, BUS, FPE, UNKNOWN SIGNAL, UNKNOWN SIGNAL, SEGV; stop: entry 8 ...; consumer bound constants [7]`. The new
  tools/byhand.py:76-89 reads each entry relative to the table and compares the strings with their NUL. My measurement
  gives the same 8 strings on A and B, with bound `addi a1,zero,7; bltu a1,a0`. F5 is closed.

### Item 4. '735 kit-certified (723 + 12 jtcheck) / 50 measured': arithmetic CONFIRMED, two FINDINGS

- The arithmetic holds. 723 = 173 + 550 = 171 + 552 (closure-*:1). closure-settlement has 62 rows, the closure_strict2
  'other' set: KIT-JTCHECK 12 and MEASURED 50. For all 50 MEASURED functions, the per-class counts equal settle2's
  closure-tagged rows. The MEASURED functions hold 149 targets (CSTR 138, TABLE 7, OPEN 4), and the KIT-JTCHECK
  functions hold 13 (12 OPEN and PlatformInit's 1 CSTR). 149 + 13 = 162, the closure full list. The 12 KIT-JTCHECK
  functions are exactly the 11 jtcheck-open functions settled there, plus PlatformInit (JM:62, settled).

**G1. The 735 / 50 split depends on which functions were given to jtcheck.** README.md:23 says "jtcheck over the closure
members", but records/jtcheck-members-* holds 173 of the 785 members. Only 11 of the 62 'other' functions are among
them: PlatformInit, ReportDeadlySignal, the three SizeClassAllocator64 functions, InitializeFlags, Allocator::Allocate,
Allocator::Deallocate, RZSize2Log, __asan_describe_address and __strftime_fmt_1. LoadedModule::addAddressRange is not
among them. The same kit jtcheck 824905e26211 on all 62 (my run, A and B) settles 13 functions: the 12 KIT-JTCHECK
functions plus addAddressRange (`ACCEPT ... initializer +0x70 [0x13e67|0x13e7d] 16`). That gives 736 / 49, which is
the central re-run's count. The README's Commands section gives no command or name list for jtcheck-members.

**G2. Both jtcheck settlements of the empty string are misreadings by jtcheck's heuristics, not readings of the
code.** The bytes are equal, so neither one hides a difference.
- PlatformInit +0x18c (JM:64, `table abs8-ptr 2 entries (bound check)`): `jtcheck.bound()` (jtcheck.py:137) took
  `addi a1,zero,2; bgeu a0,a1` at +0x164 / +0x168 (X-A 0x770a4) as the table bound. That instruction pair is a
  verbosity test, 9 words before the target's auipc. The target is the `""` that +0x234 ... +0x25c pass to
  internal_strncmp / internal_strcmp.
- addAddressRange +0x70 (`initializer 16`): `jtcheck.memcpy_len()` (jtcheck.py:154) accepts any jal after
  `addi a2,zero,L`. Here that jal is `internal_strncpy(dst, "", 16)` (+0x74 ... +0x7c), which reads the source only up
  to its NUL.
- In both cases, the 16 compared bytes (`00 27 00 48 49 4e 54 3a 20 69 66 20 79 6f 75 20`, the same on both sides)
  include the NUL. So each acceptance is a true byte equality, and the C string is equal.
- The correct reading of both targets is the CSTR row (S2:129 and S2:121), and my v1 consumer audit covers both. So
  "kit-certified" for PlatformInit here, and for both functions in the central re-run, rests on a heuristic that
  misfired.
- The same misfire appears at JO:60 (ShadowByte +0x28: the red string read as an 83-entry abs8 pointer table, bound
  taken from the jump-table dispatch). The record does not rely on it: S2:110 classes +0x28 as CSTR.
- For the kit owner (outside this record): `bound()` and `memcpy_len()` are matched by syntax only. When they misfire
  on a non-table target, jtcheck compares only k*8 or L bytes, where tsame would compare the whole region and fail
  closed.

### The new paragraph (README.md:25-29)

- "The central re-run ... counts 736 / 49": CONFIRMED. STRICTCMP-RERUN.md:77 at bdc037d1af2a ("It certifies 736 of 785
  closure members"). rerun/memmove/RESULT.md says "closure_strict2 certifies 723 of 785 members, the kit jtcheck 13
  more; the other 49 closure members are NOT certified by the kit".
- "The one function in which they differ is LoadedModule::addAddressRange (A 0x5f8f4, B 0x5f694)": CONFIRMED. My
  jtcheck run over the 62 settles exactly the KIT-JTCHECK set plus addAddressRange, and the addresses match the
  unstripped twins.
- "Its +0x70 target is the empty string X 0x13e67 / Y 0x13e7d, passed to `internal_strncpy(.., "", 16)`":
  CONFIRMED. The code at +0x68 ... +0x7c is `bnez s3; addi s3,..=0x13e67; addi a2,zero,0x10; mv a1,s3; jal
  internal_strncpy`.
- "That re-run's jtcheck settles it as an equal 16-byte initializer; here it is a CSTR row": true, but incomplete (G1).
  Here it is a CSTR row only because this record never passed addAddressRange to jtcheck. The same kit jtcheck settles
  it on these images.
- "Both readings hold, and neither is a difference": "neither is a difference" is CONFIRMED. "Both readings hold" is
  FINDING G2: the initializer reading does not describe the code (strncpy is not a 16-byte copy). It holds only as a
  16-byte equality that covers the NUL.

### v2 result

Items 1-3 are CONFIRMED. Item 4 is CONFIRMED as arithmetic, with FINDINGS G1 (the split depends on the jtcheck input
list; the kit's jtcheck over all 62 gives 736 / 49) and G2 (the two jtcheck settlements of `""` are heuristic
misreadings whose compared bytes cover the NUL). F1-F6 are closed in v2. The verdict "0 REAL, no code difference"
stands. To fix G1 and G2, either count PlatformInit and addAddressRange the same way (both KIT-JTCHECK: 736 / 49; or
both MEASURED CSTR, since their jtcheck readings are misfires: 734 / 51), give the jtcheck-members command and name
list, and replace "Both readings hold" with a statement that jtcheck's initializer / pointer-table reading is a
misfire whose 16 compared bytes include the C string's NUL.
