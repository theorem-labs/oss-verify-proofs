# Review of the comparison kit's acceptances (kit 4bbd3a74be89, stackmalloc1-A)

VERDICT: ACCEPT

No real difference found. All 200 C-string rows hold equal C strings (with the NUL) in both twins, from file bytes of
.rodata, and every one of the 200 places is read by its consumer only as a C string. The 3 'full' acceptances, the
1 '.got value' acceptance and the 1 tls_index acceptance hold equal bytes / cells under the kit's rule, and each place
is read only as the rule says: the 8-byte loads read exactly the 8 compared bytes, the 64-byte table is read at
table + [0, 63] only, the .got value is used only as a TP offset, and the tls_index address goes only to
__tls_get_addr (through the interceptor), which reads its two words.

## Inputs

- <donor twin>: fuzz_grant.asan, unstripped, sha256 57c26f99361583f69af95af52819bebfcf920468a03cf795b95e024fe9798a4d
- <target twin>: fuzz_uci.asan, unstripped, sha256 56822e263d767986a76ec862cbfbee7571b0e64df2413ad18d7201205a7563fb
  (both hashes measured here; prefixes 57c26f993615 / 56822e263d76 as in the record).
- Both are static ET_EXEC images: no PT_INTERP, no PT_DYNAMIC, no relocation section. So the file bytes of .rodata,
  .got and .data are the bytes the program starts with. .rodata (flags SHF_ALLOC | SHF_MERGE | SHF_STRINGS, no
  SHF_WRITE, SHT_PROGBITS) lies in the first PT_LOAD (PF_R only), inside p_filesz. .got lies inside PT_GNU_RELRO.
- Every instruction in the compared bodies and in the consumer functions read here is a 32-bit word (no RVC word).
- Records audited: records/cmpkit-4bbd3a74be89-pairs.out (12 pairs, 198 CSTR rows), records/cmpkit-4bbd3a74be89-pairs-by-address.out
  (MemToShadow copy, 2 CSTR rows; RegisterCommonFlags +0x358, 8 bytes, no acceptance), records/cmpkit-4bbd3a74be89-fulllist.out,
  BYTECMP.md (last section).

## Method

All reads are my own, with python3, pyelftools 0.33 and capstone 5.0.7 (RISCV64 | RVC; capstone only prints the text).
Register fields, immediates, load widths and branch / jal targets come from my own decoder of the 32-bit encodings.

1. Bodies. Each function of the records is the FUNC symbol at addr1 in <donor twin> and addr2 in <target twin>, with
   the stated size. The MemToShadow copy (0x3d410 / 0x3c348, 316 bytes) is the target of the jal at
   __asan_stack_malloc_1 +0x144 in both twins.
2. My own list of pc-relative targets. In each of the 14 compared ranges (the 13 pairs and RegisterCommonFlags +0x358,
   8 bytes): every addi / load / store whose base register
   was last written, in address order, by an auipc; the target classified by the FUNC / OBJECT symbols that cover it.
   Result: the targets that no symbol names are exactly the kit's 205 acceptances (200 C string, 3 full, 1 .got value,
   1 tls_index), plus the empty string at RegisterCommonFlags +0x1218 (the kit reports it as a difference, not an
   acceptance; out of scope here, see the last section), plus 8 .got cells read by an 8-byte load whose held values
   are addresses of the same named objects in both twins (__asan_option_detect_stack_use_after_return,
   common_flags_dont_use, current_verbosity, __asan_shadow_memory_dynamic_address, kMidMemBeg, kMidMemEnd,
   kHighMemEnd, asan_flags_dont_use_directly: name compares, not acceptances).
3. Equality of the C strings, ALL 200 rows. For each row: the bytes from addr1 in <donor twin> and from addr2 in
   <target twin> up to and including the first NUL, read from file bytes; check: every byte before the NUL is
   printable ASCII or tab / LF / CR, at least one such byte, the two strings are equal, they equal the row's hex and
   length, the whole string lies in .rodata (rules above), and no FUNC / OBJECT symbol covers the place. Also: the
   row's word offset is an `addi rd, rX, lo` whose rX was last written by an auipc, and auipc + lo gives addr1 in the
   donor and addr2 in the target.
4. Consumers, ALL 200 rows, by program. A forward data-flow over the function's control-flow graph from the addi: the
   address is followed in registers and in sp-relative stack slots, through copies (`addi rd, rs, 0`), spills and
   reloads, across branches and loops. Every other read of it is listed: argument register at a call or tail call,
   store, load or store through it, pointer arithmetic, compare, other ALU use, return. At a call the caller-saved
   registers are dropped. It ran on both twins; the 200 event lists are identical in the two twins.
5. Consumers, by hand: I read the instruction listing of every row in the sample (next section) and of every
   callee's use of the parameter (section "Callees"), in both twins. Each callee read here has the same instruction
   words in both twins apart from pc-relative fields (16 functions compared word by word).
6. Non-C-string acceptances: all 5, by hand, with the data-flow of step 4 on the loaded value / address and on the
   auipc register (to show the place has no other read).
7. The kit itself, as a check of the record: its seven files and SHA256SUMS copied into one empty directory,
   `sha256sum -c SHA256SUMS` OK for all seven, kit id (first 12 hex of sha256(SHA256SUMS)) 4bbd3a74be89. Its `cmp`
   on the 12 named pairs gives output identical to records/cmpkit-4bbd3a74be89-pairs.out (212 lines; the two image-path
   header lines left out). Its tcmp by address on the MemToShadow copy and on RegisterCommonFlags +0x358 [8] gives the
   rows of records/cmpkit-4bbd3a74be89-pairs-by-address.out (EQUAL-mod-pcrel with the same 2 CSTR rows; EQUAL).

## Sample rule

- Equality: all 200 CSTR rows (no sample).
- Consumer, by program (step 4): all 200 CSTR rows (no sample).
- Consumer, by hand (step 5): all 22 CSTR rows of the six small functions; and of the 178 RegisterCommonFlags rows,
  in word-offset order, rows 1-4 (start), every 20th row (20, 40, 60, 80, 100, 120, 140, 160) and rows 175-178
  (end): 16 rows, marked M in the RegisterCommonFlags table. Rows 177 and 178 are the two rows whose consumer pattern
  differs from the others (tail call `j` instead of `jal`).
- Each function is covered at least once; each consumer pattern (CheckFailed file / condition, Report format,
  MmapOrDie mem_type, RegisterHandler name / description through jal and through the tail call) is in the hand
  sample.
- Non-C-string acceptances: all 5 (no sample).

## __asan_stack_malloc_1 (donor 0x3cf18 / target 0x3c1b8, 400 bytes): tls_index 1

| acceptance | equality (kit rule: module words raw-equal; offset word + 0x800 names the same STT_TLS symbol+offset) | consumer |
|---|---|---|
| tls_index +0x1c: `auipc a0` +0x18, `addi a0, a0, lo` +0x1c -> .got cell 0x9d550 (donor) / 0x97d00 (target) | Both cells in .got, inside PT_GNU_RELRO, 16 file bytes. Donor and target bytes the same: module word 0x0000000000000001 / 0x0000000000000001 (raw-equal); offset word 0xfffffffffffff800 in both, + 0x800 = 0x0. PT_TLS memsz 0x14 in both; STT_TLS symbols the same in both (_ZN6__asanL14fake_stack_tlsE [0, 8), _ZN11__sanitizerL4dtlsE [8, 16), _ZN6__lsan15disable_counterE [16, 20)); offset 0 = _ZN6__asanL14fake_stack_tlsE + 0 in both. EQUAL. | The auipc register a0 has one use, the addi (which overwrites it). The address in a0 goes to `jal` +0x20 to __interceptor_trampoline___tls_get_addr (= __wrap___tls_get_addr, same address; 0x4218c / 0x410c0) and has no other use. The trampoline is one `j __interceptor___tls_get_addr`. That function keeps a0 in s0 and calls through REAL(__tls_get_addr) (`auipc a1` +0x1c, `ld a1, lo(a1)` +0x20 from .data object __interception::real___tls_get_addr, whose file value is the address of __tls_get_addr, 0x96620 / 0x90f44) with a0 = the tls_index address (`jalr a1` +0x2c), then calls DTLS_on_tls_get_addr with a0 = the same address (+0x5c). __tls_get_addr (36 bytes) reads `ld a2, 0(a0)` (module) and `ld a0, 8(a0)` (offset) only: inside the 16 bytes. DTLS_on_tls_get_addr reads its first parameter with `ld 0(s3)` (+0x58, +0x2bc) and `ld 8(s3)` (+0x228) only, and passes it once as a %p argument (a1) to Report at +0x2dc (format "__tls_get_addr: %p {0x%zx,0x%zx} => %p; ..."): no dereference. So the place is used as a GD tls_index passed to __tls_get_addr. |

## __asan::AsanTSDGet (donor 0x54b58 / target 0x53790, 64 bytes): C string 2

| word | C string (with its NUL) | donor addr / target addr | len | equal | consumer: instructions (offsets in the function, same in both twins) | use |
|---|---|---|---|---|---|---|
| +0x28 | "/llvm-project/compiler-rt/lib/asan/asan_posix.cpp" | 0x1aac4 / 0x1a932 | 50 | yes | auipc a0 +0x20; addi a0 +0x28; jal __sanitizer::CheckFailed +0x3c | CheckFailed(file=a0, line, cond=a2, ...): file string (a0) |
| +0x2c | "((tsd_key_inited)) != (0)" | 0x117a2 / 0x117a2 | 26 | yes | auipc a1 +0x24; addi a2 +0x2c; jal __sanitizer::CheckFailed +0x3c | CheckFailed(file=a0, line, cond=a2, ...): condition string (a2) |

## __sanitizer::DTLS_on_tls_get_addr (donor 0x69720 / target 0x68358, 848 bytes): C string 10, .got value 1

| word | C string (with its NUL) | donor addr / target addr | len | equal | consumer: instructions (offsets in the function, same in both twins) | use |
|---|---|---|---|---|---|---|
| +0x98 | "DTLS_NextBlock" | 0x13c04 / 0x13b04 | 15 | yes | auipc a0 +0x90; addi a1 +0x98; jal __sanitizer::MmapOrDie +0xa8 | MmapOrDie(size, mem_type=a1, ...): mem_type string (a1) |
| +0xdc | "__tls_get_addr: DTLS_NextBlock %p %zd\n" | 0x13c13 / 0x13b13 | 39 | yes | auipc a0 +0xd8; addi a0 +0xdc; jal __sanitizer::Report +0xe4 | Report format (a0) |
| +0x134 | "DTLS_NextBlock" | 0x13c04 / 0x13b04 | 15 | yes | auipc a0 +0x124; addi s7 +0x134; mv s7->a1 +0x170; jal __sanitizer::MmapOrDie +0x178 | MmapOrDie(size, mem_type=a1, ...): mem_type string (a1) |
| +0x140 | "__tls_get_addr: DTLS_NextBlock %p %zd\n" | 0x13c13 / 0x13b13 | 39 | yes | auipc a2 +0x130; addi a0 +0x140; sd 8(sp) +0x144; ld 8(sp)->a0 +0x1a4; jal __sanitizer::Report +0x1ac | Report format (a0) |
| +0x268 | "__tls_get_addr: DTLS_Find %p %zd\n" | 0x15e9c / 0x15d64 | 34 | yes | auipc a0 +0x264; addi a0 +0x268; jal __sanitizer::Report +0x27c | Report format (a0) |
| +0x2a4 | "/llvm-project/compiler-rt/lib/sanitizer_common/sanitizer_tls_get_addr.cpp" | 0x1b7a0 / 0x1b5ed | 74 | yes | auipc a0 +0x29c; addi a0 +0x2a4; jal __sanitizer::CheckFailed +0x2b8 | CheckFailed(file=a0, line, cond=a2, ...): file string (a0) |
| +0x2a8 | "((static_tls_begin)) <= ((static_tls_end))" | 0x1459a / 0x1449a | 43 | yes | auipc a1 +0x2a0; addi a2 +0x2a8; jal __sanitizer::CheckFailed +0x2b8 | CheckFailed(file=a0, line, cond=a2, ...): condition string (a2) |
| +0x2cc | "__tls_get_addr: %p {0x%zx,0x%zx} => %p; tls_beg: %p; sp: %p num_live_dtls %zd\n" | 0x1568f / 0x15557 | 79 | yes | auipc a0 +0x2c8; addi a0 +0x2cc; jal __sanitizer::Report +0x2dc | Report format (a0) |
| +0x330 | "__tls_get_addr: static tls: %p\n" | 0x13be4 / 0x13ae4 | 32 | yes | auipc a0 +0x32c; addi a0 +0x330; jal __sanitizer::Report +0x338 | Report format (a0) |
| +0x344 | "__tls_get_addr: Can't guess glibc version\n" | 0x1c7d4 / 0x1c621 | 43 | yes | auipc a0 +0x340; addi a0 +0x344; jal __sanitizer::Report +0x348 | Report format (a0) |

Row +0x134: the address is held in s7 (callee-saved) over the DTLS_Find loop; its only use is the copy to a1 at +0x170
for the MmapOrDie call at +0x178; s7 is live at later calls but is not passed to them. Row +0x140: spilled to 8(sp) at
+0x144, reloaded to a0 at +0x1a4, Report at +0x1ac; the slot has no other reload. Every '%' in the six Report formats
starts a complete conversion before the NUL (%p, %zd, %zx).

| acceptance | equality (kit rule: 8-byte load, raw value equal; a value inside PT_TLS must name the same STT_TLS symbol) | consumer |
|---|---|---|
| .got value +0x64: `auipc a0` +0x5c, `ld s5, lo(a0)` +0x64 (funct3 3: 8 bytes) -> .got cell 0x9d560 (donor) / 0x97d10 (target) | Both cells in .got, inside PT_GNU_RELRO, 8 file bytes 08 00 00 00 00 00 00 00 in both: value 0x8 = 0x8. 0x8 lies in no section (a value, not an address); it is inside PT_TLS (memsz 0x14) and names _ZN11__sanitizerL4dtlsE [8, 16) + 0 in both. EQUAL. | The auipc register a0 has one use, the ld (a0 is overwritten at +0x68). The loaded value s5 has one use: `add s5, s5, tp` at +0x6c (initial-exec TLS: TP offset + thread pointer), which overwrites s5 with the address of dtls; then `ld s6, 0(s5)` +0x74 reads dtls itself (TLS memory, not the .got place). So the cell is read once, by an 8-byte load of a TLS offset. |

## __sanitizer::RegisterCommonFlags (donor 0x61974 / target 0x605ac, 4772 bytes): C string 178

All 178 rows: equal (step 3) and, by program in both twins (step 4), each address has exactly one use: an argument
register of one call to __sanitizer::FlagParser::RegisterHandler(name = a1, handler = a2, desc = a3). There are 89
such calls (88 `jal`, 1 tail call `j` at +0x12a0 after the epilogue); each call receives exactly one row in a1 and
one row in a3. The 89 a1 strings are 89 distinct flag names (only [a-z0-9_]); the a3 strings are the descriptions.
The hand sample (rows marked M) shows the same pattern: `auipc rX` / `addi a1 or a3, rX, lo` / `jal` (or, rows 177-178,
`addi a1` +0x1260 and `addi a3` +0x1264, then +0x1268..+0x129c stores to the handler object, `mv a0, s0`, register
restores and `addi sp`, with no write to a1 or a3, then `j RegisterHandler` +0x12a0).

What RegisterHandler does with a1 and a3, and who reads it: see "Callees" below (stored as Flag.name / Flag.desc;
read only by internal_strcmp and by Printf "%s").

| # | word | auipc | donor addr / target addr | len | equal | consumer | C string (first 60 chars) |
|---|---|---|---|---|---|---|---|
| 1 M | +0x54 | +0x4c | 0x1180c / 0x1180c | 10 | yes | a1 -> jal RegisterHandler +0x60 (name) | "symbolize" |
| 2 M | +0x58 | +0x50 | 0x1e3eb / 0x1e214 | 114 | yes | a3 -> jal RegisterHandler +0x60 (desc) | "If set, use the online symbolizer from common sanitizer runt..." |
| 3 M | +0x90 | +0x88 | 0x1ab70 / 0x1a9de | 25 | yes | a1 -> jal RegisterHandler +0x9c (name) | "external_symbolizer_path" |
| 4 M | +0x94 | +0x8c | 0x16c83 / 0x16b42 | 86 | yes | a3 -> jal RegisterHandler +0x9c (desc) | "Path to external symbolizer. If empty, the tool will search ..." |
| 5 | +0xc4 | +0xbc | 0x13b84 / 0x13a84 | 16 | yes | a1 -> jal RegisterHandler +0xd0 (name) | "allow_addr2line" |
| 6 | +0xc8 | +0xc0 | 0x1d577 / 0x1d3ad | 154 | yes | a3 -> jal RegisterHandler +0xd0 (desc) | "If set, allows online symbolizer to run addr2line binary to ..." |
| 7 | +0xf8 | +0xf0 | 0x19302 / 0x191a9 | 18 | yes | a1 -> jal RegisterHandler +0x104 (name) | "strip_path_prefix" |
| 8 | +0xfc | +0xf4 | 0x18c8c / 0x18b23 | 53 | yes | a3 -> jal RegisterHandler +0x104 (desc) | "Strips this prefix from file paths in error reports." |
| 9 | +0x12c | +0x124 | 0x1f4d9 / 0x1f302 | 21 | yes | a1 -> jal RegisterHandler +0x138 (name) | "fast_unwind_on_check" |
| 10 | +0x130 | +0x128 | 0x1ab89 / 0x1a9f7 | 84 | yes | a3 -> jal RegisterHandler +0x138 (desc) | "If available, use the fast frame-pointer-based unwinder on i..." |
| 11 | +0x160 | +0x158 | 0x1098d / 0x1098d | 21 | yes | a1 -> jal RegisterHandler +0x16c (name) | "fast_unwind_on_fatal" |
| 12 | +0x164 | +0x15c | 0x1abdd / 0x1aa4b | 73 | yes | a3 -> jal RegisterHandler +0x16c (desc) | "If available, use the fast frame-pointer-based unwinder on f..." |
| 13 | +0x194 | +0x18c | 0x12179 / 0x12179 | 22 | yes | a1 -> jal RegisterHandler +0x1a0 (name) | "fast_unwind_on_malloc" |
| 14 | +0x198 | +0x190 | 0x17b0f / 0x179a6 | 72 | yes | a3 -> jal RegisterHandler +0x1a0 (desc) | "If available, use the fast frame-pointer-based unwinder on m..." |
| 15 | +0x1c8 | +0x1c0 | 0x18cc1 / 0x18b58 | 13 | yes | a1 -> jal RegisterHandler +0x1d4 (name) | "handle_ioctl" |
| 16 | +0x1cc | +0x1c4 | 0x1db52 / 0x1d97b | 37 | yes | a3 -> jal RegisterHandler +0x1d4 (desc) | "Intercept and handle ioctl requests." |
| 17 | +0x204 | +0x1fc | 0x1708d / 0x16f4c | 20 | yes | a1 -> jal RegisterHandler +0x210 (name) | "malloc_context_size" |
| 18 | +0x208 | +0x200 | 0x1b51b / 0x1b368 | 66 | yes | a3 -> jal RegisterHandler +0x210 (desc) | "Max number of stack frames kept for each allocation/dealloca..." |
| 19 | +0x238 | +0x230 | 0x19314 / 0x191bb | 9 | yes | a1 -> jal RegisterHandler +0x244 (name) | "log_path" |
| 20 M | +0x23c | +0x234 | 0x1b55d / 0x1b3aa | 114 | yes | a3 -> jal RegisterHandler +0x244 (desc) | "Write logs to "log_path.pid". The special values are "stdout..." |
| 21 | +0x26c | +0x264 | 0x1cd62 / 0x1cba7 | 13 | yes | a1 -> jal RegisterHandler +0x278 (name) | "log_exe_name" |
| 22 | +0x270 | +0x268 | 0x18414 / 0x182ab | 116 | yes | a3 -> jal RegisterHandler +0x278 (desc) | "Mention name of executable when reporting error and append e..." |
| 23 | +0x2a0 | +0x298 | 0x155d0 / 0x15498 | 11 | yes | a1 -> jal RegisterHandler +0x2ac (name) | "log_suffix" |
| 24 | +0x2a4 | +0x29c | 0x18488 / 0x1831f | 48 | yes | a3 -> jal RegisterHandler +0x2ac (desc) | "String to append to log file name, e.g. ".txt"." |
| 25 | +0x2d4 | +0x2cc | 0x11058 / 0x11058 | 14 | yes | a1 -> jal RegisterHandler +0x2e0 (name) | "log_to_syslog" |
| 26 | +0x2d8 | +0x2d0 | 0x17b57 / 0x179ee | 76 | yes | a3 -> jal RegisterHandler +0x2e0 (desc) | "Write all sanitizer output to syslog in addition to other me..." |
| 27 | +0x308 | +0x300 | 0x114f6 / 0x114f6 | 10 | yes | a1 -> jal RegisterHandler +0x314 (name) | "verbosity" |
| 28 | +0x30c | +0x304 | 0x1e45d / 0x1e286 | 69 | yes | a3 -> jal RegisterHandler +0x314 (desc) | "Verbosity level (0 - silent, 1 - a bit of output, 2+ - more ..." |
| 29 | +0x33c | +0x334 | 0x1931d / 0x191c4 | 10 | yes | a1 -> jal RegisterHandler +0x348 (name) | "strip_env" |
| 30 | +0x340 | +0x338 | 0x12891 / 0x12887 | 128 | yes | a3 -> jal RegisterHandler +0x348 (desc) | "Whether to remove the sanitizer from DYLD_INSERT_LIBRARIES t..." |
| 31 | +0x370 | +0x368 | 0x142bd / 0x141bd | 20 | yes | a1 -> jal RegisterHandler +0x37c (name) | "verify_interceptors" |
| 32 | +0x374 | +0x36c | 0x12911 / 0x12907 | 74 | yes | a3 -> jal RegisterHandler +0x37c (desc) | "Verify that interceptors are working on Apple platforms. Def..." |
| 33 | +0x3a4 | +0x39c | 0x17ba3 / 0x17a3a | 13 | yes | a1 -> jal RegisterHandler +0x3b0 (name) | "detect_leaks" |
| 34 | +0x3a8 | +0x3a0 | 0x17bb0 / 0x17a47 | 30 | yes | a3 -> jal RegisterHandler +0x3b0 (desc) | "Enable memory leak detection." |
| 35 | +0x3d8 | +0x3d0 | 0x14d99 / 0x14c99 | 19 | yes | a1 -> jal RegisterHandler +0x3e4 (name) | "leak_check_at_exit" |
| 36 | +0x3dc | +0x3d4 | 0x142d1 / 0x141d1 | 159 | yes | a3 -> jal RegisterHandler +0x3e4 (desc) | "Invoke leak checking in an atexit handler. Has no effect if ..." |
| 37 | +0x40c | +0x404 | 0x17073 / 0x16f32 | 26 | yes | a1 -> jal RegisterHandler +0x418 (name) | "allocator_may_return_null" |
| 38 | +0x410 | +0x408 | 0x1218f / 0x1218f | 76 | yes | a3 -> jal RegisterHandler +0x418 (desc) | "If false, the allocator will crash instead of returning 0 on..." |
| 39 | +0x440 | +0x438 | 0x1d611 / 0x1d447 | 14 | yes | a1 -> jal RegisterHandler +0x44c (name) | "print_summary" |
| 40 M | +0x444 | +0x43c | 0x14370 / 0x14270 | 73 | yes | a3 -> jal RegisterHandler +0x44c (desc) | "If false, disable printing error summaries in addition to er..." |
| 41 | +0x474 | +0x46c | 0x13b94 / 0x13a94 | 17 | yes | a1 -> jal RegisterHandler +0x480 (name) | "print_module_map" |
| 42 | +0x478 | +0x470 | 0x1c5e2 / 0x1c42f | 135 | yes | a3 -> jal RegisterHandler +0x480 (desc) | "Print the process module map where supported (0 - don't prin..." |
| 43 | +0x4a8 | +0x4a0 | 0x1e4a2 / 0x1e2cb | 13 | yes | a1 -> jal RegisterHandler +0x4b4 (name) | "check_printf" |
| 44 | +0x4ac | +0x4a4 | 0x1cd6f / 0x1cbb4 | 24 | yes | a3 -> jal RegisterHandler +0x4b4 (desc) | "Check printf arguments." |
| 45 | +0x4e4 | +0x4dc | 0x16cd9 / 0x16b98 | 12 | yes | a1 -> jal RegisterHandler +0x4f0 (name) | "handle_segv" |
| 46 | +0x4e8 | +0x4e0 | 0x1eddb / 0x1ec04 | 187 | yes | a3 -> jal RegisterHandler +0x4f0 (desc) | "Controls custom tool's SIGSEGV handler (0 - do not registers..." |
| 47 | +0x518 | +0x510 | 0x1c669 / 0x1c4b6 | 14 | yes | a1 -> jal RegisterHandler +0x524 (name) | "handle_sigbus" |
| 48 | +0x51c | +0x514 | 0x1295b / 0x12951 | 186 | yes | a3 -> jal RegisterHandler +0x524 (desc) | "Controls custom tool's SIGBUS handler (0 - do not registers ..." |
| 49 | +0x54c | +0x544 | 0x15d27 / 0x15bef | 13 | yes | a1 -> jal RegisterHandler +0x558 (name) | "handle_abort" |
| 50 | +0x550 | +0x548 | 0x1f4ee / 0x1f317 | 187 | yes | a3 -> jal RegisterHandler +0x558 (desc) | "Controls custom tool's SIGABRT handler (0 - do not registers..." |
| 51 | +0x580 | +0x578 | 0x1f5a9 / 0x1f3d2 | 14 | yes | a1 -> jal RegisterHandler +0x58c (name) | "handle_sigill" |
| 52 | +0x584 | +0x57c | 0x1ac26 / 0x1aa94 | 186 | yes | a3 -> jal RegisterHandler +0x58c (desc) | "Controls custom tool's SIGILL handler (0 - do not registers ..." |
| 53 | +0x5b4 | +0x5ac | 0x1bdba / 0x1bc07 | 15 | yes | a1 -> jal RegisterHandler +0x5c0 (name) | "handle_sigtrap" |
| 54 | +0x5b8 | +0x5b0 | 0x11816 / 0x11816 | 187 | yes | a3 -> jal RegisterHandler +0x5c0 (desc) | "Controls custom tool's SIGTRAP handler (0 - do not registers..." |
| 55 | +0x5e8 | +0x5e0 | 0x1fe26 / 0x1fc4f | 14 | yes | a1 -> jal RegisterHandler +0x5f4 (name) | "handle_sigfpe" |
| 56 | +0x5ec | +0x5e4 | 0x15d34 / 0x15bfc | 186 | yes | a3 -> jal RegisterHandler +0x5f4 (desc) | "Controls custom tool's SIGFPE handler (0 - do not registers ..." |
| 57 | +0x61c | +0x614 | 0x11066 / 0x11066 | 24 | yes | a1 -> jal RegisterHandler +0x628 (name) | "allow_user_segv_handler" |
| 58 | +0x620 | +0x618 | 0x1ee96 / 0x1ecbf | 106 | yes | a3 -> jal RegisterHandler +0x628 (desc) | "Deprecated. True has no effect, use handle_sigbus=1. If fals..." |
| 59 | +0x650 | +0x648 | 0x16515 / 0x163d4 | 16 | yes | a1 -> jal RegisterHandler +0x65c (name) | "use_sigaltstack" |
| 60 M | +0x654 | +0x64c | 0x16ce5 / 0x16ba4 | 50 | yes | a3 -> jal RegisterHandler +0x65c (desc) | "If set, uses alternate stack for signal handling." |
| 61 | +0x684 | +0x67c | 0x118d1 / 0x118d1 | 17 | yes | a1 -> jal RegisterHandler +0x690 (name) | "detect_deadlocks" |
| 62 | +0x688 | +0x680 | 0x143b9 / 0x142b9 | 39 | yes | a3 -> jal RegisterHandler +0x690 (desc) | "If set, deadlock detection is enabled." |
| 63 | +0x6c0 | +0x6b8 | 0x19bbd / 0x19a64 | 28 | yes | a1 -> jal RegisterHandler +0x6cc (name) | "clear_shadow_mmap_threshold" |
| 64 | +0x6c4 | +0x6bc | 0x1bdc9 / 0x1bc16 | 117 | yes | a3 -> jal RegisterHandler +0x6cc (desc) | "Large shadow regions are zero-filled using mmap(NORESERVE) i..." |
| 65 | +0x6f4 | +0x6ec | 0x19bd9 / 0x19a80 | 6 | yes | a1 -> jal RegisterHandler +0x700 (name) | "color" |
| 66 | +0x6f8 | +0x6f0 | 0x1db77 / 0x1d9a0 | 39 | yes | a3 -> jal RegisterHandler +0x700 (desc) | "Colorize reports: (always\|never\|auto)." |
| 67 | +0x728 | +0x720 | 0x1fe34 / 0x1fc5d | 20 | yes | a1 -> jal RegisterHandler +0x734 (name) | "legacy_pthread_cond" |
| 68 | +0x72c | +0x724 | 0x1a276 / 0x1a0ff | 68 | yes | a3 -> jal RegisterHandler +0x734 (desc) | "Enables support for dynamic libraries linked with libpthread..." |
| 69 | +0x75c | +0x754 | 0x109a2 / 0x109a2 | 23 | yes | a1 -> jal RegisterHandler +0x768 (name) | "intercept_tls_get_addr" |
| 70 | +0x760 | +0x758 | 0x13407 / 0x1331b | 26 | yes | a3 -> jal RegisterHandler +0x768 (desc) | "Intercept __tls_get_addr." |
| 71 | +0x790 | +0x788 | 0x1b030 / 0x1ae7d | 5 | yes | a1 -> jal RegisterHandler +0x79c (name) | "help" |
| 72 | +0x794 | +0x78c | 0x1cd87 / 0x1cbcc | 29 | yes | a3 -> jal RegisterHandler +0x79c (desc) | "Print the flag descriptions." |
| 73 | +0x7c4 | +0x7bc | 0x16d17 / 0x16bd6 | 14 | yes | a1 -> jal RegisterHandler +0x7d0 (name) | "mmap_limit_mb" |
| 74 | +0x7c8 | +0x7c0 | 0x12a15 / 0x12a0b | 118 | yes | a3 -> jal RegisterHandler +0x7d0 (desc) | "Limit the amount of mmap-ed memory (excluding shadow) in Mb;..." |
| 75 | +0x7f8 | +0x7f0 | 0x13421 / 0x13335 | 18 | yes | a1 -> jal RegisterHandler +0x804 (name) | "hard_rss_limit_mb" |
| 76 | +0x7fc | +0x7f4 | 0x19327 / 0x191ce | 153 | yes | a3 -> jal RegisterHandler +0x804 (desc) | "Hard RSS limit in Mb. If non-zero, a background thread is sp..." |
| 77 | +0x82c | +0x824 | 0x1fe48 / 0x1fc71 | 18 | yes | a1 -> jal RegisterHandler +0x838 (name) | "soft_rss_limit_mb" |
| 78 | +0x830 | +0x828 | 0x1b5cf / 0x1b41c | 352 | yes | a3 -> jal RegisterHandler +0x838 (desc) | "Soft RSS limit in Mb. If non-zero, a background thread is sp..." |
| 79 | +0x860 | +0x858 | 0x1e4af / 0x1e2d8 | 23 | yes | a1 -> jal RegisterHandler +0x86c (name) | "max_allocation_size_mb" |
| 80 M | +0x864 | +0x85c | 0x193c0 / 0x19267 | 119 | yes | a3 -> jal RegisterHandler +0x86c (desc) | "If non-zero, malloc/new calls larger than this size will ret..." |
| 81 | +0x894 | +0x88c | 0x184b8 / 0x1834f | 13 | yes | a1 -> jal RegisterHandler +0x8a0 (name) | "heap_profile" |
| 82 | +0x898 | +0x890 | 0x1107e / 0x1107e | 38 | yes | a3 -> jal RegisterHandler +0x8a0 (desc) | "Experimental heap profiler, asan-only" |
| 83 | +0x8c8 | +0x8c0 | 0x1e986 / 0x1e7af | 36 | yes | a1 -> jal RegisterHandler +0x8d4 (name) | "allocator_release_to_os_interval_ms" |
| 84 | +0x8cc | +0x8c4 | 0x19437 / 0x192de | 206 | yes | a3 -> jal RegisterHandler +0x8d4 (desc) | "Only affects a 64-bit allocator. If set, tries to release un..." |
| 85 | +0x8fc | +0x8f4 | 0x143e0 / 0x142e0 | 24 | yes | a1 -> jal RegisterHandler +0x908 (name) | "can_use_proc_maps_statm" |
| 86 | +0x900 | +0x8f8 | 0x13433 / 0x13347 | 89 | yes | a3 -> jal RegisterHandler +0x908 (desc) | "If false, do not attempt to read /proc/maps/statm. Mostly us..." |
| 87 | +0x930 | +0x928 | 0x17815 / 0x176ac | 9 | yes | a1 -> jal RegisterHandler +0x93c (name) | "coverage" |
| 88 | +0x934 | +0x92c | 0x1be3e / 0x1bc8b | 127 | yes | a3 -> jal RegisterHandler +0x93c (desc) | "If set, coverage information will be dumped at program shutd..." |
| 89 | +0x964 | +0x95c | 0x105e4 / 0x105e4 | 13 | yes | a1 -> jal RegisterHandler +0x970 (name) | "coverage_dir" |
| 90 | +0x968 | +0x960 | 0x19505 / 0x193ac | 72 | yes | a3 -> jal RegisterHandler +0x970 (desc) | "Target directory for coverage dumps. Defaults to the current..." |
| 91 | +0x998 | +0x990 | 0x15dee / 0x15cb6 | 22 | yes | a1 -> jal RegisterHandler +0x9a4 (name) | "cov_8bit_counters_out" |
| 92 | +0x99c | +0x994 | 0x184c5 / 0x1835c | 49 | yes | a3 -> jal RegisterHandler +0x9a4 (desc) | "If non-empty, write 8bit counters to this file. " |
| 93 | +0x9cc | +0x9c4 | 0x110a4 / 0x110a4 | 12 | yes | a1 -> jal RegisterHandler +0x9d8 (name) | "cov_pcs_out" |
| 94 | +0x9d0 | +0x9c8 | 0x14dac / 0x14cac | 57 | yes | a3 -> jal RegisterHandler +0x9d8 (desc) | "If non-empty, write the coverage pc table to this file. " |
| 95 | +0xa00 | +0x9f8 | 0x1a2ba / 0x1a143 | 19 | yes | a1 -> jal RegisterHandler +0xa0c (name) | "full_address_space" |
| 96 | +0xa04 | +0x9fc | 0x1ace0 / 0x1ab4e | 98 | yes | a3 -> jal RegisterHandler +0xa0c (desc) | "Sanitize complete address space; by default kernel area on 3..." |
| 97 | +0xa34 | +0xa2c | 0x1f5b7 / 0x1f3e0 | 19 | yes | a1 -> jal RegisterHandler +0xa40 (name) | "print_suppressions" |
| 98 | +0xa38 | +0xa30 | 0x203db / 0x20204 | 36 | yes | a3 -> jal RegisterHandler +0xa40 (desc) | "Print matched suppressions at exit." |
| 99 | +0xa68 | +0xa60 | 0x14de5 / 0x14ce5 | 17 | yes | a1 -> jal RegisterHandler +0xa74 (name) | "disable_coredump" |
| 100 M | +0xa6c | +0xa64 | 0x1f5ca / 0x1f3f3 | 208 | yes | a3 -> jal RegisterHandler +0xa74 (desc) | "Disable core dumping. By default, disable_coredump=1 on 64-b..." |
| 101 | +0xa9c | +0xa94 | 0x155db / 0x154a3 | 18 | yes | a1 -> jal RegisterHandler +0xaa8 (name) | "use_madv_dontdump" |
| 102 | +0xaa0 | +0xa98 | 0x1fe5a / 0x1fc83 | 70 | yes | a3 -> jal RegisterHandler +0xaa8 (desc) | "If set, instructs kernel to not store the (huge) shadow in c..." |
| 103 | +0xad0 | +0xac8 | 0x17338 / 0x171f7 | 24 | yes | a1 -> jal RegisterHandler +0xadc (name) | "symbolize_inline_frames" |
| 104 | +0xad4 | +0xacc | 0x1348c / 0x133a0 | 55 | yes | a3 -> jal RegisterHandler +0xadc (desc) | "Print inlined frames in stacktraces. Defaults to true." |
| 105 | +0xb04 | +0xafc | 0x134c3 / 0x133d7 | 9 | yes | a1 -> jal RegisterHandler +0xb10 (name) | "demangle" |
| 106 | +0xb08 | +0xb00 | 0x13ba5 / 0x13aa5 | 25 | yes | a3 -> jal RegisterHandler +0xb10 (desc) | "Print demangled symbols." |
| 107 | +0xb38 | +0xb30 | 0x1db9e / 0x1d9c7 | 19 | yes | a1 -> jal RegisterHandler +0xb44 (name) | "symbolize_vs_style" |
| 108 | +0xb3c | +0xb34 | 0x1e4c6 / 0x1e2ef | 68 | yes | a3 -> jal RegisterHandler +0xb44 (desc) | "Print file locations in Visual Studio style (e.g:  file(10,4..." |
| 109 | +0xb6c | +0xb64 | 0x110b0 / 0x110b0 | 19 | yes | a1 -> jal RegisterHandler +0xb78 (name) | "dedup_token_length" |
| 110 | +0xb70 | +0xb68 | 0x143f8 / 0x142f8 | 206 | yes | a3 -> jal RegisterHandler +0xb78 (desc) | "If positive, after printing a stack trace also print a short..." |
| 111 | +0xba0 | +0xb98 | 0x118e2 / 0x118e2 | 19 | yes | a1 -> jal RegisterHandler +0xbac (name) | "stack_trace_format" |
| 112 | +0xba4 | +0xb9c | 0x134cc / 0x133e0 | 141 | yes | a3 -> jal RegisterHandler +0xbac (desc) | "Format string used to render stack frames. See sanitizer_sta..." |
| 113 | +0xbd4 | +0xbcc | 0x1c677 / 0x1c4c4 | 21 | yes | a1 -> jal RegisterHandler +0xbe0 (name) | "compress_stack_depot" |
| 114 | +0xbd8 | +0xbd0 | 0x1fea0 / 0x1fcc9 | 37 | yes | a3 -> jal RegisterHandler +0xbe0 (desc) | "Compress stack depot to save memory." |
| 115 | +0xc08 | +0xc00 | 0x19bdf / 0x19a86 | 25 | yes | a1 -> jal RegisterHandler +0xc14 (name) | "no_huge_pages_for_shadow" |
| 116 | +0xc0c | +0xc04 | 0x184f6 / 0x1838d | 55 | yes | a3 -> jal RegisterHandler +0xc14 (desc) | "If true, the shadow is not allowed to use huge pages. " |
| 117 | +0xc3c | +0xc34 | 0x1bebd / 0x1bd0a | 21 | yes | a1 -> jal RegisterHandler +0xc48 (name) | "strict_string_checks" |
| 118 | +0xc40 | +0xc38 | 0x18cce / 0x18b65 | 64 | yes | a3 -> jal RegisterHandler +0xc48 (desc) | "If set check that string arguments are properly null-termina..." |
| 119 | +0xc70 | +0xc68 | 0x1954d / 0x193f4 | 17 | yes | a1 -> jal RegisterHandler +0xc7c (name) | "intercept_strstr" |
| 120 M | +0xc74 | +0xc6c | 0x1e50a / 0x1e333 | 86 | yes | a3 -> jal RegisterHandler +0xc7c (desc) | "If set, uses custom wrappers for strstr and strcasestr funct..." |
| 121 | +0xca4 | +0xc9c | 0x17350 / 0x1720f | 17 | yes | a1 -> jal RegisterHandler +0xcb0 (name) | "intercept_strspn" |
| 122 | +0xca8 | +0xca0 | 0x1fec5 / 0x1fcee | 82 | yes | a3 -> jal RegisterHandler +0xcb0 (desc) | "If set, uses custom wrappers for strspn and strcspn function..." |
| 123 | +0xcd8 | +0xcd0 | 0x1e560 / 0x1e389 | 17 | yes | a1 -> jal RegisterHandler +0xce4 (name) | "intercept_strtok" |
| 124 | +0xcdc | +0xcd4 | 0x110c3 / 0x110c3 | 75 | yes | a3 -> jal RegisterHandler +0xce4 (desc) | "If set, uses a custom wrapper for the strtok function to fin..." |
| 125 | +0xd0c | +0xd04 | 0x1b72f / 0x1b57c | 18 | yes | a1 -> jal RegisterHandler +0xd18 (name) | "intercept_strpbrk" |
| 126 | +0xd10 | +0xd08 | 0x1f69a / 0x1f4c3 | 71 | yes | a3 -> jal RegisterHandler +0xd18 (desc) | "If set, uses custom wrappers for strpbrk function to find mo..." |
| 127 | +0xd40 | +0xd38 | 0x14df6 / 0x14cf6 | 17 | yes | a1 -> jal RegisterHandler +0xd4c (name) | "intercept_strcmp" |
| 128 | +0xd44 | +0xd3c | 0x1b741 / 0x1b58e | 71 | yes | a3 -> jal RegisterHandler +0xd4c (desc) | "If set, uses custom wrappers for strcmp functions to find mo..." |
| 129 | +0xd74 | +0xd6c | 0x1d61f / 0x1d455 | 17 | yes | a1 -> jal RegisterHandler +0xd80 (name) | "intercept_strlen" |
| 130 | +0xd78 | +0xd70 | 0x12a8b / 0x12a81 | 83 | yes | a3 -> jal RegisterHandler +0xd80 (desc) | "If set, uses custom wrappers for strlen and strnlen function..." |
| 131 | +0xda8 | +0xda0 | 0x1c68c / 0x1c4d9 | 18 | yes | a1 -> jal RegisterHandler +0xdb4 (name) | "intercept_strndup" |
| 132 | +0xdac | +0xda4 | 0x1e571 / 0x1e39a | 72 | yes | a3 -> jal RegisterHandler +0xdb4 (desc) | "If set, uses custom wrappers for strndup functions to find m..." |
| 133 | +0xddc | +0xdd4 | 0x1110e / 0x1110e | 17 | yes | a1 -> jal RegisterHandler +0xde8 (name) | "intercept_strchr" |
| 134 | +0xde0 | +0xdd8 | 0x155ed / 0x154b5 | 95 | yes | a3 -> jal RegisterHandler +0xde8 (desc) | "If set, uses custom wrappers for strchr, strchrnul, and strr..." |
| 135 | +0xe10 | +0xe08 | 0x1cda4 / 0x1cbe9 | 17 | yes | a1 -> jal RegisterHandler +0xe1c (name) | "intercept_memcmp" |
| 136 | +0xe14 | +0xe0c | 0x1955e / 0x19405 | 70 | yes | a3 -> jal RegisterHandler +0xe1c (desc) | "If set, uses custom wrappers for memcmp function to find mor..." |
| 137 | +0xe44 | +0xe3c | 0x1852d / 0x183c4 | 14 | yes | a1 -> jal RegisterHandler +0xe50 (name) | "strict_memcmp" |
| 138 | +0xe48 | +0xe40 | 0x14e07 / 0x14d07 | 88 | yes | a3 -> jal RegisterHandler +0xe50 (desc) | "If true, assume that memcmp(p1, p2, n) always reads n bytes ..." |
| 139 | +0xe78 | +0xe70 | 0x121db / 0x121db | 17 | yes | a1 -> jal RegisterHandler +0xe84 (name) | "intercept_memmem" |
| 140 M | +0xe7c | +0xe74 | 0x19bf8 / 0x19a9f | 57 | yes | a3 -> jal RegisterHandler +0xe84 (desc) | "If set, uses a wrapper for memmem() to find more errors." |
| 141 | +0xeac | +0xea4 | 0x1ff17 / 0x1fd40 | 17 | yes | a1 -> jal RegisterHandler +0xeb8 (name) | "intercept_intrin" |
| 142 | +0xeb0 | +0xea8 | 0x13559 / 0x1346d | 87 | yes | a3 -> jal RegisterHandler +0xeb8 (desc) | "If set, uses custom wrappers for memset/memcpy/memmove intri..." |
| 143 | +0xee0 | +0xed8 | 0x15e04 / 0x15ccc | 15 | yes | a1 -> jal RegisterHandler +0xeec (name) | "intercept_stat" |
| 144 | +0xee4 | +0xedc | 0x1dbb1 / 0x1d9da | 70 | yes | a3 -> jal RegisterHandler +0xeec (desc) | "If set, uses custom wrappers for *stat functions to find mor..." |
| 145 | +0xf14 | +0xf0c | 0x1564c / 0x15514 | 15 | yes | a1 -> jal RegisterHandler +0xf20 (name) | "intercept_send" |
| 146 | +0xf18 | +0xf10 | 0x1c69e / 0x1c4eb | 70 | yes | a3 -> jal RegisterHandler +0xf20 (desc) | "If set, uses custom wrappers for send* functions to find mor..." |
| 147 | +0xf48 | +0xf40 | 0x1e5b9 / 0x1e3e2 | 19 | yes | a1 -> jal RegisterHandler +0xf54 (name) | "decorate_proc_maps" |
| 148 | +0xf4c | +0xf44 | 0x16d25 / 0x16be4 | 80 | yes | a3 -> jal RegisterHandler +0xf54 (desc) | "If set, decorate sanitizer mappings in /proc/self/maps with ..." |
| 149 | +0xf7c | +0xf74 | 0x1bed2 / 0x1bd1f | 9 | yes | a1 -> jal RegisterHandler +0xf88 (name) | "exitcode" |
| 150 | +0xf80 | +0xf78 | 0x1e5cc / 0x1e3f5 | 60 | yes | a3 -> jal RegisterHandler +0xf88 (desc) | "Override the program exit status if the tool found an error" |
| 151 | +0xfb0 | +0xfa8 | 0x1bedb / 0x1bd28 | 15 | yes | a1 -> jal RegisterHandler +0xfbc (name) | "abort_on_error" |
| 152 | +0xfb4 | +0xfac | 0x195a4 / 0x1944b | 83 | yes | a3 -> jal RegisterHandler +0xfbc (desc) | "If set, the tool calls abort() instead of _exit() after prin..." |
| 153 | +0xfe4 | +0xfdc | 0x12ade / 0x12ad4 | 19 | yes | a1 -> jal RegisterHandler +0xff0 (name) | "suppress_equal_pcs" |
| 154 | +0xfe8 | +0xfe0 | 0x12af1 / 0x12ae7 | 97 | yes | a3 -> jal RegisterHandler +0xff0 (desc) | "Deduplicate multiple reports for single source location in h..." |
| 155 | +0x1018 | +0x1010 | 0x1dbf7 / 0x1da20 | 14 | yes | a1 -> jal RegisterHandler +0x1024 (name) | "print_cmdline" |
| 156 | +0x101c | +0x1014 | 0x1f6e1 / 0x1f50a | 41 | yes | a3 -> jal RegisterHandler +0x1024 (desc) | "Print command line on crash (asan only)." |
| 157 | +0x104c | +0x1044 | 0x1565b / 0x15523 | 16 | yes | a1 -> jal RegisterHandler +0x1058 (name) | "html_cov_report" |
| 158 | +0x1050 | +0x1048 | 0x17bce / 0x17a65 | 31 | yes | a3 -> jal RegisterHandler +0x1058 (desc) | "Generate html coverage report." |
| 159 | +0x1080 | +0x1078 | 0x121ec / 0x121ec | 12 | yes | a1 -> jal RegisterHandler +0x108c (name) | "sancov_path" |
| 160 M | +0x1084 | +0x107c | 0x144c6 / 0x143c6 | 22 | yes | a3 -> jal RegisterHandler +0x108c (desc) | "Sancov tool location." |
| 161 | +0x10b4 | +0x10ac | 0x13bbe / 0x13abe | 23 | yes | a1 -> jal RegisterHandler +0x10c0 (name) | "dump_instruction_bytes" |
| 162 | +0x10b8 | +0x10b0 | 0x12b52 / 0x12b48 | 68 | yes | a3 -> jal RegisterHandler +0x10c0 (desc) | "If true, dump 16 bytes starting at the instruction that caus..." |
| 163 | +0x10e8 | +0x10e0 | 0x14e5f / 0x14d5f | 15 | yes | a1 -> jal RegisterHandler +0x10f4 (name) | "dump_registers" |
| 164 | +0x10ec | +0x10e4 | 0x195f7 / 0x1949e | 89 | yes | a3 -> jal RegisterHandler +0x10f4 (desc) | "If true, dump values of CPU registers when SEGV happens. Onl..." |
| 165 | +0x111c | +0x1114 | 0x1a2cd / 0x1a156 | 18 | yes | a1 -> jal RegisterHandler +0x1128 (name) | "detect_write_exec" |
| 166 | +0x1120 | +0x1118 | 0x1a2df / 0x1a168 | 81 | yes | a3 -> jal RegisterHandler +0x1128 (desc) | "If true, triggers warning when writable-executable pages req..." |
| 167 | +0x1150 | +0x1148 | 0x17361 / 0x17220 | 31 | yes | a1 -> jal RegisterHandler +0x115c (name) | "test_only_emulate_no_memorymap" |
| 168 | +0x1154 | +0x114c | 0x1c6e4 / 0x1c531 | 67 | yes | a3 -> jal RegisterHandler +0x115c (desc) | "TEST ONLY fail to read memory mappings to emulate sanitized ..." |
| 169 | +0x1184 | +0x117c | 0x121f8 / 0x121f8 | 38 | yes | a1 -> jal RegisterHandler +0x1190 (name) | "test_only_replace_dlopen_main_program" |
| 170 | +0x1188 | +0x1180 | 0x17380 / 0x1723f | 63 | yes | a3 -> jal RegisterHandler +0x1190 (desc) | "TEST ONLY replace dlopen(<main program>,...) with dlopen(NUL..." |
| 171 | +0x11b8 | +0x11b0 | 0x1f70a / 0x1f533 | 25 | yes | a1 -> jal RegisterHandler +0x11c4 (name) | "enable_symbolizer_markup" |
| 172 | +0x11bc | +0x11b4 | 0x144dc / 0x143dc | 85 | yes | a3 -> jal RegisterHandler +0x11c4 (desc) | "Use sanitizer symbolizer markup, available on Linux and alwa..." |
| 173 | +0x11ec | +0x11e4 | 0x1e608 / 0x1e431 | 20 | yes | a1 -> jal RegisterHandler +0x11f8 (name) | "detect_invalid_join" |
| 174 | +0x11f0 | +0x11e8 | 0x173bf / 0x1727e | 40 | yes | a3 -> jal RegisterHandler +0x11f8 (desc) | "If set, check invalid joins of threads." |
| 175 M | +0x1234 | +0x122c | 0x1c5b4 / 0x1c401 | 8 | yes | a1 -> jal RegisterHandler +0x1240 (name) | "include" |
| 176 M | +0x1238 | +0x1230 | 0x1c5bc / 0x1c409 | 38 | yes | a3 -> jal RegisterHandler +0x1240 (desc) | "read more options from the given file" |
| 177 M | +0x1260 | +0x1258 | 0x14d87 / 0x14c87 | 18 | yes | a1 -> j (tail call) RegisterHandler +0x12a0 (name) | "include_if_exists" |
| 178 M | +0x1264 | +0x125c | 0x1db1d / 0x1d946 | 53 | yes | a3 -> j (tail call) RegisterHandler +0x12a0 (desc) | "read more options from the given file (if it exists)" |

## __asan::FakeStack::GC (donor 0x3c958 / target 0x3bd6c, 744 bytes): C string 2, full 1

| word | C string (with its NUL) | donor addr / target addr | len | equal | consumer: instructions (offsets in the function, same in both twins) | use |
|---|---|---|---|---|---|---|
| +0x290 | "/llvm-project/compiler-rt/lib/asan/asan_mapping.h" | 0x1fa8a / 0x1f8b3 | 50 | yes | auipc a0 +0x288; addi a0 +0x290; jal __sanitizer::CheckFailed +0x2a4 | CheckFailed(file=a0, line, cond=a2, ...): file string (a0) |
| +0x294 | "((AddrIsInMem(p))) != (0)" | 0x17059 / 0x16f18 | 26 | yes | auipc a1 +0x28c; addi a2 +0x294; jal __sanitizer::CheckFailed +0x2a4 | CheckFailed(file=a0, line, cond=a2, ...): condition string (a2) |

| acceptance | equality (kit rule: a load is compared by the bytes it reads) | consumer |
|---|---|---|
| full +0xb0: `auipc a5` +0x84, `ld s7, lo(a5)` +0xb0 (8 bytes) -> 0x10338 in both | .rodata, file bytes; only the mapping symbol $d at the place, no FUNC / OBJECT symbol. Bytes f5 f5 f5 f5 f5 f5 f5 f5 in both. EQUAL (8 = 8 bytes). | The auipc register a5 has one memory use, this ld (it is live at the PoisonShadow call +0x11c, whose parameters are a0-a2, so it is not passed). The loaded value s7 is used only as data: `sd s7, 0(a1)` +0x1cc (writes the 0xf5 magic into shadow memory); it is live at later calls but is not passed. The place is read once, by the 8-byte load: inside the compared 8 bytes. |

## __asan::AsanThread::AsyncSignalSafeLazyInitFakeStack (donor 0x5c280 / target 0x5aeb8, 560 bytes): C string 6, full 2

| word | C string (with its NUL) | donor addr / target addr | len | equal | consumer: instructions (offsets in the function, same in both twins) | use |
|---|---|---|---|---|---|---|
| +0x1e8 | "/llvm-project/compiler-rt/lib/asan/asan_thread.cpp" | 0x1d4cf / 0x1d305 | 51 | yes | auipc a0 +0x1e0; addi a0 +0x1e8; jal __sanitizer::CheckFailed +0x1f8 | CheckFailed(file=a0, line, cond=a2, ...): file string (a0) |
| +0x1ec | "((flags()->min_uar_stack_size_log)) <= ((flags()->max_uar_stack_size_log))" | 0x1e30d / 0x1e136 | 75 | yes | auipc a1 +0x1e4; addi a2 +0x1ec; jal __sanitizer::CheckFailed +0x1f8 | CheckFailed(file=a0, line, cond=a2, ...): condition string (a2) |
| +0x204 | "/llvm-project/compiler-rt/lib/asan/../sanitizer_common/sanitizer_common.h" | 0x1df48 / 0x1dd71 | 74 | yes | auipc a0 +0x1fc; addi a0 +0x204; jal __sanitizer::CheckFailed +0x210 | CheckFailed(file=a0, line, cond=a2, ...): file string (a0) |
| +0x208 | "((size)) < (((1ULL << (up + 1))))" | 0x1495a / 0x1485a | 34 | yes | auipc a1 +0x200; addi a2 +0x208; jal __sanitizer::CheckFailed +0x210 | CheckFailed(file=a0, line, cond=a2, ...): condition string (a2) |
| +0x21c | "/llvm-project/compiler-rt/lib/asan/../sanitizer_common/sanitizer_common.h" | 0x1df48 / 0x1dd71 | 74 | yes | auipc a0 +0x214; addi a0 +0x21c; jal __sanitizer::CheckFailed +0x22c | CheckFailed(file=a0, line, cond=a2, ...): file string (a0) |
| +0x220 | "((size)) > (((1ULL << up)))" | 0x15a11 / 0x158d9 | 28 | yes | auipc a1 +0x218; addi a2 +0x220; jal __sanitizer::CheckFailed +0x22c | CheckFailed(file=a0, line, cond=a2, ...): condition string (a2) |

| acceptance | equality | consumer |
|---|---|---|
| full +0x184: `auipc a1` +0x180, `ld a1, lo(a1)` +0x184 (8 bytes) -> 0x103b0 in both | .rodata, file bytes, no symbol at the place. Bytes bf 5d 3d cd 92 a3 18 02 in both (0x0218a392cd3d5dbf, the 64-bit de Bruijn constant). EQUAL (8 = 8 bytes). | The ld overwrites the auipc register; one read of the place. The loaded value has one use: `mul a1, a2, a1` +0x190 with a2 = x & -x (`neg a2, a4` +0x188, `and a2, a4, a2` +0x18c). Inside the compared 8 bytes. |
| full +0x19c: `auipc a2` +0x194, `addi a2, a2, lo` +0x19c -> 0x20b1a (donor) / 0x2093a (target) | .rodata, file bytes; only $d at the place. The kit's region: to the next FUNC / OBJECT symbol, _ZZN11__sanitizer12ThreadLister7IsAliveEyE7kPrefix at 0x20b5a / 0x2097a, = 64 bytes in both (section end 0x22c4c / 0x225c4 is later). The 64 bytes are equal: 00010207030d081304190e1c0922142805111a260f2e1d300a1f2336153229393f060c12181b212710252d2f1e3531383e0b1720242c34373d162b333c2a3b3a in both. EQUAL. The table is the ctz table of the constant above: table[((1 << k) * C mod 2^64) >> 58] = k for every k in 0..63. | `srli a1, a1, 0x3a` +0x198 (a1 = the product >> 58, so 0 <= a1 <= 63); `add a1, a2, a1` +0x1a0; `lbu a1, 0(a1)` +0x1a4 (one byte, overwrites a1). So the only read is one byte at table + [0, 63], inside the 64 compared bytes. The base a2 has no other memory use (it is live at the FakeStack::Create call +0x1c0, whose one parameter is a0, so it is not passed). |

BYTECMP.md (last section, acceptances table) names this table "at +0x194": that is the auipc of the pair; the kit's
acceptance is reported at the addi, +0x19c. Wording only; same place.

## __asan::MemToShadow, the copy __asan_stack_malloc_1 +0x144 calls (donor 0x3d410 / target 0x3c348, 316 bytes): C string 2

| word | C string (with its NUL) | donor addr / target addr | len | equal | consumer: instructions (offsets in the function, same in both twins) | use |
|---|---|---|---|---|---|---|
| +0x124 | "/llvm-project/compiler-rt/lib/asan/asan_mapping.h" | 0x1fa8a / 0x1f8b3 | 50 | yes | auipc a0 +0x11c; addi a0 +0x124; jal __sanitizer::CheckFailed +0x138 | CheckFailed(file=a0, line, cond=a2, ...): file string (a0) |
| +0x128 | "((AddrIsInMem(p))) != (0)" | 0x17059 / 0x16f18 | 26 | yes | auipc a1 +0x120; addi a2 +0x128; jal __sanitizer::CheckFailed +0x138 | CheckFailed(file=a0, line, cond=a2, ...): condition string (a2) |

## Callees: how each consumer reads the string (both twins; offsets in the callee)

| callee | parameter | reads in the callee | C-string use |
|---|---|---|---|
| __sanitizer::CheckFailed (184 bytes) | file = a0 | `mv s0, a0` +0x34; `mv a0, s0` +0x4c; `jal StripModuleName` +0x50; result `mv a2, a0` +0x54 to `jal Printf` +0x7c | StripModuleName: `jal internal_strrchr(file, '/')`, returns that + 1 or file; internal_strrchr is a byte loop (`lbu`, `beqz` = stop at NUL). Printf format "%s: CHECK failed: %s:%d \"%s\" (0x%zx, 0x%zx) (tid=%u)\n": a2 is the 2nd %s. |
| __sanitizer::CheckFailed | cond = a2 | `mv s3, a2` +0x2c; `mv a4, s3` +0x6c; `jal Printf` +0x7c | a4 is the 3rd %s of the same format. No other use. |
| __sanitizer::Report (76 bytes) | format = a0 | `mv t0, a0` +0x8; `mv a1, t0` +0x38; `jal SharedPrintfCode` +0x3c | SharedPrintfCode passes it (a2) to SharedPrintfCodeNoBuffer, which passes it (`mv s0, a2`, `mv a2, s0`) as the format of VSNPrintf (+0xdc). VSNPrintf: `lbu a0, 0(s10)` +0x90, `beq a0, '%'`, `beqz a0` = end: a byte loop that stops at the NUL. |
| __sanitizer::MmapOrDie (268 bytes) | mem_type = a1 | `mv s1, a1` +0x1c; `mv a0, s1` +0x68 to `jal GetNamedMappingFd` +0x70; `mv a1, s1` +0x100 to `jal ReportMmapFailureAndDie` +0x108 | GetNamedMappingFd: `jal internal_strlen(name)` +0x5c (byte loop to NUL), then `internal_snprintf(buf, 200, "/dev/shm/%zu [%s]", pid, name)` with name = a4 = the %s (+0x84). ReportMmapFailureAndDie: name to a5 of Report (+0xb0) with format "ERROR: %s failed to %s 0x%zx (%zd) bytes of %s (error code: %d)\n" or "ERROR: %s: out of memory: failed to %s 0x%zx (%zd) bytes of %s (error code: %d)\n": a5 is the 5th conversion, %s, in both. No other use. |
| __sanitizer::FlagParser::RegisterHandler (96 bytes) | name = a1, desc = a3 | `mv a4, a3` +0x0; CHECK n_flags_ < 200; `ld a5, 0(a0)` (flags_) +0x10; entry = flags_ + n * 24; `sd a1, 0(a5)` +0x28 (Flag.name); `sd a4, 8(a5)` +0x2c (Flag.desc); `sd a2, 0x10(a5)` +0x30 (handler) | Stored for later use as strings. No other use of a1 / a3. |
| FlagParser::parse_flag (784 bytes) | Flag.name | `ld a0, 0(s0)`, `add a0, a0, s2`, `ld a1, 0(a0)` +0x208..+0x210; `jal internal_strcmp` +0x218 (a0 = the parsed name) | internal_strcmp: `lbu` both, stop at the first unequal byte or at NUL: never reads past the NUL of either string. Flag.desc (+8) is not read here. |
| FlagParser::PrintFlagDescriptions (288 bytes) | Flag.name, Flag.desc | `ld a1, 0(a0)` +0x84, `ld a2, 8(a0)` +0x88; `jal Printf` +0x94 with format "\t%s\n\t\t- %s (Current Value%s: %s)\n" | a1 and a2 are the 1st and 2nd %s (no precision). VSNPrintf's 's' branch (+0x1f8..+0x290): `ld a5, 0(s2)` (the argument), then `lbu a4, 0(a5)` / `beqz a4` loop: stops at the NUL. |

Readers of Flag entries: flags_ (FlagParser field 0) is a private member. Of the FlagParser member functions in .symtab
(constructors C1 / C2, RegisterHandler, parse_flag, ParseString, ParseFile, ParseStringFromEnv, PrintFlagDescriptions),
only RegisterHandler (stores), parse_flag (+0x208: name; +0x25c: handler) and PrintFlagDescriptions (+0x7c: name and
desc; +0xa8: handler) load field 0; the constructors store it; the other three do not load it.

## Counts checked

- C-string rows: 200 of 200 equal (2 AsanTSDGet, 10 DTLS_on_tls_get_addr, 178 RegisterCommonFlags, 2 FakeStack::GC,
  6 AsyncSignalSafeLazyInitFakeStack, 2 MemToShadow copy); 200 of 200 consumers checked by program in both twins;
  38 read by hand (all 22 of the six small functions, 16 of RegisterCommonFlags).
- 'full': 3 of 3 (GC +0xb0, LazyInit +0x184, LazyInit +0x19c), equal and read inside the compared bytes.
- '.got value': 1 of 1 (DTLS_on_tls_get_addr +0x64), equal, used as a TP offset only.
- tls_index: 1 of 1 (__asan_stack_malloc_1 +0x1c), equal, passed to __tls_get_addr only.

## Not checked, limits, and notes

- RegisterCommonFlags +0x1218 (the unnamed empty string the kit reports as a difference) is not an acceptance of the
  kit and is not audited here; it has its own settlement and review (BYTECMP.md, records/settle-sm1-review.md).
- Readers of Flag.name / Flag.desc are bounded to FlagParser's member functions in .symtab (flags_ is private); I did
  not scan the whole image for other loads of the Flag array.
- VSNPrintf: I read the format loop and the %s branch; I did not trace each other conversion branch (reached through
  a jump table). The six Report formats of the rows use only %p, %zd and %zx; the strings passed as arguments here
  (file, condition, mem_type, flag name, description) are all printed through %s.
- REAL(__tls_get_addr): I read the file value of __interception::real___tls_get_addr (.data, the address of
  __tls_get_addr in both twins). A run-time write to that writable variable is not excluded by this static read.
- The data-flow of step 4 lists a register that still holds the value at a call even when the callee does not take
  that register as a parameter. In the 200 CSTR rows every call that receives the address in an argument register
  takes that register as its string parameter (CheckFailed a0 / a2, Report a0, MmapOrDie a1, RegisterHandler a1 / a3).
  In the callee and non-C-string traces a value is live in such a register at GetTid (CheckFailed, a2), Abort and
  RawWrite (ReportMmapFailureAndDie, a1), PoisonShadow (GC, a5) and FakeStack::Create (LazyInit, a2); none of these
  takes that register as a parameter.
