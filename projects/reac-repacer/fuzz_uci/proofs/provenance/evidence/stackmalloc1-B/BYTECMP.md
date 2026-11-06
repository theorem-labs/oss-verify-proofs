# bytecmp: __asan_stack_malloc_1, donor fuzz_grant.asan-ubsan vs target fuzz_uci.asan-ubsan

donor  unstripped twin sha256 5a5ee7c02b4e2a1d1653dc0c256182c9b65c33dde3a7ddc98b9de2afffe7a417 (twin of pin fde52226dc48), __asan_stack_malloc_1 at 0x3d0c0, 400 bytes
target unstripped twin sha256 8d07ffcf594874884207465cc34ff9f3b1062f21f6d9b3622e0771fa76490b16 (twin of pin a1b86e424add), __asan_stack_malloc_1 at 0x3c1b8, 400 bytes
tool: pyelftools 0.33 + capstone 5.0.7 (RISCV64 | RVC), linear disassembly of the symbol's bytes

instructions: donor 100, target 100; identical (mnemonic + operands + size): 91
differing: 9, every one a pc-relative immediate; each resolves to the same target in both images:

| donor pc | target pc | insn | donor target | target target | verdict |
|---|---|---|---|---|---|
| 0x3d0d8 | 0x3c1d0 | auipc | auipc+addi: .got, $d+0xdd8 (24 bytes at the slot equal) | auipc+addi: .got, $d+0xdd8 (24 bytes at the slot equal) | SAME |
| 0x3d0e0 | 0x3c1d8 | jal | ('call', ('__interceptor_trampoline___tls_get_addr', 0)) | ('call', ('__interceptor_trampoline___tls_get_addr', 0)) | SAME |
| 0x3d100 | 0x3c1f8 | jal | ('call', ('_ZN6__asan9FakeStack2GCEm', 0)) | ('call', ('_ZN6__asan9FakeStack2GCEm', 0)) | SAME |
| 0x3d178 | 0x3c270 | auipc | ('got', None, ('__asan_option_detect_stack_use_after_return', 0)) | ('got', None, ('__asan_option_detect_stack_use_after_return', 0)) | SAME |
| 0x3d188 | 0x3c280 | jal | ('call', ('_ZN6__asan16GetCurrentThreadEv', 0)) | ('call', ('_ZN6__asan16GetCurrentThreadEv', 0)) | SAME |
| 0x3d204 | 0x3c2fc | jal | jal: __asan::MemToShadow (local, size 0) | jal: __asan::MemToShadow (local, size 0) | SAME |
| 0x3d240 | 0x3c338 | jal | ('call', ('_ZN6__asan10AsanThread32AsyncSignalSafeLazyInitFakeStackEv', 0)) | ('call', ('_ZN6__asan10AsanThread32AsyncSignalSafeLazyInitFakeStackEv', 0)) | SAME |

The two auipc/ld and auipc/addi second halves (ld/addi at +4) are counted in the 9 differing lines; each pair resolves as one row above.
Class / call site at the target (all jal in the executable PT_LOAD scanned): ONE call into any __asan_stack_malloc_*: check_clamp 0x7f9b4, `addi a0, zero, 0x60`; LLVMFuzzerTestOneInput (0x7f2e8, 644 bytes) makes none. The image links no __asan_stack_malloc_0 / 2 / 4.
VERDICT: equal up to relocation.

## Every body lib/B/Rt/YF0r.v / YF0s.v step through (bytecmp.py; full output records/bytecmp-bodies.out)

The bodies: the twelve ranges of YF0r.v's code table `fs_ranges` (by symbol: stack_malloc_1, the tls_get_addr interceptor,
__tls_get_addr, GetCurrentThread, AsanTSDGet, __pthread_getspecific, DTLS_on_tls_get_addr, the MemToShadow copy
stack_malloc_1 calls, the 2 words of RegisterCommonFlags at +0x358, and stack_malloc_0 / _2 / _4), and every callee the
class-1 code names: the trampoline, TryAsanInitFromRtl, FakeStack::GC, AsyncSignalSafeLazyInitFakeStack. Each WHOLE
function is compared (a range that covers part of a function is inside it). A local name with several copies
(MemToShadow: 5 in each image) is taken where the paired call lands. A pc-relative word is resolved even when its text
is the same in both images. A place with no sized symbol is read by its kind:
- A cell of a POINTER section (.got, .got.plt, .data.rel.ro, .plt.got) is read as its 8-byte value and RESOLVED to the
  symbol + offset it names; a relocated pointer is not byte-equal across two images unless both name the same address.
  A TLS symbol is skipped in that resolve, because its st_value is an offset in the TLS block, not an address. A value
  that resolves to no sized symbol is reported as the cell's 16 bytes, which is what a TLS index pair is.
- Any other place: its section, the NUL-terminated string at it AND a fixed 64-byte window. The window is what makes
  that fail closed: a NUL cut alone calls two DIFFERENT places equal whenever their strings agree, and for an EMPTY
  string that is one zero byte (the defect class of jtcheck 2e2f9c2126b2 and repin_check 9cbc3553c09e).
- The offset in the section is NOT compared: a relocated place legitimately moves inside its section.

Three rows resolve to such a place. The two empty strings (at AsanTSDGet +0x1c and in RegisterCommonFlags' table) are
equal on the window. The third is the .got cell whose address the `auipc + addi` at stack_malloc_1 +0x18 takes: both
images hold the same TLS index pair, module id 1 and offset -0x800, which is `__tls_get_addr`'s argument. An earlier
run of this record reported that cell as a single zero byte for a WRONG reason: the reader zero-filled a WHOLE window
that crossed p_filesz instead of only the part beyond it, so both sides read zeros. The reader and the rule are fixed
and the record re-run; the verdict is unchanged, because the two cells do hold the same pair.

| body | donor | target | bytes | insns | identical | pc-relative, same place | different | verdict |
|---|---|---|---|---|---|---|---|---|
| __asan_stack_malloc_1 (FS_ENTRY .. FS_RET; fs_ranges) | 0x3d0c0 | 0x3c1b8 | 400 / 400 | 100 / 100 | 91 | 9 | 0 | EQUAL UP TO RELOCATION |
| __interceptor_trampoline___tls_get_addr (callee of stack_malloc_1 +0x20) | 0x42518 | 0x410c0 | 4 / 4 | 1 / 1 | 0 | 1 | 0 | EQUAL UP TO RELOCATION |
| ___interceptor___tls_get_addr (fs_ranges) | 0x46e38 | 0x45924 | 124 / 124 | 31 / 31 | 26 | 5 | 0 | EQUAL UP TO RELOCATION |
| __asan::TryAsanInitFromRtl (callee of the interceptor +0x18) | 0x59b98 | 0x58444 | 160 / 160 | 40 / 40 | 38 | 2 | 0 | EQUAL UP TO RELOCATION |
| __tls_get_addr (fs_ranges; the interceptor calls it through .got) | 0x97484 | 0x9104c | 36 / 36 | 9 / 9 | 9 | 0 | 0 | EQUAL UP TO RELOCATION |
| __asan::GetCurrentThread (fs_ranges) | 0x5c398 | 0x5ac44 | 32 / 32 | 8 / 8 | 8 | 0 | 0 | EQUAL UP TO RELOCATION |
| __asan::AsanTSDGet (fs_ranges, first 6 words) | 0x54ee4 | 0x53790 | 64 / 64 | 16 / 16 | 9 | 7 | 0 | EQUAL UP TO RELOCATION |
| __pthread_getspecific (fs_ranges) | 0x98538 | 0x92100 | 28 / 28 | 7 / 7 | 7 | 0 | 0 | EQUAL UP TO RELOCATION |
| __sanitizer::DTLS_on_tls_get_addr (fs_ranges, first 140 words) | 0x69aac | 0x68358 | 848 / 848 | 212 / 212 | 180 | 32 | 0 | EQUAL UP TO RELOCATION |
| __asan::MemToShadow, the copy stack_malloc_1 +0x144 calls (fs_ranges, first 28 words) | 0x3d79c | 0x3c348 | 316 / 316 | 79 / 79 | 64 | 15 | 0 | EQUAL UP TO RELOCATION |
| __sanitizer::RegisterCommonFlags (fs_ranges: the 2 words at +0x358) | 0x61d00 | 0x605ac | 4772 / 4772 | 1193 / 1193 | 823 | 370 | 0 | EQUAL UP TO RELOCATION |
| __asan::FakeStack::GC (callee of stack_malloc_1 +0x40) | 0x3cb00 | 0x3bd6c | 744 / 744 | 186 / 186 | 165 | 21 | 0 | EQUAL UP TO RELOCATION |
| __asan::AsanThread::AsyncSignalSafeLazyInitFakeStack (callee of stack_malloc_1 +0x180) | 0x5c60c | 0x5aeb8 | 560 / 560 | 140 / 140 | 120 | 20 | 0 | EQUAL UP TO RELOCATION |

bodies 13, not equal 0; `python3 bytecmp.py <donor twin> <target twin>` exit 0.

fs_ranges' other three entries, fuzz_grant B's __asan_stack_malloc_0 (0x3cf4c, 93 words), _2 (0x3d250, 103) and _4
(0x3d3ec, 115), have no body in fuzz_uci B: the image links class 1 only (above). The class-1 code calls none of them
(its five calls are the rows of the first table), so no step of the two proofs runs them.

Controls (records/bytecmp-control-1.out, -2.out): `--plant 0x3c24c:00e668b3` (`or` for the `and` at uci's FS_LOOP) gives
exactly one DIFFERENT row (0x3d154 / 0x3c24c) and exit 1; `--plant 0x3c280:2101f0ef` (the donor's own `jal 0x1f210`
left at the GetCurrentThread call: the same word, which lands on AsanThread::Init+936 in uci) gives exactly one DIFFERENT
row (0x3d188 / 0x3c280, "same word") and exit 1. Unplanted: exit 0.

## The same address in uci A and uci B

fuzz_uci.asan (unstripped twin sha256 56822e263d767986a76ec862cbfbee7571b0e64df2413ad18d7201205a7563fb, twin of pin
6ea017c24525) and fuzz_uci.asan-ubsan (twin 8d07ffcf5948) both carry `__asan_stack_malloc_1` at the SAME address 0x3c1b8,
400 bytes, and each links no other class. 98 of the 100 words are equal; the 2 that differ are the low halves of the
auipc pairs to the TLS descriptor (0x3c1d4) and to the .got slot of __asan_option_detect_stack_use_after_return (0x3c274).

## Re-run with the comparison kit of record (cmpkit 4bbd3a74be89, its one compare strictcmp2 16982e3ef42b)

`records/strictcmp2-bodies.out`: the 13 bodies above, donor image B vs target image B, both unstripped twins. Verdicts:
10 EQUAL-mod-pcrel and 3 EQUAL, 0 different, exit 0. No verdict changes from this record's own tool. The kit reads the
.got cell whose address stack_malloc_1 +0x1c takes as a GD tls_index, and in both images it names the same TLS symbol
(`fake_stack_tls`). The kit's 23 planted controls are its own (cmpkit README, CONTROLS); they are not re-planted here.

## The partner's own fields (added after a fresh review)

A pc-relative word that is not text-identical, and the low half of a matched `auipc` pair, now count as SAME only when
the two words agree outside their pc-relative immediate (`fields()`: auipc / jal keep rd + opcode, I-type keeps rs1 +
funct3 + rd + opcode, S-type keeps rs2 + rs1 + funct3 + opcode). Before, a partner was judged by its resolved target
alone, so a different destination register was called SAME. The base run reproduces records/bytecmp-bodies.out byte
for byte, so no verdict changes. Control 5 (`--plant 0x3c1d4:c3850593`: `addi a1, a0, ..` for `addi a0, a0, ..`, the
low half of the TLS-index pair at stack_malloc_1 +0x18) gives `fields outside the immediate differ`, exit 1:
records/bytecmp-control-5.out.

## Re-run on the comparison kit cmpkit 86da41d3ef68 (strictcmp3), and a CORRECTION to the 4bbd3a74be89 section

The 4bbd3a74be89 section above reported its 13 bodies as 10 EQUAL-mod-pcrel + 3 EQUAL. That read only the verdict
column, which in strictcmp2 compares the instruction words alone; the target-differ column was not read. That column
holds ONE target the kit did not settle: RegisterCommonFlags +0x1218 (`data-differs`, .rodata / .rodata). So that
section's claim was wrong for that one row; the other 12 bodies had no differing target.

records/strictcmp3-bodies.out: the same 13 bodies on strictcmp3 (the kit's combined verdict). 12 are EQUAL or
EQUAL-mod-pcrel with target-differ 0. MemToShadow is compared as the copy stack_malloc_1 +0x144 calls,
`_ZN6__asanL11MemToShadowEm{asan_fake_stack.cpp}` (grant B 0x3d79c / uci B 0x3c348): EQUAL-mod-pcrel 15. The
by-name compare of the old record took copy 1 of 5 (asan_errors.cpp); records/ambiscan.out lists that row.
RegisterCommonFlags is DIFFERENT-target at the one +0x1218 target, settled by hand below.

records/luiscan.out: rule 8 (lui-built absolute addresses) exposure 0 in both images over the 13 functions.

### The +0x1218 settlement (records/settle-rcf.out, gates/settle-rcf-sm1.py)

| | kit (strictcmp3 tsame) | settled |
|---|---|---|
| RegisterCommonFlags +0x1218, .rodata 0x13e96 / 0x13e5f | NOT SETTLED: data-differs, region lengths 51658 / 51165 | EQUAL: both read-only, bytes up to and including the NUL `\x00` / `\x00` |

It is the kit's documented fail-closed class (1): an UNNAMED target in read-only data whose first byte is NUL (an
empty string), compared by the kit on its whole region to the next symbol. The settlement compares it as a C string,
because that is how it is consumed. The addi at +0x1218 writes x18, and its first use is `sd x18, 24(x12)` at
+0x1228: the address is stored into a field of the flag-registration record, the same word in both images.
Control: a printable byte planted at the uci target makes the settled compare DIFFERENT (caught).
And the proof never steps through that word: its code table (lib/B/Rt/YF0r.v fs_ranges) holds only RegisterCommonFlags
+0x358 and +0x35c. The same settlement for libdiginet/fuzz_decode's identical body was audited SOUND by a fresh
reviewer.
