# bytecmp: __asan_stack_malloc_1, donor fuzz_grant.asan vs target fuzz_uci.asan

**RESTATED (comparison kit 4bbd3a74be89, last section):** the claim "13 bodies equal up to relocation" below, made with
bytecmp.py, is RESTATED as: 12 of 13 kit-EQUAL; RegisterCommonFlags: 1 unnamed empty-string place at +0x1218 not
certified by the kit (whole-region compare). Settled by hand as an ACCEPTANCE: the place is the C string "" (one NUL
byte) in both images and its one consumer reads it only as a C string, so it is EQUAL as a C string
(gates/settle-sm1.py, records/settle-sm1.out, reviewed in records/settle-sm1-review.md). After settlement: 13 of 13
equal, 1 by the empty-string measurement. The bytes the proof reads of RegisterCommonFlags (fs_ranges at +0x358) are
kit-EQUAL.

donor  unstripped twin sha256 57c26f99361583f69af95af52819bebfcf920468a03cf795b95e024fe9798a4d (twin of pin c2c7559b29bd), __asan_stack_malloc_1 at 0x3cf18, 400 bytes
target unstripped twin sha256 56822e263d767986a76ec862cbfbee7571b0e64df2413ad18d7201205a7563fb (twin of pin 6ea017c24525), __asan_stack_malloc_1 at 0x3c1b8, 400 bytes
tool: `bytecmp.py` (pyelftools 0.33 + capstone 5.0.7, RISCV64 | RVC), linear disassembly of each symbol's bytes

instructions: donor 100, target 100; identical (mnemonic + operands + size): 91
differing: 9, every one a pc-relative immediate; each resolves to the same place in both images:

| donor pc | target pc | insn | donor resolves to | target resolves to | verdict |
|---|---|---|---|---|---|
| 0x3cf30 | 0x3c1d0 | auipc | auipc+addi: the .got cell 0x9d550 (no sized symbol), read as a pointer cell: the TLS index pair module id 1, offset -0x800 | auipc+addi: the .got cell 0x97d00, the same TLS index pair | SAME |
| 0x3cf38 | 0x3c1d8 | jal | call __interceptor_trampoline___tls_get_addr+0 | call __interceptor_trampoline___tls_get_addr+0 | SAME |
| 0x3cf58 | 0x3c1f8 | jal | call __asan::FakeStack::GC+0 | call __asan::FakeStack::GC+0 | SAME |
| 0x3cfd0 | 0x3c270 | auipc | auipc+ld: .got slot of __asan_option_detect_stack_use_after_return | auipc+ld: .got slot of __asan_option_detect_stack_use_after_return | SAME |
| 0x3cfe0 | 0x3c280 | jal | call __asan::GetCurrentThread+0 | call __asan::GetCurrentThread+0 | SAME |
| 0x3d05c | 0x3c2fc | jal | call __asan::MemToShadow+0 (the copy at 0x3d410) | call __asan::MemToShadow+0 (the copy at 0x3c348) | SAME |
| 0x3d098 | 0x3c338 | jal | call __asan::AsanThread::AsyncSignalSafeLazyInitFakeStack+0 | call __asan::AsanThread::AsyncSignalSafeLazyInitFakeStack+0 | SAME |

The two auipc second halves (addi / ld at +4) are counted in the 9 differing lines; each pair resolves as one row above.
Class / call site at the target (`sites.py`, every jal of the executable PT_LOAD scanned: 6594; records/sites-target.out):
ONE call into any __asan_stack_malloc_*: check_clamp 0x7f8ec, `addi a0, zero, 0x60` at 0x7f8e8. The image links no
__asan_stack_malloc_0 / 2 / 4. The donor (records/sites-donor.out) links classes 0, 1, 2 and 4 and calls class 1 at
reac_ctrl_parse 0x82070 (a0 = 0x80) and ctrl_lay_block 0x83070 (a0 = 0x60).
VERDICT: equal up to relocation.

## Every body lib/A/Rt/AF0r.v / AF0s.v step through (bytecmp.py; full output records/bytecmp-bodies.out)

The bodies: the twelve ranges of AF0r.v's code table `fs_ranges` (by symbol: stack_malloc_1, the tls_get_addr interceptor,
__tls_get_addr, GetCurrentThread, AsanTSDGet, __pthread_getspecific, DTLS_on_tls_get_addr, the MemToShadow copy
stack_malloc_1 calls, the 2 words of RegisterCommonFlags at +0x358, and stack_malloc_0 / _2 / _4), and every callee the
class-1 code names: the trampoline, TryAsanInitFromRtl, FakeStack::GC, AsyncSignalSafeLazyInitFakeStack. Each WHOLE
function is compared (a range that covers part of a function is inside it). A local name with several copies
(MemToShadow) is taken where the paired call lands. A pc-relative word is resolved even when its text is the same in
both images. A place with no sized symbol is read by its kind (the image-B record's rules, its tool f31bad62a6cb):
- A cell of a POINTER section (.got, .got.plt, .data.rel.ro, .plt.got) is read as its 8-byte value and RESOLVED to the
  symbol + offset it names. A TLS symbol is skipped in that resolve, because its st_value is an offset in the TLS
  block, not an address (without the skip the value 1 resolves to fake_stack_tls+1 in fuzz_uci.asan). A value that
  resolves to no sized symbol is reported as the cell's 16 bytes, which is what a TLS index pair is.
- Any other place: its section, the NUL-terminated string at it AND a fixed 64-byte window. The window makes the
  rule fail closed: a NUL cut alone calls two different places equal whenever their strings agree, and for an EMPTY
  string that is one zero byte.
- The offset in the section is not compared: a relocated place legitimately moves inside its section.
- The reader zero-fills only the part of a range beyond p_filesz.

Three rows resolve to such a place. The .got cell stack_malloc_1 +0x18 takes the address of (0x9d550 / 0x97d00) holds
the same TLS index pair in both images, module id 1 and offset -0x800 (`__tls_get_addr`'s argument). The two EMPTY
strings, RegisterCommonFlags +0x1210 (.rodata 0x13f5f / 0x13e5f) and AsyncSignalSafeLazyInitFakeStack +0x194 (.rodata
0x20b1a / 0x2093a, a zero byte that starts a 64-byte table), are equal on the 64-byte window too. The record of this
slice at commit 2894d73b0f91 (tool blob sha256 96785f56336f) reported the .got cell as a single zero byte for a wrong
reason: the cell is 0x18 bytes before the end of p_filesz (0x9d568 / 0x97d18), and that reader zero-filled the WHOLE
64-byte window that crossed it, so both sides read zeros; and the empty strings were compared by the NUL cut alone.
With the fixed reader and rules the verdicts are unchanged (13 bodies, 0 not equal, 249 rows SAME, 0 DIFFERENT, before
and after), because the cells hold the same pair and the windows agree.

| body | donor | target | bytes | insns | identical | pc-relative, same place | different | verdict |
|---|---|---|---|---|---|---|---|---|
| __asan_stack_malloc_1 (FS_ENTRY .. FS_RET; fs_ranges) | 0x3cf18 | 0x3c1b8 | 400 / 400 | 100 / 100 | 91 | 9 | 0 | EQUAL UP TO RELOCATION |
| __interceptor_trampoline___tls_get_addr (callee of stack_malloc_1 +0x20) | 0x4218c | 0x410c0 | 4 / 4 | 1 / 1 | 0 | 1 | 0 | EQUAL UP TO RELOCATION |
| ___interceptor___tls_get_addr (fs_ranges) | 0x46aac | 0x45924 | 124 / 124 | 31 / 31 | 26 | 5 | 0 | EQUAL UP TO RELOCATION |
| __asan::TryAsanInitFromRtl (callee of the interceptor +0x18) | 0x5980c | 0x58444 | 160 / 160 | 40 / 40 | 38 | 2 | 0 | EQUAL UP TO RELOCATION |
| __tls_get_addr (fs_ranges; the interceptor calls it through .got) | 0x96620 | 0x90f44 | 36 / 36 | 9 / 9 | 9 | 0 | 0 | EQUAL UP TO RELOCATION |
| __asan::GetCurrentThread (fs_ranges) | 0x5c00c | 0x5ac44 | 32 / 32 | 8 / 8 | 8 | 0 | 0 | EQUAL UP TO RELOCATION |
| __asan::AsanTSDGet (fs_ranges, first 6 words) | 0x54b58 | 0x53790 | 64 / 64 | 16 / 16 | 9 | 7 | 0 | EQUAL UP TO RELOCATION |
| __pthread_getspecific (fs_ranges) | 0x976d4 | 0x91ff8 | 28 / 28 | 7 / 7 | 7 | 0 | 0 | EQUAL UP TO RELOCATION |
| __sanitizer::DTLS_on_tls_get_addr (fs_ranges, first 140 words) | 0x69720 | 0x68358 | 848 / 848 | 212 / 212 | 180 | 32 | 0 | EQUAL UP TO RELOCATION |
| __asan::MemToShadow, the copy stack_malloc_1 +0x144 calls (fs_ranges, first 28 words) | 0x3d410 | 0x3c348 | 316 / 316 | 79 / 79 | 64 | 15 | 0 | EQUAL UP TO RELOCATION |
| __sanitizer::RegisterCommonFlags (fs_ranges: the 2 words at +0x358) | 0x61974 | 0x605ac | 4772 / 4772 | 1193 / 1193 | 823 | 370 | 0 | EQUAL UP TO RELOCATION |
| __asan::FakeStack::GC (callee of stack_malloc_1 +0x40) | 0x3c958 | 0x3bd6c | 744 / 744 | 186 / 186 | 166 | 20 | 0 | EQUAL UP TO RELOCATION |
| __asan::AsanThread::AsyncSignalSafeLazyInitFakeStack (callee of stack_malloc_1 +0x180) | 0x5c280 | 0x5aeb8 | 560 / 560 | 140 / 140 | 120 | 20 | 0 | EQUAL UP TO RELOCATION |

bodies 13, not equal 0; `python3 bytecmp.py <donor twin> <target twin>` exit 0.

fs_ranges' other three entries, fuzz_grant A's __asan_stack_malloc_0 (0x3cda4, 93 words), _2 (0x3d0a8, 103) and _4
(0x3d244, 115), have no body in fuzz_uci A: the image links class 1 only (above). The class-1 code calls none of them
(its five calls are the rows of the first table), so no step of the two proofs runs them.

## The tool: the image-B record's fixed tool and one change, measured

`bytecmp.py` is the image-B record's tool at commit 51cfb939a547 (../stackmalloc1-B/bytecmp.py, sha256 f31bad62a6cb:
the pointer-cell and window rules, the p_filesz reader, `--plant-data`) with the two image shas changed and one change:
an `addi rd, rs, 0` word (OP-IMM, funct3 0, immediate 0; capstone prints it `mv rd, rs`) is taken as the addi half of an
auipc pair, offset 0; `--no-addi0` turns it off. `bytecmp.py --no-addi0` prints, byte for byte, what f31bad62a6cb
prints with these two shas (records/bytecmp-bodies-b-tool.out): one body NOT EQUAL with two DIFFERENT rows,
TryAsanInitFromRtl +0xc / +0x10, donor `auipc a0, 0x4c` + `addi s0, a0, 0` (word 0x00050413, printed `mv s0, a0`)
against target `auipc a0, 0x48` + `addi s0, a0, -0x778`. Both pairs form the address of __asan::asan_inited (donor
0x59818 + 0x4c000 + 0 = 0xa5818; target 0x58450 + 0x48000 - 0x778 = 0x9fcd8; each is asan_inited's st_value in its own
twin), so the pair is a pc-relative address formation, the kind every SAME row is. The donor's low half is 0 because
asan_inited - pc (0x4c000) is a multiple of 4 KiB there. The changed tool decides this pair SAME and no other row
changes (bodies-b-tool.out and bodies.out differ in that body's line, its two rows and the summary only). Regression
control: the changed tool with the image-B shas, run on the image-B twins (fuzz_grant.asan-ubsan 5a5ee7c02b4e,
fuzz_uci.asan-ubsan 8d07ffcf5948), prints the image-B record at 51cfb939a547 (../stackmalloc1-B/records/
bytecmp-bodies.out) line for line.

Controls (records/bytecmp-control-1.out .. -6.out), each exit 1, unplanted exit 0:

| # | plant | what it tests | result |
|---|---|---|---|
| 1 | `--plant 0x3c24c:00e668b3` | an instruction word: `or` for the `and` at uci's FS_LOOP | exactly one DIFFERENT row (0x3cfac / 0x3c24c) |
| 2 | `--plant 0x3c280:02c1f0ef` | a re-pointed call: the donor's own `jal 0x1f02c` left at the GetCurrentThread call (the same word, which lands on AsanThread::Init+452 in uci) | exactly one DIFFERENT row (0x3cfe0 / 0x3c280, "same word") |
| 3 | `--plant 0x58454:00050413` | the addi-0 rule: the donor's own `addi s0, a0, 0` left at uci's TryAsanInitFromRtl +0x10 | exactly one DIFFERENT row (the auipc 0x59818 / 0x58450: asan_inited+0 against internal_alloc_placeholder+592) |
| 4 | `--plant-data 0x97d00:02` | a pointer cell's contents: the module id of the .got cell's TLS index pair, 1 -> 2 | the two rows of that auipc + addi pair DIFFERENT (cell 0100...f8ff... against 0200...f8ff...) |
| 5 | `--plant-data 0x97d00:b8c1030000000000` | the resolve branch: the same cell pointed at __asan_stack_malloc_1 | the same two rows DIFFERENT (cell against ptr __asan_stack_malloc_1+0) |
| 6 | `--plant 0x13e5f:48002800` | the window rule: one byte (0x27 -> 0x28) in the 64-byte window after the empty string at RegisterCommonFlags +0x1210 | the two rows of that auipc + addi pair DIFFERENT (string 00 on both sides, windows differ) |

Control 6 run with the tool of 2894d73b0f91 (`git show 2894d73b0f91:<this directory>/bytecmp.py`, the same arguments;
records/bytecmp-control-6-before-fix.out) misses the plant: the row stays SAME (`'00'` against `'00'`) and the run
exits 0. That is the empty-string defect, caught by the fixed rule.

`gates/run-gates.sh` re-runs all of it (section 0) and `gates/records-sm1.py` writes the records/ files named here.

## The same address in uci A and uci B

fuzz_uci.asan (twin 56822e263d76) and fuzz_uci.asan-ubsan (twin 8d07ffcf5948) both carry `__asan_stack_malloc_1` at the
SAME address 0x3c1b8, 400 bytes, and each links no other class (../stackmalloc1-B/BYTECMP.md, last section). The class-1
call site differs: check_clamp 0x7f8ec on A, 0x7f9b4 on B, a0 = 0x60 on both.

## Re-run on the comparison kit 4bbd3a74be89 (records/cmpkit-4bbd3a74be89-*.out)

The kit of record, tools/cmpkit/4bbd3a74be89 at commit 3c3e62ee278 (kit id = sha256(SHA256SUMS)[:12]; SHA256SUMS pins its seven files):
strictcmp2 16982e3ef42b is the compare (tcmp per function pair), drvcmp 4d70e90bc1fa the loader, bytecmp 1480ca2faea0.
`cmpkit-sm1.py KITDIR OUTDIR` (env P, R) checks that KITDIR holds exactly the seven pinned files and SHA256SUMS, each
matching, and runs: `drvcmp.py twins` on each side; the kit's own `strictcmp2.py cmp` command over the 12 bodies named
once in each image; strictcmp2's tcmp, imported from KITDIR and given addresses, on the 2 pairs a name does not fix;
`region()` of the kit on each target it reports different; and the controls on planted FILE copies of the target twin.
It adds no compare of its own. closure_strict2 is not run: this record lists its 13 bodies and claims no closure.

Twins (cmpkit-4bbd3a74be89-twins.out): fuzz_grant.asan c2c7559b29bd / twin 57c26f993615 and fuzz_uci.asan
6ea017c24525 / twin 56822e263d76: PT_LOAD layout equal, no differing loadable byte outside the ELF header and
.note.gnu.build-id. Both sides are read from their unstripped twins (.symtab).

Result (cmpkit-4bbd3a74be89-summary.out, -pairs.out, -pairs-by-address.out): of the 13 bodies, **12 EQUAL, 1 NOT EQUAL;
0 UNMEASURED, 0 SIZE / ABSENT.** No differing target is cut off by the kit's 2-target print (closure_strict2 / paircl):
every row has target-differ 0 except RegisterCommonFlags (1), and strictcmp2's tcmp called directly on all 13 pairs
gives the same lists, 1 target in all (cmpkit-4bbd3a74be89-fulllist.out). The C-string acceptances counted below are of
the kit's own byte compare and stay as they are (one CSTR row each in -pairs.out / -pairs-by-address.out).

| body | kit verdict | target-differ | acceptances (full bytes, .got value / tls_index, C string) |
|---|---|---|---|
| __asan_stack_malloc_1 | EQUAL (EQUAL-mod-pcrel) | 0 | 0, 1 (tls_index +0x1c: module 1, fake_stack_tls+0 on both), 0 |
| __interceptor_trampoline___tls_get_addr | EQUAL (EQUAL-mod-pcrel) | 0 | 0, 0, 0 |
| ___interceptor___tls_get_addr | EQUAL (EQUAL-mod-pcrel) | 0 | 0, 0, 0 |
| __asan::TryAsanInitFromRtl | EQUAL (EQUAL-mod-pcrel) | 0 | 0, 0, 0 |
| __tls_get_addr | EQUAL | 0 | 0, 0, 0 |
| __asan::GetCurrentThread | EQUAL | 0 | 0, 0, 0 |
| __asan::AsanTSDGet | EQUAL (EQUAL-mod-pcrel) | 0 | 0, 0, 2 |
| __pthread_getspecific | EQUAL | 0 | 0, 0, 0 |
| __sanitizer::DTLS_on_tls_get_addr | EQUAL (EQUAL-mod-pcrel) | 0 | 0, 1 (.got value +0x64: dtls+0 on both), 10 |
| __asan::MemToShadow, the copy stack_malloc_1 +0x144 calls (0x3d410 / 0x3c348, by address) | EQUAL (EQUAL-mod-pcrel) | 0 | 0, 0, 2 |
| __sanitizer::RegisterCommonFlags (whole function, 4772 bytes) | **NOT EQUAL** (EQUAL-mod-pcrel, 1 target not certified); settled: EQUAL as a C string (acceptance, below) | 1 | 0, 0, 178 |
| __asan::FakeStack::GC | EQUAL (EQUAL-mod-pcrel) | 0 | 1 (8 bytes at 0x10338), 0, 2 |
| __asan::AsanThread::AsyncSignalSafeLazyInitFakeStack | EQUAL (EQUAL-mod-pcrel) | 0 | 2 (8 bytes at 0x103b0; the 64-byte table at +0x19c, the addi of its auipc at +0x194, 0x20b1a / 0x2093a), 0, 6 |

The kit's acceptances above (200 C strings, 3 full-byte compares, 1 .got value, 1 tls_index) were audited by a fresh reviewer, records/cmpkit-acceptances-review.md: **VERDICT: ACCEPT**. Every C string is equal and is read only as a C string; the 3 full-byte places are read within the compared bytes; the .got value and the tls_index are used as those kinds. Equality was checked for all 200 rows and every use was traced by data flow; 38 rows were also read by hand, by the sample rule stated in the review.

**Kit verdict and settled verdict, side by side.** Kit: RegisterCommonFlags NOT EQUAL, against the earlier rows of this
file (13 / 13 equal up to relocation). The one target the kit does not certify is at +0x1218, the `addi` of the auipc
pair at +0x1210: the address of an unnamed EMPTY string in .rodata (0x13f5f / 0x13e5f). The kit's C-string rule needs
one printable byte, so it compares that target's whole region to the next symbol or the section end: 51389 / 51165
bytes, equal for the first 4241 bytes, then different (cmpkit-4bbd3a74be89-region.out). This is the class the kit's
README lists as a cost of failing closed ("an unnamed EMPTY string ... compared by its region to the next symbol, which
differs across images"; a record that needs such a function EQUAL "must settle it another way and say so"). Settled:
EQUAL as a C string, an ACCEPTANCE by the named measurement below. Restatement: 12 of 13 kit-EQUAL; RegisterCommonFlags:
1 unnamed empty-string place at +0x1218 not certified by the kit (whole-region compare); 13 of 13 equal after
settlement, 1 by the empty-string measurement.

The settlement (`gates/settle-sm1.py <donor twin> <target twin>`, output records/settle-sm1.out, exit 0):
- The place: the byte at 0x13f5f (donor) and at 0x13e5f (target) is 0x00, a file byte of a PT_LOAD in both; the C
  string there, with its NUL, is "" (1 byte) on both sides.
- The consumer in RegisterCommonFlags: from +0x121c to the function's end the code is straight-line (no branch; it ends
  in the tail call to FlagParser::RegisterHandler). The address register (s2) is read twice before the epilogue
  restores it at +0x1288: `sd s2, 0x18(a2)` at +0x1228 and at +0x1274. Each stores it into field +0x18 of a 0x20-byte
  object from LowLevelAllocator::Allocate whose field +0 receives _ZTVN11__sanitizer18FlagHandlerIncludeE+0x10, field
  +8 the parser and field +0x10 the byte 0 / 1: the two FlagHandlerInclude handlers, registered by the following
  RegisterHandler calls (the flags `include` and `include_if_exists`: their name arguments at +0x1234 / +0x1260 are
  the kit's CSTR rows of cmpkit-4bbd3a74be89-pairs.out). So the address is each handler's initial path field, not a
  flag name or a description.
- That field's readers: the class's vtable has two methods. FlagHandlerInclude::Parse only stores into field +0x18
  (`sd a1, 0x18(a0)` at +0x1c). FlagHandlerInclude::Format loads it (`ld a3, 0x18(a0)` at +0x10) and passes it as the
  argument of internal_snprintf whose format string is exactly "%s" (0x170a1 / 0x16f60), a conversion with no precision,
  which reads the string up to its NUL. No call in either method receives the object pointer.
- Hence the consumer reads the place only as a C string, and the two C strings are equal: EQUAL as a C string.

Review (records/settle-sm1-review.md, a fresh reviewer that re-derived every fact with its own reads): **VERDICT:
ACCEPT.** It also checked what the record leaves out: FlagHandlerInclude::Format is reached only through its vtable
slot, from FlagParser's flag-description printing; no other code reads the field; each binary's own printf code stops
a "%s" at the first NUL. Its three wording notes do not change the verdict: the listing in records/settle-sm1.out stops
where the address register is restored (+0x1288), not at the function's end (+0x12a0, the tail call, also straight-line);
the register set printed for Parse is an over-approximation (only a0 and s0 hold the object pointer there); and the
three facts above are in the review, not in the script's output.

What the proof steps through of RegisterCommonFlags: only the 2 words at +0x358 that AF0r.v's code table covers
((0x61ccc, 2) / (0x60904, 2)). strictcmp2's tcmp on those 8 bytes: EQUAL, no pc-relative word
(cmpkit-4bbd3a74be89-pairs-by-address.out). The differing target at +0x1218 is outside them.

TryAsanInitFromRtl is EQUAL under the kit without this slice's addi-0 rule: the kit's auipc dataflow (bytecmp
1480ca2faea0) reads the instruction encoding, so `addi s0, a0, 0` is an addi to it.

Controls (cmpkit-4bbd3a74be89-control-N.out; each a FILE copy of the target twin with the bytes written at the address,
compared with the kit's `strictcmp2.py cmp` on the planted function): all 6 caught.

| # | function | planted | kit result |
|---|---|---|---|
| 1 | __asan_stack_malloc_1 | `or` for the `and` at FS_LOOP (0x3c24c) | verdict DIFFERENT |
| 2 | __asan_stack_malloc_1 | the donor's own jal word at the GetCurrentThread call (0x3c280) | target differs at +0xc8: GetCurrentThread+0 / AsanThread::Init+0x1c4 (names) |
| 3 | __asan::TryAsanInitFromRtl | the donor's own `addi s0, a0, 0` at +0x10 (0x58454) | target differs at +0x10: asan_inited+0 / internal_alloc_placeholder+0x250 (names) |
| 4 | __asan_stack_malloc_1 | the .got tls_index's module id 1 -> 2 (0x97d00) | target differs at +0x1c (got-tls-index) |
| 5 | __asan_stack_malloc_1 | the same .got cell holding __asan_stack_malloc_1's address (0x97d00) | target differs at +0x1c (got-tls-index) |
| 6 | __asan::AsanTSDGet | one byte of the C string +0x2c takes, t -> T (0x117a4) | target differs at +0x2c (cstr-differs) |

This slice's control 6 of the earlier section (a byte in the empty string's window at RegisterCommonFlags +0x1210) is
not repeated: under the kit that target already differs unplanted. Its place here is the C-string control 6 above.

Scans clear on cmpkit 86da41d3ef68 (tools/cmpkit/86da41d3ef68 at commit 98e50c029045; `cmpkit-86da41d3ef68-scans.sh KIT P R OUT`, records/cmpkit-86da41d3ef68-kit.out / -luiscan.out / -ambiscan.out): luiscan 9ae61e4a0e01 exposure 0 in both images for all 13 functions above (the MemToShadow copy as `_ZN6__asanL11MemToShadowEm{asan_fake_stack.cpp}`, 0x3d410 / 0x3c348; RegisterCommonFlags has no lui word, so its +0x358 words have none), so rule 8 leaves every verdict of this section unchanged; ambiscan 9f61b4cee422 0 ambiguous hits in the 12 records/cmpkit-4bbd3a74be89-*.out files (12 by-name compares, none of a duplicated name; MemToShadow was compared by address).

Rule 8 by hand (records/cmpkit-86da41d3ef68-lui-trace.md): luiscan's `memfed 0` is not proof (the tool set's README at commit 6d8ff128a01 records that rule 8's dataflow does not follow add / sub / sh*add), and every lui row above was cleared on `memfed 0` or the section test. Each of the 10 lui words per image (stack_malloc_1 1, TryAsanInitFromRtl 2, DTLS_on_tls_get_addr 2, FakeStack::GC 1, AsyncSignalSafeLazyInitFakeStack 4) is traced through every use, add / sub / sh*add included, to its next write, in both images: none forms a static address. 0x1000 in stack_malloc_1 and FakeStack::GC is added to a runtime FakeStack pointer (fake_stack_tls's value / `this`); TryAsanInitFromRtl's 0xff0000 / 0x10000 are the data of an `sc.w` to asan_inited+0; DTLS_on_tls_get_addr's 0xff8 is a size argument; AsyncSignalSafeLazyInitFakeStack's four popcount masks reach an address only as the index 0..63 into a 64-byte unnamed .rodata table whose bytes are equal in both images. No verdict changes.

Ops followed by that trace (the tool set's README at commit 797c750bbb0 records that a `lui-const (dataflow)` settlement fails open through logical ops): every register-register op (add, sub, sh*add, shifts, slt / sltu, and / or / xor, mul, the *w forms) and every register-immediate op (addi / mv, andi / ori / xori / not, slti / sltiu, shifts, addiw / sext.w) that reads a lui-derived register, to its destination's next write, plus memory base / data, branches, AMO / LR / SC, call arguments / returns and stack spills. The logical ops a lui value passes (TryAsanInitFromRtl's xor / and into the sc.w data; AsyncSignalSafeLazyInitFakeStack's popcount and / xori into the table index 0..63) are traced there; no row is `lui-const (dataflow)` (insec 0) and no row changes.
