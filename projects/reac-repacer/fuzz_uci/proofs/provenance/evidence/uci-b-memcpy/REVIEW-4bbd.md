CONFIRM: all 145 rows of settle.out are settled by the fixed settle.py (BYTE64 6, WORDS(3) 1, REL4 2, CSTRANY 136, all EQUAL). Two things remain open, and neither changes any row:
- The use check `cstr_use` still lets some uses escape: R1 (a regression from the last fix), R3-R6, and G3a under its documented rule (section 5). No path of the 145 rows reaches any of them.
- RECORD.md has two text errors (section 6).

# Fresh review of the UCI-B-MEMCPY donor byte compare: the 49 named-measurement settlements

The reviewer made none of the settlements. Three passes were run: the original record, then the fix of the one sent-back row, then the fix of the use-check gaps. All measurements were taken from the two images with the reviewer's own tools. The author's files were used only as the list of claims. In the second and third passes, the author's own code was also run to check it.

## Inputs

| role | name | sha256 |
|---|---|---|
| X | uci image B, unstripped twin | `8d07ffcf594874884207465cc34ff9f3b1062f21f6d9b3622e0771fa76490b16` |
| Y | fuzz_grant image B, unstripped twin | `5a5ee7c02b4e2a1d1653dc0c256182c9b65c33dde3a7ddc98b9de2afffe7a417` |
| claims | jtcheck-others.out (kit jtcheck 824905e26211, cmpkit 4bbd3a74be89) | `e3049451aa51…` |
| claims | settle.py, first pass / second / final | `d985ce5b4701` / `694c37f356e2` / `0a89ccf4c24e` |
| claims | settle.out, first pass / final | `0757410cdda3` / `7485132f2f4e` |
| control | control-notable.out | `afe5976dd8d3…` |

Row numbers below are settle.out data rows in file order. The file line is the row number + 1.

## Method

- **Bytes:** an independent ELF reader (pyelftools) reads file bytes inside a PT_LOAD's p_filesz only. Disassembly is capstone 5.
- **Decoder and trace:** an independent RV64 decoder and a path-exploring use trace. For each row, on X and on Y:
  - the word at fn+offset is `addi rd, rs, lo12`, and its auipc gives the row's address (290 of 290);
  - the trace follows every register and sp slot that holds the address, through copies and spill/reload, over both branch directions, in-function jumps and calls (callee-saved registers survive);
  - it records every use: call argument, tail argument, return, store, load base, arithmetic, compare, indirect jump;
  - for printf-like callees it resolves the format string and maps the argument register to its conversion.
- **Same on both images:** for every row, the X and Y use lists are identical.
- **Functions:** the 49 functions have unique symtab names. Each one decodes completely as 32-bit words (no RVC). Every row's X and Y address lies in `.rodata` of the read-only PT_LOAD.

## 1. Result per measurement (final)

| measurement | rows | applies to how the code uses the address | bytes equal | verdict |
|---|---|---|---|---|
| BYTE64 | 6 | 6 | 6 | confirm |
| WORDS(3) | 1 | 1 | 1 | confirm (was CSTRANY in the first pass: sent back, now fixed) |
| REL4 | 2 | 2 | 2 | confirm |
| CSTRANY | 136 | 136 | 136 | confirm |

**Coverage:**
- jtcheck-others.out leaves 141 words open in 49 functions (140 UNMEASURED, 1 DIFF). The header counts equal the listed lines, and the header addresses equal the symtab.
- Every open word has a settle.out row: 0 missing.
- The 4 extra rows are words that form an address which another, jtcheck-listed word in the same function also forms. jtcheck had accepted each of them as an `abs8-ptr` table (section 6): `ErrorMallocUsableSizeNotOwned::Print` +0x6c, `ErrorSanitizerGetAllocatedSizeNotOwned::Print` +0x6c, and `ReportDeadlySignal` +0x29c and +0x2a0. All 4 are `Printf` `%s` arguments.

## 2. The sent-back row, now WORDS(3): `__sanitizer::OpenFile` +0x60 (row 118)

```
+0x1c mv s1,a1 (mode) ; +0x50 addi a1,zero,2 ; +0x54 bltu a1,s1,+0x1c ; +0x58 slli s1,s1,2
+0x5c auipc a1 ; +0x60 addi a1,a1,lo (X 0x20990 / Y 0x20bb4) ; +0x64 add a1,a1,s1 ; +0x68 lw a1,0(a1)
```

- This is the `switch (mode)` open-flags table {0, 0x241, 0x42}, and it is passed to `internal_open(path, flags, 0660)`.
- The first pass called it CSTRANY, which compared 1 byte of the 12 the code reads. Two settle.py faults caused this:
  - `table4` gave up when the index `add` wrote back into the table register;
  - the CSTRANY gate checked only whether the forming `addi` was a load (never true), not how the address is used.
- Final: WORDS(3), 12 bytes X = Y = `000000004102000042000000`. The next table (Describe's) starts at base + 12 on both images.

## 3. BYTE64 (rows 1-6), REL4 (rows 119, 139)

### BYTE64

Each row, at the same offsets on both images:
- `srli rI, rX, 58` is a 64-bit SRLI, so rI is in [0, 63], and it is rI's last writer before `add rA, rT, rI`;
- `lbu _, 0(rA)` follows the add directly;
- the 64 bytes are equal.

All six tables have the same bytes, a permutation of 0..63 (the de Bruijn ctz table): `00010207030d0813…2a3b3a`.

| row | function | word | X / Y | srli / add / lbu |
|---|---|---|---|---|
| 1 | `Allocator::Deallocate` | +0x20c | 0x103e0 / 0x103e8 | +0x208 / +0x210 / +0x214 |
| 2 | `Allocator::Allocate` | +0xdc | 0x10420 / 0x10428 | +0xd8 / +0xe0 / +0xe4 |
| 3 | `SizeClassAllocator64::MaybeReleaseToOS` | +0x140 | 0x10460 / 0x10468 | +0x13c / +0x144 / +0x148 |
| 4 | `SizeClassAllocator64::ReleaseFreeMemoryToOS` | +0x128 | 0x104a0 / 0x104a8 | +0x124 / +0x12c / +0x130, and a 2nd use +0x244 / +0x248 / +0x24c |
| 5 | `PackedCounterArray` ctor | +0x190 | 0x104e0 / 0x104e8 | +0x194 / +0x198 / +0x19c |
| 6 | `RZSize2Log` | +0x44 | 0x10520 / 0x10528 | +0x4c / +0x50 / +0x54 |

settle.py's `byte64()` (and `table4()`) look only at the first use of the base register. The second use in row 4 was checked here: it is also a 58-bit shift then `lbu`.

### REL4

- **Row 119, `SignalContext::Describe` +0x1c, REL4(8) string.**
  - Code: `addiw a0,signo,-4`, then the bound `addi a1,zero,7` + `bltu a1,a0` (unsigned), then `slli`, `add a0,a1,a0`, `lw a0,0(a0)`, `add a0,a1,a0`, `ret`. It returns table + sx32(entry), with no `jr`. The bound is identical in Y.
  - The 8 entries resolve to equal strings on both images: `ILL`, `TRAP`, `ABRT`, `BUS`, `FPE`, `UNKNOWN SIGNAL` ×2, `SEGV`.
- **Row 139, `libunwind::CFI_Parser::parseCIE` +0x23c, REL4(47) jump (jtcheck's DIFF).**
  - Code: `addi s5,zero,0x2e`, `s6` = the table address, idx = c - 'L', `bltu s5,idx`, then `slli`, `add`, `lw`, `add a0,a0,s6`, `jr a0`. The bound is identical in Y.
  - s5 and s6 are written only at +0x234 / +0x23c and by the epilogue restores. The loop head is reachable only through those writes, on the CFG with the jump-table edges included.
  - All 47 entries land at the same in-function offset, 4-aligned, inside the function: 'L' +0x270, 'P' +0x2b4, 'R' +0x298, 'S' +0x248, 'z' +0x28c, and the rest +0x24c (skip the letter).
  - The raw entries differ by a constant, which is why jtcheck's region compare reported a difference.

## 4. CSTRANY (136 rows)

**Bytes:** through the first NUL, equal on X and Y for every row. The 8 distinct pairs:

| X / Y | bytes | rows |
|---|---|---|
| 0x13e5f / 0x13e96 | `\0` (the empty string) | 65 |
| 0x18da2 / 0x18e32 | `\x1b[1m\x1b[0m\0` | 34 |
| 0x17764 / 0x17804 | `\x1b[1m\x1b[31m\0` | 24 |
| 0x1d709 / 0x1d817 | `\x1b[1m\x1b[35m\0` | 5 |
| 0x176fa / 0x1779a | `\x1b[1m\x1b[32m\0` | 4 |
| 0x1f9aa / 0x1fb89 | `\x1b[1m\x1b[34m\0` | 2 |
| 0x20198 / 0x20377 | `\x1b[1m\x1b[33m\0` | 1 |
| 0x10903 / 0x1090b | `\x1b[1m\x1b[36m\0` | 1 |

**Use:** every row was traced, not a sample. A row can have several uses:

| use | rows |
|---|---|
| `Printf` argument, conversion `%s` (format resolved on each image; 123 row/site uses, all `%s`) | 96 |
| `InternalScopedString::AppendF` argument, `%s` | 10 (22, 24, 26, 103-106, 124, 133, 134) |
| `InternalScopedString::Append(const char*)` | 7 (7, 8, 13, 14, 28-30) |
| `PrintMemoryByte(…, const char* before, …, const char* after)`; inside it, both go to AppendF `%s` | 2 (97, 98) |
| returned in a0: `Decorator::ShadowByte` (its only direct caller passes the result as AppendF `%s`), the three `*_default_options` / suppressions functions, `__nl_langinfo_l`, `__tm_to_tzname`, `__strftime_fmt_1` (with `*l = 0`) | 14 |
| 8-byte pointer store into an object field: CommonFlags `strip_path_prefix`, `cov_8bit_counters_out`, `cov_pcs_out` (each registered with a `FlagHandler<const char*>` handler); `__lsan::Flags` +0x20 and `__ubsan::Flags` +8 (`this`); `FlagHandlerInclude::original_path_` (heap object); the global ASan flags object + 0x68 | 5 (102, 115, 116, 135, 137) |
| `FlagParser::ParseString(const char*)`, `PrintAddressDescription(…, const char* bug_type)`, tail `__fstatat(fd, path, …)`, tail `__lctrans(const char*)` | 1 each |
| `lbu a3,0(a0)` at `__nl_langinfo_l` +0x100: the `*str` test, reading byte 0 (the NUL), inside the compared bytes | 1 (142) |

On these rows there is no indexing, no non-zero offset, no pointer arithmetic, and no load beyond byte 0. The other registers that still hold the address at a call are not parameters of the callee.

**Accepting non-printable bytes is sound here, and only because the use is checked.**
- The kit's printable-only rule is a classifier: it uses printability as evidence that an unknown address is a string.
- Here the use is established from the code instead. For a consumer that reads a NUL-terminated string, the observable content is exactly the bytes through the first NUL, whatever their values. ESC is an ordinary byte, and `""` is one byte (the NUL).
- The one row where that failed was OpenFile, which was not a string.

## 5. The `cstr_use` gate (added in the second pass, revised in the final)

**Where the gate stands on the 145 rows:**
- The author's `cstr_use` was loaded from settle.py by AST and run on every row of both images. It passes all 136 CSTRANY rows and refuses all 9 table rows (BYTE64 at the table `add`; OpenFile +0x64, Describe +0x20, parseCIE +0x260).
- This matches the reviewer's trace on 145 of 145 rows, and each refusal is at the same word as the trace's first non-string use.
- An event-logging replica gives the author's result on every row and image.
- control-notable.out reproduces byte-identically (settle.py with table matching off: 3 OPEN, exit 1).
- A re-run of the final settle.py reproduces settle.out `7485132f2f4e`.

Small instruction sequences were used as probes.

| gap | probe | second pass | final |
|---|---|---|---|
| G1 | an FP destination (`fld fa1`, `fadd.d fa1`) dropped integer register a1, so a later use through a1 escaped | escaped | **closed** (the kit's WRITES_RD / FP_WRITES_XRD) |
| G2 | an in-function `jr` (jump table) ended the path | escaped | **closed** (refused while the address is live) |
| G3b | a mid-function `addi sp,+N` released the spill slots | escaped | **closed** (released only before an epilogue to `ret`) |
| G3c | a narrow store of the address counted as storing it | escaped | **closed** |
| G3d / G3e | a store through s0; an FP reload of a slot | — | refused |
| G3a | an 8-byte store through a base other than sp/s0 (e.g. `addi a5,sp,8; sd a1,0(a5)`), then a reload via sp | escaped | **still escapes**, now documented as a "pointer field, copy not followed". It is wrong for a base that points into the function's own stack. |
| **R1** | `ecall` clears a0 **and a1**, then `lw a0,4(a1)` | — | **escapes; introduced by the final fix.** A Linux RISC-V syscall returns in a0 only: syscall(2) note 6 names the architectures that use a second return register, and riscv is not one of them. musl's riscv64 syscall asm declares only a0 as output, so compiled code may reuse a1 after the ecall. Fix: clear a0 only. |
| R3 | `addi sp,+N` before `ld a2,-8(sp); add …; ret`: `epilogue()` allows the reload of a released slot | — | escapes. Theoretical: compilers do not read below sp. |
| R4a | a conditional branch out of the function | — | escapes (dropped silently, not documented) |
| R4b/c | `jal t0` / `jalr t0` (a link register other than ra) is treated as an ABI call that clobbers a0-a7 | — | escapes |
| R5 | a narrower integer reload of a spilled slot (`lwu`) | — | escapes (silently untracked) |
| R6 | a path that runs off the function end | — | escapes (silent) |

**Impact on the 145 rows: none.** Over all 136 CSTRANY paths on both images:
- no ecall is reached with a0/a1 live, no branch leaves the function, no link register other than ra is used, and no narrow reload occurs;
- the 9 fall-offs follow noreturn `CheckFailed` / `Die` calls;
- the 5 slot releases are `addi sp,sp,N; ret`;
- the 8 field stores go through `this`, a heap object, or a global, none of them stack-derived.

What a callee does with an address passed on is not checked by the gate. For these rows it was checked by the trace in section 4.

**Remaining work on the gate:**
1. Fix R1.
2. Refuse R3-R6, or state them in the docstring and in RECORD.md.
3. State G3a as a limit, or track sp-derived bases as slots.

## 6. Record text

- **jtcheck misclassifies five words.** It accepts as `abs8-ptr` tables five words whose addresses the code uses as C strings: the 4 extra rows (section 1) and `Decorator::ShadowByte` +0x28.
  - +0x28 is the red colour string, loaded into a1 before the switch's `jr` and returned (`mv a0,a1; ret`).
  - It is not a settle.out row. Its bytes are equal through the NUL, and the 664 bytes from it are raw-equal, so the verdict holds.
- **RECORD.md (current text) errors:**
  - It says jtcheck "settled that function" (ShadowByte). In fact jtcheck lists it with `target unmeasured 6`, and those six targets are settle.out rows 107-112.
  - It says all five words are used "as `%s` string arguments". ShadowByte +0x28 is returned; "used as C strings" is accurate.
  - "the script closes them" must be qualified per section 5.
- The first-pass record faults are fixed:
  - the hash label of settle.py vs settle.out;
  - the CSTRANY rule wording, which said "not loaded from" (it is loaded from, by `lbu` of byte 0, at `__nl_langinfo_l` +0xf8);
  - the counts, now including the WORDS(3) row.
