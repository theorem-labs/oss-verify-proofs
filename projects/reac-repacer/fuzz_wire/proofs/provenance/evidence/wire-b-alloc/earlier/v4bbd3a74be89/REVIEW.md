# APPROVE 0 rows

Fresh review of the WIRE-B-ALLOC acceptances (slice `proofs/reac-repacer/fuzz_wire/provenance/evidence/wire-b-alloc/`
in a worktree at commit 5193e9e56091; kit cmpkit 4bbd3a74be89).
Reviewer: a fresh reviewer, 2026-10-30. Read-only on every input; no file in the slice was changed.

All 178 target pairs (67 functions) were re-measured from the two images with my own ELF/symtab reader
(`elfx.py`, see "Scripts"), my own RISC-V decoder and
capstone 5.0.7 for display. **0 rows rejected, 0 rows doubtful.**

Images read by me, sha256 computed from the files named in
the record's `env.sh` (not committed):

| token | sha256 | matches RECORD.md |
|---|---|---|
| X = WIRE_B_TWIN (unstripped) | `51eb4bef24252e4df6e11baa89f653d20d74e38ae684f61bc94f4fb339ac97c3` | yes |
| Y = GRANT_B_TWIN (unstripped) | `5a5ee7c02b4e2a1d1653dc0c256182c9b65c33dde3a7ddc98b9de2afffe7a417` | yes |
| WIRE_B_PIN | `af4534831a4528320c7dc74ca3f64bb96e8232ed2e313f01126d10879f3417d6` | yes |
| GRANT_B_PIN | `fde52226dc48de254681156061de9263409c123ca0a0d6c5010ded4e17f602df` | yes |

Twin relation re-measured byte by byte over all four PT_LOADs of each pair: wire pin vs twin 25 differing
loadable bytes, grant pin vs twin 25; every one of them is inside the ELF header `[0x10000,0x10040)` (5 bytes)
or `.note.gnu.build-id` `[0x102a8,0x102cc)` (20 bytes), 0 elsewhere. So reading the unstripped twins is
equivalent to reading the pinned images for code and rodata, as `twins.out` states.

## Rejected or doubtful rows

None. Every ACCEPT row is settled by a measurement I repeated myself in both images.

One **record-text defect, not a row** (must be corrected; it does not touch any acceptance):

- `RECORD.md` line 90-92, in the section headed "Kit verdict (unchanged, as the kit printed it)", says
  "**jtcheck.py** on the 16 members ...: 15 settled; parseCIE `target differs 1` at +0x23c".
  The committed `jtcheck-grant.out` prints, for its 16 member rows: `target differs 1` on parseCIE **and**
  `target unmeasured` 6 on `_ZN6__asan9Decorator10ShadowByteEh`, 1 on `_ZNK11__sanitizer13SignalContext8DescribeEv`,
  2 on `__strftime_fmt_1`, 4 on `_ZN6__asan22ErrorAllocTypeMismatch5PrintEv` (0 unpaired everywhere).
  In the kit's own vocabulary (README "settled -> not settled: ... (unmeasured N)") that is 11 settled,
  1 differs, 4 unmeasured, not "15 settled". The raw output file is committed unaltered and every one of
  those unmeasured targets does have an acceptance row that I verified below, so no row changes; the
  sentence that paraphrases the kit must be restated with the kit's numbers.

## Checks I did

### 1. Every row's target pair re-derived from the instruction words (178/178)

For each row I decoded the word at `function+word` in each image myself, walked back to the `auipc` that
writes its base register, and recomputed `auipc_pc + immU + imm(I|S)`. All 178 X targets and 178 Y targets
equal the values in `ACCEPTANCES.tsv`. (A first run disagreed by 2^32 on every row; the fault was my own
missing sign-extension of the U-immediate, fixed and re-run.)

### 2. CSTR and CSTR-ESCAPE: extent, bytes, printability (152/152)

Reading each target to and including the first NUL in each image: X bytes == Y bytes for all 152 rows,
each equals the row's recorded `X bytes` / `Y bytes` hex, each row's extent equals the measured length
including the NUL, and every byte before the NUL is printable (SP..~, or TAB/LF/CR/ESC for the colour
escapes). No row's string differs across the images.

### 3. CSTR: the reader reads only to the NUL

I wrote my own forward may-taint over the function CFG (copies, `addi` offsets, sp-slot spill/reload,
caller-saved clobber at calls) starting at each row's word, and enumerated **every** use of the pointer in
**both** images. The use sets are structurally identical in X and Y for all 152 rows (0 differences:
same offsets, same callees, same argument registers). The consumers are only:

- `__sanitizer::Printf`/`Report`/`InternalScopedString::AppendF`/`internal_snprintf` varargs: 304 uses.
  For each I resolved the format pointer in that image, read the format string, and checked that the
  register holding the target is vararg #k and that the k-th conversion of that format is `%s`:
  304/304 pass, 0 failures.
- `const char *` parameters by prototype: `InternalScopedString::Append(a1)`, `PrintMemoryByte(a1,a4)`,
  `PrintAddressDescription(a2)`, `FlagParser::ParseString(a1)`, `internal_strcmp(a0)`,
  `internal_strncmp(a0)`, `internal_strncpy(a1 = src)`, `fstatat(a1 = path)`, `__lctrans(a0)`.
  I then tainted those parameters at each callee's entry: `Append` -> `internal_strlen` then a memcpy of
  that length; `PrintMemoryByte` a1 -> AppendF vararg #0, a4 -> vararg #4; `PrintAddressDescription` a2 ->
  `GlobalAddressDescription::Print(const char*)`; `ParseString` -> `lbu 0(a2)` at +0x5c/+0x74 only;
  strcmp/strncmp/strncpy/strlen -> `lbu 0(reg)` loops with `addi +1`; `__lctrans` -> tailcall
  `__lctrans_impl(a0)`. Every one stops at the first NUL.
- `Printf`'s own `%s` handler: in `VSNPrintf` (both images, identical offsets) the vararg string path is
  `+0x230 ld a5,0(s2)`, `+0x234 beqz` (null check), `+0x238 lbu a4,0(a5)`, `+0x23c beqz`, then the copy
  loops at +0x254 / +0x284 / +0x2bc, each `lbu; addi ptr,ptr,1; beqz/bnez` - NUL-stopped (and additionally
  precision-stopped).
- Two apparent uses that are not uses, both confirmed by reading the callee: `a6` live at
  `StaticSpinMutex::LockSlow` and `ReportFile::ReopenIfNecessary` (one-argument methods, `a6` is not an
  argument register) - the record says the same; and a leftover table base in `a4` at
  `Allocator::Deallocate +0x230 jal ReportNewDeleteTypeMismatch` - that callee takes 4 arguments
  (`...EmmmPN11__sanitizer18BufferedStackTraceE`) and never reads `a6`/`a4`, so nothing escapes.

Returned pointers (9 CSTR rows) traced to their callers in both images, with identical results:
`Decorator::ShadowByte` -> `PrintMemoryByte+0x44` -> `AppendF` vararg #1 `%s`;
`__asan_default_suppressions` -> `InitializeSuppressions+0x50` -> `SuppressionContext::Parse(a1)`
(byte loop); `__lsan_default_options` / `__ubsan_default_options` -> `InitializeFlags +0xcc8 / +0xcb4`
-> `FlagParser::ParseString(a1)`. The one `jr` (ShadowByte +0x2c, the jump-table dispatch) lands on tails
that return the pointer, which is the same path.

### 4. CSTR-ESCAPE: the primary settlement, per row (10/10)

My taint found exactly the escapes the record names, at the same pcs, in both images:

| row | escape I measured | record |
|---|---|---|
| `__asan::InitializeFlags +0x104` | spill/reload resolved; `jal FlagParser::ParseString` at +0xc9c with the pointer in a1; remaining store `sd ..,104(s3)` at +0x220 | same |
| `CommonFlags::SetDefaults +0x48` | `sd a1,24(a0)` +0x94, `sd a1,200(a0)` +0xd8, `sd a1,208(a0)` +0xdc | same |
| `RegisterCommonFlags +0x1218` | `sd a1,24(a2)` +0x1228 and +0x1274 | same |
| `__lsan::Flags::SetDefaults +0xc` | `sd a1,32(a0)` +0x1c | same |
| `__ubsan::Flags::SetDefaults +0x4` | `sd a1,8(a0)` +0xc | same |
| `__nl_langinfo_l +0x5c`, `+0xf8` | return at +0x118 (and `lbu 0(a0)` at +0x100, tailcall `__lctrans(a0)` at +0x114) | same |
| `__tm_to_tzname +0x74` | return at +0xa4 | same |
| `__strftime_fmt_1 +0x530`, `+0x54c` | return at +0x614 | same |

Readers across the escape, read in the images:

- `FlagParser::ParseString` reads the string only with `lbu 0(a2)` (+0x5c, +0x74) and `internal_strlen`/
  `internal_strcmp`, all NUL-stopped (checked above).
- `__strftime_fmt_1` returns only to `__strftime_l` and `strftime_l` (I enumerated the direct callers of
  each function in both images). In `__strftime_l` the returned pointer is read at `+0x1cc lbu 0(a1)`,
  `+0x1e4 / +0x208 lbu 1(a1)` and the digit loop `+0x23c lbu 0(a3); addi a4,a4,-0x30; addi a3,a3,1;
  bltu a4,s7` - a NUL byte gives `0-0x30` unsigned, which fails `bltu`, so the walk stops on the NUL.
  Byte-identical code at the same offsets in X and Y.
- The length that travels with the empty string is 0: at `__strftime_fmt_1 +0x528` and `+0x544` the code
  does `sd zero,0(s0)` (`*l = 0`) immediately before the `auipc/addi` pair at +0x52c/+0x530 and
  +0x548/+0x54c that materialises the pointer, so `__strftime_l`'s `memcpy` copies 0 bytes.
- Target first byte: `00` in both images at X `0x13e67` / Y `0x13e96`, both in `.rodata`.
- SUPPORT window re-measured by me: the equal run from the target is exactly **4241 bytes** in both
  images, first mismatch at X `0x14ef8` / Y `0x14f27`. Matches the record; it is support only.

### 5. TABLE rows: entry by entry as symbol + offset, and the guard (14 rows, 513 entries)

For each TABLE row I read the entries myself (rel4: `table + int32(entry)`; abs8: the stored address),
resolved each target to a covering `.symtab` symbol + offset in its own image, and compared:
**513/513 entries resolve to the same symbol+offset in X and Y, none unnamed**, and every entry matches
the corresponding `ENTRY` row (raw bytes, target address, name+offset) in `ACCEPTANCES.tsv`. Extents
equal entries x width for all 14 rows.

Guard bounds found independently (same in both images): AddressDescription::Print K=4 (+0x8) -> 5;
ErrorGeneric K=81 (+0x218) -> 82; ShadowByte K=82 (+0x8) -> 83; ErrorDescription::Print K=24 -> 25;
force_interface_symbols K=51 -> 52; GetHandleSignalMode K=7 -> 8; VSNPrintf K=32 (+0x1b4) -> 33;
parseCIE K=46 (+0x258) -> 47; parseFDEInstructions K=47 (+0x134) -> 48; getEncodedP K=12 -> 13 and K=5 -> 6;
getTableEntrySize K=11 -> 12; sysconf K=12 (+0xd0) -> 13; `__strftime_fmt_1` K=85 (+0x34) -> 86.
Every count the record uses equals K+1, so no entry beyond the guard is left uncompared. The one jtcheck
`target differs 1` row (parseCIE +0x23c) is the guard-after-the-auipc case; its 47 entries are all the
same symbol+offset in both images.

### 6. INDEXED rows (7) and the planted De Bruijn control

Each De Bruijn row's access is, in both images, `srli r,*,0x3a` (58) -> `add` -> `lbu 0(r)`, at exactly the
offsets the row cites, so index 0..63 and 1 byte per entry: extent 64 bytes. The 64 bytes are
byte-identical in X and Y for all six rows and equal the row's recorded hex.
`OpenFile +0x60`: `addi a1,zero,2` (+0x50), `bltu` (+0x54), `slli s1,s1,2` (+0x58), `add` (+0x64),
`lw 0(a1)` (+0x68) -> 3 entries x 4 bytes = 12 bytes, `000000004102000042000000` in both. It is an
integer mode table, not a string.
The table base never leaves the function: the only candidate escapes were dead registers at calls whose
callees do not take them (checked above).

Planted control: in GRANT_B_TWIN, vaddr `0x10432` = file offset `0x432` = index 10 of the table at
`0x10428`, byte `0e`. `planted/planted.cmp` line 4 (`grantB-U-debruijn.elf: 1075 17 16`) is byte 1075
(1-based) = `0x432`, octal 17 = `0x0f` planted against 16 = `0x0e` original - exactly the record's plant,
and `planted.sha256` gives `780f7b2d2d3a`, the sha in the header of `ctl-settle-debruijn-planted.tsv`,
which reports `DIFFERS` on that row while `ctl-settle-debruijn-untouched.tsv` reports `SETTLED-EQUAL`.
I also re-derived the other two plants from the image: `___interceptor_malloc+0x130` (file `0x421e0`,
word `0x98dde0ef`) is `jal __asan::asan_malloc` (0x31b6c), re-pointed to `__sanitizer_get_allocated_begin`
(0x32eb8), and `__intscan+0x4c8` (file `0x850cc`, word `0x79858a93`) is the `addi` to `table`; both
`planted.cmp` byte lists (offsets and octal values) match those words exactly, and both controls report
the planted target difference.

### 7. RELSTR, INITIALIZER, NOT-PCREL

- `SignalContext::Describe +0x1c`: 8 rel4 entries (guard K=7 at +0x10). Each entry's string, read to the
  NUL in its own image: ILL, TRAP, ABRT, BUS, FPE, UNKNOWN SIGNAL, UNKNOWN SIGNAL, SEGV - identical in X
  and Y and identical to the `ENTRY` rows.
- `__synccall +0x54`: the memcpy is `addi a1,a1,lo` (+0x54), `addi a2,zero,0x98` (+0x58) = 152 bytes,
  `jal` memcpy (+0x5c). Word 0 of the blob is `handler+0x0` in both images (X 0x94774, Y 0x9945c); the
  other 144 bytes are byte-identical.
- The 3 NOT-PCREL words: I built the function CFG and walked backwards from each word over every
  predecessor path, collecting the reaching definitions of the base register.
  `CheckForLeaksCallback +0x484` and `+0x48c` (base a3): `ld a3,0x140(sp)` at +0x800 and +0x824 only.
  `__sanitizer_dump_coverage +0x118` (base a0): `addi a0,s0,-1` at +0xf0 and `addi a0,a0,-1` at +0x118 only.
  No auipc on any path in either image, so the words are not pc-relative; their raw 4 bytes are equal
  (`93851600`, `93963600`, `1305f5ff` on disk = the words `00168593`, `00369693`, `fff50513`).

### 8. Completeness: no target pair dropped

`paircl-malloc-grant.out` prints 67 "other" rows whose `target-diff` counts sum to **178**; per function,
every kit count equals the number of ACCEPT rows for that function (65 printed names, two of them
truncated prefixes shared by two acceptance functions each, summed - 0 mismatches, 0 acceptance
functions absent from the kit's list). All 100 `(function, word)` pairs that survive the kit's printed
truncation have an acceptance row. `ACCEPTANCES.tsv` carries 178 ACCEPT rows over 67 functions, 67 ROW
lines, all `ROW SETTLED-EQUAL`, 0 DIFFERS. The by-name closure's 62 "other" names are a subset of
paircl's 65.

### 9. Kit verdict stated first and unchanged

`ACCEPTANCES.tsv` lines 2-3 are the kit verdict, before any settle row, and they are verbatim the lines in
the kit outputs:
closure `closure 784 functions (register-indirect call sites inside: 97) | EQUAL 200 |
EQUAL-mod-pcrel(all targets equal) 522 | other 62 | members with value / full-bytes / C-string
acceptances 421` (`closure-grant.out`, same for all 4 roots) and paircl `closure 943 functions paired;
EQUAL 241; EQUAL-mod-pcrel (targets paired) 635; other 67; pairing conflicts 0`
(`paircl-malloc-grant.out`). `roots.tsv` shows EQUAL / EQUAL-mod-pcrel 3 pcrel, real 0, target-differ 0 on
all 4 roots against grant and against identity. The one paraphrase that is not the kit's own number is the
jtcheck sentence listed above.

`dupcheck.tsv`'s duplicate claim checks out against my own symbol table counts: `_ZN6__asanL11MemToShadowEm`
5 entries in each image, `dummy` 5 in each.

## Observation for the record (no row affected)

The empty string at X `0x13e67` / Y `0x13e96` has one consumer the record does not name. The
`CommonFlags` field at +24, which `CommonFlags::SetDefaults +0x94` sets to it, is loaded in
`StackTraceTextPrinter::ProcessAddressFrames +0xbc` and `ReportErrorSummary +0xc4` (both images,
reached through the `.got` cell that holds `__sanitizer::common_flags_dont_use`) and passed in `a7` to the
virtual frame renderer (`ld t1,0(a1); jalr t1`). That is a `const char *` format argument and the target's
first byte is the NUL in both images, so it reads 1 byte, but the row's settlement text names only
`FlagParser::ParseString` and `Printf`'s `%s`. Adding this consumer would make the row's reader list
complete. I checked every other reader of the escaped fields the same way: fields +200 and +208 of
`common_flags_dont_use` and +104 of `asan_flags_dont_use_directly` have no other reader in these images
except `InitializeSuppressions +0x40` -> `SuppressionContext::ParseFromFile(a1)`, a C-string parameter.

## Scripts

My own, written for this review (kept with the review, not committed): `elfx.py` (ELF64 reader, symtab with
STT_FILE scope, vaddr->file mapping, RISC-V decode), `taint.py` (CFG may-taint), `chk1_bytes.py`,
`chk2_readers.py`, `chk4_uses.py`, `chk5_fmt.py`, `chk6_callee.py`, `chk7_vsnprintf.py`, `chk8_ret.py`,
`chk9_fields.py`, `chk10_got.py`, `chk11_tables.py`, `chk12_guard.py`, `chk13_indexed.py`,
`chk14_rel_init.py`, `chk15_notpcrel.py`. `chk16_coverage.py` is an abandoned attempt to re-derive the
kit's "other" set from scratch; it re-implements too little of `strictcmp2`'s rules to be evidence, and the
completeness check in section 8 replaces it.
