# WIRE-B-ALLOC bytecmp record: fuzz_wire image B malloc / free chain against fuzz_grant image B

Read-only on every input. Version of record: **cmpkit 4bbd3a74be89** (strictcmp2 the one compare; closure_strict2 by
name; paircl against the stripped grant pin; jtcheck 824905e26211; drvcmp twins). Earlier versions of record are kept
unchanged in `earlier/`: va88c2822a0f2/, v9cbc3553c09e/, each with its own `tools/`, outputs, run.sh
and RECORD.md. `./run.sh` repeats every measurement (two full runs gave byte-identical outputs). The committed slice
is `commit/` plus this file (section "The committed slice"); the file names below are those in `commit/`.

**Verdict (cmpkit 4bbd3a74be89): SAME CODE up to relocation. fuzz_wire B's malloc / free interceptor chain is equal to fuzz_grant B's (pinned fde52226dc48), the same donor as uci B. The kit reports 62 by-name "other" rows and 67 paircl "other" rows (union 67, same across the 4 roots): all 67 settle to equal under the criterion below. All 178 target pairs are settled by a NAMED READER and the extent it reads: 168 where the reader is in the traced function, 10 where the pointer escapes (CSTR-ESCAPE: every use is measured -- the decoded escape stores, spills and returns, the direct readers, every load of each field the pointer is stored into found by a whole-image scan, and the caller words of each return -- and each reader reads it only as a C string, to the NUL; the equal window at the target is supporting evidence only). 0 DIFFERS, 0 unmeasured. The 3 planted controls were caught; the De Bruijn settlement control was caught.**

## Criterion

**Settled by the extent a NAMED reader can read; if the pointer escapes, name the reader, or give a measured equal
window.** For every target pair the kit calls "other" (`strictcmp2.tcmp` reports it with no name on either side, so
the pair cannot settle by name), one acceptance row names an instruction that reads the target and the extent that
reader covers; the X and Y bytes of exactly that extent are compared.

Classes (`commit/ACCEPTANCES.tsv`, column `class`):
- **TABLE** -- the kit's `jtcheck.table` reads a jump table (each entry a function-relative offset) or a pointer
  table (each entry the same named symbol+offset). Entry count from a measured guard. One `ENTRY` row per entry.
- **INDEXED** -- every use of the address is `add rB, rT, rS` followed by a load `l* rD, off(rB)` of width w in the
  same block, where rS is `srli *, 58` (index 0..63), `andi *, M` (index 0..M), or `slli rI, s` with rI guarded by
  `bltu rK, rI` / `bgeu rI, rK`, rK = `addi rK, zero, K`. Extent = bytes from off to the last index's entry end.
- **CSTR** -- every reader of the address reads it as a C string: a `const char *` parameter of the callee (its
  mangled name, or its C prototype -- table PARAMS in settle.py), a `%s` argument of a printf-like callee (every
  format reaching the call), an `lb`/`lbu` inside the string, a pointer compare (no read), a stack spill and its
  reloads, or a return value whose callers do one of these (2 levels). Extent = to and including the first NUL.
- **RELSTR** -- a relative table of string pointers; each entry's string to its NUL. One `ENTRY` row per entry.
- **INITIALIZER** -- the kit's `jtcheck.blob` for a memcpy-copied constant initializer. One `ENTRY` row per word.
- **NOT-PCREL** -- an I/S-type word on an auipc register the kit flags "unmeasured" because, in address order, the
  register's last writer is an auipc. Measured on the CFG: no auipc reaches the register on any path to the word, so
  the word is not pc-relative. Compared as the 4 raw bytes.
- **CSTR-ESCAPE** -- the pointer escapes the traced function: it is stored into an object field, spilled, or
  returned. Every use is measured (`tools/escape.py`, per row in `commit/settle.tsv`):
  - ESCAPE: each use, decoded from the image (for example `sd t5,104(s3)` at +0x220), the same in X and Y;
  - DIRECT READERS: the CSTR rule, applied to the uses inside the traced function (a spill and its reloads included);
  - FIELD READS: for a store into an object field, `tools/objscan.py` scans the whole image for every load of that
    field (`commit/fieldscan.tsv`): through the global object, every copy of it (CopyFrom / memcpy; a stack copy only
    within its measured lifetime, because stack slots are shared by objects of disjoint scopes), and every
    flag-handler object that holds the field's address (through that class's vtable methods). Each load is followed
    to its readers with the CSTR rule; a register-indirect call is resolved through the vtables of the object it is
    made on. The scan also lists every data word that points into the object. Required: 0 unresolved rows, and the
    same reads in X and Y;
  - RETURN: for a returned pointer, the caller path and every caller word that reads it, each decoded in X and Y;
  - SUPPORT: the equal window at the target (4241 bytes here); a second check, not the bound.
  The target's first byte is the NUL in both images, and every measured reader reads the pointer only as a C string.

## Tools (`commit/tools/`, `commit/tools.sha256`, `commit/tools/DIFFS.md`)

Every script these records ran is committed in `tools/` and runs from the slice: its inputs are arguments, and
`run.sh` takes the image paths from `env.sh` (variables `UNIT X_S X_U GR_S GR_U ID_S ID_U`; env.sh not committed).
`tools/DIFFS.md` records each copy's sha256, the original's sha256 and source, and the unified diff.

The kit is cmpkit 4bbd3a74be89 (sha256 of SHA256SUMS; one tree, one SHA256SUMS). Six of its seven files are host-path
scrubbed at the writer; one (paircl.py) is byte-identical to the kit. The scrub removes host paths and names; the
code logic is unchanged. drvcmp's `BC_SHA` and jtcheck's `strictcmp2.py` / `drvcmp.py` sha256 constants were updated
to pin the scrubbed copies instead of the originals (block checks over `repin_check` lines 31-80 and 209-231 still
pass, so drvcmp still rejects any logic change).

Alongside the kit, `tools/` holds the per-record helpers:
- `settle.py` -- per-target settlement; loads the kit's `strictcmp2` and `jtcheck` and uses their functions only.
- `escape.py` -- the second settlement pass for an escaping empty-string pointer (above).
- `objscan.py` -- the whole-image field scan the escape pass uses (above); writes `fieldscan.tsv`.
- `dupcheck.py` -- duplicate-name check for every function compared by name.
- `otherrows.py` -- the function-name list the kit reports as "other".
- `mkaccept.py` -- writes `ACCEPTANCES.tsv` (kit verdict first, settle rows unchanged).
- `syms.py` -- symbol lookup.
- `scrub_out.py` -- the one writer of `commit/`.
- `mkdiffs.py` -- the writer of `tools/DIFFS.md`.

## Images (`commit/images.sha256`, `commit/twins.out`)

Grant B's addresses are the ones the released donor names: grant `lib/B/YF0l.v:11-12` @ 4f87de75d67 gives
`pc_malloc := 0x530b0; pc_wrap_malloc := 0x52edc` and `pc_free := 0x52ee0; pc_wrap_free := 0x52ed8`. Wire B's
roots, by its own symbol table (`commit/roots-syms.out`): 0x5226c / 0x52098 and 0x5209c / 0x52094.

| token | file | sha256 | pin / twin check |
|---|---|---|---|
| `WIRE_B_PIN` | `fuzz_wire.asan-ubsan` | `af4534831a4528320c7dc74ca3f64bb96e8232ed2e313f01126d10879f3417d6` | index/binaries.tsv:7525 and `projects/reac-repacer/fuzz_wire/harness.yaml:64` @ f47e2a8927b9 |
| `WIRE_B_TWIN` | `fuzz_wire.asan-ubsan`, unstripped | `51eb4bef24252e4df6e11baa89f653d20d74e38ae684f61bc94f4fb339ac97c3` | PT_LOAD equal to the pin (`twins.out`): 25 bytes differ, all in the ELF header / `.note.gnu.build-id` |
| `GRANT_B_PIN` | `fuzz_grant.asan-ubsan` | `fde52226dc48de254681156061de9263409c123ca0a0d6c5010ded4e17f602df` | index/binaries.tsv:5591 @ 4f87de75d67 (released) and @ f47e2a8927b9 |
| `GRANT_B_TWIN` | `fuzz_grant.asan-ubsan`, unstripped | `5a5ee7c02b4e2a1d1653dc0c256182c9b65c33dde3a7ddc98b9de2afffe7a417` | PT_LOAD equal to the pin |
| `IDENT_B_PIN` (control) | `fuzz_identity.asan-ubsan` | `baf1a4d065e02f55521d39f05d8c8d9ed763a0ef798c70cc3eabe5816ffb3f66` | index/binaries.tsv:5595 @ f47e2a8927b9 |
| `IDENT_B_TWIN` (control) | `fuzz_identity.asan-ubsan`, unstripped | `43b44d50be8a5e68f626662181c9cc17c0e0fef138e55f3c8bab371987a9c064` | PT_LOAD equal to the pin |
| `GRANT_B_{PIN,TWIN}_PLANTED_{CALL,RODATA}` and `GRANT_B_TWIN_PLANTED_DEBRUIJN` | planted copies | see "Controls" | written by `run.sh`; not committed |

## Kit verdict (unchanged, as the kit printed it)

**strictcmp2.py cmp** on the 4 roots (`commit/roots.tsv`): `__interceptor_trampoline_malloc` EQUAL 0; `___interceptor_malloc` EQUAL-mod-pcrel 3 pcrel; `__interceptor_trampoline_free` EQUAL 0; `___interceptor_free` EQUAL-mod-pcrel 3 pcrel. Real 0 and target-differ 0 everywhere, both against grant B and against the identity B control.

**closure_strict2.py** from `___interceptor_malloc` (`commit/closure-grant.out`): closure 784 functions
(register-indirect call sites inside: 97), EQUAL 200, EQUAL-mod-pcrel-with-all-targets-equal 522, **other 62**. The
same for the other 3 roots.

**paircl.py** from `___interceptor_malloc` against the grant pin (`commit/paircl-malloc-grant.out`): 943 functions
paired, EQUAL 241, EQUAL-mod-pcrel 635, **other 67**, 0 pairing conflicts. The same for the other 3 roots.

**jtcheck.py** on the 16 members (`commit/jtcheck-members.txt`, `commit/jtcheck-grant.out`), in the kit's own words: 11 settled, 1 `target differs` (parseCIE: 1 target, at +0x23c) and 4 with `target unmeasured` (Decorator::ShadowByte 6, SignalContext::Describe 1, `__strftime_fmt_1` 2, ErrorAllocTypeMismatch::Print 4); 0 unpaired words in all 16. The other 5 are settled in `commit/ACCEPTANCES.tsv`: parseCIE +0x23c by TABLE (jtcheck's `bound()` cannot see the dispatch after the auipc; settle.py takes the guard of the dispatch, 47 entries, all equal); ShadowByte by 7 CSTR rows and 1 TABLE row; SignalContext::Describe +0x1c by RELSTR; `__strftime_fmt_1` +0x530 / +0x54c by CSTR-ESCAPE (its jump table at +0x44 by TABLE); ErrorAllocTypeMismatch::Print +0x38, +0x44, +0xb8, +0xc4 by CSTR.

## Acceptances (`commit/ACCEPTANCES.tsv`)

Union of the kit's two "other" rows: **67 functions**, **178 target pairs** (= paircl's own target-diff total; the
full list is read from `strictcmp2.tcmp` directly, not from the kit's printed first 2 lines).

| class | target pairs | verdict | notes |
|---|---|---|---|
| CSTR | 142 | SETTLED-EQUAL | the extent to the first NUL; every reader is a named `const char *` parameter, a `%s` vararg (format verified in X and Y), an lb/lbu inside the string, a pointer compare, a stack spill-reload, or a return value with named callers |
| TABLE | 14 | SETTLED-EQUAL | kit `jtcheck.table`; one ENTRY row per entry resolves to the same function-relative offset or named symbol+offset in both images |
| INDEXED | 7 | SETTLED-EQUAL | 6 De Bruijn ctz tables (64 bytes, srli 58 + lbu, extent exact); OpenFile mode table (3 x 4 bytes, bltu guard, slli 2 + lw) -- **not** a CSTR / empty-string pointer |
| RELSTR | 1 | SETTLED-EQUAL | SignalContext::Describe: 8-entry rel4 table of string pointers; each string equal to its NUL |
| INITIALIZER | 1 | SETTLED-EQUAL | __synccall: 152-byte memcpy source, each 8-byte word by qname_ok |
| NOT-PCREL | 3 | SETTLED-EQUAL | lsan I/S-type words the kit flagged "unmeasured" by its address-order heuristic; no auipc reaches the base register on any CFG path, so the word is not pc-relative; raw 4 bytes equal |
| CSTR-ESCAPE | 10 | SETTLED-EQUAL | the 8 rows whose target is the byte-equal empty string (1 NUL byte in both) and whose pointer escapes the traced function; every use measured, per row in `commit/settle.tsv`. **Field stores** (decoded, the same in X and Y): CommonFlags::SetDefaults `sd a4,24(a0)` +0x94, `sd a4,200(a0)` +0xd8, `sd a4,208(a0)` +0xdc; RegisterCommonFlags `sd s2,24(a2)` +0x1228 and +0x1274; InitializeFlags `sd t5,104(s3)` +0x220 (and the spill `sd t5,288(sp)` +0x108, reloaded by `ld a1,288(sp)` +0xc94 into a1 of FlagParser::ParseString(const char *) at +0xc9c); lsan Flags::SetDefaults `sd a3,32(a0)` +0x1c; ubsan Flags::SetDefaults `sd a1,8(a0)` +0xc. **Field reads, whole-image scan** (`commit/fieldscan.tsv`: 0 unresolved, the same 12 reads in X and Y): CommonFlags +24 -> FlagHandler<const char*>::Format +0x14 (`%s` of internal_snprintf), and ReportErrorSummary +0xc4 and StackTraceTextPrinter::ProcessAddressFrames +0xbc, which pass it in a7, a `const char *` parameter, to the virtual RenderFrame of the Markup and the Formatted stack-trace printer; CommonFlags +200 and +208 and lsan Flags +32 -> Format only; asan Flags +104 and ubsan Flags +8 -> Format and InitializeSuppressions +0x40 (a1 of SuppressionContext::ParseFromFile(const char *)); the heap FlagHandlerInclude +24 -> FlagHandlerInclude::Format +0x10 (`%s`). The handlers' Parse methods and the setters only write these fields. The data words that point into the objects are the 4 `.got` cells of the object bases (followed) and 6 `.data.rel.ro` words at CommonFlags +88 .. +108, none at a scanned field. **Returns** (__nl_langinfo_l, __strftime_fmt_1, __tm_to_tzname) -> `__strftime_l`: a null test at +0x1c0, `lbu` of byte 0 at +0x1cc; the `lbu 1` at +0x1e4 / +0x208 runs only when byte 0 is '+', '-' or '0'; the digit loop at +0x23c stops on the NUL; the memcpy at +0xa0 copies the length returned with the pointer, 0 here (`sd zero,0(s0)` at `__strftime_fmt_1` +0x528 / +0x544, or strlen at +0x514); each word decoded in X and Y. **Support: equal window 4241 bytes**. |

**All 178 pairs: SETTLED-EQUAL. 0 DIFFERS. 0 unmeasured. All 67 rows: ROW SETTLED-EQUAL.** No row stays "other"; the
`same code up to relocation` claim is for the whole chain, no exceptions.

**Fresh review (`REVIEW.md`).** `REVIEW.md` is the fresh review of these fuzz_wire acceptances (its own ELF reader and
RISC-V decoder, capstone for display; APPROVE, 0 rows rejected, 0 doubtful). It found text defects only, and they
are fixed: the jtcheck sentence (it now gives the kit's own numbers, 11 settled, 1 differs, 4 unmeasured, and where the other 5 are settled) and one reader of CommonFlags +24 that the row text did not name (the virtual frame renderer, a7; the whole-image scan now lists every reader). The fresh review of the EGRESS-B-ALLOC record found further text defects of the same kind; they are fixed
here too, as in all three records. OpenFile is INDEXED (12 bytes) here, not an empty-string CSTR.

## The 8 escaping empty strings

Measured in this record's own images, the same way as in the UCI-B-ALLOC record: `commit/fieldscan.tsv`
(`objscan.py`) and the CSTR-ESCAPE rows of `commit/settle.tsv` (`escape.py`). The escape stores, the 12 field reads
and their readers, the data words that point into the objects, and the decoded return-path words are the same in X
and Y, and the same as in the uci record; 0 unresolved. The target byte is `00` in both images, and the support
window at the target is 4241 bytes in both.

## Duplicate names (`commit/dupcheck.tsv`)

893 names are compared by name in this record. 5 have more than one `.symtab` entry in X or in Y:
`_ZN6__asanL11MemToShadowEm` in 4 asan compilation units (5 copies in each image), and `dummy{__stdio_close.c}` (5
copies each). For each, the Y copy `closure_strict2` picks by qualified name (name+STT_FILE) is the Y copy the code
actually calls (the jal target at the same word in Y's counterpart of an X caller). By-address verdict equals the
by-name verdict in every case: MemToShadow 4 x EQUAL-mod-pcrel, dummy EQUAL. **No ambiguous-name row changes verdict.**

## Controls

**(a) Known-equal, identity B** (`commit/closure-identity.out`, `commit/ctl-jtcheck-identity.out`). The 4
roots are EQUAL / EQUAL-mod-pcrel. The by-name closure gives the same 62 "other" rows as against grant (every
EQUAL-mod-pcrel count differs because the two donors sit at different addresses, but the row set is identical). All
jtcheck rows match.

**(b) Planted changes** (`commit/planted/planted.sha256`, `commit/planted/planted.cmp`). Each plant is a one-word
change in a copy of grant B. Each must be caught; each is.

| plant | word changed | caught by |
|---|---|---|
| call: `___interceptor_malloc`+0x130 re-pointed from `__asan::asan_malloc` to `__sanitizer_get_allocated_begin` | 0x530b0+0x130 (file 0x421e0): `98dde0ef` -> `cd9df0ef` | strictcmp2 (target-differ 1 at +0x130); closure_strict2 (other 62 -> 63); paircl (named target differs; new "other" row); jtcheck not applicable (`jal` is not a lo12 pair) |
| rodata: `__intscan`+0x4c8 re-pointed from `table` to `all_mask` | 0x95c04+0x4c8 (file 0x850cc): `79858a93` -> `46058a93` | strictcmp2 on `__intscan` (target-differ 1 at +0x4c8); jtcheck (`DIFF +0x4c8 table+0x0 \| all_mask+0x0`); closure_strict2 (other 62 -> 63); paircl (named target differs; new "other" row) |
| settlement control (debruijn): one byte of the 64-byte De Bruijn ctz table that `Allocator::Allocate` reads at +0xdc | vaddr 0x10432 (file 0x432): `0e` -> `0f` | settle.py's INDEXED class on `Allocator::Allocate`: planted copy **DIFFERS** at that byte; untouched GRANT_B_TWIN **SETTLED-EQUAL** |

**(c) The kit's own controls** (run on this box on 2026-10-30; their outputs are not part of this slice).
- `controls/negctl.py`: output byte-identical to the kit's registered `repin-negctl.out` (natural FA:DP 11 target
  differences, baseline FA:DA 0, planted main+0x50 caught, under the old and the kit target pass).
- `controls/suite.py` (23 plants, every applicable old and kit tool, run as registered: `SUITE_EXTRA_JT` for jtcheck
  824905e26211, and the cross-check jtcheck_strict2 cf27b4d8093a beside the kit files): all 291 cells match the
  registered `SUMMARY.tsv` in tool sha, version, baseline verdict and planted verdict. The 134 kit cells are 132
  caught and 2 noteq-both (P9: reported before and after the plant); 0 EQUAL.
- One path constant in a copy of suite.py was changed: its old-tool columns (paircl a88c2822a0f2, closure
  b50998fb3bd3, jtcheck f95cc8e243d1) now read this record's archived copies in `earlier/`, where those tools moved.

## Limits

- **Code only.** Register-indirect call sites (97 in each root's by-name closure) take their targets from data, and
  paircl's / strictcmp2's target rule skips `.got` / `.data` / `.data.rel.ro` cells unless a settlement class gives
  them a reader with an extent. Neither is a code comparison.
- **Not a proof of context.** "Same code" does not say that grant's released walks prove the chain in fuzz_wire B's call
  contexts.

## The committed slice

`commit/` holds everything committed except this file, `REVIEW.md` and MANIFEST.md. Its last writer is
`tools/scrub_out.py`, the last step of `run.sh`:
- In the raw outputs, each image path becomes the token that `images.sha256` defines by sha256 and index line.
- Tool scripts and `run.sh` are copied byte for byte, with their modes.
- scrub_out refuses its own output (exit 1, `commit/` left as it was) if any file or file name in it still holds a
  host path, an internal branch prefix, a worker name or the tool registry's branch name.

Earlier versions of record live in `earlier/` (va88c2822a0f2/, v9cbc3553c09e/), each with its own
tools, outputs, run.sh and RECORD.md. They are archived unchanged and are not shipped with this slice; scrub_out
skips the `earlier/` directory.

**Checks (2026-10-30, after the move to cmpkit 4bbd3a74be89):**
- **Scrubbed vs pristine kit:** `strictcmp2 cmp`, `closure_strict2`, `paircl`, `jtcheck` outputs are byte-identical
  between the scrubbed and pristine kit files (measured on uci; the kit files are the same bytes here) (jtcheck sha-checks the scrubbed copies via its updated
  constants; drvcmp block checks over `repin_check` lines 31-80 and 209-231 still pass).
- **Only paths rewritten:** every raw output, with each image path replaced by its token and each tool path by the
  tool's name, equals its `commit/` copy byte for byte (29 raw outputs; `ACCEPTANCES.tsv` names the token
  `GRANT_B_TWIN` in its own header text, so only this direction is a byte identity).
- **Runnable from the slice:** `./run.sh`, run from a copy of `commit/` with an `env.sh` beside it, reproduces
  `commit/` exactly.
- **Scanner of record:** run over this slice at its repository path (`commit/` plus this file and `REVIEW.md`), it
  reported 0 files with an uncleared flag-tier hit.
