# UCI-B-ALLOC bytecmp record: fuzz_uci image B malloc / free chain against fuzz_grant image B

Read-only on every input. Version of record: **cmpkit 4bbd3a74be89** (strictcmp2 the one compare; closure_strict2 by
name; paircl against the stripped grant pin; jtcheck 824905e26211; drvcmp twins). Earlier versions of record are kept
unchanged in `earlier/`: va88c2822a0f2/, v9cbc3553c09e/, v7daa0e2a03d9/, each with its own `tools/`, outputs, run.sh
and RECORD.md. `./run.sh` repeats every measurement (two full runs gave byte-identical outputs). The committed slice
is `commit/` plus this file (section "The committed slice"); the file names below are those in `commit/`.

**Verdict (cmpkit 4bbd3a74be89): SAME CODE up to relocation. fuzz_uci B's malloc / free interceptor chain is equal to fuzz_grant B's (pinned fde52226dc48), the donor of uci B's lib/B/YF0w.v / YF0q.v. The kit reports 62 by-name "other" rows and 67 paircl "other" rows (union 67, same across the 4 roots): all 67 settle to equal under the criterion below. All 178 target pairs are settled by a NAMED READER and the extent it reads: 168 where the reader is in the traced function, 10 where the pointer escapes (CSTR-ESCAPE: the reader is named across the escape and reads only to the NUL; a measured equal window at the target is supporting evidence only). 0 DIFFERS, 0 unmeasured. The 3 planted controls were caught; the De Bruijn settlement control was caught.**

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
- **CSTR-ESCAPE** -- the pointer escapes the traced function (stored into a `const char *` field, or returned to
  another function). PRIMARY settlement: the escape is traced to the reader that consumes it, and that reader reads
  only to the first NUL. Per row: the store or return pc, the field or return path, the reader function and pc,
  and why it reads only to the NUL (internal_strlen / internal_strcmp in FlagParser::ParseString; Printf's `%s`
  handler; `__strftime_l`'s format walker). The target's first byte is the NUL, equal in both images. SUPPORT (a
  second check, not the settlement): the equal window measured at the target in both images (4241 bytes here); the
  window does not bound what a reader may read, the reader's own NUL stop does.

## Tools (`commit/tools/`, `commit/tools.sha256`, `commit/tools/DIFFS.md`)

Every script these records ran is committed in `tools/` and runs from the slice: its inputs are arguments, and
`run.sh` takes the image paths from `env.sh` (variables `UCI_S UCI_U GR_S GR_U ID_S ID_U`; env.sh not committed).
`tools/DIFFS.md` records each copy's sha256, the original's sha256 and source, and the unified diff.

The kit is cmpkit 4bbd3a74be89 (sha256 of SHA256SUMS; one tree, one SHA256SUMS). Six of its seven files are host-path
scrubbed at the writer; one (paircl.py) is byte-identical to the kit. The scrub removes host paths and names; the
code logic is unchanged. drvcmp's `BC_SHA` and jtcheck's `strictcmp2.py` / `drvcmp.py` sha256 constants were updated
to pin the scrubbed copies instead of the originals (block checks over `repin_check` lines 31-80 and 209-231 still
pass, so drvcmp still rejects any logic change).

Alongside the kit, `tools/` holds the per-record helpers:
- `settle.py` -- per-target settlement; loads the kit's `strictcmp2` and `jtcheck` and uses their functions only.
- `escape.py` -- the second settlement pass for an escaping empty-string pointer (above).
- `dupcheck.py` -- duplicate-name check for every function compared by name.
- `otherrows.py` -- the function-name list the kit reports as "other".
- `mkaccept.py` -- writes `ACCEPTANCES.tsv` (kit verdict first, settle rows unchanged).
- `syms.py` -- symbol lookup.
- `scrub_out.py` -- the one writer of `commit/`.
- `mkdiffs.py` -- the writer of `tools/DIFFS.md`.

## Images (`commit/images.sha256`, `commit/twins.out`)

Grant B's addresses are the ones the released donor names: grant `lib/B/YF0l.v:11-12` @ 4f87de75d67 gives
`pc_malloc := 0x530b0; pc_wrap_malloc := 0x52edc` and `pc_free := 0x52ee0; pc_wrap_free := 0x52ed8`. Uci's
`lib/B/YF0l.v:12-13` @ f47e2a8927b9 gives 0x5195c / 0x51788 and 0x5178c / 0x51784.

| token | file | sha256 | pin / twin check |
|---|---|---|---|
| `UCI_B_PIN` | `fuzz_uci.asan-ubsan` | `a1b86e424adde6f65d345459822690a6c21e9e606446b91b4ad25e9f3ef6e7fc` | index/binaries.tsv:7521 and `proofs/reac-repacer/fuzz_uci/provenance/PROVENANCE.yaml:83` @ f47e2a8927b9 |
| `UCI_B_TWIN` | `fuzz_uci.asan-ubsan`, unstripped | `8d07ffcf594874884207465cc34ff9f3b1062f21f6d9b3622e0771fa76490b16` | PT_LOAD equal to the pin (`twins.out`): 25 bytes differ, all in the ELF header / `.note.gnu.build-id` |
| `GRANT_B_PIN` | `fuzz_grant.asan-ubsan` | `fde52226dc48de254681156061de9263409c123ca0a0d6c5010ded4e17f602df` | index/binaries.tsv:5591 @ 4f87de75d67 (released) and @ f47e2a8927b9 |
| `GRANT_B_TWIN` | `fuzz_grant.asan-ubsan`, unstripped | `5a5ee7c02b4e2a1d1653dc0c256182c9b65c33dde3a7ddc98b9de2afffe7a417` | PT_LOAD equal to the pin |
| `IDENT_B_PIN` (control) | `fuzz_identity.asan-ubsan` | `baf1a4d065e02f55521d39f05d8c8d9ed763a0ef798c70cc3eabe5816ffb3f66` | index/binaries.tsv:5595 @ f47e2a8927b9 |
| `IDENT_B_TWIN` (control) | `fuzz_identity.asan-ubsan`, unstripped | `43b44d50be8a5e68f626662181c9cc17c0e0fef138e55f3c8bab371987a9c064` | PT_LOAD equal to the pin |
| `GRANT_B_{PIN,TWIN}_PLANTED_{CALL,RODATA}` and `GRANT_B_TWIN_PLANTED_DEBRUIJN` | planted copies | see "Controls" | written by `run.sh`; not committed |

## Kit verdict (unchanged, as the kit printed it)

**strictcmp2.py cmp** on the 4 roots (`commit/roots.tsv`): `__interceptor_trampoline_malloc` EQUAL 0; `___interceptor_malloc` EQUAL-mod-pcrel 3 pcrel; `__interceptor_trampoline_free` EQUAL 0; `___interceptor_free` EQUAL-mod-pcrel 3 pcrel. Real 0 and target-differ 0 everywhere, both against grant B and against the identity B control.

**closure_strict2.py** from `___interceptor_malloc` (`commit/closure-uci-grant.out`): closure 784 functions
(register-indirect call sites inside: 97), EQUAL 172, EQUAL-mod-pcrel-with-all-targets-equal 550, **other 62**. The
same for the other 3 roots.

**paircl.py** from `___interceptor_malloc` against the grant pin (`commit/paircl-malloc-grant.out`): 943 functions
paired, EQUAL 213, EQUAL-mod-pcrel 663, **other 67**, 0 pairing conflicts. The same for the other 3 roots.

**jtcheck.py** on the 16 members (`commit/jtcheck-members.txt`, `commit/jtcheck-uci-grant.out`): 15 settled; parseCIE
`target differs 1` at +0x23c (jtcheck's `bound()` heuristic cannot see the dispatch after the auipc; settle.py's
TABLE class resolves it against the guard of the dispatch, 47 entries, all equal).

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
| CSTR-ESCAPE | 10 | SETTLED-EQUAL | the 8 rows whose target is the byte-equal empty string (1 NUL byte in both) and whose pointer escapes the traced function. **Primary: the named reader, per row in `commit/settle.tsv`**: flag-store rows (CommonFlags::SetDefaults sd at +0x94/+0xd8/+0xdc, RegisterCommonFlags sd at +0x1228/+0x1274, InitializeFlags spill/reload then jal ParseString at +0xc9c plus sd at +0x220, lsan Flags sd at +0x1c, ubsan Flags sd at +0xc) -> FlagParser::ParseString (internal_strlen / internal_strcmp stop at the NUL) and Printf `%s` in PrintFlagDescriptions; return rows (__nl_langinfo_l, __strftime_fmt_1, __tm_to_tzname) -> `__strftime_l`'s format walker (lbu 0 at +0x1cc / +0x23c, stops on the NUL byte). **Support: equal window 4241 bytes** at the target in both images. |

**All 178 pairs: SETTLED-EQUAL. 0 DIFFERS. 0 unmeasured. All 67 rows: ROW SETTLED-EQUAL.** No row stays "other"; the
`same code up to relocation` claim is for the whole chain, no exceptions.

**Fresh review (`commit/REVIEW.md`).** r-decbox commissioned a fresh reviewer (independent ELF reader + own symtab
resolver + capstone RISC-V disassembler). It reproduced every ACCEPT verdict, resolved every ENTRY row from the
images, decoded every INDEXED guard, and tested whether a bound was load-bearing. Decision: APPROVE, 0 rows rejected.
Separately it confirmed OpenFile is INDEXED (12 bytes), not an empty-string CSTR.

## Duplicate names (`commit/dupcheck.tsv`)

893 names are compared by name in this record. 5 have more than one `.symtab` entry in X or in Y:
`_ZN6__asanL11MemToShadowEm` in 4 asan compilation units (5 copies in each image), and `dummy{__stdio_close.c}` (5
copies each). For each, the Y copy `closure_strict2` picks by qualified name (name+STT_FILE) is the Y copy the code
actually calls (the jal target at the same word in Y's counterpart of an X caller). By-address verdict equals the
by-name verdict in every case: MemToShadow 4 x EQUAL-mod-pcrel, dummy EQUAL. **No ambiguous-name row changes verdict.**

## Controls

**(a) Known-equal, identity B** (`commit/closure-uci-identity.out`, `commit/ctl-jtcheck-uci-identity.out`). The 4
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

## Limits

- **Code only.** Register-indirect call sites (97 in each root's by-name closure) take their targets from data, and
  paircl's / strictcmp2's target rule skips `.got` / `.data` / `.data.rel.ro` cells unless a settlement class gives
  them a reader with an extent. Neither is a code comparison.
- **Not a proof of context.** "Same code" does not say that grant's released walks prove the chain in uci B's call
  contexts.

## The committed slice

`commit/` holds everything committed except this file, `REVIEW.md` and MANIFEST.md. Its last writer is
`tools/scrub_out.py`, the last step of `run.sh`:
- In the raw outputs, each image path becomes the token that `images.sha256` defines by sha256 and index line.
- Tool scripts and `run.sh` are copied byte for byte, with their modes.
- scrub_out refuses its own output (exit 1, `commit/` left as it was) if any file or file name in it still holds a
  host path, an internal branch prefix, a worker name or the tool registry's branch name.

Earlier versions of record live in `earlier/` (va88c2822a0f2/, v9cbc3553c09e/, v7daa0e2a03d9/), each with its own
tools, outputs, run.sh and RECORD.md. They are archived unchanged and are not shipped with this slice; scrub_out
skips the `earlier/` directory.

**Checks (2026-10-30, after the move to cmpkit 4bbd3a74be89):**
- **Scrubbed vs pristine kit:** `strictcmp2 cmp`, `closure_strict2`, `paircl`, `jtcheck` outputs are byte-identical
  between the scrubbed and pristine kit files on uci (jtcheck sha-checks the scrubbed copies via its updated
  constants; drvcmp block checks over `repin_check` lines 31-80 and 209-231 still pass).
- **Only paths rewritten:** every raw output, with each image path replaced by its token and each tool path by the
  tool's name, equals its `commit/` copy byte for byte (29 raw outputs; `ACCEPTANCES.tsv` names the token
  `GRANT_B_TWIN` in its own header text, so only this direction is a byte identity).
- **Runnable from the slice:** `./run.sh`, run from a copy of `commit/` with an `env.sh` beside it, reproduces
  `commit/` exactly.
- **Scanner of record:** run over this slice at its repository path (`commit/` plus this file and `REVIEW.md`), it
  reported 0 files with an uncleared flag-tier hit.
