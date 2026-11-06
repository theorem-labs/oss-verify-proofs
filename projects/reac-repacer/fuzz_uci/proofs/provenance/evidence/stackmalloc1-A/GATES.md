# fuzz_uci image-A class-1 stack_malloc contract: gate record

The files: lib/A/Rt/AF0r.v, lib/A/Rt/AF0s.v and the shared lib/Reusable/YF0v.v (applied.txt), relocated from
fuzz_grant's released lib/A/Rt/AF0r.v, AF0s.v and lib/Reusable/YF0v.v (recipes 4f87de75d67) by `run.sh` (port_core
0e4e065eab9f, core-A's route): staged 3, kept 0, required.tsv empty, 0 override values, 2 / 2 patches, symbol gate PASS.
port_core's FAIL rows are core-A's known `rename-new-undeclared UciSyms` (its Record is in the start-up file
lib/A/AF0m.v, never staged) and three `data-symbol` review rows on the model constant FS_FROFF 0x109000 (METHOD.md);
its advisory cell gate `cellcheck` finds 0 file-backed cells in these files (nothing to check; their data cells are
checked by the build, section 5). So `apply-sm1.sh` copies by --apply's rule (nothing overwritten) and `header-sm1.py`
does the comments-only header step (code bytes unchanged; the 4 inherited lines of each file equal the donor's byte for
byte; day-level dates, host paths, agent / lane and cold branch names in comments: 0 before, 0 after).
`gates/run-gates.sh` runs every gate below with its controls; `gates/records-sm1.py` writes records/.

The statement, fixed by the consumer (lib/A/UciClose.v's Section hypothesis H_RT_STACK_MALLOC1 cites it):

    Corollary stack_malloc1_contract : forall B, AR_laws tfibsegs B -> UciSyms B -> astack_malloc_realizes tfibsegs B 1.

in `OssFuzzTheorems.Proofs.reac_repacer.fuzz_uci.lib.A.Rt.AF0s`: grant's AF0s.v:513 with GrantSyms renamed UciSyms, word
for word the image-B row's statement (lib/B/Rt/YF0s.v:516).

## 0. Bytecmp of every body the proofs step through (BYTECMP.md; records/bytecmp-*.out, records/sites-*.out)

**RESTATED (comparison kit 4bbd3a74be89):** the claim "13 bodies equal" of this section is RESTATED as: 12 of 13
kit-EQUAL; RegisterCommonFlags: 1 unnamed empty-string place at +0x1218 not certified by the kit (whole-region compare).
Settled by hand as an ACCEPTANCE (EQUAL as a C string; gates/settle-sm1.py, records/settle-sm1.out, reviewed in
records/settle-sm1-review.md): 13 of 13 equal after settlement, 1 by the empty-string measurement. The bytes the proof
reads of RegisterCommonFlags (fs_ranges at +0x358) are kit-EQUAL. The paragraphs below give the bytecmp.py runs, then
the kit's, then the settlement.

13 bodies (the code table's nine fuzz_uci rows by symbol and every callee of the class-1 code), 13 equal up to
relocation; fuzz_grant's __asan_stack_malloc_0 / _2 / _4 rows have no body in fuzz_uci. The tool is the image-B
record's fixed tool (51cfb939a547, sha256 f31bad62a6cb: a .got / .data.rel.ro cell by the symbol its value names, TLS
symbols skipped; an unnamed place by section, NUL string and a 64-byte window; zero-fill only beyond p_filesz) plus one
rule. That tool unchanged (`--no-addi0`) leaves TryAsanInitFromRtl's auipc pair to asan_inited as 2 DIFFERENT rows (the
donor's low half is an `addi s0, a0, 0`, printed `mv`); the added rule decides it SAME, changes nothing else, and
reproduces the image-B record line for line on the image-B twins. Re-run with the fixed data-place rules: no verdict
changed (13 bodies, 0 not equal, 249 rows SAME before and after); the .got cell at stack_malloc_1 +0x18 now reads as
the TLS index pair it holds (module id 1, offset -0x800, both images) instead of the zero byte the old reader made of
it. Six controls, each exit 1: an `or` planted for the `and` at FS_LOOP, the donor's own `jal` word left at the
GetCurrentThread call, and the donor's own `addi s0, a0, 0` left at uci's TryAsanInitFromRtl +0x10 each give exactly
one DIFFERENT row; the .got cell's module id planted 1 -> 2, the same cell pointed at __asan_stack_malloc_1, and one
byte planted in the window after the empty string at RegisterCommonFlags +0x1210 each give the two rows of their auipc
pair DIFFERENT (the last one the old tool misses: records/bytecmp-control-6-before-fix.out). sites.py: fuzz_uci.asan
calls only __asan_stack_malloc_1, once, at check_clamp 0x7f8ec with a0 = 0x60.

Re-run on the comparison kit 4bbd3a74be89 (strictcmp2 16982e3ef42b; BYTECMP.md last section; records/cmpkit-4bbd3a74be89-*.out,
by `cmpkit-sm1.py`): 12 of the 13 bodies kit-EQUAL, 0 UNMEASURED. RegisterCommonFlags (the whole function): kit verdict
NOT EQUAL, 1 unnamed empty-string place at +0x1218 not certified by the kit (its region to the next symbol is compared,
51389 / 51165 bytes); settled verdict EQUAL as a C string. The 2 words of RegisterCommonFlags at +0x358, the only part
AF0r.v's code table covers, are kit-EQUAL. The kit's 6 controls (3 planted words, the .got tls_index's module id, the
same cell re-pointed, a byte of an accepted C string) are each caught.

The settlement (BYTECMP.md, "The settlement"; `gates/settle-sm1.py <donor twin> <target twin>`, records/settle-sm1.out,
exit 0): the place is one NUL byte, a file byte, in both images (0x13f5f / 0x13e5f), so the same C string ""; its address
goes, by straight-line code, only into field +0x18 of the two FlagHandlerInclude handlers RegisterCommonFlags
registers (`include`, `include_if_exists`); that field is only overwritten by FlagHandlerInclude::Parse and only read by
FlagHandlerInclude::Format, as the argument of internal_snprintf's "%s". Hence EQUAL as a C string. A fresh reviewer's
audit (records/settle-sm1-review.md): VERDICT: ACCEPT (three wording notes, none changing the verdict; BYTECMP.md lists
them). The kit's 2-target print cut hides nothing: every row has target-differ 0 except RegisterCommonFlags (1), and
strictcmp2's tcmp called directly gives the same lists (records/cmpkit-4bbd3a74be89-fulllist.out).

## 1. Flag gate: port_addr_check efa19b81e92b --fail-on-flags (records/flag-gate.txt, records/flag-triage.tsv)

Of record: efa19b81e92b (flag classes 575d398c6022). Donor = the run's stage/ (fuzz_grant's text, module paths renamed),
ported = the committed files, each image with its unstripped twin (no symbol recovery). `FLAGGED 8 rows in 3 classes:
STALE-DONOR-CODE-POINTER=1 UNPAIRED-SOURCE=6 UNRESOLVED=1`, no GENERATOR-FILL row, rc 4. `triage-sm1.py`: 8 of 8
explained.

| class | rows | measured reason |
|---|---|---|
| STALE-DONOR-CODE-POINTER + UNPAIRED-SOURCE | 1 + 6 | AF0r.v :41 fs_ranges: A-fs-ranges.patch drops fuzz_grant's (0x3cda4, 93), (0x3d0a8, 103), (0x3d244, 115) (classes 0, 2, 4: fuzz_uci links class 1 only), so the checker pairs by position donor row 0 (stack_malloc_0) with target row 0 (0x3c1b8 = __asan_stack_malloc_1+0, the twin of donor row 1); the range-table check (2b) pairs every row by key |
| UNRESOLVED | 1 | AF0s.v :253, the donor's low-shadow bound 0x800b2400 = 2148213760, unchanged: at most kLowShadowBeg + IMG_TOP / 8 on both images (measure-sm1.py: 0x800b6400 / 0x800b5800); the checker reads it as the shadow of a .bss address |

Controls, both planted pointers caught (records/flag-gate.txt): AF0r.v FS_LOOP planted as the donor's code address
0x3cfac gives `STALE-DONOR-CODE-POINTER=2` (the plant) and 4 TARGET-DIFFERENT-SYMBOL rows (the fetch / branch lemmas at
FS_LOOP + 0xc / + 0x18, which now name __asan::InitializeFlags), and triage-sm1.py leaves exactly those 5 unexplained
(exit 1); AF0r.v TSD planted as the donor's data address 0x5f8e78 (__pthread_tsd_main in fuzz_grant.asan) gives
`STALE-DONOR-DATA-POINTER=1`, the one row triage-sm1.py leaves unexplained (exit 1).

e165063a0081, the checker efa19b81e92b replaces, run beside it on the same inputs: the same FLAGGED lines for the record
run and both controls (8 / 13 / 9 rows, the same classes). It reports no DIFFERENT-SYMBOL row here, so this slice has no
e165 false positive to record.

## 2. codeptr, the atable replacement, and the by-value check

### 2a. codeptr 12348302dfd2 (start-up set dbb5a97ad14, frozen-run.sh; records/codeptr.txt)

On fuzz_uci.asan, stale against fuzz_grant.asan with each file's donor text: 5 findings, every one a non-address
(0x100000 = 1 << kStackSizeLog; 0x109000 = FS_FROFF; 0x160613 = the instruction word at FS_LOOP + 0x14; 0x160000 =
(kFakeStackSize - kFakeFramesOff) / 8), declared in gates/codeptr-notaddr-sm1.tsv (every occurrence:
gates/codeptr-occurrences-sm1.tsv). With the declarations: 0 findings. Controls: the donor text on its own image gives 0
findings (the baseline); AF0r.v FS_ENTRY planted as the donor's 0x3cf18 gives that finding (STALE), also under the
declarations (exactly 1 finding, rc 1).

### 2b. In place of atable: keyset and the keyed range-table check (records/atable-replacement.txt)

atable is N/A for these files: atable.py 42e18a7eef50 only emits the start-up layer's atable record, and AF0r / AF0s /
YF0v state no atable field. These two checks replace it here:

- keyset f050b43e480e `classes`: fuzz_uci.asan has stack class 1 only (`1 -> 0x3c1b8`, found by the twin's names, each
  body's compiled cid and the stripped image's call-target scan); control, fuzz_grant.asan: classes 0, 1, 2, 4. This is
  the evidence for dropping fuzz_grant's class 0 / 2 / 4 rows of fs_ranges. `keyset check` over the three files: no
  keyed table (NOTE per file, rc 2, nothing measured).
- `gates/rangetab-sm1.py`, the keyed range-table check of fs_ranges: each of the 9 target rows is the twin of exactly
  one donor row by key (symbol from the image's own twin, which copy of the name, offset), with the same word count, and
  lies inside its symbol; the 3 donor rows without a twin name symbols fuzz_uci does not define. PASS. Controls: the row
  (0x60904, 2) planted as (0x60908, 2) and the row (0x68358, 140) planted as (0x68358, 141) are each REFUSED (rc 1).

### 2c. The by-value check (gates/decval-sm1.py; records/byvalue.txt, byvalue-rows.tsv, byvalue-review.tsv)

88 numerals in [0x10000, donor top): TARGET 24, OTHER 64, SHARED 0, DONOR-STALE 0, with one declared row: AF0r.v :37
`Definition FS_FROFF : Z := 0x109000` (kFakeFramesOff + (1 << kStackSizeLog) = 0x9000 + 0x100000, the model's fake-frame
offset of class 1, proved by frame_addr_cid; `--declare`, the image-B record's one added option). Without the
declaration that row is DONOR-STALE 1 and nothing else changes. The review rows: 1 comment numeral of the donor's own
notice (stack_malloc_1 at 0x3cf18), 2 fetch lines (their words are checked in the build by `ftac`), 10 unmoved model
constants and instruction words (1085440, 1048576, 1441792, 0x00160613, 0x0007c283). Control: AF0r.v FS_ENTRY planted as
the donor's 0x3cf18 gives DONOR-STALE 1 (that row; TARGET 24 -> 23) and nothing else changes.

## 3. v10: global_settings 439f8e3bd463 (records/settings-count.txt)

The three files: ESCAPES 3, PLAIN 6, UNMEASURED 0, KERNEL 0 (TACTIC 9). fuzz_grant's released counterparts (lib/A/Rt/
AF0r.v, AF0s.v, lib/Reusable/YF0v.v at 4f87de75d67): ESCAPES 3, PLAIN 6, UNMEASURED 0, KERNEL 0: equal. The three
ESCAPES rows are the donor's own global `Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).`,
one per file. Control: a second global Zify flag line planted in AF0s.v gives ESCAPES 4.

## 4. yh03check ca63d81d7725 (records/yh03check.txt)

N/A: the three files carry no YH03 value (no `src0_A_` / `src0_E_` / `src0_D_` definition); the tool refuses with
`0 src0_A_ / src0_E_ definitions parsed` per file (rc 2, nothing checked). Its known-answer controls on fuzz_uci.asan's
twin: a row `src0_A___asan_stack_malloc_1 := 0x3c1b8` / `src0_E_ := 0x3c348` is OK (rc 0); the same with A planted as
0x3c1bc is BAD (rc 1).

## 5. Build (records/build.txt, records/print-assumptions.txt, records/consumer-fit.txt)

`cb build` of lib/Reusable/YF0v.vo, lib/A/Rt/AF0r.vo, lib/A/Rt/AF0s.vo (dune, CB_COMPILE: each target compiled, the
cache not consulted): rc 0, 4 PINNED at facts 25e3d17bdb50 (fuzz_uci.asan 6ea017c24525, asan-ubsan a1b86e424add, plain
a6119aa7f1f2, ubsan fa87ac3037db), each file's own `.vo (real ...)` line. Control: AF0r.v's data cell (0x9e860, ...)
planted as (0x9e868, ...) fails the same build at AF0r.v:76 (`fsA_rodata_chk`, "Unable to unify "true" with
"false""), rc 1; the plant was reverted before the build of record. No admit / Admitted / Axiom / Parameter and no nia /
psatz / nra tactic in the three files (the word nia occurs once, in YF0v.v's header notice of the step it replaced).

Print Assumptions of `stack_malloc1_contract` (an uncommitted scratch file, built and deleted): 14 axioms, PrimInt63
(sub, ltb, lsr, lsl, lor, leb, land, int, eqb), PrimString (string, length, get), PrimArray.array and
functional_extensionality_dep; every one is in toolchain/allowed-axioms.txt.

The consumer's hypothesis: on a scratch merge (never pushed) of the consumer's commit 9ee6811b6c95 with this branch
(no conflict), a scratch file states lib/A/UciClose.v:143's type `forall (rc : YM05.RunCeil) (fx : YK11.FPState),
@astack_malloc_realizes fx rc segs B 1` under UciClose.v's bindings (segs := ucisegs0, B := AD2l.UciB) and closes it by
`exact (@AF0s.stack_malloc1_contract fx rc B (AR_laws_ok tfibsegs B) AD2l.UciB_syms)`: cb rc 0, the same 14 axioms.
