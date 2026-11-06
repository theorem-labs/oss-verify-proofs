# fuzz_uci image-B class-1 stack_malloc contract: gate record

The files: lib/B/Rt/YF0r.v, lib/B/Rt/YF0s.v and the shared lib/Reusable/YF0v.v (applied.txt), relocated from
fuzz_grant's released lib/B/Rt/YF0r.v, YF0s.v and lib/Reusable/YF0v.v (recipes 4f87de75d67) by `run.sh` (port_core
0e4e065eab9f, image-B mode, core-B's route): staged 3, kept 0, required.tsv empty, 1 override value, 1/1 patch, symbol
gate PASS; the one FAIL row is core-B's known `rename-new-undeclared UciSyms` (its Record is in the start-up file
lib/B/YF0m.v, never staged), so `apply-sm1.sh` copies by --apply's rule (nothing overwritten) and `header-sm1.py` does the
comments-only header step (code bytes unchanged; dates, host paths, lane and branch names in comments: 14 before, 0
after). `gates/run-gates.sh` runs every gate below with its controls; `gates/records-sm1.py` writes records/.

The statement, fixed by the consumer (lib/B/UciBClose.v's Section hypothesis H_RT_STACK_MALLOC1 cites it):

    Corollary stack_malloc1_contract : forall B, AR_laws tfibsegs B -> UciSyms B -> astack_malloc_realizes tfibsegs B 1.

in `OssFuzzTheorems.Proofs.reac_repacer.fuzz_uci.lib.B.Rt.YF0s`: grant's YF0s.v:515 with GrantSyms renamed UciSyms.

## 0. Bytecmp of every body the proofs step through (BYTECMP.md; records/bytecmp-*.out)

13 bodies (the code table's nine fuzz_uci rows by symbol and every callee of the class-1 code), 13 equal up to
relocation; fuzz_grant's __asan_stack_malloc_0 / _2 / _4 rows have no body in fuzz_uci. Controls: an `or` planted for
the `and` at FS_LOOP and the donor's own `jal` word left at the GetCurrentThread call each give exactly one DIFFERENT
row and exit 1.

## 1. Flag gate: port_addr_check e165063a0081 --fail-on-flags (records/flag-gate.txt, records/flag-triage.tsv)

Donor = the run's stage/ (fuzz_grant's text, module paths renamed), ported = the committed files. `FLAGGED 11 rows in 4
classes: GEOMETRY-CHANGED=3 STALE-DONOR-CODE-POINTER=1 UNPAIRED-SOURCE=6 UNRESOLVED=1`, no GENERATOR-FILL row, rc 4.
`triage-sm1.py`: 11 of 11 explained.

| class | rows | measured reason |
|---|---|---|
| GEOMETRY-CHANGED | 3 | FS_N = 8192 (YF0r.v :35, :249; YF0s.v :56), the number of class-1 fake frames: `fs_frames_cid : fs_frames CID = FS_N` (Qed); a model constant |
| STALE-DONOR-CODE-POINTER + UNPAIRED-SOURCE | 1 + 6 | YF0r.v :43 fs_ranges: B-fs-ranges.patch drops fuzz_grant's (0x3cf4c, 93), (0x3d250, 103), (0x3d3ec, 115) (classes 0, 2, 4: fuzz_uci links class 1 only), so the checker pairs by position donor row 0 (stack_malloc_0) with target row 0 (0x3c1b8 = __asan_stack_malloc_1+0, the twin of donor row 1); the range-table check (2b) pairs every row by key |
| UNRESOLVED | 1 | YF0s.v :255, the override value 0x800b5800 = kLowShadowBeg + IMG_TOP / 8 (measure-sm1.py; donor control 0x800b6600); the checker reads it as the shadow of a .bss address |

Control (records/flag-gate.txt): YF0r.v FS_LOOP planted as the donor's 0x3d154 gives `STALE-DONOR-CODE-POINTER=2` (the
plant) and 4 TARGET-DIFFERENT-SYMBOL rows (the fetch / branch lemmas at FS_LOOP + 0xc / + 0x18 that now name
__asan::InitializeFlags); triage-sm1.py leaves exactly those 5 unexplained and exits 1.

## 2. codeptr, the atable replacement, and the by-value check

### 2a. codeptr 12348302dfd2 (start-up set dbb5a97ad14, frozen-run.sh; records/codeptr.txt)

On fuzz_uci.asan-ubsan, stale against fuzz_grant.asan-ubsan with each file's donor text: 5 findings, every one a
non-address (0x100000 = 1 << kStackSizeLog; 0x109000 = FS_FROFF; 0x160613 = the instruction word at FS_LOOP + 0x14;
0x160000 = (kFakeStackSize - kFakeFramesOff) / 8), declared in gates/codeptr-notaddr-sm1.tsv (every occurrence:
gates/codeptr-occurrences-sm1.tsv). With the declarations: 0 findings. Controls: the donor text on its own image gives
0 findings (the baseline); YF0r.v FS_ENTRY planted as the donor's 0x3d0c0 gives that finding (STALE), also under the
declarations (exactly 1 finding, rc 1).

### 2b. In place of atable: keyset and the keyed range-table check (records/atable-replacement.txt)

atable is N/A for these files: atable.py 42e18a7eef50 only emits the YB12 atable record, and YF0r / YF0s / YF0v state
no atable field and Require no YB12. These two checks replace it here:

- keyset f050b43e480e `classes`: fuzz_uci.asan-ubsan has stack class 1 only (`1 -> 0x3c1b8`, found by the twin's names,
  each body's compiled cid and the stripped image's call-target scan); control, fuzz_grant.asan-ubsan: classes 0, 1, 2,
  4, 6. This is the evidence for dropping fuzz_grant's class 0 / 2 / 4 rows of fs_ranges. `keyset check` over the three
  files: no keyed table (NOTE per file, rc 2, nothing measured).
- `gates/rangetab-sm1.py`, the keyed range-table check of fs_ranges: each of the 9 target rows is the twin of exactly
  one donor row by key (symbol from the image's own twin, which copy of the name, offset), with the same word count, and
  lies inside its symbol; the 3 donor rows without a twin name symbols fuzz_uci does not define. PASS. Controls: the row
  (0x60904, 2) planted as (0x60908, 2) and the row (0x68358, 140) planted as (0x68358, 141) are each REFUSED (rc 1).

Observation outside this slice (records/atable-replacement.txt): `keyset check` over the image-B core's lib/B/YF0l.v
REFUSES it because the record field pc_asan_memset names __asan_memset, which fuzz_uci.asan-ubsan does not define (the
core gives the field 0: core-B GATES.md section 1, KIND-CHANGED). It refuses the same with the field removed, so it is
the acode record's field set, not this slice's text.

### 2c. The by-value check (gates/decval-sm1.py = core-B's decval-B.py with this slice's file list; records/byvalue.txt)

128 numerals in [0x10000, donor top): TARGET 24, OTHER 104, SHARED 0, DONOR-STALE 0, with one declared row: YF0r.v :39
`Definition FS_FROFF : Z := 0x109000` (kFakeFramesOff + (1 << kStackSizeLog) = 0x9000 + 0x100000, the model's fake-frame
offset of class 1, proved by frame_addr_cid; `--declare`, the one option added to the script). Without the declaration
that row is DONOR-STALE 1 (the decision tree classes every unmoved hex Definition as an address role) and nothing else
changes. The review rows (byvalue-review.tsv): 19 comment numerals of the donor's notices, 2 fetch lines (their words are
checked in the build by `ftac`), 10 unmoved model constants and instruction words (1085440, 1048576, 1441792, 0x00160613,
0x0007c283). Control: YF0r.v FS_ENTRY planted as the donor's 0x3d0c0 gives DONOR-STALE 1 (that row; TARGET 24 -> 23)
and nothing else changes.

## 3. v10: global_settings 439f8e3bd463 (records/settings-count.txt)

The three files: ESCAPES 1, PLAIN 6, UNMEASURED 0, KERNEL 0 (TACTIC 7). fuzz_grant's released counterparts (lib/B/Rt/
YF0r.v, YF0s.v, lib/Reusable/YF0v.v at 4f87de75d67): ESCAPES 1, PLAIN 6, UNMEASURED 0, KERNEL 0: equal. The one ESCAPES row
is YF0v.v's global `Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).`, the donor's line;
its one importer, YF0s.v, sets the same value `#[local]` itself. Control: YF0s.v's `#[local]` Zify flag made global
gives ESCAPES 2.

## 4. yh03check ca63d81d7725 (records/yh03check.txt)

N/A: the three files carry no YH03 value (no `src0_A_` / `src0_E_` / `src0_D_` definition); the tool refuses with
`0 src0_A_ / src0_E_ definitions parsed` per file (rc 2, nothing checked). Its known-answer controls on fuzz_uci's twin:
a row `src0_A___asan_stack_malloc_1 := 0x3c1b8` / `src0_E_ := 0x3c348` is OK (rc 0); the same with A planted as 0x3c1bc
is BAD (rc 1).

## 5. Build (records/build.txt, records/print-assumptions.txt)

`cb build` of lib/Reusable/YF0v.vo, lib/B/Rt/YF0r.vo, lib/B/Rt/YF0s.vo (dune, each target
compiled, not restored from the cache): rc 0, 4 PINNED at facts 25e3d17bdb50 (fuzz_uci.asan 6ea017c24525, asan-ubsan
a1b86e424add, plain a6119aa7f1f2, ubsan fa87ac3037db), each file's own `.vo (real ...)` line. Control: YF0r.v's data
cell (0x9e960, ...) planted as (0x9e968, ...) fails the same build at YF0r.v:78 (`fsA_rodata_chk`, "Unable to unify
"true" with "false""), rc 1; the plant was reverted before the build of record. No admit / Admitted / Axiom / Parameter in
the three files.

Print Assumptions of `stack_malloc1_contract` (an uncommitted scratch file, built and deleted): 14 axioms, PrimInt63
(sub, ltb, lsr, lsl, lor, leb, land, int, eqb), PrimString (string, length, get), PrimArray.array and
functional_extensionality_dep; every one is in toolchain/allowed-axioms.txt.
