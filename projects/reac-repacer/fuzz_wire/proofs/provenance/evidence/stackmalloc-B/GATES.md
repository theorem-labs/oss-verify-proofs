# Gates of fuzz_wire's image-B __asan_stack_malloc_0 / _1 contracts

Images: donor fuzz_grant.asan-ubsan (pin fde52226dc48, unstripped twin 5a5ee7c02b4e); target fuzz_wire.asan-ubsan (pin
af4534831a45 = harness.yaml, twin 51eb4bef2425). fuzz_wire links __asan_stack_malloc_0 at 0x3c524 (372 bytes) and
__asan_stack_malloc_1 at 0x3c698 (400 bytes) and no other class; the donor links 0, 1, 2, 4 and 6. All runs:
gates/run-gates.sh (records/gates.txt holds one line per run).

## 1. The relocation run of record (records/portcore-run.txt)

port_core 0e4e065eab9f (resolve_code 81803218fe79, gen_traces a78026af1ae2, adapted.patch 27bb43cc1436, symbol gate
5033540ba83b): staged 5, kept 0, `required.tsv` empty, 2 values from --override, B-smB.patch applied (3 hunks, 0
failed), refused 2 (code-no-counterpart: the fs_ranges rows of __asan_stack_malloc_2 / _4, which the patch removes),
decode check 14 / 14 ok, symbol gate PASS, exit 3 for these FAIL rows:

| FAIL row | judgement |
|---|---|
| rename-new-undeclared WireSyms | core-B's known row: the Record WireSyms is declared in the start-up file lib/B/YF0m.v, which no run stages; the build compiles both contracts against it |
| data-symbol 0x109000, YF0r.v:38 (FS_FROFF), :357 / :366 (1085440) | not an address: fs_frame_off 1 0 = kFakeFramesOff + 1 * Z.shiftl 1 kStackSizeLog = 0x9000 + 0x100000 (lib/Reusable/YG0f.v, YG00.v), unchanged; numerals-smB.tsv MODEL rows (the code of __asan_stack_malloc_1 forms it from the stack size log; its 32 immediates are the same in both images) |

## 2. The numeral table (records/numerals-smB.tsv; gates/numerals-smB.py)

116 rows: every numeral of the five files that differs from the donor or lies in [0x10000, 0x5fb000] (the address
ranges of both images). 114 OK, 2 DROPPED, 0 WRONG, 0 UNMEASURED; unaligned donor lines 0.

| role | rows | the rule (each also run on fuzz_grant's image, where it gives the donor's own value) |
|---|---|---|
| CODE | 27 | pc = the same-named FUNC (NAME{STT_FILE} for a duplicated local name, the same size) + the same offset; the function a pair of the body compare (section 3). Probe points FS_ENTRY / FS_LOOP / FS_FOUND / FS_SDFF / FS_SDSH of both classes, FS_FOUND's bit-vector literal, and the 10 code-table rows (with their word counts) |
| DROPPED | 2 | the code-table rows of __asan_stack_malloc_2 / _4: fuzz_wire's twin has no symbol of either name |
| INSN | 8 | the 4 bytes of the image at the fetch lemma's pc (FS_LOOP + 0x8, + 0x14); the decode lemma's word is the fetch lemma's |
| GOT | 8 | the cell's word(s) read from the image name a target (tls_index {1, fake_stack_tls}; tp-offset of dtls; common_flags_dont_use + 0; current_verbosity + 0); the ONE fuzz_wire .got cell naming the same target; the code that loads it at the same function + offset in both images |
| WORD | 6 | a value a cell holds = the word read from fuzz_wire's image at the relocated cell, naming the same target (__tls_get_addr, common_flags_dont_use, current_verbosity) |
| DATA | 26 | the same symbol + offset, the symbol of equal size: TSD = __pthread_tsd_main (1024 bytes), common_flags_dont_use + 0x89 (288), current_verbosity (4), tsd_key_inited with tsd_key at + 4, the thread-object cells T + 48 / T + 56 = builtin_tls + 0x800 / + 0x8dc (131280; also stated by the record lib/B/YF0m.v Tfib_const_sym (AT 48) / (AT 56)) |
| TLS | 8 | from PT_TLS and musl's static TLS layout (mem = builtin_tls, sizeof(struct pthread) 200, MIN_TLS_ALIGN 8, DTP_OFFSET 0x800): TP 0x5d3790, dtv 0x5d37b0 (the word at TP - 8), the dtv[1] slot 0x5d37b8, dtv[1] = TP + 0x800 = 0x5d3f90; equal to the record's TFIB_TP and (ATp (-8)) |
| IMG | 16 | IMG_TOP = the last PT_LOAD end page-rounded (wire 0x5f5070 -> 0x5f6000 = 6250496; grant 0x5fb000), IMG_TOP / 8 = 781312, kLowShadowBeg + IMG_TOP / 8 = 2148228096 (the two --override values) |
| MODEL | 11 | unchanged model constants over the kernel constants of lib/Reusable/YG00.v / YG0f.v: Z.shiftl 1 kStackSizeLog = 1048576, (kFakeStackSize - kFakeFramesOff) / 8 = 1441792, fs_frame_off 1 0 = 0x109000 = 1085440 (with the immediates check above) |
| PATCH | 4 | the `0` of `ly_NB ly =? 0` / `ly_SB ly =? 0` that B-smB.patch adds; no image value |

Planted control: TP of B/Rt/StackMalloc0Tbl.v moved by 8 (0x5d3790 -> 0x5d3798) gives 1 WRONG row (that one) and rc 1
(records/numerals-plant.tsv).

## 3. The body compare (records/bodycmp-*.out; gates/bodycmp-smB.py)

cmpkit 86da41d3ef68 (its SHA256SUMS: 9 files OK; strictcmp3.py 65688e94214a), run with PYTHONDONTWRITEBYTECODE=1.
`drvcmp.py twins`: each twin against its pin, PT_LOAD layout equal, differing bytes only in the ELF header and the
build-id note (both images). The functions are every row of the relocated fs_ranges (the files' code table), paired by
name and offset with the donor's rows:

| function (wire / grant) | decoded words | `strictcmp3.py cmp` (whole function) | tcmp over the decoded range |
|---|---|---|---|
| __asan_stack_malloc_0 0x3c524 / 0x3cf4c | 93 | EQUAL-mod-pcrel, 0 target differences | EQUAL-mod-pcrel |
| __asan_stack_malloc_1 0x3c698 / 0x3d0c0 | 100 | EQUAL-mod-pcrel, 0 | EQUAL-mod-pcrel |
| RegisterCommonFlags 0x60ebc / 0x61d00 (+0x358) | 2 | DIFFERENT-target, 1: +0x1218 data-differs (JUDGED, below) | EQUAL |
| ___interceptor___tls_get_addr 0x45ec4 / 0x46e38 | 31 | EQUAL-mod-pcrel, 0 | EQUAL-mod-pcrel |
| __tls_get_addr 0x9279c / 0x97484 | 9 | EQUAL, 0 | EQUAL |
| __asan::GetCurrentThread 0x5b554 / 0x5c398 | 8 | EQUAL, 0 | EQUAL |
| __asan::AsanTSDGet 0x540a0 / 0x54ee4 | 6 | EQUAL-mod-pcrel, 0 | EQUAL-mod-pcrel |
| __pthread_getspecific 0x93850 / 0x98538 | 7 | EQUAL, 0 | EQUAL |
| __sanitizer::DTLS_on_tls_get_addr 0x68c68 / 0x69aac | 140 | EQUAL-mod-pcrel, 0 | EQUAL-mod-pcrel |
| __asan::MemToShadow{asan_fake_stack.cpp} 0x3c828 / 0x3d79c | 28 | EQUAL-mod-pcrel, 0 | UNMEASURED-target only (PARTIAL, below) |

- JUDGED (the one function row that is not clean): RegisterCommonFlags' differing target at +0x1218 lies outside the
  two words the table decodes (+0x358..+0x360, the return site of a call), which compare EQUAL. The target is an empty
  C string in both images (wire 0x13e67, grant 0x13e96; the same 24 bytes `\0'\0HINT: if you don't ca`): the kit's
  full-region rule for an empty string reads past its NUL.
- PARTIAL: the table decodes MemToShadow's first 28 words; the range cut leaves the auipc at +0x6c without its consumer
  (past +0x70), so the range is UNMEASURED-target only; the whole function compares EQUAL-mod-pcrel with 0 target
  differences.
- Dropped donor rows: __asan_stack_malloc_2 / _4 (fuzz_wire's twin has no symbol of either name).
- The table's base tbl_icpt is lib/B/YE34.v's, a kept file of the unit's image-B core (core-B's gates).
- PLANT: one word flipped inside each of fuzz_wire's __asan_stack_malloc_0 / _1 (+0x4, 0x00113c23 -> 0x00013c23,
  plant image sha256 42527e7fe564): both rows DIFFERENT (real 1), caught 2 of 2.
- Measured before the relocation (the roots, the same kit): wire _0 vs grant B _0 and wire _1 vs grant B _1
  EQUAL-mod-pcrel with 0 target differences (the tls index of fake_stack_tls equal).

## 4. Size check (records/size-moves*.tsv)

size_moves 7edcb4804346 over the run of record: 10 moves of a power-of-two / page-aligned donor value;
size_moves_classify 810be4eaa791: 10 RIGHT (each = wire's measured image.top 0x5f6000, the relocated-symbol reading
0x5f5e80 rejected), 0 WRONG, 0 UNDECIDED; all 10 in the final tree. The 3 lines the scan does not pair are the lines
B-smB.patch writes (YF0r.v fs_ranges; the SZ step of StackMalloc0.v and YF0s.v): numerals-smB.tsv pairs the code-table
rows by function (word counts equal) and lists the added 0s as PATCH rows.

## 5. port_addr_check 45b78aaa48c3 (records/flag*.tsv, flag*.log, flag-triage.tsv)

versions/45b78aaa48c3.SHA256SUMS sha256 d0f4d698fd8e; donor -> ported, src = the run's stage/ (the donor files at their
target paths), dst = the five files; `--paired-only --fail-on-flags`. 5 files paired, 4517 numerals, rc 4: FLAGGED 13
rows in 4 classes, triage-smB.py 13 explained, 0 UNEXPLAINED:

| class | rows | reason |
|---|---|---|
| UNPAIRED-PORTED | 4 | the `0` of `ly_NB ly =? 0` / `ly_SB ly =? 0` that B-smB.patch adds (StackMalloc0.v:66, YF0s.v:66) |
| UNPAIRED-SOURCE | 4 | the donor fs_ranges rows of __asan_stack_malloc_2 / _4 (start, word count) that B-smB.patch removes; fuzz_wire's twin has no symbol of either name |
| GEOMETRY-CHANGED | 3 | 8192 = fs_frames 1 = Z.shiftl 1 (kStackSizeLog - 6 - 1) (FS_N of class 1), unchanged; a count of the model that happens to equal a donor image quantity |
| UNRESOLVED | 2 | kLowShadowBeg + IMG_TOP / 8 (grant 2148230656 -> wire 2148228096; overrides-smB.tsv, numerals IMG rows) |

Planted control: FS_ENTRY of B/Rt/StackMalloc0Tbl.v put back to the donor's 0x3cf4c: FLAGGED 14, the new row
STALE-DONOR-CODE-POINTER, and triage leaves exactly it UNEXPLAINED (rc 1).

## 6. Crossed pairs (records/ab1w-*.tsv)

ab1w_swaps 3f885801a1f5: the five files define no `tfib_A_ / tfib_E_ / tfib_D_` cell and read none (0 cells, 0 crossed
pairs each); their code values are named function by function in numerals-smB.tsv (CODE rows). The unit's image-B cell
record lib/B/YB1w.v: 782 cells, 0 crossed pairs.

## 7. No admit; Print Assumptions (records/print-assumptions.txt)

No Admitted / admit / Axiom / Parameter / Abort / Conjecture in the five files. Print Assumptions of
stack_malloc0_contract and of stack_malloc1_contract: the same 14 axioms, PrimInt63 (9), PrimString (3),
PrimArray.array and functional_extensionality_dep, each one entry of toolchain/allowed-axioms.txt.

## 8. Builds (records/build.txt)

- Iterating builds (cb d02a58a345b9, dune cache): the donor text failed at StackMalloc0.v:67 and YF0s.v:67 (`No
  applicable tactic`, the empty-depot owned_extents; section 3 of MANIFEST.md); with B-smB.patch both contracts compile
  (rc 0, 2 targets compiled, 0 failed; vo check 0 failed).
