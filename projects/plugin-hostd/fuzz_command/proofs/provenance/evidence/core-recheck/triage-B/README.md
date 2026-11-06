# Triage of the flagged lib/B rows: gate runs RB and RAB (plugin-hostd/fuzz_command)

Rule 24: no function proved. Read-only: no .v file was edited, nothing was built or committed.

## What was triaged

- **RB**: port_addr_check 3d2eee813cce, donor cgif_file_fuzzer `lib/Y*.v` -> ours `lib/B/Y*.v`, image key B. The 809
  OPEN rows that the mechanical pass (`base_triage.py`) left in relocated (not generated) files:
  639 UNPAIRED-PORTED, 152 NON-ADDRESS-CHANGED, 6 DIFFERENT-SYMBOL, 6 KIND-CHANGED, 5 UNRESOLVED, 1 GEOMETRY-CHANGED.
- **RAB** (the relay view): the same gate, ours `lib/A/A*.v` -> ours `lib/B/Y*.v`, both sides keyed B. 86 rows:
  every STALE-DONOR-CODE-POINTER (31), STALE-DONOR-DATA-POINTER (28), SAME-VALUE-DIFFERENT-OBJECT (10) and
  STALE-DERIVED-QUOTIENT (3) row, generated files included, and the 14 open NON-ADDRESS-CHANGED rows of `base_triage.py`
  on RAB (its 3 open UNRESOLVED rows are keying artefacts of a run that keys both sides on B and are not taken).
  In RAB a STALE-DONOR-* row means an image-A value in a lib/B file.

Images (role, sha256 first 12): fuzz_command.asan-ubsan (image B) bbe55d24d096, symbols from its twin 658cefbe806b;
fuzz_command.asan (image A) c0661b96b5bd, twin 68db792d5fa7; cgif_file_fuzzer.asan-ubsan 1c29845fe605, twin
ce511d541cda. Ours at plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record), cgif at c8557374ad2e.

## What was run

    run.sh WORK        # WORK = the re-check work area (layout in run.sh's header)

`run.sh` runs `base_triage.py` on the RAB full table (writes `RAB.open.tsv`, `RAB.settled.tsv`, `RAB.base_triage.out`)
and then `triage.py` (sha256 `83133334cc1a`), which writes:

| file | content |
|---|---|
| triage-rows.tsv | the 809 RB rows: the 16 gate columns, then reason, measurement, result, finding_kind, new_value, read_by |
| rab-rows.tsv | the 86 RAB rows, same columns |
| controls.tsv | one control row per settled row: judge(value), judge(value+4), judge(donor value) |
| code-findings.tsv | the FINDING rows (file, line, old, new, read_by, evidence) |
| extra-findings.tsv | a finding outside the triaged rows (from the relay scan below) |
| relay-moved.tsv | every round A value (multiple of 4096 or a power of two) that the relay changed in a non-generated lib/B file |
| kept-counts.tsv | counts that a lib/B file says it took from image A, measured again on image B |
| triage.out | the printed counts |

The run took 29 s on the build VM.

## How a row is settled

Each rule finds the numeral's role on the lib/B line (comments blanked, the gate's numeral scan), computes the value
that role must have from a measurement, and compares. The measurement is one of: image B's symbol table, section or
program headers, image bytes (GOT words, instruction words, cell bytes), image B's 180 `asan_globals` descriptors
(beg, size, size_with_redzone, ...: the start-up shadow poisoning), the generated start-up certificate `lib/B/YB01.v`
and region list `lib/B/YD2j.v` (both written from image B), or the text of the definition or Qed lemma the line
restates (for example the malloc contract `lib/B/Rt/RtDMallocI.v` ipre_chain, `astrace_at`, `spZ`, `DEPOT_CAP`).
Each row's measurement column names the file and line, or the image address, it read.

Main rules:

- CONTRACT-RESTATED: the line repeats a conjunct of the Qed contract ipre_chain token for token (trace length 1..30,
  pT mod 8, pT + 16 + 8 * 30, register 11 = pT, `r <> 2%bv`, `getr regsI 2 = w64 (sp0 - IFRAME)`). This settles the
  106 NON-ADDRESS-CHANGED Hch rows too: the gate paired a rewritten sentence by name with an unrelated cgif sentence.
- REG-INDEX-WIDTH, REG-SP, REG-A0, ATOM-PT, FCSR-FRM, WIDTH, ENTRY-STACK-LAYOUT, TRACE-LAYOUT, OWNED-CORE: machine
  and model constants, each compared with the library definition that fixes it (`bvmap 5`, `getr regs 2`, `10 + i`,
  `sr_atoms`, `rdword`, `w64`, `R_hdr`, `astrace_at`, `core_extents`), or with the RISC-V fcsr layout (frm = bits 7..5).
- STARTUP-CERT: TFIB_HEAD4, eDM, dDM, TFIB_RANGES, AVIS14 and the a_eager bound compared with the 50 hand-off states
  of `lib/B/YB01.v`; the class instances of `lib/B/CmdStartInstB.v` check them by kernel computation as well.
- ZERO-SHADOW-MEASURED / ZERO-SHADOW-MARGIN: zero-shadow ranges recomputed from image B's descriptors (first poisoned
  granule 0x210e0 in .rodata and 0x5e3680 in .bss, last redzone end 0x5e3800); the hull bounds keep the A twin's
  margin (0x20) from the edge that each image's own descriptors give.
- GOT-CELL, SAME-SYMBOL-OFFSET, RET-INSTRUCTION, GI-RANGES, STACK-MALLOC-CLASSES, GENERATED-CELL, GENERATED-RANGE,
  GENERATED-REGION-BOUND, DECODED-IMMEDIATE, IMAGE-GEOMETRY, IMAGE-SHADOW-GEOMETRY, SHADOW-LENGTH: image measurements
  (.got word contents, symbol and offset in both images, the `ret` words of asan_malloc, g_rec / record.spill /
  g_quitting objects, `__asan_stack_malloc_N` symbols, cell bytes, auipc+addi/load cross references, J-type immediates
  of fetched words, .text size / 4, e_phoff, image extent / 8, map length / 8).
- REUSABLE-CONSTANT, LIST-COUNT, TOPF-ARITH, EVENT-BUDGET: values computed from named constants and lists (DEPOT_CAP
  + 1 / + 2, kFreeArrayOffset, the 4 head and 12 tail maps, REG0's 3 register-based head regions and its first
  per-chunk region at entry 43, uTopRel's 160 and 3935, EV_LIB against ev_ltoi_lib).
- Value-independent rules (27 rows, marked `na` in controls.tsv): SOUND-FOR-ANY-VALUE (startup_plan_tfib_ranges only
  feeds `mk_itab_ranges`, sound for every list), UNREAD-FIELD (YE2k's four cgif sink-string addresses, set to 0, are
  read only by lib/Reusable definitions that no lib/B file uses), STOP-PC-SENTINEL, TRUE-WEAKER-BOUND.

## Counts

RB (809 rows, 0 without a reason):

| reason | result | rows | gate verdicts |
|---|---|---|---|
| CONTRACT-RESTATED | OK | 439 | NON-ADDRESS-CHANGED 106, UNPAIRED-PORTED 333 |
| REG-INDEX-WIDTH | OK | 55 | UNPAIRED-PORTED 55 |
| TRACE-LAYOUT | OK | 53 | UNPAIRED-PORTED 53 |
| STARTUP-CERT | OK | 33 | NON-ADDRESS-CHANGED 1, UNPAIRED-PORTED 32 |
| WIDTH | OK | 31 | UNPAIRED-PORTED 31 |
| LIST-COUNT | OK | 23 | NON-ADDRESS-CHANGED 10, UNPAIRED-PORTED 13 |
| REUSABLE-CONSTANT | OK | 23 | GEOMETRY-CHANGED 1, NON-ADDRESS-CHANGED 22 |
| REG-SP | OK | 21 | UNPAIRED-PORTED 21 |
| OWNED-CORE | OK | 16 | UNPAIRED-PORTED 16 |
| ATOM-PT | OK | 15 | UNPAIRED-PORTED 15 |
| FCSR-FRM | OK | 12 | UNPAIRED-PORTED 12 |
| GI-RANGES | OK | 12 | UNPAIRED-PORTED 12 |
| TOPF-ARITH | OK | 10 | UNPAIRED-PORTED 10 |
| SOUND-FOR-ANY-VALUE | OK | 7 | NON-ADDRESS-CHANGED 7 |
| SAME-SYMBOL-OFFSET | OK | 7 | UNPAIRED-PORTED 7 |
| GOT-CELL | OK | 6 | UNPAIRED-PORTED 6 |
| STACK-MALLOC-CLASSES | OK | 5 | NON-ADDRESS-CHANGED 1, UNPAIRED-PORTED 4 |
| ZERO-SHADOW-MEASURED | OK | 4 | DIFFERENT-SYMBOL 3, KIND-CHANGED 1 |
| ENTRY-STACK-LAYOUT | OK | 4 | UNPAIRED-PORTED 4 |
| UNREAD-FIELD | OK | 4 | KIND-CHANGED 4 |
| IMAGE-SHADOW-GEOMETRY | OK | 3 | UNPAIRED-PORTED 3 |
| ZERO-SHADOW-MARGIN | OK | 3 | DIFFERENT-SYMBOL 3 |
| IMAGE-GEOMETRY | OK | 2 | NON-ADDRESS-CHANGED 1, UNRESOLVED 1 |
| EVENT-BUDGET | OK | 2 | NON-ADDRESS-CHANGED 2 |
| REG-A0 | OK | 2 | UNPAIRED-PORTED 2 |
| GENERATED-REGION-BOUND | OK | 2 | UNRESOLVED 2 |
| ZERO-BYTES | OK | 2 | UNPAIRED-PORTED 2 |
| FP-TOKEN | OK | 2 | UNPAIRED-PORTED 2 |
| GENERATED-CELL | OK | 2 | UNPAIRED-PORTED 2 |
| DECODED-IMMEDIATE | OK | 2 | NON-ADDRESS-CHANGED 2 |
| RET-INSTRUCTION | OK | 2 | UNPAIRED-PORTED 2 |
| MOVED-MODEL-BOUND | FINDING | 2 | UNRESOLVED 2 |
| SAME-LAYOUT-LENGTH | OK | 1 | UNPAIRED-PORTED 1 |
| STOP-PC-SENTINEL | OK | 1 | KIND-CHANGED 1 |
| FILE-ANCHOR | OK | 1 | UNPAIRED-PORTED 1 |

RAB (86 rows, 0 without a reason):

| reason | result | rows | gate verdicts |
|---|---|---|---|
| SHADOW-LENGTH | OK | 30 | STALE-DONOR-CODE-POINTER 30 (YB01/YB03: 465920 = 3727360 / 8, a shadow length) |
| GENERATED-CELL | OK | 27 | STALE-DONOR-DATA-POINTER 24, STALE-DERIVED-QUOTIENT 3 (YF0m cells = image B bytes) |
| SOUND-FOR-ANY-VALUE | OK | 14 | NON-ADDRESS-CHANGED 14 (YB05 startup_plan_tfib_ranges) |
| GENERATED-REGION-BOUND | OK | 5 | SAME-VALUE-DIFFERENT-OBJECT 5 (0x10330: region R_A1d, formed by mix_call in both images) |
| ZERO-SHADOW-MARGIN | OK | 4 | STALE-DONOR-DATA-POINTER 4 (YD1k 0x210c0) |
| IMAGE-SHADOW-GEOMETRY | OK | 3 | SAME-VALUE-DIFFERENT-OBJECT 3 (YD1f 0xbec00 = (0x606000 - 0x10000) / 8) |
| DERIVED-QUOTIENT | OK | 1 | STALE-DONOR-CODE-POINTER 1 (YFk5 524280 = SHADOW_OFF / 4096, a proof step) |
| TRUE-WEAKER-BOUND | OK | 1 | SAME-VALUE-DIFFERENT-OBJECT 1 (YE7d 0x148680 >= the rom end 0xa4258) |
| GENERATED-RANGE | OK | 1 | SAME-VALUE-DIFFERENT-OBJECT 1 (YF0m 0x522e00 = read_stage - 0xb0490 in B; the same in A) |

The example lib/B/YD1k.v:215 rodata_hull_zero 0x210c0 (A 0x21080) is right for image B: image B's first poisoned
.rodata granule is 0x210e0 (.str, 3 bytes in a 32-byte slot), image A's is 0x210a0, and both files keep the bound 0x20
below that edge. The gate's "A address of kSuppressionLeak" reading is a coincidence of image A's layout.

## Controls

controls.tsv has one row per settled row. Of the 895 rows: 868 have a value-based judge; it accepts the file's value
on all 866 OK rows, refuses it on the 2 FINDING rows, and refuses value+4 on all 868. 188 rows have a donor value
(cgif's value for RB, the A twin's value for RAB) different from ours; the judge refuses it on all 188. 27 rows are
value-independent (`na`, see above). Per-reason counts are at the end of triage.out.

## FINDINGs

All three are code findings, harmless: the statements stay true and are Qed, so no claim or release-check result
changes. They were reported to the series owner under the STOP rule because proofs read them.

| file:line | old | new | read by | measurement |
|---|---|---|---|---|
| lib/B/YFjm.v:429 (map_zoneN) | 2148223601 (0x800b4a71) | 2148236288 (0x800b7c00) | lib/B/YFjh.v:153 | YFjm.v states the case as `kLowShadowBeg + TFIB_IMG_END / 8 <= SMv`; kLowShadowBeg 0x7fff7000 (lib/Reusable/YG0f.v:21), TFIB_IMG_END 0x606000 (lib/B/YF0x.v:26, = the image B top) |
| lib/B/YFk1.v:697 (sm_bounds) | 2148223601 | 2148236288 | lib/B/YFk0.v:567 | the same bound |
| lib/B/YE6k.v:1388 (entD_ro, proof-local assert) | 0x1ffb80 | 0x200000 | the proof itself | the A twin AE6k.v:1387 writes 0x200000 = 2^21; the relay moved it as if it were the address theDepot+0x6d068 |

The first two are class B: 0x800b4a71 = 0x7fff8000 + 0x5e5388 / 8 is cgif's 2148217856 (the shadow of a cgif .bss
address) that port_core moved as a shadow-of-address. The other numerals of the same line are exactly TFIB_IMG_END,
kLowShadowBeg and kLowShadowEnd. The A twins (lib/A/AFjm.v:428, lib/A/AFk1.v:696) have the same value. The third
one came from the relay (a2b) only: the largest end in lib/B/YE2y.v icpt_rodata is 0xb1938, so both values bound it.

## Other checks

- Relay scan (relay-moved.tsv): 4 round A values changed in non-generated lib/B files. 3 are code addresses at the
  same symbol and offset in both images (same instruction word). 1 is the YE6k.v:1388 finding.
- Kept counts (kept-counts.tsv): lib/B/YB05.v's header says its tail was measured on image A (180 descriptors, 181
  XMemset steps, descriptor 68 first with an ODR indicator). Image B has 180 descriptors, and descriptor 68 is its
  first with an ODR indicator: OK.
- Class A (.got cell on the wrong word): CmdB's as_got_shadow 0xa5f50 and as_got_uar 0xa5fa8 are the only image B .got
  words that hold __asan_shadow_memory_dynamic_address and __asan_option_detect_stack_use_after_return; the program
  GOT words 0xa6bc8..0xa6be8 hold g_rec, rec_ncodes, rec_codes and g_quitting. No finding.
