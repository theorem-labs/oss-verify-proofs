# Kept-donor-geometry gate v2 on plugin-hostd/fuzz_command

The by-value gate v2 (`roundconst.py` sha256 `32b39f3b34e9`, checked against its `SHA256SUMS`) was run on the full TSVs
of the value gate of record (`port_addr_check` `3d2eee813cce`) for the unit's relocated core: RA (donor lib/A to the
unit's lib/A, key A), RB (donor lib/Y*.v to lib/B, key B) and RU (donor lib/Y*.v to lib/Reusable, key B). All controls
of the gate README pass on this unit. Every non-SAME row (12 585) was settled with a measured reason. No row is a
kept donor quantity: **0 FINDING** from the gate rows. Outside the gate, lib/Reusable/YH03.v keeps cgif addresses in
rows that no proof reads (section "Adjacent findings").

## Inputs

| role | file | sha256 |
|---|---|---|
| donor A (pin / twin) | cgif_file_fuzzer.asan | 7093581aab04 / 488e39500746 |
| donor B (pin / twin) | cgif_file_fuzzer.asan-ubsan | 1c29845fe605 / ce511d541cda |
| target A (pin / twin) | fuzz_command.asan | c0661b96b5bd / 68db792d5fa7 |
| target B (pin / twin) | fuzz_command.asan-ubsan | bbe55d24d096 / 658cefbe806b |
| donor P (pin / twin), extra run only | cgif_file_fuzzer.plain | 19dedd1bc682 / 6ab540c43108 |
| target P (pin / twin), extra run only | fuzz_command.plain | a20873dc7f0e / fbe3a48ad296 |

Tools: `tool/roundconst.py` (v2, 32b39f3b34e9), `tool/v1/roundconst.py` (v1, 8ad299147f2e, from the tools tree of the
series), `port_addr_check.py` 3d2eee813cce, `tool/roles.py` 3bae7181ab01 (`roles_unit.py` is the same file with `ROOT`
set to this unit's roots, tree plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record), and the git directory taken from `$ROLES_GIT`). The unit tree read is
plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record) (proofs/plugin-hostd/fuzz_command/lib; the local extract equals the git tree for all 3159 files of A, B and
Reusable, by blob hash). Gate inputs, gzip'd: `in/{RA,RB,RU,CA,CB}.full.tsv.gz`.

## What was run

1. `run_main.sh IMGDIR`: v2 normal and `--moved` on RA, RB, RU (outputs `main/rc-{A,B,U}`, `main/mv-{A,B,U}`), and
   control (1) on the donor-on-donor TSVs CA, CB (`controls/c1-*`).
2. `mkplants_rc2.py UNIT_LIB plants` and `PAR=4 run_plants.sh PAC_WRAPPER RUNS_DIR IMGDIR`: 9 plant copies and 8
   unplanted base runs, each `port_addr_check` run restricted to the planted file (`--include F --dst-include F`, donor
   tree c8557374ad2e lib/A for lib/A, lib for lib/B, images keyed with their twins), then v2 and v1 with
   `--all-verdicts` on every base and plant (`controls/pac/`, `controls/v2/`, `controls/v1/`). The plant positions were
   chosen with `find_plants.py` (`controls/plant_candidates.{A,B}.txt`).
3. `compare_plants.py .` writes `controls.tsv`.
4. `ROLES_GIT=<repo> python3 roles_unit.py rc-A rc-B rc-U mv-A > roles.out` in `main/` (before the TSVs were gzip'd):
   2690 rows listed to read by hand.
5. `triage_rows.py --unit-lib UNIT_LIB --img IMGDIR --pimg img --main main --in in --pac port_addr_check.py --v2
   tool/roundconst.py --out .` writes `rows.tsv`, `rows_UP.tsv`, `rows.summary`, `triage_controls.tsv`.
6. `run_extra.sh`: v2 on RU with the plain images in place of B (see "Reusable describes the plain image").

## Gate results (main runs)

| run | selected | MISMATCH | MIXED | NO-COUNTERPART | non-SAME |
|---|---|---|---|---|---|
| rc-A (RA) | 124 507 | 1 427 | 7 396 | 0 | 8 823 |
| rc-B (RB) | 123 822 | 528 | 2 002 | 0 | 2 530 |
| rc-U (RU) | 66 763 | 182 | 1 038 | 0 | 1 220 |
| mv-A (RA, --moved) | 188 | 0 | 12 | 0 | 12 |
| mv-B (RB, --moved) | 176 | 0 | 0 | 0 | 0 |
| mv-U (RU, --moved) | 0 | 0 | 0 | 0 | 0 |

## Controls (`controls.tsv`): 13 of 13 PASS

| control | case | result |
|---|---|---|
| 1 donor-on-donor | CA normal / --moved, CB normal / --moved | 0 non-SAME rows in all four (selected 238 530 and 423 853) |
| 2 kept PT_LOAD length | A AB13.v:119 tfib_len0 143360 -> 131072 (cgif PT_LOAD0 page length) | valid plant (NON-ADDRESS-SAME); v2 +1 MISMATCH at the planted row |
| 2 kept PT_LOAD length | A AB1h.v:49 0x72000 -> 0x6d000 (cgif PT_LOAD1 page length) | valid (ROUND-CONSTANT-SAME); v2 +1 MISMATCH |
| 2 kept PT_LOAD length | B YB13.v:120 143360 -> 131072 | valid; v2 +1 MISMATCH |
| 3 kept word count | A AB01.v:188 seg length 1215 -> 214 (cgif .relro_padding.size/4) | valid; v2 +1 MISMATCH section/4; v1 rows = base |
| 3 kept word count | A AD1k.v:260 chunk 631 -> 67 (cgif sym(errmsgidx).extent/4) | valid; v2 +1 MISMATCH extent-to-next/4; v1 rows = base |
| 3 kept word count | B YB01.v:225 seg length 1127 -> 126 (cgif sym(sysconf.values).extent/4) | valid; v2 +1 MISMATCH; v1 rows = base |
| 3 kept small table length | A AB01.v:107 seg length 1091 -> 88 (cgif sym(states).extent) | valid; v2 +1 MISMATCH extent-to-next; v1 rows = base |
| 4 gap control | A AF0m.v:5175 0x2d00 -> 0xc0 (cgif .asan_globals.size; also sym(_ZN6__lsanL23suppression_placeholderE).extent, 192 in both) | valid; v2 calls it SAME, MISMATCH rows = base |
| 4 gap control | B YF0m.v:5176 0x2d00 -> 0xc0 | valid; v2 SAME, MISMATCH rows = base |

A plant is valid when the plant run keeps the donor numeral at the planted position (src = dst = column 11 of the base
run) with a passing verdict. v1 misses every plant of control 3 (same rows as on base) and catches the plants of
control 2. No lib/B small-table-length plant: no lib/B position qualified (`plant_candidates.B.txt`, C3t empty).

## Triage of every non-SAME row (`rows.tsv`)

Schema: the value-gate row's 16 columns, then `reason`, `measurement`, `result`, `finding_kind`, `new_value`,
`read_by`, then `gate_run`, `v2_status`, `v2_class`, `v2_value`, `differing_names` (the cgif quantities of the value
whose fuzz_command value differs). 12 585 rows, all `OK`.

Global measurement used by the run-time rules: every function that both images have under one name has the same size
in cgif and fuzz_command except `LLVMFuzzerTestOneInput` (asan 1400 of 1401, asan-ubsan 1400 of 1401, plain 123 of 124;
`.symtab` of the twins). So stack frames, code offsets, structure fields and constants of the sanitizer run-time and of
musl are the same numbers in both images. What differs is the image layout, and every differing name is a layout
quantity (PT_LOAD and section lengths, spans, object extents, unnamed runs).

| reason | rc-A | rc-B | rc-U | mv-A | what was measured |
|---|---|---|---|---|---|
| COLLECTED_STATE | 4 526 | 838 | | | lib/A/AB01.v, AB03.v, lib/B/YB01.v, YB03.v: the file header says the whole file was collected over fuzz_command's image by the start-up state collector |
| PAGE_SIZE | 1 375 | | | | 4096 = p_align of every PT_LOAD of all four images, not halved in its text |
| BYTE_ARITH | 904 | 904 | 748 | | 256 = 2^8 in a sentence doing 8-bit arithmetic |
| RT_OFFSET | 661 | 272 | 59 | | an offset or size from a run-time base of the allocator / stack / shadow / thread model; the base's definition is named |
| NOT_FLAGGED_QTY | 430 | 162 | 153 | | below the image base, and the sentence holds no bound address or object name of the differing quantities (cgif or fuzz_command), no table/length/slice role, no image identifier or image-address literal within two tokens, no x k or / k of a quotient name |
| INDEX / VAR_INDEX / EXPONENT | 502 | 127 | 27 | | the numeral's own text makes it a register / atom / variable index or an exponent |
| ARITH_EQ | 168 | 59 | 18 | | the numeral is the value of the expression its sentence rewrites (unit definitions substituted), or an operand of an arithmetic identity the sentence states (three random draws of its variables) |
| RT_CONST | 99 | 85 | 62 | | a named run-time constant (stack windows, buffer size, size class, pointer-array commit = kPtrArrayCommit 131072, lib/Reusable/YG00.v:22) |
| SYMLIT | 90 | 44 | 97 | | a literal of a symbolic register / expression value, below the image base or a power of two |
| FETCH_WORD_AT | 28 | 30 | 38 | | `fetch_word segs (SYM + N) = Some (W)`: the image word at SYM+N is W (image bytes) |
| FUNC_OFFSET | 5 | 1 | 13 | | SYM+N is inside the function SYM of the image's .symtab |
| KERNEL_CHECKED | 15 | | 1 | | the statement is closed by `vm_compute. reflexivity.` (fail-loud) |
| BUILD_TABLE_RANGE, CELL_STARTUP, LAYOUT_MEASURED, COUNT_MEASURED, CODE_SITE_CONST, RANGE_HINT, ABSTRACT_GOAL | 20 | 8 | 4 | | per-family image measurements (see `triage_rows.py` HANDLERS) |
| MOVED_TO_SEGMENT | | | | 12 | the port's value 0x3000 is fuzz_command.asan's PT_LOAD2 page length (program headers) |

Known-answer controls of the triage rules (`triage_controls.tsv`):
- **Plants**, judged with the planted donor value: AD1k.v:260 (word count) is refused (an image-address literal next to
  it), the three AB01/YB01 plants are refused by every rule except COLLECTED_STATE (provenance: a collected file has
  no port_core value), and the three tfib_len0 / tfib_res_eq plants are accepted only by KERNEL_CHECKED (those
  statements are closed by vm_compute, so a kept wrong value fails the build).
- **Known geometry** (the value gate's own SAME-GEOMETRY / IMAGE-EXTENT rows where the port moved a cgif quantity to
  fuzz_command's, re-judged with the cgif value put back): 300 rows, 256 refused by every rule, 44 accepted only by
  KERNEL_CHECKED (fail-loud statements).
- **Perturbation** (value + 4, and value := the fuzz_command value of the first differing name), per rule, over the
  rows of `rows.tsv` and `rows_UP.tsv`: the value-checked rules refuse (at value+4: PAGE_SIZE 2930/2930, BYTE_ARITH
  2556/2556, FETCH_WORD_AT 150/150, BUILD_TABLE_RANGE 5/5, CELL_STARTUP 6/6, COUNT_MEASURED 5/5, LAYOUT_MEASURED 8/8,
  ARITH_EQ 284/284); FUNC_OFFSET refuses only 1 of 35 (the offset stays inside the function) and CHUNK_IN_SEGMENT 0
  of 3 (any chunk inside the segment is valid); the role rules (INDEX, VAR_INDEX, EXPONENT, RT_OFFSET, RT_CONST,
  SYMLIT, NOT_FLAGGED_QTY) accept perturbed values: they read the numeral's role, not its value.

## Reusable describes the plain image (extra run, `rows_UP.tsv`)

lib/Reusable/YH00.v sets `src0segs := zsegs` of `images.Plain`, and `src0_A_memcpy` = 0x20510 is `memcpy` of
fuzz_command.plain (.symtab of twin fbe3a48ad296). The run of record RU is keyed B, so its quantities (and
port_addr_check's named-symbol cells of lib/Reusable/YH03.v: 366 UNMEASURED, RU summary) are read against the
asan-ubsan image. `run_extra.sh` gated the same RU TSV with the plain images: `main/rc-UP` selects 56 150 rows, 2 833
non-SAME (927 MISMATCH, 1 899 MIXED, 7 NO-COUNTERPART); `mv-UP` selects none. All 2 833 rows were triaged the same
way (`rows_UP.tsv`, all `OK`; e.g. YL0v.v:389 `chunk_bytes src0segs E 65536 (CImg 8192)`: [0x10000, 0x12000) lies in
fuzz_command.plain's first segment [0x10000, 0x12a5c) and the read offsets lie inside the chunk; YO0f.v:401 CTX_SIZE
928 = size of `__malloc_context` in fuzz_command.plain).

## Adjacent findings (`adjacent_findings.tsv`), outside this gate

lib/Reusable/YH03.v lines 126-134 keep cgif_file_fuzzer.plain addresses or wrong ends in its row table (measured
against fuzz_command.plain .symtab, twin fbe3a48ad296): src0_A_bcmp / src0_E_bcmp, src0_A_memcmp, src0_E_memset
(0x1d6b4, cgif's memset end; fuzz_command's is 0x20a0c), src0_A/E_strchr (no strchr in fuzz_command.plain),
src0_A/E_strchrnul, src0_A/E_strlen, src0_E_strnlen, src0_E_memchr. By-use grep over the unit: none of these names is
used outside YH03.v (lib/Reusable and lib/U/Reusable), so no proof reads them (finding_kind code, not read). The same
three cgif values (0x1d6b4, 0x1d6f0, 0x1d7d0) are in lib/U/Reusable/YH03.v lines 129-131. The rest of YH03.v (385
definitions) was not measured here.

## Named gaps

Of the gate (its README):
1. A kept small donor value that is also a right target quantity reads SAME (control 4: both gap plants are SAME).
2. An unnamed run that does not pair is not gated at any size.
3. Function sizes and extents are not quantities, nor are non-allocated sections.
4. Only kept values are gated; a changed value is port_addr_check's *-CHANGED verdict or `--moved`.

Of the triage rules (this directory):
5. The role rules settle "the numeral is not the flagged quantity"; they do not measure the value (perturbation
   counts above). A numeral that is another image quantity coinciding with a flagged value is settled by its role.
6. KERNEL_CHECKED accepts any value by design: its 16 rows (AD2e.v / AFks.v list lengths, YO01.v:47) rely on the
   unit's build.
7. COLLECTED_STATE is provenance: values in the four collected-state files are not re-derived here.

## Files

- `rows.tsv`, `rows_UP.tsv`, `rows.summary`, `triage_controls.tsv`: triage of the main runs and of the extra run.
- `controls.tsv`, `adjacent_findings.tsv`.
- `main/`: v2 outputs (`*.tsv.gz`, `*.summary`), `roles.out`; `controls/`: c1 outputs, plant runs (`pac/`), v2 and
  v1 on plants, logs; `plants/plants.tsv`; `in/`: gate inputs; `img/`: the two plain images and twins.
- Scripts: `run_main.sh`, `mkplants_rc2.py`, `find_plants.py`, `run_plants.sh`, `compare_plants.py`, `run_extra.sh`,
  `triage_rows.py`, `roles_unit.py`; `tool/` holds the gate files as checked (v2 and its SHA256SUMS, v1).
