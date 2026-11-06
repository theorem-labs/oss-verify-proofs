# Gate 7 — roundconst v2: kept donor image geometry, by value, image A (fuzz_disco.asan)

Kind: measurement; proves no function. `port_addr_check` never reads a row it classes ROUND-CONSTANT-SAME,
SAME-GEOMETRY or NON-ADDRESS-SAME, yet such a row can keep a DONOR image quantity (a segment or section length, a word
count, a table extent) where fuzz_disco.asan's own differs. roundconst v2 selects every kept numeral equal to a quantity
of the donor image of the row's build and looks the same quantity up in the target image by name.

## Command (run.sh `rc`)

```
gzip -c $OUT/addr3/pac-A.tsv > $OUT/rc/pac-A.tsv.gz        # gate 6's full table (every row), keyed A / B / P / U
roundconst.py $OUT/rc/pac-A.tsv.gz \
  A=$CGIF_BIN.asan:$CGIF_TWINS/cgif_file_fuzzer.asan,B=$CGIF_BIN.asan-ubsan:$CGIF_TWINS/cgif_file_fuzzer.asan-ubsan,P=$CGIF_BIN.plain:$CGIF_TWINS/cgif_file_fuzzer.plain,U=$CGIF_BIN.ubsan:$CGIF_TWINS/cgif_file_fuzzer.ubsan \
  A=$PINS/fuzz_disco.asan:$TWINS/fuzz_disco.asan,B=$PINS/fuzz_disco.asan-ubsan:$TWINS/fuzz_disco.asan-ubsan,P=$PINS/fuzz_disco.plain:$TWINS/fuzz_disco.plain,U=$PINS/fuzz_disco.ubsan:$TWINS/fuzz_disco.ubsan \
  $OUT/rc/rc-A
rc_triage.py --rc $OUT/rc/rc-A.tsv --lib $LIB --pin $PIN_A --twin $TWIN_A --cgif-pin $CGIF_BIN.asan \
  --cgif-twin $CGIF_TWINS/cgif_file_fuzzer.asan --hand rc/hand-triage.tsv --out $OUT/rc/triage-A.tsv
```

Each image spec is `pin:unstripped twin`; the tool stops if a twin's PT_LOAD table or allocated sections differ from its
pin's (none did). cgif's asan twin sha256 `488e39500746…`, image A's twin `b8aac6eee6a6…` (twin-check.txt).

## Tools of record (cited by name + sha256, not copied)

- `roundconst.py` v2 sha256 `32b39f3b34e97818cd71be57afda15f6aba21ede5fe2d1016f939ede19ac26cc` (its README is the
  method and the controls); v1 `roundconst.py` sha256 `8ad299147f2e67fbeb40ee47592152377082e6c55e745a16d9b45b65d84e27b3`
  only for the v1 half of the planted controls.
- `port_addr_check.py` 3d2eee813cce (gate 6) for the full tables of the base, the donor-on-donor run and the plants.

## Verdict

Exit 0. **127504 kept rows selected** (equal to a donor quantity; floor 0x100 on spans only): SAME 120548 (NON-ADDRESS-SAME
120471, SAME-GEOMETRY 77), **MISMATCH 1406** (NON-ADDRESS-SAME), **MIXED 5550** (NON-ADDRESS-SAME 900, SAME-GEOMETRY 4650),
NO-COUNTERPART 0. Non-SAME rows by the donor quantity class:

| status | class | rows |
|---|---|---|
| MISMATCH | extent-to-next(unnamed run) /4, /2, plain (+1 with section/4; span/4) | 445 / 33 / 13 (+1) |
| MISMATCH | segment/4096 | 299 |
| MISMATCH | span/2, span/4, span, span/8 (+1 span/2; span/4) | 216 / 97 / 62 / 4 (+1) |
| MISMATCH | extent-to-next | 134 |
| MISMATCH | segment/2; span/2 · segment/8; span/8 · segment/4; span/4 | 60 · 22 · 1 |
| MISMATCH | section/4; span/4; span/8 · section/2; span/2 (; span/4) · section; span | 14 · 2 (+1) · 1 |
| MIXED | extent-to-next; segment/2; span; span/2; symbol-size (value 4096) | 4978 |
| MIXED | extent-to-next/8; segment; span; symbol-size/8 (value 8192) | 414 |
| MIXED | extent-to-next .. symbol-size/4 (value 1024) · .. segment/4 .. (value 2048) | 122 · 30 |
| MIXED | extent-to-next/2; symbol-size/2 · extent-to-next/4; symbol-size/4 · extent-to-next; .. /2 | 2 · 2 · 2 |

## Controls (README §Controls; a control that does not fire makes the gate void)

| control | plant (a copy of the lib/A file, outside the branch) | donor quantity the planted value is | result |
|---|---|---|---|
| 1 donor on donor | none: cgif's lib against itself, cgif's four pins on both sides (port_addr_check 3d2eee813cce, 728 files, 346194 numerals) | — | 240603 rows selected, **0 non-SAME** (PASS) |
| 2 kept PT_LOAD length | `AB13.v:122` `tfib_len1 … = 454656%N` → 446464 (0x6d000) | cgif PT_LOAD1 page length 0x6d000; disco's 0x6f000 | v2 **+1 MISMATCH** (segment; span) at AB13.v:122; v1 +1 too (FIRED) |
| 3 kept word count | `AB01.v:181` `seg HS_tfib_10_kn 389 670` → 214 | cgif `.relro_padding` size / 4 = 0x358 / 4; disco's 0xdf8 / 4 | v2 **+1 MISMATCH** (section/4) at AB01.v:181; v1 the same rows (FIRED) |
| 4 kept small table length | `AB01.v:102` `seg HS_tfib_0_kn 263 13` → 88 | cgif `sym(states).extent` 88; disco's 0x1d0 | v2 **+1 MISMATCH** (extent-to-next) at AB01.v:102; v1 the same rows (FIRED) |
| 5 gap control | `AD2j.v:31` `(CImg 112)` → 192 | cgif `asan_globals` size 192 (disco's 0xc40), also `sym(_ZN6__lsanL23suppression_placeholderE).extent` = 192 in both | v2 **SAME**, non-SAME rows unchanged, as README gap 1 says (FIRED) |

Each plant sets the disco numeral back to the DONOR's numeral at that position (column 11 of the base run), so
port_addr_check passes it (NON-ADDRESS-SAME); each is judged by `rc/plant_check.py` against the same file unplanted, both
through port_addr_check 3d2eee813cce and roundconst v2 / v1.

## Every MISMATCH / MIXED row read (README gap 5)

`rc/rc_triage.py` gives each of the **6956 non-SAME rows** one class by a rule its docstring states, measured where the
rule names an image fact; `rc/hand-triage.tsv` names the 4 groups no rule covers, each with a check the script
evaluates. Per-row table: `rc/triage-A.tsv` (grouped by file, line, value, kind and class; 2910 lines; reproduced byte
for byte by run.sh). The rows' idx is not a position on the line, so every occurrence of the value on the
comment-stripped line is classified and must agree. Measurements the script prints: page alignment 0x1000 for every
PT_LOAD of the pin, the twin and cgif's pin; the sanitizer runtime is one build (1402 runtime FUNC / OBJECT names in both
twins, all 1402 the same size); every start-up file header states how it was made from fuzz_disco.asan.

**Result: 6956 classed, 6956 right, 0 DEFECT, 0 untriaged.**

| class | rows | the measured rule (rc_triage.py docstring) |
|---|---|---|
| GENERATED | 4180 | the row's file is a start-up file written from fuzz_disco.asan, not a port output: AB01 3687 and AB03 231 (the start-up collector's 50 hand-off states and join state), AB05 251 (the start-up plan), AF0m 5, AD2i 4, AD1k 2 (the start-up generators; header lines 3-6). Re-checks: gate 3 (codeptr) every hex and decimal ≥ 0x10000 of the nine files against the pin; gate 4 (ifchk) AF0m's TFIB_CONST cells against each of AB01's 50 states; gate 5 (cellcheck) AF0m's file-backed cells against the pin. A decimal below 0x10000 (a page multiplier `ELit 4096` of `4096 * EVar k`, an `EVar k` index, an `a_off` access offset, an entry length) no gate re-checks: it is the collector's or planner's own symbolic-state field, re-derivable only by a collector run; the role is read from the text per occurrence |
| PAGE | 913 | 4096 in a clause naming no image address; every PT_LOAD p_align is 0x1000 (measured) |
| VAR-INDEX | 449 | an index of the proof's symbolic state (`SOff k`, `EVar k`, `epg k`, `ew E k`, `HEn k`, `havoc E k`, `k%nat` …): cgif's PT_LOAD1 page count 109 and the run extents /4 (37) are coincidences |
| STRUCT-OFFSET | 334 | an offset from a run-time base (`T + 2800`, `T + t_cache + 1936`, `SMv + 768`) or a symbolic region field, clause naming no image address, runtime one build |
| DERIVED | 334 | inside `change E with F` / `replace E with F`, E = F re-evaluated (exactly or at 4 sample points) |
| STACK-OFFSET | 151 | a distance below a stack pointer (`sp0 - 2432`, `SOff 2 (-332)`) or a stack-window constant (FP_WIN, VP_WIN) |
| FACT-RANGE | 145 | a bound inside a value fact `mkAF lo hi k` |
| MODEL-CONSTANT | 81 | a named run-time model constant where defined (`class_size kBatchClass = 8192`, `ESTACK = 4096`, path limit 4096, malloc fill 4096) |
| ALIGN | 78 | 1024 / 2048 / 8192 / 32768 as a modulus or factor |
| OBJECT-FIELD | 73 | `B + N` inside a named twin object B, cgif's same-named object of the same size (A_ALLOCATOR + 704 in `__asan::instance`, 3632 bytes) |
| INSN-OFFSET | 37 | `fetch_word (tfib_A_f + N) = Some W`: N inside twin FUNC f, the pin's word at f + N = W |
| RT-ARITH / BOUND | 30 / 29 | an operand / one side of a comparison in a clause naming no image address |
| IMAGE-CELL | 29 | a cell value = the pin's bytes, or past the file bytes AF0m's const cell at that address |
| POW2-EXPONENT | 23 | `2 ^ 37` (the allocator space) |
| LIST-SLICE | 20 | `firstn N` / `skipn N` / `length .. = N` positions in the proof's own lists |
| RT-CELL | 14 | a run-time word inside a twin object of the same size in cgif, no file bytes, no AF0m cell |
| STDOUT-BUFSIZE | 13 | STDOUT_BSZ 1024 = the pin's musl FILE.buf_size at F_STDOUT + 96; the buf object = 1024 + 8 |
| STATE-VALUE | 10 | `ELit / SLit N` at a run-time address (AB01 holds the same ELit) |
| DECODE-IMM | 8 | the immediate field decoded from the stated word W equals N; the pin's word at the fetched pc is W |
| TABLE-COUNT | 3 | `build_table PC N`: [PC, PC + 4N) is a run of whole twin FUNCs (AB1q.v 88 and 324, AB1t.v 1194) |
| IMAGE-SHADOW | 2 | 8192 = IMG_LO / 8 beside the shadow offset |

Hand rows (4): `AD1g.v:1070` (4096 in the dead second arm `|| (change 6217728 with (1482 * 4096); …)`; the series code
commit ac99185f1f10 removes that arm), `AD2a.v:363` (the 4096-byte path limit), `AFjq.v:709` and `:799` (ASan's malloc
fill of 4096 bytes, fill byte 190, at the call returning to 0x327d0 in `__asan::Allocator::Allocate`).

No row is a real kept donor quantity. The count recompute (gate 8) covers what this gate cannot see by value.

## Registered limits (README "Remaining named gaps")

1. A small kept donor quantity whose value is also a right target quantity reads SAME (control 5 shows it).
2. An unnamed run that does not pair is not gated at any size.
3. Function sizes and extents, and quantities of non-allocated sections, are not quantities of this gate.
Gate 8 recomputes every count of lib/A from the image, which covers these three for counts.
