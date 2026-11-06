# G8: kept donor image geometry by value, roundconst v2, over the image B files (gate record)

Proves no function (kind: measurement). Re-run 2026-10-30 on the series base b1afc3e80791 (`run.sh g8`).

## Tool
roundconst.py v2, sha256 `32b39f3b34e97818cd71be57afda15f6aba21ede5fe2d1016f939ede19ac26cc` (its README is the method
of record: quantities, selection policy, controls, named gaps); v1 `8ad299147f2e67fbeb40ee47592152377082e6c55e745a16d9b45b65d84e27b3`
for the controls only. It selects every row G7's checker passes (ROUND-CONSTANT-SAME, SAME-GEOMETRY, NON-ADDRESS-SAME)
whose ported value equals the donor's and equals a donor image quantity (segment / section / symbol-size /
extent-to-next / unnamed run / span / top-extent, each also /2 /4 /8 /4096), and compares the target's quantity of the
same name. The per-object classes read `.symtab` from the unstripped twins (host binaries, not shipped; PT_LOAD table
and allocated sections equal to their pins: roundconst checks it and stops otherwise).

## Command
```
python3 "$RC2" "$WORK/g7/pac3-Y.tsv.gz" \
  "A=$CGIF_BIN/cgif_file_fuzzer.asan:$CGIF_TWIN_DIR/cgif_file_fuzzer.asan,B=$CGIF_BIN/cgif_file_fuzzer.asan-ubsan:$CGIF_TWIN_DIR/cgif_file_fuzzer.asan-ubsan,P=$CGIF_BIN/cgif_file_fuzzer.plain:$CGIF_TWIN_DIR/cgif_file_fuzzer.plain,U=$CGIF_BIN/cgif_file_fuzzer.ubsan:$CGIF_TWIN_DIR/cgif_file_fuzzer.ubsan" \
  "A=$PIN_DIR/fuzz_disco.asan:$TWIN_DIR/fuzz_disco.asan,B=$PIN_DIR/fuzz_disco.asan-ubsan:$TWIN_DIR/fuzz_disco.asan-ubsan,P=$PIN_DIR/fuzz_disco.plain:$TWIN_DIR/fuzz_disco.plain,U=$PIN_DIR/fuzz_disco.ubsan:$TWIN_DIR/fuzz_disco.ubsan" \
  "$WORK/g8/rc-Y"
```
Input: G7's full table (gzip of `$WORK/g7/pac3-Y.tsv`). The same command on the `PIN:TWIN` table of G7 gives a
byte-equal output (cmp): the rows roundconst reads do not change between the two.
cgif twins (sha256): asan `488e39500746...`, asan-ubsan `ce511d541cda...`, plain `6ab540c43108...`, ubsan
`101571498dad...`; fuzz_disco twins as in run.sh.

## Result: 239221 kept rows selected; 3502 not SAME, every one read
| status | verdict of G7 | rows |
|---|---|---|
| SAME | NON-ADDRESS-SAME / SAME-GEOMETRY | 229582 / 6137 |
| MISMATCH | NON-ADDRESS-SAME / ROUND-CONSTANT-SAME | 1353 / 1 |
| MIXED | NON-ADDRESS-SAME / SAME-GEOMETRY | 629 / 1515 |
| NO-COUNTERPART | NON-ADDRESS-SAME | 4 |

Non-SAME by roundconst class (largest): MIXED `segment; segment/2; span; span/2` 1026 and `extent-to-next; segment/2;
span; span/2; symbol-size` 878 (all 4096), MISMATCH `segment/4096` 301 (109 = cgif's PT_LOAD1 page count: EVar 109 of
the hand-off states), `extent-to-next` 212, `extent-to-next/2` 112, `extent-to-next(unnamed run)` 102, `segment/8` 98,
`span` 75, `span/4` 72, `extent-to-next(unnamed run); section; span` 66, `top-extent/4096` 54; 42 more classes.

## Controls (roundconst README, all run; a gate that finds nothing on a plant is broken)
Each plant is a copy of one image B file with ONE numeral set back to the DONOR's numeral at that position (column 11
of the unplanted run), checked with G7's command on that file (`--dst <copy dir> --include <file>`) and an unplanted
copy of the same file, then roundconst v2 (and v1) on both tables.
1. **Donor on donor**: port_addr_check 3d2eee813cce, cgif's lib c8557374ad2e against itself with cgif's four images
   on both sides (`--include 'Y*.v'`, 1449 files paired), then roundconst with cgif's images and twins on both sides:
   504706 kept rows selected, **0 non-SAME**.
2. **Kept donor PT_LOAD length** (rc2): `lib/Reusable/YB1h.v:47` `tfib_res_eq ... (Z_to_bv 64 0x30000, Z_to_bv 64
   0x70000)` -> `0x6d000` (cgif's PT_LOAD1 page length; fuzz_disco's is 0x70000). G7's verdict on the planted value:
   ROUND-CONSTANT-SAME (a pass; the file's flagged count stays 1). v2: **one MISMATCH more** (class `segment; span`,
   PT_LOAD1.pagelen 0x6d000 vs 0x70000); v1: one MISMATCH more.
3. **Kept donor word count** (rc3): `lib/Reusable/YN06.v:513` `unch (201312 + o)` -> `164` (164 = cgif plain
   PT_LOAD2.memsz / 4; fuzz_disco's is 0x7a). G7: NON-ADDRESS-SAME (flags 40 -> 39). v2: **one MISMATCH more**
   (class `segment/4`); v1: no change (no /4 divisor, 0x100 floor).
4. **Kept donor small table length** (rc4): `lib/Reusable/YB01.v:189` `++ seg HS_tfib_11_kn 387 1` -> `212` (212 =
   cgif `__asan::dead_threads_stats` extent / 2; fuzz_disco's is 11). G7: NON-ADDRESS-SAME (2179 -> 2178). v2: **one
   MISMATCH more** (class `extent-to-next/2`); v1: no change.
5. **Gap control** (rc5): `lib/Reusable/YE37.v:35` `(0xa5160, 3136, [` -> `192` (192 = cgif's `.asan_globals` size;
   fuzz_disco's is 3136; 192 is also `__lsan::suppression_placeholder`'s extent in both). G7: NON-ADDRESS-SAME
   (1171 -> 1170). v2: one **SAME** row more, no non-SAME change, as the README's named gap 1 states; v1: no change.

## Per-row triage: `G8-rows.tsv` (written by `rc_triage.py` from roundconst's output; re-derived by run.sh, cmp)
One row per non-SAME row: class, rule, status, key, file:line, value, roundconst class, the measured fact, the text
read around the numeral. A row takes the FIRST rule (rc_triage.py, in order) that holds; a rule that rests on an image
fact measures it on the pins and twins and holds only when it agrees. Classes: GENERATED (the file is written by a
start-up generator from fuzz_disco's own image, re-checked by a gate of this directory), ROLE (the numeral's role,
read from its sentence, is not the donor quantity it equals), DEFECT (a donor quantity kept where the target's differs:
none). Result: **0 UNTRIAGED, 0 DEFECT** (rc_triage.py exit 0).

| rule | rows (MISMATCH / MIXED / NO-COUNTERPART) | files | what holds, and the measurement |
|---|---|---|---|
| PAGE-4096 | 1881 (0 / 1881 / 0) | 158 | 4096 used as the page size (alignment, x / 4096, round up, pages to bytes, one-page lengths, the first page above the null page, page masks, PGSZ) or another 2^12 constant (GIF LZW's 4096-entry table, PATH_MAX, errno < 4096); measured: every PT_LOAD of both pins has p_align 0x1000, and 4096 is also the target's own value of most of its donor names: key A 14 of 23 (the others PT_LOAD2.pagelen/2 and spans), key P 22 of 26 (the others spans); on B and U all agree, so no B / U row is selected |
| VAR-INDEX | 401 (397 / 4 / 0) | 49 | index of a symbolic variable / value / atom of the abstract state (EVar n, SOff n k, ew E n, (n%nat, fact), fresh-variable arguments); for EVar 109 (YB05, YD1*): `(EVar 109)` occurs 299 times in YB01.v, the states the collector wrote from fuzz_disco's image |
| COLLECTOR-STATE (GENERATED) | 349 (348 / 1 / 0) | 2 | YB01 (50 hand-off states) and YB03 (join state): written by the start-up collector run on fuzz_disco and hsform.py; re-checked by YB1m startup_cert in the kernel, G4 ifchk, G6 kimg_overlap, G3 codeptr |
| ARITH-STEP | 127 (79 / 48 / 0) | 37 | a constant of an arithmetic identity (`change (E) with N`, `replace (E) with (F)`, `assert (L = R)`); measured: both sides evaluate equal (constants from the lib's own Definitions), or agree at sample points (closed by lia) |
| BASE-OFFSET | 125 (60 / 65 / 0) | 39 | byte offset from a run-time base (CTX, T + 80 i, ly_F, ms_debruijn, shadow_off, ...); offsets from CTX measured within the target's `__malloc_context` (size 928) |
| CODE-OFFSET | 99 (85 / 11 / 3) | 13 | `fetch_word (tfib_A_f + N) = Some w`: measured, f + N lies in f in the twin and the pin word there is w |
| STACK-OFFSET | 82 (78 / 4 / 0) | 12 | offset from sp (sp0 - N, SOff 2 (-N), regions based at x2); the immediate's occurrences in the pin .text given |
| ALLOC-MODEL | 64 (13 / 51 / 0) | 21 | allocator model constants named in the sentence (size classes, redzones, max_cached, batch, bounce caps 100 / 150, KMmap lengths) |
| SYSCALL-NO | 62 (62 / 0 / 0) | 10 | RISC-V Linux syscall number in a7 (214 brk, 222 mmap, ...); measured: `addi a7, zero, N` in the pin .text |
| NAMED-CONST | 59 (31 / 28 / 0) | 19 | named model constants (VF_STK, ALLOC_STACK, FILE_BUFSIZ, ...), the donor's same-named definition and the immediate's occurrences given |
| REGION-OFFSET / FIELD-TABLE | 45 / 31 | 11 / 18 | offsets relative to a region's symbolic base / field offsets of a run-time structure |
| TEST-DATA / FUEL | 34 / 22 | 4 / 6 | inputs and expected values of executable Examples; fuel of vm_compute runs |
| LZW-384 | 29 (29 / 0 / 0) | 3 | 384 = 12 * 2^32 / 2^27 of the LZW output-size formula (YCbw.v states it); measured by evaluation |
| CHAR-CODE | 14 | 9 | a byte of a string literal; measured: the list decodes to printable text |
| SPEC-BOUND / SYM-LITERAL / ARGC-BOUND | 13 / 12 / 8 | 9 / 5 / 6 | bounds of a precondition or comparison on a run-time quantity; literals of the abstract machine state; argc <= 1024 |
| INSN-IMM | 9 | 6 | branch / jal immediate of a decoded word; measured: the word decodes to that immediate |
| MODEL-PC / TP-OFFSET / MASK / STACK-LIMIT | 7 / 4 / 4 / 4 | 3 / 4 / 2 / 1 | routine-relative pcs below the image base; errno's offset from the thread pointer; alignment masks -2^k; 8 * 1024 * 1024 |
| FRAME-SIZE | 3 | 3 | measured on the pin: MC_FRAME 2240 = the frame of printf_common; VF_STK's 912 = the frames of vfprintf (368) + printf_core (544) |
| CODE-WINDOW / SIZE-CLASS-TABLE / OBJECT-END / MMAP-BOUND / PAGES / GIF-TRAILER / POW2-EXP | 2 / 2 / 1 / 1 / 2 / 2 / 1 | | measured: build_table windows cover whole functions of the twin; musl size_classes entries read from the target's `__malloc_size_classes`; 0x51938 + 1024 = the end of the object `buf`; MMAP_THRESHOLD + IB + UNIT = 131072; 2 * PGSZ; the GIF trailer byte 0x3B; 2 ^ n |
| HAND | 3 | 2 | YG0s.v:787 (a divisibility witness q * 1024 in shadow arithmetic), YP08.v:288 (atom 3 = argc, range [1, 1024]) |

## Registered limits of roundconst v2 (its README's named gaps)
1. A small kept donor quantity whose value is also a right target quantity reads SAME (shown by control 5).
2. An unnamed run that does not pair is not gated at any size.
3. Function sizes and extents, and quantities of non-allocated sections, are not quantities of it.
G9 (count recompute) covers the counts these leave. The status says the value equals a donor quantity whose target
counterpart differs, not that the numeral is that quantity: hence the per-row reading above.
