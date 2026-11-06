# Value checks of libdiginet/fuzz_transport's image-A core on the run of record

proves no function (kind: measurement). The value lane: gate (c) (by-value check, atable core side), the section cells, the
stated memory values, the .got words, the four compensating checks of port_core's registry entry, the symbol + offset sweep
and roundconst-gate v2, each with its planted control. Method: libdiginet/fuzz_decode's checks of record
(checks/decval-A.sh, decval.py, decval_extra.py, decval_hand.py, atable-A.sh; decval-A.sh sha256 58524d54aa5f, decval.py
b0b5ced070ea, atable-A.sh e70b2029bec9; internal records) with the pins,
names and trees changed, plus the checks the registry entry of port_core d9e0589898fd requires (`run the registry entry's
FOUR CHECKS on every output`: recompute every kept image-derived count from the target's own headers; check every GOT[0]
cell; check shadow offsets and model constants by role; confirm every no-twin drop against the target symtab) and the
symbol + offset sweep of the registry's `KNOWN LIMIT, ALL RELOCATION TOOLS` entry.

## Command

    checks/run-all.sh WORK LIB OUT/values        (run by checks/run-gates.sh; records/run-gates.txt has its exit status and time)

WORK = work-rec5 (the run of record), LIB = the run's lib (T3r's cut start-up layer). Script sha256 and the decisions
file: records/RESULTS.txt line 3 (decval.py cf8670c113f1, decval_extra.py 58a00e492ae6, decval_hand.py 6b25010288f8,
decval-A.sh 4859ddab2d36, ..., run-all.sh c7e5b4471bb5, compcheck-decided.tsv eb7c648644ea). RESULTS.txt line 2 gives the
trees in its own form (sha256 of the sorted list of A/ and Reusable/ paths without `./`): stage-out 00c62e8a18a3, stage
ed4d18586a03, the same 492 files as records/run-of-record.txt's 3df9dee2b44d / cb94de36d3c6. Tools: start-up set
2026-10-30d (atable e88affcf0526 by its frozen-run.sh), atable 1ce98fbad397, roundconst-gate 32b39f3b34e9, each from the
tool registry (its README.md, sha256 05596ed48d98; internal record) and sha256-checked. Every step exits 0 (`== N rc=0`,
records/RESULTS.txt).

## Results (records/RESULTS.txt, each with its control)

| item | result | control |
|---|---|---|
| 1 by-value (decval-A.sh; decval.txt, decval-hand-rows.tsv) | 492 files (A 370, Reusable 122), 8655 numerals in [0x10000, 0x616001); classes TARGET 3258, OTHER 4812, SHARED 584, DONOR-STALE 1; `DONOR-STALE after the look by hand 0` (Reusable/YG0f.v:34 kNodesBlockSize 0x100000, a constant unchanged from the donor text); stage 2 NO TWIN 24: 2 decided by their 8 bytes (A/AE39.v:32, A/AE3a.v:17, 0x8080808080808080 once in the target .rodata), 22 open, each read by hand below; .got rows wrong 0, constant rows changed 0 | tfib_at_x_memset set to grant's 0x95e30: `stage-1 DONOR-STALE 1 -> 2; changed rows 1`: PASS |
| 1b section-bound cells (secbounds.txt) | 22 cells: OK 22, KNOWN 0, DIFF 0 | tfib_data_hi set to grant's .data end 0xa1120: `DIFF rows 0 -> 1`: PASS |
| 1c stated memory values (cellvals.txt) | 145 file-backed statements: SAME 145, DIFF 0; 165 in .bss (run-time values) | A/AD20.v:49 a stated value + 1: `DIFF 0 -> 1`: PASS |
| 2 atable, core side (atable.txt) | stage-out/A/AB1w.v's 26 tfib_at_* rows vs the twin's fields: 0 differ; the fields from AB1w.v equal the twin's (28); atable 1ce98fbad397 = e88affcf0526 on the twin (28 fields); donor: 0 of 28 differ (AB12) and 0 (AB1w) | plant-row x_memset -> grant's: 1 row differs; plant-tab musl_memset A / E -> grant's: x_memset differs: PASS, PASS |
| 3 .got words (gotwords.txt) | the whole .got: 427 words, 0 hold another symbol + offset at the same offset; 167 core numerals in .got over 20 cells, all GOT-SAME; 60 stated cell values = the bytes; check.tsv got-value 182 / got-word 165 SAME; OK-GOT0: GOT[0] 0xa4030 holds 0 (no .dynamic), named by 2 rows, both right | 3 planted lines, each caught, 0 findings elsewhere: PASS |
| 4 compensating checks (compcheck.txt, compcheck-rows.tsv) | (a1) 264 kept spans beside moved partners SAME; (a1b) 122 code ranges SAME; (a2) 454 kept numerals equal to a differing donor quantity, all decided by hand (449 no image role, 5 the same quantity); (a3) port_core's derived counts: GEO-SAME 114, DERIVED-SAME 3, KNOWN 1 (the AD1g dead arm), NOT-A-NUMERAL 1, DECIDED-PATCH-REWROTE 5; (b) OK-GOT0; (c1) 3437 numerals >= 0x7fff0000: CONST-SAME 3405, SHADOW-SAME 14 + 9 kept, DECIDED-UNIT-BOUND 9 (CZONE); (c1w) 5 format windows exact; (c2) 12477 operands and 2375 multipliers unchanged, 7 multipliers moved as the image-top page count; (c3) 1239 arithmetic constants unchanged; (c4) YG0f.v 180 numerals unchanged; (d) 22 dropped function-table rows, 0 in the target symtab. `FINDING rows 0; open CANDIDATE rows 0; open AMBIGUOUS rows 0; rows decided by hand (--decided) 468` | 8 plants, each caught, 0 new open rows elsewhere: PASS |
| 5 symbol + offset (symoff.txt, symoff.tsv) | SYMBOL 914, BYTES 288, GOT-CELL 167, GEOMETRY 86, CODEREF 26, OTHER-SYM 21, UNALIGNED 2, KNOWN 1; `rows that land in .got / .got.plt or on a symbol other than the donor's twin: 24 (1 of them known to the owner and handled, 23 new)`: the same 22 positions as item 1's open rows (measured: the two lists are equal) and the 2 numerals of the comment line g-AD2f.patch adds at A/AD2f.v:149, each read by hand (records/symoff-hand-rows.tsv) | `__sanitizer::PageSizeCached` -> its .got word, `__asan::instance+0x2b0` moved by the address delta: exactly these 2 findings: PASS |
| 6 roundconst-gate v2 (roundconst.txt) | R1 (the run's gate-raw.tsv): MISMATCH 371, MIXED 217, SAME 127850 + 47 moved; R2 (the lane's report, --all-verdicts): MISMATCH 361, MIXED 783, SAME 120452; 1732 non-SAME rows | PR1 tfib_at_rw_len written back as grant's 0x55c000 and PR2 a synthetic kept 83: 2 new MISMATCH rows: PASS |

## Rows decided by hand on the run of record

- Item 1, the 22 open stage-2 rows (records/decval-open-rows.tsv): A/AB1w.v:11 tfib_rodata_hi 0x22b4c (the pin's .rodata
  end, port_core 83f5203d2a2f item 97); 16 A/AD1o.v rows and 3 A/AD25.v rows, each an end, the start + 0x20 or a quotient by
  8 of the zero-shadow piece the lemma takes (METHOD.md item 2); A/AFem.v:129 and :207 TOT_range 127008 (METHOD.md item 3).
  22 RIGHT, 0 open. The open rows are the same 22 as on the earlier run work-rec2 (file:line, donor and written value;
  measured: equal lists).
- Item 5, 24 rows (records/symoff-hand-rows.tsv): the 22 positions of item 1 with the same decisions, and A/AD2f.v:149
  0x5df080 and 0x5f3060, the numerals of the comment g-AD2f.patch adds: g_cfg and OW, the first and last of the 18 writable
  harness globals, at those addresses in the twin's symtab and asan_globals (records/ghunks-asan_globals.tsv). 24 RIGHT.
- Item 4, records/compcheck-decided.tsv: 468 rows decided by hand (a row applies only where part, file:line and written
  value are unchanged). 15 were added on the run work-rec2: A/AFem.v:207 `32`, the exponent of `0 <= STD < 2 ^ 32` (the
  decision of A/AFem.v:343; the line qualifies only because the TOT override moved a numeral on it); 5 A/AD1o.v a3 rows
  whose derived value bss-zero-range.patch rewrote (the line holds 779840, 6238688, 779836, 17860 of the piece [0x5f31e0,
  0x616000)); 9 c1 rows, the CZONE bound 0x800b9c00 (METHOD.md item 1). On the run of record one row moved with its line:
  a2 A/AD2f.v:156 `208` is now A/AD2f.v:161 (g-AD2f.patch adds 5 lines above it; the line text is byte-equal), with the
  same decision; all 468 apply (`rows decided by hand (--decided) 468`, 0 open).
- Item 6: the 1732 non-SAME rows of this run are each a row of the dry run's 1751 (work2) with the same run, status, file
  and value (measured: 0 keys (run, status, file, value) of this run are not in the dry run's set; the line differs only in
  the G-patched files A/ACfn, AD1r, AD1w, AD2f, whose lines the G patches shift). records/roundconst-read.txt is the
  reading by hand of each value, by value with each shape of context: 0x10000 (IMG_LO, the same in both), 0x20000 (the
  allocator 2^17), R_A3 832, word counts 633 / 1146 (item 4 a1b SAME), and otherwise model constants, stack frame sizes
  (0xd0 = 208), struct and frame offsets, symbolic variable ids, character codes. None is a kept image-derived count of the
  donor.

## Changes to the dry run's scripts for the run of record

- decval_hand.py section 4: an address outside its image's loaded bytes (A/AD25.v's donor 0x5fa000 is fuzz_grant's image
  top, past its last loaded byte 0x5f93b0) made the step crash (AttributeError at the 8-byte read); it now leaves the row
  open with that reason.
- decval-A.sh exits 1 when any step or its summary fails (the crash above had left decval.txt without its result lines and
  an exit 0); run-all.sh exits 1 when a step fails; compcheck-A.sh refuses to run without compcheck-decided.tsv (it reads it
  from records/ beside it, else ../records/, the slice's layout).
- No script writes a host path: the image trees, the donor lib and the evidence dir are the named variables P, PG, DON, EV.

## Measured limits

- The a2 and roundconst decisions are by reading: a by-value test cannot separate a coincident low value from a count
  (the roundconst README, gap 1). a1 / a1b decide spans and code word counts mechanically.
- symoff's BYTES and CODEREF rules decide unnamed .rodata data by content and by the code that forms its base; a by-address
  move onto an unrelated location with the same 16 bytes found once would pass (the two planted shapes are caught).
