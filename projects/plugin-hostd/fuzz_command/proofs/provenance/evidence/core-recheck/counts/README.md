# counts: every image-derived count of the relocated core, recomputed from our images

plugin-hostd/fuzz_command, relocated core (lib/A/A*.v, lib/B/Y*.v, lib/A/Rt, lib/B/Rt, lib/Reusable), series head
plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record). rule 24: no function proved. No .v file was changed. Check of record for addresses stays the value gate
port_addr_check 3d2eee813cce; this slice recomputes the COUNTS (word and instruction counts, table lengths, sizes,
region lengths, page counts, shadow lengths, descriptor counts, quotients in proof steps) and the section / segment
bound cells, which a value-gate pass does not prove.

## Result

| | rows |
|---|---:|
| candidates | 12,462 |
| SAME (recomputed from our image, equal) | 2,633 |
| DIFFERS (FINDING) | **0** |
| NOT-IMAGE-DERIVED (reason in the row) | 9,829 |

- FINDINGs: none. Code-commit list: empty. measured-rows.tsv: header only. No STOP-rule message was needed.
- Every row of counts.tsv names what it measured: for SAME, the expression, the image and the command that prints it;
  for NOT-IMAGE-DERIVED, the rule and the reason.

| area | SAME | NOT-IMAGE-DERIVED |
|---|---:|---:|
| lib/A/A*.v | 911 | 1,974 |
| lib/A/A*.v, generated files | 163 | 1,627 |
| lib/B/Y*.v | 913 | 1,959 |
| lib/B/Y*.v, generated files | 160 | 1,627 |
| lib/A/Rt | 120 | 345 |
| lib/B/Rt | 116 | 350 |
| lib/Reusable | 250 | 1,947 |

Generated files (written whole by the unit's generators from our image): A AB01 AB03 AF0m AD2j AE3i ACej AB1w, and
their B twins.

## Images (role, pin sha256, twin sha256, first 12)

| key | image | pin | twin |
|---|---|---|---|
| A | fuzz_command.asan | c0661b96b5bd | 68db792d5fa7 |
| B | fuzz_command.asan-ubsan | bbe55d24d096 | 658cefbe806b |
| P | fuzz_command plain (the `src0` build of lib/Reusable files) | a20873dc7f0e | fbe3a48ad296 |
| dA | cgif_file_fuzzer.asan (donor) | 7093581aab04 | 488e39500746 |
| dB | cgif_file_fuzzer.asan-ubsan (donor) | 1c29845fe605 | ce511d541cda |

A file of lib/A is measured in A, lib/B in B. A lib/Reusable file is measured in the image its own `images Require`
line names, in P when it names the plain build's segments (src0), else in both A and B. img/ holds local copies of
the plain pin and twin used by the run (sha256 above); the other images are the check's shared copies.

## What was run

    python3 enumerate.py LIB DONOR_LIB RUNS IMG candidates.tsv
    python3 recompute.py LIB DONOR_LIB RUNS IMG PLAIN_IMG          # writes counts.tsv, recompute.log, controls.tsv
    python3 recompute.py --img A --expr "(sec('.text').hi-sym('sysconf').addr)//4" IMG PLAIN_IMG   # one quantity
    LIB=... python3 recompute.py --chunk "A/AD2j.v R_A1j: mkChunk 118583 (CImg 16113)"           # one GEN-CHUNK row

LIB = proofs/plugin-hostd/fuzz_command/lib at plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record); DONOR_LIB = proofs/cgif/cgif_file_fuzzer/lib at
c8557374ad2e; RUNS = the gate runs RA, RB, RU of port_addr_check 3d2eee813cce (full.tsv); IMG = the A, B, dA, dB
copies (cmd.A.pin, cmd.A.twin, ... cgif.B.twin); PLAIN_IMG = img/. pyelftools 0.33. enumerate.py and recompute.py
each finish in under a minute on a free machine.

Files: enumerate.py (candidates), imgq.py (image quantities, pyelftools), recompute.py (rules, output, controls),
judgments.tsv (the hand judgments, one row per settled pattern or row, with its reason), candidates.tsv,
counts.tsv, recompute.log (one line per recomputed quantity), controls.tsv, measured-rows.tsv.

## Enumeration (enumerate.py; a row can come from several sources)

| source | rows | what |
|---|---:|---|
| a | 8,813 | gate rows of RA, RB, RU: src_class GEOM or EXTENT; SAME-GEOMETRY, GEOMETRY-CHANGED, ROUND-CONSTANT-SAME, IMAGE-EXTENT-*; NON-ADDRESS-CHANGED with value >= 2; NON-ADDRESS-SAME whose value is a donor quantity that differs in our image |
| b | 538 | Definition / Let / Notation / record field named count, len, length, size, n, num, words, pages, bytes, top, end, hi, lo, span, cap, bound with a literal value (symbol cells *_A_ / *_E_ / *_D_ left to the gate's named-symbol rule) |
| c | 1,488 | numerals equal to a DONOR image quantity whose value in our image differs or is absent: header quantities and their /4, /8, >>3, /4096, ceil /4096 forms; object and function sizes (and /4, /8) from the donor twin; asan_globals / 64, .got / 8, .init_array / 8, .fini_array / 8 |
| d | 394 | comment numerals next to a count word (instructions, words, bytes, entries, descriptors, globals, ...) |
| e | 912 | region lengths over named image objects (`X <= a < X + N`, `(X, X + N)`, `(X, N)`, `img_covered`), `change (.. / 8 ..) with N` |
| t | 386 | the word count N of every code table range: `build_table SEGS START N` and `(START, N%nat)` range-list entries |
| s | 1,665 | lib/A/A*.v and lib/B/Y*.v: every numeral >= 64 KiB equal to a section, PT_LOAD, TLS, RELRO, PT_PHDR or EH_FRAME bound, the image base or the image top of our image or of the donor image |

Source c leaves out powers of two and symbol sizes under 256 bytes, and takes a header value from 16 to 255 or the
descriptor count only with a count word within 40 characters (below that a value matches some donor quantity in
almost every file by chance). Small counts are reached by sources a, b, d, e, t instead. lib/Reusable/YH03.v is left
out (a file another check owns; 19 rows).

## How a row is settled (recompute.py; the first rule that applies)

SAME / DIFFERS (value checked against a recomputed quantity):

| rule | rows | what it measures |
|---|---:|---|
| ANCHOR-MOVED | 1,068 | the donor numeral at the gate-paired place is quantity Q of the donor image (header quantity or form, symbol start / end / size, descriptor count, symbol + offset of a same-size symbol, a .rodata string + offset, or the ASan shadow address of one); ours is the same Q of our image |
| MANUAL (expression) | 484 | a judgments.tsv row: the quantity read from the file and its use, as an expression over our image (symbol sizes, prologue frame sizes, string bytes, asan_globals records, section headers) |
| IMAGE-BASE | 472 | 0x10000 written in hex or as a range bound: the first PT_LOAD start rounded down |
| TABLE-DONOR | 252 | a code table count: the donor range's two ends named by the donor twin's symbols, the same names in our image, (end - start) / 4 |
| TABLE-FUNC | 76 | a table range of lib/*/Rt that starts and ends at our function bounds |
| OUR-HEADER / KEPT-HEADER | 74 | a value >= 64 KiB that is a header quantity of our image (unchanged in the donor, or with no donor numeral) |
| QUOTIENT / STEP-ARITH | 87 | `change (X op Y) with N` where X is an address or header quantity of our image |
| SECTION-BOUND | 52 | a cell named for its section (`tfib_rodata_hi`, `TFIB_TEXT_LO`, `tfib_img_hi` ...) against our pin's section header |
| GEN-CHUNK | 24 | a pair restating a chunk of IMG_REGIONS in the generated lib/A/AD2j.v (lib/B/YD2j.v) |
| IMAGE-CELL | 16 | a start-up cell `zN (ANum ADDR) V` in read-only memory: V is our image's N bytes at ADDR |
| TWIN, LEN-ANCHOR, AGLOBAL-ROW, AGLOBAL-BEG, REGION-SIZE | 28 | the twin file's expression in this image; a (start, length) pair whose two ends map by symbol or string; a row of the generated destructor table against our asan_globals record; an object size |

NOT-IMAGE-DERIVED (the reason column says what the numeral is):

| rule | rows | what |
|---|---:|---|
| PAGE-SIZE | 3,090 | 4096, the model's page size (p_align of every PT_LOAD of our images is 0x1000) |
| MANUAL:GENSTATE | 2,765 | a value of a start-up hand-off state in A/AB01, A/AB03 and their B twins: the unit's collector computed it by running the checker over our image (machine-generated, written whole; not a port_core copy). Not a closed-form image quantity; this check does not rerun the collector |
| MANUAL (pattern or file judgment) | 2,336 | judgments.tsv patterns: register and slot numbers, list positions, allocator / musl / FakeStack / process-layout constants, frame offsets, errno and word widths, power-of-two arithmetic, cited line numbers, dates, stack-budget sums |
| POW2-16 | 570 | 65536 written in decimal in model arithmetic |
| ROLE-* | 600 | context roles: symbolic-state literals and indices, alignments and scale factors, allocator constants, stack offsets |
| LITERAL-ARITH | 172 | arithmetic of literals that are no address or size of our image |
| FIELD-OFFSET | 103 | an offset from a named address that stays inside the object there (instruction offsets in a function, struct fields) |
| ADDRESS, CELL-ADDRESS | 65 | an address in our image (a pc where a walk stops, a return site, a start-up cell address): the gate's domain, not a count |
| TABLE-PREFIX | 46 | a chosen part of one function in a table range; measured that it fits in the function |
| NO-QUANTITY | 42 | a value that is no quantity of our image or of the donor image (catalog: header quantities and forms, symbol starts / ends / sizes, descriptor counts) |
| GEN-CHUNK-FIT, START-UP-VALUE | 40 | a cut of the generated region list (measured: inside one PT_LOAD of our image); a value start-up code writes into writable memory (our image holds another value there) |

Pattern judgments (judgments.tsv rows for any file and any value) never settle a value between 64 KiB and the image
top as NOT-IMAGE-DERIVED unless the row is marked so (`!`): such a value can be an address or size of the image, so it
is left to the measuring rules.

## Known-answer controls (controls.tsv)

- Every SAME row re-judged with value + 4: 2,633 of 2,633 refused (the recomputed quantity is the original value).
- Every SAME row re-judged with the donor's numeral: 1,297 refused, 0 accepted; 1,336 rows have no donor numeral, or
  the quantity has one value in the donor image and ours (image base 0x10000, a function of the same size), so the
  donor value cannot test them.
- NOT-IMAGE-DERIVED rows re-run through their own rule with value + 4: 4,748 refused (value-specific rules: PAGE-SIZE,
  POW2-16, value-specific judgments); 5,081 settled again (context rules: they read the slot the numeral stands in,
  not the value). The context rules carry the guard above.
- Cross-check of the context rules: the NOT-IMAGE-DERIVED rows whose value equals a donor image quantity that has a
  different value in our image (2,032 rows: where a kept donor quantity of the catalog kinds would show) were read in
  context, group by group. All are coincidences: allocator and musl struct offsets, slot and register numbers, stack
  offsets, FakeStack constants, instruction offsets inside musl memcpy, and hand-off state values.

## Observations (not FINDINGs)

1. The port corrected three donor counts and one donor bound to our image: lib/A/AB1v.v tfibmusl_text_count (donor
   16403 ran 12 bytes past the donor's .text end; ours 16397 = .text end - sysconf, / 4), lib/A/AB12.v TFIB_TEXT_N
   (donor 111012 stopped 0x90 bytes short of the donor's .text end; ours 115951 = .text size / 4), lib/A/AB1w.v
   tfib_text_hi (donor 0x9ca00 was its TLS start; ours 0xa46fc = .text end) and tfib_rodata_hi (donor 0x2278c is not
   the donor's .rodata end 0x227cc; ours 0x246a4 = our .rodata end). The B twins agree with B's headers.
2. lib/A/AE34.v musl_sel_ranges keeps the wrapper block at its full length, 46 entries (__wrap_strlen to the end of
   __wrap_atoi); the donor's range had 38. The file's header says so. Recomputed SAME.
3. lib/Reusable/YK09.v defines records ASAN and BOTH of an image that is none of the unit's builds (img_hi 0x671000),
   kept from the donor with module paths only. A by-use search over lib/ finds no use of ASAN, BOTH, asan_init or
   both_init outside their own definitions (28 rows, NOT-IMAGE-DERIVED with that reason).
4. lib/B/YE3i.v line 4 is the A file's provenance line (IMG_RO_HI = 0x32340, A's .eh_frame end); line 5 states B's
   value 0x3238c. Both recomputed SAME in their own image.
5. lib/B/Rt/RtDStrdupS.v says "the 24 instruction words": the file has 24 distinct fetch_word facts (11 at
   0x4cd84..0x4cdac, 13 at 0x4cf98..0x4cfc8); its range table holds 12 + 13 = 25 words, the last of the first range
   without a fact. Consistent.
6. lib/A/AD25.v and lib/A/AD1o.v: the zero-shadow ranges end at g_rec's object end (0x5e3b00) and restart after the
   last instrumented .bss global's redzone (0x5e3c80); the donor had no instrumented .bss global and ran to its image
   top. Recomputed SAME from the asan_globals records (B: 0x5e3680, 0x5e3800).

## Limits

- The hand-off states of A/AB01, A/AB03 and their B twins (2,765 rows) are generator outputs; they are listed, not
  recomputed. Their image-header values (image top, page counts, descriptor counts) are recomputed by the anchor rules
  where the state holds them.
- GEN-CHUNK-FIT checks only that a generated region chunk is image memory; the chunk cuts are the generator's.
- Addresses are the gate's: rows that turned out to be addresses carry ADDRESS / CELL-ADDRESS, or SAME where the
  address moved by symbol or string from the donor's.
