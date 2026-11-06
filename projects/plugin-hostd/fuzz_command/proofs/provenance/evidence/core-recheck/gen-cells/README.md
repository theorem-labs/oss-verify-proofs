# gen-cells: measured triage of the gate rows of the six generated cell files

Unit: plugin-hostd/fuzz_command. Files: lib/A/AF0m.v, lib/A/AE3i.v, lib/A/AD2j.v (key A) and lib/B/YF0m.v,
lib/B/YE3i.v, lib/B/YD2j.v (key B). Gate: port_addr_check 3d2eee813cce, runs RA (key A) and RB (key B), the rows
of these six files from the first triage (RA.gen.tsv, RB.gen.tsv).

## Result

- Flagged rows: 22641 (AF0m 10386, AE3i 517, AD2j 415, YF0m 10388, YE3i 520, YD2j 415).
  Every row has a measured reason. 22641 OK, 0 OPEN, 0 code FINDING.
- Whole files: every numeral the gate reads in the six files (10915 + 563 + 691 per key, 24338 in all) has a rule.
  All 24338 are OK. Each cell of Tfib_const_abs and Tfib_const_shadow is counted against its own image.
- Comment FINDINGs: 3 (comment-rows.tsv), all in lines that the B files copied from the A files. No proof reads a
  comment, so the STOP rule does not apply.

## Inputs (all read-only)

| what | identity |
|---|---|
| ported files | series head plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record); the same bytes in the merged tree 781f46bc05cd (sha256 of each file compared) |
| AF0m / AE3i / AD2j | 5d0364c54727 / 879a68b5b682 / a6d247bd1c98 |
| YF0m / YE3i / YD2j | 334ce661197c / 1d1167146619 / 1d1255fdb75e |
| lib/A/Prog/CmdGlob.v, lib/B/Prog/CmdGlob.v | f2547db2ff96, b0196c8706f9 |
| donor files | cgif_file_fuzzer lib at c8557374ad2e: lib/A/AF0m.v, lib/A/AE3i.v, lib/A/AD2j.v, lib/YF0m.v, lib/YE3i.v, lib/YD2j.v |
| image A | fuzz_command.asan pin c0661b96b5bd, twin 68db792d5fa7 |
| image B | fuzz_command.asan-ubsan pin bbe55d24d096, twin 658cefbe806b |
| donor image A | cgif_file_fuzzer.asan pin 7093581aab04, twin 488e39500746 |
| donor image B | cgif_file_fuzzer.asan-ubsan pin 1c29845fe605, twin ce511d541cda |

Bytes, section headers and segment headers come from the pin. Symbols come from the twin (the same link).

## Commands

`<lib>` is the unit's proofs folder lib/, `<dlib>` the donor's lib/, `<img>` a folder with cmd.A.pin, cmd.A.twin,
cmd.B.pin, cmd.B.twin, cgif.A.pin, cgif.A.twin, cgif.B.pin, cgif.B.twin, `<gate>` the port_addr_check
3d2eee813cce folder (its `sentences()` gives the numeral list the gate judged).

    python3 triage.py --lib <lib> --donor-lib <dlib> --img <img> --gate-dir <gate> \
        --gen-a RA.gen.tsv --gen-b RB.gen.tsv --out .          # triage-rows.tsv, controls.tsv, numerals-*.tsv, run.out
    python3 comments_check.py --lib <lib> --donor-lib <dlib> --img <img> --out .   # comment-checks.tsv, comment-rows.tsv
    python3 plant_got.py --lib <lib> --donor-lib <dlib> --img <img> --out .        # plant-got.tsv
    python3 premises.py <img> > premises.out

Run time: about 15 s for triage.py, under 10 s for each of the others.

## Scripts

- imgmeas.py: image measurements (pyelftools 0.33). File bytes, section and segment headers, twin symbols,
  asan_globals descriptors, auipc-pair references of .text, field loads from a register that holds an object
  (`field_reads`), and names of an address that can be compared across two images (`ident_set`, `end_ident_set`:
  symbol+offset, string bytes, section bound, .got word target or number, .rodata bytes with the functions that
  form the address, jump-table place, padding after an object).
- f0m_rules.py, e3i_rules.py, d2j_rules.py: one rule per numeral place (their docstrings list every rule).
- triage.py: matches each flagged row to its numeral (line and value), writes the row with the rule's result, and
  runs the controls.
- comments_check.py: the numerals of the header comments, each against the file's own image.
- plant_got.py: the class (A) plant control. premises.py: image facts the start-up rules use.

## Rules (reason ids) and flagged-row counts

Key A / key B. The rule text is in the docstrings; the measured values are in each row's `measurement`.

| file | reason | A | B | what is measured |
|---|---|---|---|---|
| F0m | CELL-IMAGE-BYTES | 2590 | 2591 | V = pin bytes at A (little endian), [A, A+w) has file bytes |
| F0m | ADDR-DESCRIPTOR-WORD | 1439 | 1439 | A = 8-aligned word of asan_globals; all 180 x 8 words pinned |
| F0m | ADDR-GUARD-BYTE | 641 | 641 | A in [beg+size, beg+roundup8(size)) of descriptor k; all 641 guard bytes pinned |
| F0m | ADDR-OWNED-RO-BYTE | 521 | 521 | A in an owned range of a read-only PT_LOAD, pinned by no other cell |
| F0m | SHADOW-CELL | 4352 | 4351 | the shadow list = the set recomputed from the 180 descriptors (2194 = 2194) |
| F0m | ZERO-SHADOW-BOUND | 406 | 406 | the j-th run of [0x10000, 0x606000) between poisoned granules (137 = 137) |
| F0m | OWNED-GUARD-RANGE | 360 | 360 | (beg+size, size_with_redzone-size) of descriptor k |
| F0m | OWNED-SAME-AS-DONOR-ROW | 4 | 5 | lo and end named as the donor row's; each .got word of a .got range paired |
| F0m | OWNED-SECTION, OWNED-RODATA-CONST | 2 | 2 | asan_globals bounds; (0x10340, 8) loaded by __asan_stack_free_5 |
| F0m | ADDR-SAME-AS-DONOR-ROW | 15 | 16 | row k at donor row k: the twin names A as the donor twin names the donor's A |
| F0m | ADDR-REAL-SLOT | 12 | 12 | A = start of an 8-byte __interception::real_* symbol |
| F0m | ADDR-FLAG-BYTE, CELL-FLAG-BYTE | 10 | 10 | flags+off read by a byte load of a run-time function; V = that byte of the pinned word |
| F0m | CELL-BSS-GUARD-ZERO | 2 | 2 | guard byte of a .bss global: NOBITS, load value 0 |
| F0m | CELL-STARTUP-AS-DONOR | 1 | 1 | .bss start-up value = the donor's value at the same object+offset |
| F0m | PROG-STATIC | 6 | 6 | g_rec / record.spill / g_quitting: symbol start, descriptor size field (960, 56, 4) |
| F0m | HASH-OF-TR0 | 4 | 4 | tfib_dhash of the file's TFIB_TR0 (Reusable/YF0p.v), mod 2^20 for the buckets |
| F0m | RECORD-BOUND, MODEL-CONSTANT | 6 | 6 | 0xa5000 = page floor of PT_GNU_RELRO; 0x606000 = hull end; 40, 2, 2, 64 = the donor record |
| F0m | RENAMED-SENTENCE, DONOR-HI-AS-SIZE, DONOR-GUARD-ROW-DROPPED | 15 | 15 | UNPAIRED-SOURCE rows: the ported numeral in their place, judged; or a donor guard row of cgif's own globals |
| E3i | RO-CHUNK-BOUND, RO-HI | 517 | 520 | runs of [0x10000, .eh_frame end) minus Tfib_owned_static, cut at the .rodata end (186 = 186) |
| D2j | RO-RUN, RELRO-RUN | 398 | 398 | runs of [0x10000, 0xa5000) and [RELRO page, .data start) minus Tfib_owned_static (186 = 186, 12 = 12) |
| D2j | PROG-STATICS | 16 | 16 | R_A5a: GI_cmdA's five sub-ranges (Prog/CmdGlob.v) and the runs outside cmd_PG, owned ranges, ODR-indicator bytes, __environ |
| D2j | HULL-END | 1 | 1 | R_A9b ends at the hull end |

Most rows are pairing artefacts: 22286 UNPAIRED-PORTED rows (11143 per key) are numerals of generated rows that
have no donor row, and the DIFFERENT-SYMBOL / KIND-CHANGED / NON-ADDRESS-CHANGED rows pair a generated numeral
with a donor numeral of another place (difflib alignment). Rows of note:

- AF0m.v:123 STALE-DONOR-DATA-POINTER 0xa70f8: the number is the donor's address of __asan::asan_thread_registry,
  but here it is the .got word at donor row 86 (donor 0x9ec98). Both words hold 0xfffffffffffff800 (a TLS offset)
  and no auipc pair reads either. The word before each holds 0x1 (read by SetTLSFakeStack and
  __asan_stack_malloc_*), the word after each holds 0x8 (read by the DTLS functions). YF0m.v:124 is the same.
- AF0m.v:239-240 NO-COUNTERPART / STALE-DONOR-CODE-POINTER: cgif's REAL(fclose)/REAL(fopen) rows. This twin has no
  real_fclose / real_fopen symbol; the rows are REAL(strlen) / REAL(strndup) slots (symbols of 8 bytes) and hold
  the image's bytes, strlen+0 and strndup+0.
- AD2j.v:261 KIND-CHANGED 0x5e3740: R_A5a's write window ends at g_rec (the file's header comment says so); the
  donor's window ran to its region end.

## Known-answer controls (controls.tsv, plant-got.tsv)

For every numeral the rule is re-run on value + 4, on the donor's value (the gate's src_value, else the donor
numeral at the same position), and on the value of the neighbouring row of the same block and place.

- Flagged rows, key A (11318 rows; 6 donor rows have no ported numeral to perturb): value + 4 refused 11311,
  accepted 1; donor value refused 152, accepted 0 (28 rows are the same as the donor's, 11132 have no donor
  numeral); neighbour value refused 8031, accepted 0 (3281 have no different neighbour). Key B (11323 rows): value
  + 4 refused 11316, accepted 1; donor value refused 157, accepted 0; neighbour value refused 8036, accepted 0.
- Whole files, per key (12169 numerals): value + 4 refused 12168, accepted 1; donor value refused 317, accepted 0
  (241 the same as the donor's); neighbour value refused 8600, accepted 0.
- The 2 accepted perturbations are ADDR-FLAG-BYTE AF0m.v:2313 0x142ce2 and YF0m.v:2314 0x142862
  (common_flags+0xfa). +4 is common_flags+0xfe, which MemcmpInterceptorCommon also reads by a byte load, and its
  value is also 1 (byte 6 of the pinned word 0x101010101010101). So the perturbed cell is also a true cell. No
  proof names 0x142ce2 or 0x142862 by its numeral (by-use grep of lib/A, lib/B: only the comment of
  Rt/RtStrcmpTbl.v, which says the strcmp proof uses the 8-byte word cells).
- Class (A) plant: each donor-position .got cell moved 8 and 16 bytes down and up, with the image's bytes at the
  new word as its value, and each owned .got range moved one word: 230 plants, 230 refused.

## Premises the start-up rules use (premises.out)

The .bss start-up values that the files keep from the donor (CELL-STARTUP-AS-DONOR, the CVal words of the moved
regions of D2j) are right only if the run-time does the same at start-up in both images. Measured:

- toolchain: `Alpine clang version 20.1.8`, `Linker: LLD 20.1.8` in all four images;
- `__asan_default_options` returns "allocator_may_return_null=1"; `__ubsan_default_options`,
  `__lsan_default_options`, `__asan_default_suppressions` return "" in all four images;
- PT_TLS (filesz, memsz, align) = (0, 20, 8) in all four images;
- __asan::instance 0xe30, builtin_tls 0x200d0, __pthread_tsd_main 0x400, __libc 0x68, common_flags 0x120,
  asan_flags 0x78, stackStore 0x10010, theDepot 0x440010 bytes in all four images.

Start-up pointers are not kept: each points at the same string or object+offset as the donor's (measured).
This slice does not run the start-up code. The AD2j hand-off cut (no CImg byte that a hand-off state of
AB01.v / YB01.v writes differently) is measured only through the bytes the rule cuts (the descriptors'
ODR-indicator bytes and __environ); the 50 hand-off states themselves are not re-read here.

## FINDINGs

Code: none.

Comment (comment-rows.tsv, measured-rows form):

| file | line | old | new | evidence |
|---|---|---|---|---|
| lib/B/YE3i.v | 4 | 0x32340 | 0x3238c | .eh_frame end of fuzz_command.asan-ubsan bbe55d24d096 |
| lib/B/YE3i.v | 4 | 0x246a4 | 0x246e4 | .rodata end of fuzz_command.asan-ubsan bbe55d24d096 |
| lib/B/YD2j.v | 4 | [0x5e3710, 0x5e3740) | [0x5e3290, 0x5e32c0) | R_A5a write window of this file (read_stage end, g_rec) |

YE3i.v line 4 is word for word line 4 of lib/A/AE3i.v, and YD2j.v line 4 is an earlier form of line 4 of
lib/A/AD2j.v: modification lines of the A file, copied into the B file with the A image's values. Line 5 of each
B file states the B values (measured OK). The owner can keep line 4 as history or correct it. All other header
numerals are OK (comment-checks.tsv: 180 registered globals, 172 .rodata globals, 0x2f1ac donor IMG_RO_HI, 50
hand-off states).
