# port_core d9e0589898fd second view: d9e0 stage-out against the runs of record (plugin-hostd/fuzz_command)

Unit: plugin-hostd/fuzz_command. Paths are relative to the unit's proofs folder (lib/A/AB1w.v). Images by role and
sha256 (first 12): donor cgif_file_fuzzer.asan 7093581aab04 (unstripped twin 488e39500746); ours fuzz_command.asan
c0661b96b5bd (twin 68db792d5fa7), fuzz_command.asan-ubsan bbe55d24d096 (for lib/B only). Our tree:
plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record); merged tree: commit 781f46bc05cd.

## What was compared

port_core d9e0589898fd was re-run `--dry` on the inputs of the two untagged runs of record (donor lib at c8557374ad2e):

| set | files | run of record | d9e0 run |
|---|---|---|---|
| A1 | 377 lib/A files (core) | stage-out of port_core blob bebe64d6f526 | rc 3 (cell gate FAIL rows on AF0m; 12 generated slots) |
| A2 | 14 lib/A runtime files (AE2q AE2r AE6k..AE6v) | its stage-out, then 48 hand values (hand.tsv) | rc 3 |

The two runs staged the same donor text: A1 376 of 377 staged files are byte-equal, the one difference is
lib/A/AD2l.v:86 (TfibB_pair renamed CmdB_pair by d9e0's rename); A2 differs only by the rename target of TfibSyms
(CmdSyms in d9e0's command line, CmdBSyms in the run of record; our tree defines Record CmdBSyms in lib/A/AF0m.v:5394).

## Commands (names relative; host wrappers only fill in the paths)

```
python3 d9e0_diff.py --set A1 --old-out <A1 run-of-record stage-out> --new-out <A1 d9e0 stage-out> \
  --ours <our lib> --merged <merged lib> --files-out files.tsv --rows-out rows.raw.tsv --agree-out agree.tsv
python3 d9e0_diff.py --set A2 ... (same, A2 inputs, appends)
python3 d9e0_triage.py --rows rows.raw.tsv --stage A1=<d9e0 A1 stage> --stage A2=<d9e0 A2 stage> \
  --work A1=<d9e0 A1 work dir> --work A2=<d9e0 A2 work dir> --ours <our lib> \
  --old-img <cgif_file_fuzzer.asan 7093581aab04> --old-syms <twin 488e39500746> \
  --new-img <fuzz_command.asan c0661b96b5bd> --new-syms <twin 68db792d5fa7> \
  --hand HAND.md --hand HAND-walks.md --hand hand.tsv --gate <gate run RA full.tsv> \
  --slots AB01,AB03,AB05,AB12,AB1h,AB1k,AB1m,AB1v,AD1k,AD2i,AD2j,ACej \
  --generated AB01,AB03,AF0m,AD2j,AE3i,ACej,AB1w --out rows.tsv --controls controls.tsv        # pass 1
python3 d9e0_manual.py --rows rows.tsv --ours <our lib> --donor <donor lib> --old-img ... --old-syms ... \
  --new-img ... --new-syms ... --out manual.tsv
python3 d9e0_triage.py ... (same as pass 1) --manual manual.tsv                                    # pass 2 -> rows.tsv
python3 d9e0_secbounds.py lib/A/AB1w.v <fuzz_command.asan c0661b96b5bd> lib/B/YB1w.v <fuzz_command.asan-ubsan bbe55d24d096> \
  (also the merged tree's two files, and the donor's A/AB1w.v and YB1w.v against their pins as known answer) > secbounds.out
```

Script sha256 (first 12): d9e0_diff.py 33898be1f5d6, d9e0_triage.py 7022b7ec6ddc, d9e0_manual.py a62df8742503,
d9e0_secbounds.py ce4b767f8f1c. `--slots` is d9e0's own list ("generated slots applied: 12" in its log); `--generated`
is the unit's generator list. The hand notes are the relocation run's hand-resolve tables (HAND.md, HAND-walks.md) and
the runtime run's hand values (hand.tsv); a row is `patched/HAND-NOTE` only when a table row names the file, the old
value and our value.

## Method

1. files.tsv: per file the sha256 of the run-of-record stage-out, the d9e0 stage-out, our file and the merged tree's
   file, and equal/differs for old vs d9e0, ours vs old, ours vs d9e0, ours vs merged.
2. rows.raw.tsv: the two stage-outs are aligned by line on numeral-blind text (every hex or decimal numeral and every
   `port_core_refused_<x>` marker replaced by one placeholder), so the provenance header and renames never shift the
   alignment; then numerals are compared position by position. Our line is found the same way (exact numeral-blind
   match, else block position, else most similar line); our token is the one at the same index, else the one with the
   same numeral-blind context. A Coq lexer pass marks comment positions (code_or_comment column).
3. rows.tsv: every differing row gets a class and a measured reason. The donor value is read from d9e0's stage file
   (donor text) at the same place. A row is settled only when our value and the donor value resolve to the same thing
   in their own image: SAME-SYMBOL (symbol+offset in both twins; code rows also compare the 4-byte word, a pc-relative
   jal/auipc/branch with only the immediate changed counts as the same instruction), SECTION-EDGE, SEGMENT (PT_LOAD
   base/end/sizes, page-rounded), IMAGE-TOP (top, top/8, top/4096, its shadow, image size), GOT-WORD (8-byte .got
   content resolves to the same symbol+offset), SAME-STRING (both start the same NUL-terminated .rodata string),
   SHADOW-OF and QUOTIENT (value*8 / value*4 by symbol). Rows no rule settles get a named measurement from
   d9e0_manual.py (asan_globals descriptors, format-string bytes, our generated AD2j regions, section headers, image
   byte searches, by-use grep). In generated files and on lines our file no longer has, GEN-NO-CARRY / NO-CARRY means:
   the donor value occurs nowhere in our file (scan of every numeral), so nothing was carried from the donor; the
   generated values themselves are measured by the generated-file checks.

## Counts

files.tsv:

| set | files | old vs d9e0 differs | differ only in the header line | ours = old stage-out | ours = merged | not in our tree |
|---|---|---|---|---|---|---|
| A1 | 377 | 377 | 280 | 120 | 300 | 2 (lib/A/AF0r.v, AF0s.v) |
| A2 | 14 | 14 | 0 | 0 | 14 | 0 |

rows.tsv, 4446 rows, every row result OK, 0 FINDING:

| set | provenance-only | patched | refused | slot | VALUE | generated | other | not-in-tree | total |
|---|---|---|---|---|---|---|---|---|---|
| A1 | 378 | 514 | 179 | 3213 | 4 | 26 | 51 | 3 | 4368 |
| A2 | 30 | 48 | 0 | 0 | 0 | 0 | 0 | 0 | 78 |

By reason:

| set | class | reason | rows |
|---|---|---|---|
| A1 | provenance-only | HEADER (d9e0's header adds the donor image sha256) | 377 |
| A1 | provenance-only | RENAME (lib/A/AD2l.v TfibB_pair) | 1 |
| A1 | patched | OURS-EQ-D9E0 (+ rule: SAME-SYMBOL 277, SEGMENT 22, IMAGE-TOP 18, SECTION-EDGE 10, QUOTIENT 4, GOT-WORD 2; no rule 169) | 502 |
| A1 | patched | HAND-NOTE (2 also SECTION-EDGE; lib/A/AE3i.v:24 IMG_RO_HI 0x32340 = our PT_LOAD0 end) | 3 |
| A1 | patched | DROPPED-DEF 6, PATCHED-TEXT 1, TRAMPOLINE-BLOCK 1, CLASS-MAP 1 | 9 |
| A1 | refused | REFUSED-MARKER + SAME-SYMBOL 45, SEGMENT 12, SAME-STRING 1, GEN-NO-CARRY 44, NO-CARRY 27 | 129 |
| A1 | refused | ZERO-SHADOW-START 17, FMT-SHADOW 10, LOW-SHADOW-BAND 9, NO-SUCH-OBJECT 4, REPLACED-CELL 4, ZERO-SHADOW-END 3, DTOR-WRITE-SET 3 | 50 |
| A1 | slot | GEN-SLOT + SAME-SYMBOL 1424, IMAGE-TOP 101, SEGMENT 30, GOT-WORD 14, SAME-STRING 11, SECTION-EDGE 2, GEN-NO-CARRY 1627 | 3209 |
| A1 | slot | REGION-OF-AD2J 3, TEXT-START 1 | 4 |
| A1 | VALUE | OURS-EQ-OLD + SECTION-EDGE 2, SEGMENT 1; ROM-BOUND 1 | 4 |
| A1 | generated | FUNCTION-TABLE (lib/A/AB1w.v rows) | 26 |
| A1 | other | LINE-GONE/GEN-NO-CARRY 32, LINE-GONE/NO-CARRY 8, DTOR-COUNTS 4, OWNED-CELL 3, OURS-THIRD/GEN-NO-CARRY 3, GEN-OWN-VALUE 1 | 51 |
| A1 | not-in-tree | FILE-DROPPED (lib/A/AF0r.v) | 3 |
| A2 | provenance-only | HEADER 14, RENAME 16 (CmdBSyms / CmdSyms) | 30 |
| A2 | patched | OURS-EQ-D9E0/SAME-SYMBOL (the 48 hand.tsv values: d9e0 writes them itself) | 48 |

d9e0 wrote 181 `port_core_refused_<donor>` markers (A1); 179 are rows of class refused, each with our measured
value, and 2 lie in lib/A/AF0r.v, which is not in our tree. The 1002 markers of the run of record lie in d9e0's
generated slots (class slot) and 6 more where our file holds d9e0's value (patched).

## The four VALUE rows (our file holds the old run's value; d9e0 wrote another)

| file:line | old = ours | d9e0 | measurement | read by |
|---|---|---|---|---|
| lib/A/AD1y.v:17 | 0xaacf8 | 0xaad00 | .data end of our pin (section header .data 0xa8108..0xaacf8); the donor value 0xa2870 is both cgif's .data end and __start_asan_globals, d9e0 took the asan_globals reading (its review row "bound-ambiguous"); the interval is DRV_IVS, the driver's writable statics | lib/A/AD1u.v:111 |
| lib/A/AD1y.v:36 | 0xaacf8 | 0xaad00 | same quantity in DRVW_cases | lib/A/AD1z.v:88 |
| lib/A/AB1w.v:586 | 0x55e000 | 0x55c000 | tfib_at_rw_len = page-rounded size of our last writable PT_LOAD (0xa8000..0x606000); d9e0 kept the donor's 0x55c000 (a kept donor size) | - (no use outside the definition) |
| lib/A/AE7d.v:76 | 0x148680 | 0x153740 | snl_rom_low: every read-only byte lies below the bound; our non-writable PT_LOADs end at 0xa46fc, so the statement holds; the bound is no image quantity (donor 0x148680 = __sanitizer::useCounts+0x107c0 in .bss); d9e0 moved it by symbol (a class-B move) | - (3 other files define their own lemma of that name; no use) |

In all four our value is the right one: no FINDING.

## Controls

controls.tsv: the 2026 rule-settled rows were re-judged with our value + 4 and with our value := the donor value.
The rules accept 0 of the donor-value variants and 3 of the +4 variants. The 3 are lib/A/AB1w.v end rows (lines 82,
83, 96: tfib_E_strnlen, tfib_E_strcmp, tfib_E_vfprintf_2): in the donor the end of one 4-byte trampoline is the start of the next; in ours
another trampoline lies between, so value + 4 is the start of the donor's next trampoline. The rows are E (end) rows
and our value is the symbol end, so the end reading is the right one. FMT-SHADOW is checked by the same formula on the
donor's FMT, which reproduces the donor's SH_LO/SH_HI in all 5 files. A first QUOTIENT rule accepted 8 donor-value
variants (8192 * 8 = 0x10000 = PT_LOAD0 base in both images); QUOTIENT was then restricted to symbols.

## Section bounds (tfib_rodata_hi and the other AB1w/YB1w image bounds)

secbounds.out: every `tfib_<section>_lo/_hi`, tfib_img_*, tfib_entry and tfib_at_* definition of lib/A/AB1w.v
(against fuzz_command.asan c0661b96b5bd) and lib/B/YB1w.v (against fuzz_command.asan-ubsan bbe55d24d096): 33 + 33
definitions, 0 differ from the pin's section headers / program headers / ELF header; the merged tree's two files give
the same. tfib_rodata_hi: A 0x246a4 = A .rodata end, B 0x246e4 = B .rodata end. Known answer: the donor's
lib/A/AB1w.v differs at 2 (tfib_rodata_hi 0x2278c vs cgif A .rodata end 0x227cc; tfib_text_hi 0x9ca00 vs .text end
0x9c9fc); the donor's YB1w.v tfib_rodata_hi 0x2278c equals the cgif B .rodata end. Both port_core runs wrote
tfib_rodata_hi 0x24664 (= our .rodata end - 0x40) and tfib_text_hi 0xa4700 (= .tbss start): they inherit the donor's
offsets ("bound-released-elsewhere" in d9e0's review table). Our file holds the section ends. These two lines are
agree rows (both runs wrote the same value), so they are not rows of rows.tsv.

## Rows where both runs agree and our file differs

agree.tsv: 0 lines where our file differs from both runs only in comments, so there is no stale-comment candidate and no
measured-rows TSV row. 6242 lines differ in code (A1 6228, A2 14): later proof edits and hand patches (for example
the two section bounds above, and `Local Ltac` in the 14 runtime files). Both runs agree on those lines, so they are
outside this comparison; agree.tsv lists them.

## Observations on d9e0 (our file is right in every case)

- d9e0 keeps donor text in its 12 generated slots by design (3213 rows); our values there were compared with our image.
- Kept donor image values: tfib_at_rw_len 0x55c000 (lib/A/AB1w.v:586); AF0m owned cells 0x21448 and 0x214ac (our
  AF0m lists 0x2331c = sysconf.values-0x28 and 0x23380 = sysconf.values+0x3c of our twin).
- A donor address with two readings mapped to the other one: cgif .data end = __start_asan_globals 0xa2870 ->
  0xaad00 (lib/A/AD1y.v:17,36; also lib/A/AD28.v:293 and lib/A/AD1l.v:129, where our hand patch holds .data end 0xaacf8).
- A model bound moved by symbol: lib/A/AE7d.v:76 0x148680 -> 0x153740.
- lib/A/AE34.v:26: d9e0 splits the trampoline block into the sub-ranges it paired (36 of 46 entries); the old run
  kept the donor count 38; our file has (0x45130, 46%nat), our twin's contiguous block of 46 trampolines.
- 181 refused values; each has a measured value in our file.

## FINDINGs

None (code: none; comment: none). No STOP-rule message was needed.

## Files

files.tsv, rows.tsv (columns: set, file, line (our line), stage_line (old stage-out line), d9e0_line, pos, old_val,
d9e0_val, our_val, donor_val, class, reason, measurement, code_or_comment, read_by, result, finding_kind, new_value),
rows.raw.tsv (diff output, input of the triage), manual.tsv (hand-measured rows), controls.tsv, agree.tsv,
secbounds.out, d9e0_diff.py, d9e0_triage.py, d9e0_manual.py, d9e0_secbounds.py.
