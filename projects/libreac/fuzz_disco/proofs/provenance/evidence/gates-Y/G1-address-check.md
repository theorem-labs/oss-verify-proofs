# G1: the address checker of record over the image B files (gate record)

Proves no function (kind: measurement). Re-run 2026-10-30 on the series base b1afc3e80791 (`run.sh g1`).

## Tool
port_addr_check.py, the address checker of record, sha256
`efa19b81e92ba289e7c185d481faadf045ce7d52d092cc10642fec69924aba03` (checked before the run). Images keyed by build
letter A / B / P / U (a run keyed otherwise leaves the named-symbol rule unmeasured). `--fail-on-flags`: exit 4 when a
row carries a finding class; the classes come from the tool (`FLAG-CLASSES 575d398c6022`, 27 classes).

## Command
```
python3 "$PAC" --git "$GIT" --donors-from "$DONORS" --summary --fail-on-flags \
  --src c8557374ad2e:proofs/cgif/cgif_file_fuzzer/lib --dst b1afc3e80791:proofs/libreac/fuzz_disco/lib \
  --paired-only --map A/=A/ --map =Reusable/ \
  --src-image A="$CGIF_BIN/cgif_file_fuzzer.asan" --src-image B="$CGIF_BIN/cgif_file_fuzzer.asan-ubsan" \
  --src-image P="$CGIF_BIN/cgif_file_fuzzer.plain" --src-image U="$CGIF_BIN/cgif_file_fuzzer.ubsan" \
  --dst-image A="$PIN_DIR/fuzz_disco.asan" --dst-image B="$PIN_DIR/fuzz_disco.asan-ubsan" \
  --dst-image P="$PIN_DIR/fuzz_disco.plain" --dst-image U="$PIN_DIR/fuzz_disco.ubsan" \
  --assign '**=auto' --include 'Y*.v' --cache "$WORK/g1/cache" --out "$WORK/g1/pac-Y.tsv"
```
cgif's top-level `Y*.v` files pair with fuzz_disco's `lib/Reusable/Y*.v` (`--map =Reusable/`). Pins (sha256): cgif
asan `7093581aab04...`, asan-ubsan `1c29845fe605...`, plain `19dedd1bc682...`, ubsan `44a34d2e23b6...` (cgif's
harness.yaml at the base); fuzz_disco asan `5e39150dd810...`, asan-ubsan `cee6f04ad3d4...`, plain `04988e3ab313...`,
ubsan `56121de6ba4c...` (fuzz_disco's harness.yaml at the base). The checker reads the stripped pins only: symbols of
all 8 images recovered from 28 symbolised donors (fresh cache: 8 misses, 0 hits; image B: 1280 functions, 736 objects).

## Result (wall 29 min): rc 4, 27544 flagged rows, every one triaged, 0 defects
- Files: cgif 2467 read, 1449 after `--include`; fuzz_disco 3758 read; **836 paired**; 397413 numerals. Image of each
  file (rule (i) its `images` Require, (i') its directory, (ii) its numerals): B 567, P 224, U 39, A 5, A->B 1.
- Not flagged: NON-ADDRESS-SAME 339408, SAME-SYMBOL 9942, SAME-GEOMETRY 7910, IDENT-NAME 4844, INSN-SAME 3004,
  NAMED-CONSTANT 144, ROUND-CONSTANT-SAME 120, IMAGE-EXTENT-SAME 80, LABEL-KEPT 65, SAME-CONTENT 12,
  TARGET-SYMTAB-MATCH 3, OK-BY-LOAD 1; reported, measured by nothing: GENERATOR-FILL 115, UNMEASURED-NAME 1 (YB1w.v:1311
  `tfib_D_fini_array_0_1 := 0xa0268`, the .fini_array start in both readings), UNPAIRED-FILE-UNMEASURED 2922 (every
  fuzz_disco file with no cgif twin, the whole tree: Reusable 226, Y 345, B 152, the rest other trees).
- `FLAGGED 27544 rows in 13 classes`: UNPAIRED-PORTED 16038, UNPAIRED-SOURCE 7282, NON-ADDRESS-CHANGED 2595,
  KIND-CHANGED 942, DIFFERENT-SYMBOL 415, UNRESOLVED 190, SAME-VALUE-DIFFERENT-OBJECT 51, STALE-DONOR-CODE-POINTER 15,
  STALE-DONOR-DATA-POINTER 5, STALE-DONOR-ROUNDED 4, GEOMETRY-CHANGED 3, IMAGE-EXTENT-CHANGED 2, NO-COUNTERPART 2.
- Where they are: YI0z 10031 (the program listing), YB1w 3571 (the symbol table), YF0m 2718, YB01 2179, YC1i 1628,
  YCej 1620, YE37 1171, YC8g 644, YCbf 420, YI12 375, YD2j 366, 146 other files 2821. Most come from tables the port
  regenerated from the image B pin, whose rows are image B's own and so pair by position with unrelated cgif rows.

## Per-row triage: `G1-flagged-rows.tsv` (written by `g1_triage.py` from the checker's output; re-derived by run.sh)
One row per flagged row: verdict, image, kernel, where (file:line), sentence, idx, src_value, dst_value, rule, detail.
Each row takes the first rule (g1_triage.py RULES) that holds; a rule resting on a measurement makes it on the pins and
the unstripped twins, and holds only when it agrees. Twins (host binaries, not shipped; PT_LOAD 2..4 byte-equal to their
pins, measured): image B `ead714913acd1e81835e08e021456cebcb35c09af2f87f4e7e2b6891f1b92489`, plain
`115e0dcb29bc5963917708dd1d76a7b38df31bb665938ae75fd6f583c9d3d9b7` (read for names and section bounds only). Result:
**0 UNTRIAGED, 0 DEFECT**.

| rule | rows | the evidence |
|---|---|---|
| DONOR-ONLY | 7282 | UNPAIRED-SOURCE: a cgif numeral with no partner; the shipped file does not carry it there |
| LISTING-WORD | 7997 | YI0z `PW w` = the pin's word at LLVMFuzzerTestOneInput + 4 * index (all 8016 PW words measured equal) |
| LISTING-OPERAND | 1098 | YI0z PCall / PHi / PAddHi / PLdHi / PTail fields (register, object index, offset) |
| LISTING-OFFSET | 40 | YI0z `AF_both3_<f>` = <f> - LLVMFuzzerTestOneInput in the twin (40 / 40) |
| LISTING-TARGET | 371 | YI12 tfib_B0 / sigma / obj / hi: checked against the decoded image code by `tfib_lib_check0` (vm_compute); sigma values measured function starts |
| LISTING-BOUNDS | 2 | YCef tfib_lib_start 0x80fbc / tfib_lib_count 8769 = the listing's start and length (measured) |
| SYMTAB-ROW | 2504 | YB1w tfib_A / tfib_E = start / end of a symbol of that name in the twin (all 2574 tfib_A / tfib_E definitions of the file measured) |
| PHDR-ADDR | 8 | 0x10040 = 0x10000 + e_phoff 0x40 (pin) |
| YF0M-CELL / -ZERO / -OWNED / -HASH | 2525 / 69 / 105 / 4 | YF0m cells, zero ranges, owned ranges, hashes: G4 (ifchk) and G5 (cellcheck, shadowcheck, ownedcheck, covcheck) check them against the pin; `Example tfib_hash_buckets` in the kernel |
| HANDOFF-STATE | 2218 | YB01 / YB03 states: inputs of YB1m's startup_cert (`check TSEGS ... = COk`, vm_cast_no_check, Qed); G6 0 contradicting bytes, 50 states; G3 0 findings |
| REGION-TABLE / REGION-LEMMA | 364 / 128 | YD2j regions (G6: 81 regions, 0 MISMATCH against cgif's same-named regions; G3 0 findings) and YD1k's kernel-checked lemmas over them |
| RO-CHUNK | 154 | YE3i chunks checked against the image in the kernel (img_ro_bytes_ok, img_ro_chunks_inside); IMG_RO_HI = end of PT_LOAD 1 |
| X2-CONST | 1145 | YE37 x2_rodata / x2_shw checked in the kernel against YF0m's cells (rodata_chk_true, shbyte_chk_true) |
| TRACE-TABLE | 29 | YCej: each address a return pc (the word before it is jal / jalr ra) or a function start (measured) |
| MODEL-CONST | 41 | mmap flags words (0x100022 = MAP_FIXED_NOREPLACE \| MAP_ANONYMOUS \| MAP_PRIVATE, ...), the V_HW range bound 0x20112D, YE7d's loose rom bound 0x148680: model constants, equal to the donor's |
| NON-ADDRESS | 1239 | the checker reads the value as a non-address; a value inside the image is kept here only with a sub-reason on its line (a kernel `change ... with N`, a decoded instruction operand, a quotient in a lia / zlia step, .text's word count, an allocator size) |
| IMAGE-B-QUANTITY | 28 | the checker's own reading of the ported value is a bound / extent / header quantity of the target |
| HAND | 193 | one by one, each with its measurement in the detail: format-string pointers that moved with their string (both pins read: 'cli: cannot open %s\n' +17 / +19, 'usage: %s INPUT\n' +7 / +9, ...); VSNPrintf's jump-table cell 0x20d00 holding 0x468fc; ofl_lock / ofl_head / __libc / __stack_chk_guard / interceptor_metadata_map cells by name; RELRO bounds; target_run's empty-input buffer oft_aligned_copy.empty and its return pc 0x80eb8; zero-shadow windows (start-up shadow measured 0); the plain image's extent [0x10000, 0x52000), RELRO list and __set_thread_area end; tfibmusl_text_count 16102 = the words to .text's end (the checker's 16105 applies cgif's span to tls.hi - 8, which in cgif runs 12 bytes past its .text) |

The STALE-DONOR-* rows: STALE-DONOR-CODE-POINTER 15 = YI12 tfib_sigma 11 (LISTING-TARGET, each a measured function start),
YCef tfib_lib_start 1 (LISTING-BOUNDS), YI0z 3 (odd PW words, LISTING-WORD); STALE-DONOR-DATA-POINTER 5 = YF0m 3
(YF0M-CELL), YE3i 2 (RO-CHUNK); STALE-DONOR-ROUNDED 4 = the region R_A1d [0x10340, 0x10350) of YD2j / YD1k / YE3i
(REGION-TABLE, REGION-LEMMA, RO-CHUNK: the chunk covers the object at 0x10348). None is a cgif value left in place.

## lib/Y and lib/B
cgif's lib has no `Y/` or `B/` subtree, so the checker pairs nothing there: the same command with `--map Y/=Y/ --map
B/=B/ --include 'Y/**' --include 'B/**'` gives `count src files after --include: 0`, `count files paired: 0`, rc 3
(zero files paired). Their decimal literals are scanned against cgif's addresses by G2.

## Planted control: fired
A copy of `lib/Reusable/YE23.v` outside the tree with line 474's `Z_to_bv 64 6277920` (buf+0x8, judged SAME-SYMBOL in
the run above) moved to `6277936`, run with `--dst <dir holding that copy> --include 'YE23.v'` and the same images and
cache: rc 4, `count files paired: 1`, `FLAGGED 19 rows` (the run above flags 18 in YE23.v), the new one
`NON-ADDRESS-CHANGED 0x5f9920 -> 0x5fcb30` at YE23.v:474.
