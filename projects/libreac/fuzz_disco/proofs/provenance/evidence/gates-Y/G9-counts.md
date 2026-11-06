# G9: every image-derived count of the image B files recomputed from the pins (gate record)

Proves no function (kind: measurement). Run 2026-10-30 on the series base b1afc3e80791 (`run.sh g9`). It covers what
G8's roundconst v2 cannot (its named gaps: a small kept donor value that is also a right target quantity reads SAME;
unpaired unnamed runs are not gated; function sizes are no quantity of it).

## Script and command
`count_recompute.py` (this directory; every input an argument; its docstring states every pattern and rule):
```
python3 count_recompute.py --lib "$LIB" --cgif-lib "$CLIB" --pac "$WORK/g7/pac3-Y.tsv.gz" \
  --pin A="$PIN_DIR/fuzz_disco.asan" --twin A="$TWIN_DIR/fuzz_disco.asan" \
  --cgif-pin A="$CGIF_BIN/cgif_file_fuzzer.asan" --cgif-twin A="$CGIF_TWIN_DIR/cgif_file_fuzzer.asan" \
  (the same four arguments for B = asan-ubsan, P = plain, U = ubsan) \
  --accept 'Reusable/YE34.v:24=DIFFERS:38 -> fixed in b0078622dec (build check pending)' \
  --accept 'Reusable/YE34.v:20=DIFFERS:435 -> fixed in b0078622dec (build check pending)' \
  --accept "Reusable/YB1t.v:28:0x64c74=MEASURED TRUE:decode table, 30 words inside .text, one word past internal_madvise decodes internal_close's first instruction" \
  --out "$WORK/g9/G9-counts.tsv"
```
`$LIB` / `$CLIB` are the base lib and the cgif donor lib as run.sh extracts them; G7's table gives the build each file
is read against (column 3). Each twin is checked against its pin (same PT_LOAD table, PT_LOAD 2..4 byte-equal: true
for all 8 images); code bytes and headers come from the pin, symbols from the twin. Output: `G9-counts.tsv`, one row
per count (key, form, name / call, shipped, rule, recomputed, measurement, images, donor shipped, donor recomputed,
verdict, status, note, accept); exit 0 only when every count is MEASURED TRUE, NOT-A-COUNT with its reason, or a
DIFFERS row carrying an `--accept`.

## Method (the script's docstring has the exact patterns)
- Counts are found by fixed text patterns over every `lib/Reusable/Y*.v` (comments blanked): code ranges
  (`build_table SEGS 0xPC N%nat` 67, `(PC, N%nat)` 66, the four build_table count definitions), count-named
  definitions (roles.py's TABLE suffixes, `TEXT_N`, `tfib_n*`: 96) and record fields (7), segment spans and offsets
  in proof text (YB13, YB1h: 42), YB01 `seg` slices (301), `firstn` / `skipn N` (324), `length .. OP N` (295),
  `mkChunk A (CImg N)` (95), `mkRegion None LO (LO + N)` (3), read-only cell tables (64).
- Each count is recomputed by the rule its comment or the donor's states: text N = .text size / 4; text-tail N =
  (.text end - PC) / 4; donor structure: the cgif range read as "function S + s to function E + e" and moved by
  function name, N = (start of E here + e - PC) / 4; segment spans from the pin's program headers; header and table
  counts (n_res, e_phnum, TFIB_TEXT_N, CTX_SIZE / FILE_SZ from st_size, the de Bruijn extent, match-table arms);
  region slices from each tree's YD2j region list; message lengths from the pin's strings; YD2j's CImg chunks from
  the collector's `KImg` runs in YB01. NOT-A-COUNT rows name what the numeral is (an address, an index, a width,
  PATH_MAX, a model bound, a proof-local list), with a check where one is cheap.
- Rulings of the unit owner (binding, this unit): FIX a count whose meaning is wrong for this image (a range named
  for a set of functions or a section that now covers other or absent code, as YE34; or a table that runs outside its
  section / segment); KEEP a count whose every element is a true fact of this image, even if it differs from the
  exact function cover (YE3h.v:1725, YB1t.v:28). A ruling is recorded in the row's accept column by `--accept`.

## Result: 1364 count rows from 218 of 1043 files
| verdict | rows |
|---|---|
| MEASURED TRUE (status EQUAL 493, TRUE 1) | 494 |
| NOT-A-COUNT | 868 |
| DIFFERS (accepted, see below) | 2 |
| UNMEASURED | 0 |

- **DIFFERS: lib/Reusable/YE34.v:20** musl_sel_ranges `(0x95808, 435%nat)`: the cgif range runs `__stdio_write` + 0
  to `__stdio_exit` + 28; here (twin `__stdio_exit` 0x95de8 + 28 - 0x95808) / 4 = 383; the shipped 435 ends at
  0x95ed4, 52 words past that point (cgif ships 435). `DIFFERS: 435 -> fixed in b0078622dec (build check pending)`.
- **DIFFERS: lib/Reusable/YE34.v:24** icpt_ranges first tuple `(0x42a3c, 38%nat)`: in cgif the 38 words are 38
  trampolines from `__interceptor_trampoline_strlen` to the end of `__interceptor_trampoline_sigaction`; in
  fuzz_disco B the same cover is 36 words, [0x42a3c, 0x42acc); the shipped 38 runs 2 words into
  `___interceptor_strlen`. `DIFFERS: 38 -> fixed in b0078622dec (build check pending)`.
- lib/Reusable/YB1v.v:10 tfibmusl_text_count ships 16102 = (.text end 0x9f248 - 0x8f6b0) / 4: MEASURED TRUE (cgif
  ships 16403; the same rule on cgif gives 16400). YE3h.v:1725 `(0x7057c, 12)` = the exact cover of
  `__sanitizer_cov_dump` (cgif's 13 is its own cover plus one word): MEASURED TRUE.
- Code ranges that end part-way into a following function ship the donor's structure exactly (same functions, same
  offset into the next one) and read MEASURED TRUE by the donor-structure rule: YB1q.v:25 / :31 `(0x64c74, 27)` and
  `(0x669a0, 111)`, YB1t.v:28 `(0x53164, 50)`, YE34.v:20 `(0x9945c, 47)`.
- lib/Reusable/YB1t.v:28 `build_table tfibsegs 0x64c74 30%nat`: whole functions from internal_iserror to the end of
  internal_madvise plus the first word of internal_close (exact cover 29; cgif's 30 has the same shape). Ruled KEEP,
  recorded exactly: `MEASURED TRUE: decode table, 30 words inside .text, one word past internal_madvise decodes
  internal_close's first instruction`.
- Weaker checks, named: YCef.v:9 tfib_lib_count 8769 (whole functions from LLVMFuzzerTestOneInput to the end of
  reac_ports_parse; the donor range starts at another function), 63 image-region slices with donor count <= 4,
  the 64 read-only cell tables (end of the last cell), and five runtime / model constants checked against the
  donor's value only (BST_SIZE, META_SIZE, MAX_DICT_LEN, d_tab_words, MG_SLOTS).

## Planted control: fired
A tree of links to the base lib with five files planted, each numeral set back to the donor's value at that position
(one per rule family): YB1v.v:10 16102 -> 16403, YB12.v:26 112841 -> 111037, YB13.v:128 458752 -> 446464,
YCef.v:9 8769 -> 7052, YD2f.v:194 `length IMG_B = 81` -> 33. Same command and accepts: exit 1, `DIFFERS 7 (accepted 2,
not accepted 5)`, and exactly the five planted keys are the new DIFFERS rows.
