# G7: the address checker of record 3d2eee813cce over the image B files (gate record)

Proves no function (kind: measurement). Re-run 2026-10-30 on the series base b1afc3e80791 (`run.sh g7`). The
port_addr_check of record is now 3d2eee813cce; the G1 record (efa19b81e92b) stands beside this one, unchanged.

## Tool
port_addr_check.py, sha256 `3d2eee813cce41c92be6131e56292d73e473d2582156655895ff2a1ce5c73b82` (checked before the
run). Images keyed by build letter A / B / P / U. `--fail-on-flags`: exit 4 when a row carries a finding class. Its
`--list-flag-classes` output is byte-equal to efa19b81e92b's (27 classes, sha256 `191b74b7661b...`; `FLAG-CLASSES
575d398c6022` in both summaries).

## Command
G1's command with the tool replaced, every other argument the same:
```
python3 "$PAC3" --git "$GIT" --donors-from "$DONORS" --summary --fail-on-flags \
  --src c8557374ad2e:proofs/cgif/cgif_file_fuzzer/lib --dst b1afc3e80791:proofs/libreac/fuzz_disco/lib \
  --paired-only --map A/=A/ --map =Reusable/ \
  --src-image A="$CGIF_BIN/cgif_file_fuzzer.asan" --src-image B="$CGIF_BIN/cgif_file_fuzzer.asan-ubsan" \
  --src-image P="$CGIF_BIN/cgif_file_fuzzer.plain" --src-image U="$CGIF_BIN/cgif_file_fuzzer.ubsan" \
  --dst-image A="$PIN_DIR/fuzz_disco.asan" --dst-image B="$PIN_DIR/fuzz_disco.asan-ubsan" \
  --dst-image P="$PIN_DIR/fuzz_disco.plain" --dst-image U="$PIN_DIR/fuzz_disco.ubsan" \
  --assign '**=auto' --include 'Y*.v' --cache "$WORK/g7/cache" --out "$WORK/g7/pac3-Y.tsv"
```
Fresh cache (cache hits 0, misses 8: the symbols of all 8 stripped pins recovered from 28 symbolised donors).

## Result (wall 9 min): rc 4, 27544 flagged rows in 13 classes, the same rows as G1
- `count files paired: 836`; 397413 numerals; image of each file as in G1 (B 567, P 224, U 39, A 5, A->B 1).
- `FLAGGED 27544 rows in 13 classes`: UNPAIRED-PORTED 16038, UNPAIRED-SOURCE 7282, NON-ADDRESS-CHANGED 2595,
  KIND-CHANGED 942, DIFFERENT-SYMBOL 415, UNRESOLVED 190, SAME-VALUE-DIFFERENT-OBJECT 51, STALE-DONOR-CODE-POINTER 15,
  STALE-DONOR-DATA-POINTER 5, STALE-DONOR-ROUNDED 4, GEOMETRY-CHANGED 3, IMAGE-EXTENT-CHANGED 2, NO-COUNTERPART 2.
  `UNMEASURED 2923 rows in 2 classes`: UNMEASURED-NAME 1 (YB1w.v:1311, as in G1), UNPAIRED-FILE-UNMEASURED 2922.
- **Diff against efa19b81e92b on the same file set: 0 rows.** The table's rows (header and 397413 numeral rows, the
  lines not starting with `#`) are byte-equal to G1's `pac-Y.tsv`; only the `#` header lines differ (3d2eee813cce adds
  four `count file pairs whose build came from ...` lines). run.sh g7 compares the two tables row for row.
- Per-row triage: `g1_triage.py` (this directory) on this table, with `--pac "$PAC3"`, exits 0 and writes a table
  byte-equal (cmp) to `G1-flagged-rows.tsv`: 0 UNTRIAGED, 0 DEFECT, the G1 rules and counts unchanged.
- The same command with the dst images given as `PIN:TWIN` (the unstripped twins' `.symtab` instead of recovered
  symbols) also gives 836 paired and `FLAGGED 27544 rows in 13 classes`; 19469 rows differ from the pins-only table,
  all in `dst_res` / `note` naming (a recovered `foo+0x10[data]` read as the twin's `foo+0x10`), and 23 rows change
  verdict between flagged classes (YF0m 20 UNRESOLVED -> DIFFERENT-SYMBOL, YE3i 2 NON-ADDRESS-CHANGED -> KIND-CHANGED)
  plus YB1w.v:1311 UNMEASURED-NAME -> SAME-SYMBOL; `g1_triage.py` on that table also exits 0 with the same per-rule
  counts. G8 (roundconst) gives byte-equal output on either table.

## Planted control: fired
The G1 plant (a copy of `lib/Reusable/YE23.v` with line 474's `Z_to_bv 64 6277920` moved to `6277936`) run with
`--dst <dir holding that copy> --include 'YE23.v'` and the same images: rc 4, `count files paired: 1`, `FLAGGED 19
rows` (the run above flags 18 in YE23.v), the new one `NON-ADDRESS-CHANGED 0x5f9920 -> 0x5fcb30` at YE23.v:474. The
`PIN:TWIN` form fires the same row.

## Registered limits of this checker (classes that can read EQUAL where the meaning differs)
1. SAME-CONTENT across two different symbols whose strings agree up to the NUL.
2. INSN-SAME on a jal / auipc / lui word compares opcode + rd only.
3. ROUND-CONSTANT-SAME passes a page-multiple value without reading it (G8, roundconst v2, reads it by value).
4. Predict mode's MAPS-STRING maps by string content alone.
5. The named-symbol rule depends on the donor's recovered symbols.
