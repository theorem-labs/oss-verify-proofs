# G6: kimg_overlap on the image B start-up tables (gate record)

Proves no function (kind: measurement). Re-run 2026-10-30 on the series base b1afc3e80791 (`run.sh g6`).

## Tool
kimg_overlap.py, the FROZEN version, sha256 `5db341e3cd628ad07bde939c902db9ecc0c3e5791fa3947434ad729031239d3a` (its
README's donor control: a known-filled AB01 gives 40 duplicates, a walk-only one 0). What it reads in a file: KImg
ranges and the constant-address KWord / KZero / KFill writes of the same list (contradicting bytes), `acs` states with
their `_kn` lists (aliases, duplicates), `Definition X : region := mkRegion ...` regions with their mkChunk lists
(checked against the donor's same-named region), `<X>_lo` / `<X>_hi` pairs, `ex_consts<S>` cell lists, refused
relocation markers. Exit 1 on a contradiction, 2 on a fill / region MISMATCH / range finding.

## Command (per file)
```
python3 kimg_overlap.py "$GIT" b1afc3e80791 proofs/libreac/fuzz_disco/lib/Reusable/<F>.v "$PIN_B" \
  --donor c8557374ad2e:proofs/cgif/cgif_file_fuzzer/lib/<F>.v "$CGIF_B"
```
`$PIN_B` = fuzz_disco.asan-ubsan (sha256 `cee6f04ad3d4928e242405689ae058bb9e8b6533000c90bde984a2f0d5ff5146`), `$CGIF_B` =
cgif_file_fuzzer.asan-ubsan (`1c29845fe6058de6e1dbf3f6ec6abd566ea612d76b65ea5435d7ff77c63e08ef`), the donor's file the
region control.

## Verdict on YB05, YF0m, YD1k (the files named): VOID
All three runs exit 0 and print only `overlapping write bytes 0  contradicting bytes 0` and `states: 0, aliases 0,
duplicate states 0`: the tool reads NO entity in these files. Measured by count over each file's text: KImg 0, `: acs :=`
0, `: region :=` 0, `<X>_lo / _hi` 0, `ex_consts` 0, constant KWord 0 in all three (YD1k cites regions by name, e.g.
`apply (CH R_A1c 66320 40)` at line 252, and the regions themselves are defined in YD2j.v).
Planted control: a copy of YD1k.v outside the tree with line 252 `apply (CH R_A1c 66320 40)` -> `apply (CH R_A1c 66300 40)`
(a chunk overlapping R_A1b [66288, 66312)): rc 0, the same two lines, no finding. **The control does not fire, so this
gate is VOID on YB05 / YF0m / YD1k: it is not shipped as a pass, and it measures nothing about their values.** Their
values are carried by G3 (codeptr, all three), G4 / G5 (YF0m's cells) and G1 (address checker).

## The same tool on the image B start-up files that hold the forms it reads: PASS
| file | rc | result |
|---|---|---|
| YB01.v | 0 | `overlapping write bytes 0  contradicting bytes 0`; `states: 50, aliases 0, duplicate states 0`; `KImg ranges: 139, findings 0` |
| YB03.v | 0 | `overlapping write bytes 0  contradicting bytes 0`; `states: 0`; `KImg ranges: 66, findings 0` |
| YD2j.v (holds the regions YD1k cites) | 0 | `overlapping write bytes 0  contradicting bytes 0`; `regions: 81, MISMATCH 0, by design (donor same shape) 0, broken with no donor region 0` |

Planted controls (copies outside the tree, `FILE <copy>` in place of the ref and path): both fired.
- YD2j.v line 19 `[ mkChunk 66320 (CImg 40) ]` -> `[ mkChunk 66300 (CImg 40) ]` (an overlapping region chunk): rc 2,
  `regions: 81, MISMATCH 1, ...`, `('R_A1c', '0x10310', '0x10338', ['chunk at 66300 overlaps or precedes 66320'])`.
- YB01.v line 15, HS_tfib_0_kn's first write `KWord {| a_base := ELit 0; a_off := 683312 |} 8 (ELit 0)` moved to
  `a_off := 66320` (inside the list's KImg [0x10000, 0xa2758)): rc 1, `overlapping write bytes 8  contradicting bytes 3`,
  rows at 0x10315 / 0x10316 / 0x10317 (image bytes 112, 183, 64 against the written 0).
