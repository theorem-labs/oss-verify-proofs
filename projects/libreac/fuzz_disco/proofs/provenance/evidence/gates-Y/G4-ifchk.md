# G4: ifchk, YF0m's cells at the 50 image B hand-off states (gate record)

Proves no function (kind: measurement). Re-run 2026-10-30 on the series base b1afc3e80791 (`run.sh g4`).

## Tool
- ifchk.py sha256 `f5cde600cc1886bb65200495a69e1eb3afb936ea5512edb8c581edc0299847fb`, through the start-up set of record
  2026-10-30d (`sha256sum -c SHA256SUMS`: 50 OK; bundle `startup-set-2026-10-30d.tsv` sha256
  `bde9702390640d7bfc5a23702de239154ed4130e863e475ca109455c2648dbab`).

## Command
```
frozen-run.sh startup-set-2026-10-30d.tsv ifchk.py --owned "$LIB/Reusable/YF0m.v" --states "$LIB/Reusable/YB01.v" \
  --ad1g "$LIB/Reusable/YD1g.v" --image "$PIN_B"
```
`$LIB` = the base's `proofs/libreac/fuzz_disco/lib`; `$PIN_B` = fuzz_disco.asan-ubsan, sha256
`cee6f04ad3d4928e242405689ae058bb9e8b6533000c90bde984a2f0d5ff5146` (the tool prints it). All three file names exist at
the base.

## Verdict: PASS (rc 0)
```
ifchk: 1461 cells (sym 22, abs 853, shadow 586) x 50 states: 73050 = stated, 0 different, 0 undetermined (None), 0 inexpressible
ifchk: sources: 35900 of 73050 pairs decided by the CERTIFICATE (1500 of them KImg over NOBITS, 30 cells, the KIMG-BSS rule), 37150 by the IMAGE (743 cells), 0 by the unit's xcell at width 0, 0 undetermined
ifchk: self-test 2/2 KIMG-BSS cases (KImg 0x351d58 in .bss -> certificate, KImg 0x19940 in .rodata -> image; sources 108/108); 8 width-0 / empty-class cases
  Tfib_const_sym     1100/0/0/0/0 (22 cells)
  Tfib_const_abs     42650/0/0/0/0 (853 cells)
  Tfib_const_shadow  29300/0/0/0/0 (586 cells)
  sources, state 0: 101: 139, 104: 546, 108: 764, 301: 3, 309: 9
```
The KIMG-BSS rule applied to 5 listed abs cells (cells 58, 61, 63, 67, 68 at 0xa6c88, 0xa6ca0, 0xa6cb0, 0xa6cd0, 0xa6cd8,
section .bss), as the tool prints them.

Compared with the earlier record (1460 cells = sym 22 + abs 852 + shadow 586): the base has ONE more abs cell, the row
`z8 (ANum 0xa2618) 0x99478` appended as the last row of Tfib_const_abs (index 852; the cell
`__interception::real_vsnprintf` holding vsnprintf 0x99478; it was added after that record). With it the counts are
those the regenerated YF0m's own gates stated: 1461 cells, 73050 = stated, and 743 image-decided cells (= G5's cellcheck
743). Nothing else differs.

## Planted control: fired
A copy of YF0m.v outside the tree with that last row's value changed, `0x99478` -> `0x99479` (a flipped cell), same
command: rc 1, `73000 = stated, 50 different`, `Tfib_const_abs 42600/50/0/0/0 (853 cells)`, and per state
`state 0 Tfib_const_abs ('ANum', 665112) w8: verdict 1 (different), source 108, kernel read 0x99478`.
