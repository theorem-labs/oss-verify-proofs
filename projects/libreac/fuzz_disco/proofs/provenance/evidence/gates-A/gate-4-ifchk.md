# Gate 4 — ifchk of record, image A (AF0m cells × the start-up states)

Kind: measurement; proves no function. For every TFIB_CONST cell (`Tfib_const_sym ++ Tfib_const_abs ++
Tfib_const_shadow` of AF0m.v) and every one of the 50 start-up states of AB01.v, ifchk decides the stated cell value
from the certificate or from the image and checks the two agree. A disagreement is a wrong cell.

## Command (run.sh, through the frozen start-up set)

```
frozen-run.sh startup-set-2026-10-30d.tsv ifchk.py \
  --owned $A/AF0m.v --states $A/AB01.v --ad1g $A/AD1g.v --image $PIN_A
```

The A file names exist at the base: `AF0m.v`, `AB01.v`, `AD1g.v` (checked; sha256 in the slice's MANIFEST is not
needed — these are proof files, not shipped here).

## Tool of record (cited by name + sha256, not copied)

`ifchk.py` sha256 `f5cde600cc1886bb65200495a69e1eb3afb936ea5512edb8c581edc0299847fb` — it supersedes bc48411567d7
(an empty TFIB_CONST class exited 1, a width-0 cell read `undetermined`); a width-0 cell is now decided by the unit's
own xcell (`--ad1g`) and the run refuses without `--ad1g`. Run through `startup-set-2026-10-30d` (frozen-run.sh
`40cd8a4bf5bf…`); 2 KIMG-BSS self-test cases and 8 width-0 / empty-class cases pass before any input is read.

## Verdict (run.sh `ifchk/base`)

**0 different.** `1380 cells (sym 22, abs 772, shadow 586) × 50 states: 69000 = stated, 0 different, 0 undetermined
(None), 0 inexpressible`, exit 0. By class: `Tfib_const_sym 1100/0`, `Tfib_const_abs 38600/0`, `Tfib_const_shadow
29300/0`. Sources: 35900 of 69000 pairs decided by the certificate (1500 of them KImg over NOBITS, 30 cells, the
KIMG-BSS rule), 33100 by the image (662 cells). Image A sha256 `5e39150dd810…`.

(The earlier record read 1379 cells / 1460 = sym 22 + abs 771 + shadow 586 × 50; the base AF0m.v has one more abs cell —
the REAL(vsnprintf) pin added by a22072733a16 — so 772 abs, 1380 cells; still 0 different. The abs / shadow split
matches the 662 file-backed cells of gate 5 and the 586 shadow cells of shadowcheck.)

## Planted control (must fire)

A copy of `lib/A/AF0m.v` outside the branch with the file-backed cell `z8 (ANum 0xa1200) 0x8` flipped to `0x9`. Re-run:
the run reports `… N different` (the flipped cell disagrees with the image) and exits 1. A run with `0 different` would
be void. Recorded `FIRED` in run.sh.
