# alreloc cross-check of the image-A core relocation on the run of record

proves no function (kind: measurement). Every numeral position of WORK/stage-out (WORK = work-rec5) is paired with the
donor text and with alreloc's own relocation of it, and every position in scope is decided by reading the two ELF images;
neither tool's value is evidence. alreloc a5c53bb2bed4 (the ASan toolchain's owner's frozen alreloc.py.frozen-a5c53bb2bed4ad03, sha256
a5c53bb2bed4ad039a60...) is of record for new runs and DEFECTIVE (its rules `gap` and `symbol`; the tool owner's notice),
so it decides nothing here. Method: libdiginet/fuzz_decode's checks of record (sha256 93e6e8cff620, e6d5a5dd551b, 7ec2eb592622, 6c4f2678caa8 and c9f8b7410e16 in that order; internal records:
checks/alreloc-xcheck.sh, alreloc_compare.py, alreloc_decide.py, alreloc_plant.py, alreloc-xcheck-control.sh) with the
names, pins and paths changed and the decision groups this unit needs (rodata-const, region-split, img-b-eq, czone,
and for the run of record two more: a donor line a patch rewrote, a comment line a patch added), each with a plant where
a plant can reach it.

## Command

    checks/alreloc-gate.sh WORK LIB OUT/alreloc     (run by checks/run-gates.sh; records/run-gates.txt)

alreloc-gate.sh runs, as one command: alreloc-xcheck.sh (the record run; two `--dry` alreloc passes over a scratch tree
that holds LIB minus every relocated file, then alreloc_compare.py and alreloc_decide.py), alreloc-xcheck-control.sh (the 8
plants), the two seeded sweeps (`SWEEP="80 1"`, `SWEEP="120 2"`) and alreloc_record.py (records/record-tables.md, the
generated tables). Each step's status and time: records/alreloc-gate.txt. Inputs, each sha256-checked by the scripts:
fuzz_grant.asan c2c7559b29bd (twin 57c26f993615), fuzz_transport.asan e89be137db17 (twin 86efc3a80314), the model images
fuzz_manifest.asan 0ba7e1695886 and cgif_file_fuzzer.asan 7093581aab04, the donor text at origin/ossv/recipes 25e3d17bdb50,
`--unit-ref` a494a3cb4a09 (its harness.yaml pins asan e89be137db17).

## Result (records/xcheck.log)

    alreloc_compare.py: 492 files, 189718 numeral positions: agree 6305, both-kept 182141, disagree 191, alreloc-unmapped 828, alreloc-refused 0, not-covered 83, added 170
    alreloc_decide.py: .got tables: 427 / 427 slots, 427 aligned by content
    alreloc_decide.py: 189718 positions; decided: port_core WRONG 22, port_core right 9290; not in scope: 180406

The 22 positions the decision rules call `port_core WRONG` are the values this unit states otherwise than the donor, each
read by hand (records/alreloc-wrong-rows.tsv): 17 in A/AD1o.v and 3 in A/AD25.v are ends, start + 0x20 or quotients by 8 of
the zero-shadow piece each lemma takes (METHOD.md item 2; the rules read the donor's one whole-.bss range); 2 in A/AFem.v
are the TOT_range count 127008 (METHOD.md item 3; the rules read the donor's 127070 as a kept constant). All 22: port_core
RIGHT. port_core is wrong at 0 numeral positions; 0 positions are undecided.

The G patches add 16 numeral positions (`added` 170 against 154 before them) and rewrite 3 donor lines (`not-covered` 83
against 80): the two groups added for the run of record decide them. A numeral below 0x10000 on an added line is no
address (the existing `added-line` group); a comment line g-AD2f.patch adds names g_cfg at 0x5df080 and OW at 0x5f3060,
and the group checks each against the twin's symbol of that name; a donor line g-AD1r.patch rewrote (A/AD1r.v:232, 294,
330, `(-208)` / `(usp - 208)`) keeps its numeral in the line written in its place (the whole donor line inside it, or
similarity >= 0.8). Without these groups a first pass (on work-rec4, before afet-cost.patch) left 5 positions UNDECIDED.

## Planted control and sweeps

- `alreloc-xcheck-control.sh WORK LIB OUT`: `controls: 8 planted, 8 caught, 0 other rows changed` (records/control.log).
  The czone plant writes the donor's 0x80050000 back: `port_core WRONG: the bound must be >= 0x800b663c and <= 0x800b9c00`.
- Sweep seed 1, 80 plants: `controls: 80 planted, 80 caught, 1 other rows changed` (records/sweep.log). The changed row,
  A/AFkp.v:62 tok 7, is the value 0xad6f0 of `lit8 0xa40a0 0xad6f0`, whose address (tok 6) was planted.
- Sweep seed 2, 120 plants: `controls: 120 planted, 120 caught, 4 other rows changed` (records/sweep2.log). Each changed row
  reads a planted value: A/AB1u.v:316, :896, :1176 are `fetch_word ... = Some W_x` facts whose W_x is the Definition planted
  on the line above; A/AB1u.v:1285 is the W_x of the fetch fact at :1286, whose address was planted.
- The seeded sweeps draw their plants from the positions the record run decides right (8690 candidates), so a change in
  the decided set changes which positions are planted; the changed rows above are those of this run's plants.

## The czone decision group, for the run of record

The group accepted any CZONE bound at or above the highest constant shadow byte (0x800b663c). In a first pass on this run
the sweeps planted 0x800b9c08 (A/AFju.v:577, A/AFix.v:290) and the group took it as right, though the build's goal at
A/AFju.v:663 needs the bound at or below kLowShadowBeg + IMG_TOP / 8 (METHOD.md item 1). The group now also requires HI <=
kLowShadowBeg (read from stage-out Reusable/YG0f.v) + IMG_TOP / 8 (read from the image) when stage-out A/AFjm.v states
map_facts SM1: 0x7fff7000 + 0x616000 / 8 = 0x800b9c00. Both sweep plants are now caught (`the bound must be >= 0x800b663c
and <= 0x800b9c00`, records/sweep.log, sweep2.log).

## alreloc's own mis-maps (from the rows, records/alreloc-crosscheck-rows.part-1.tsv to part-5.tsv)

records/alreloc-crosscheck-rows.tsv is kept in five parts (over the 5 MiB cap per file); only part 1 has the header
line. `cat records/alreloc-crosscheck-rows.part-*.tsv` restores it byte for byte (sha256
9c5dc1563e33e376afcea11093f96d4666a76dfa9eef419dd2e5e2b6c4a84009).

alreloc's value is wrong where the decisions settle a disagreement against it. records/record-tables.md, generated by
alreloc_record.py from the rows, lists the 22 port_core WRONG rows, the 0 UNDECIDED rows, the counts by class and decision
group, alreloc judged by the decisions, every disagreement (191 rows) with its decision, the planted control and sweep, and
the pins of the run.

## Limits

- Out of scope, as in D9's record: both-kept values below 0x10000 with no alreloc rule row (function offsets, counts,
  immediates) and values above the image outside its shadow; they are listed with decision `-`.
- img-b-eq (A/AD2f.v IMG_B_eq) rests on a premise each of its rows states: the paths through the split region R_A5a call
  no unwinder function (libunwind, unw_*). The lemma's proof is `vm_compute. repeat split; reflexivity.`, so the closing
  build checks these positions when it compiles A/AD2f.v. region-count and img-b-eq read LIB/A/AD2j.v (T3r's cut file at
  the pin: 54 regions).
