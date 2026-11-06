# Gate (a) on the run of record: port_addr_check 205a90fd19b8

proves no function (kind: measurement). The address checker over the relocated core (WORK = work-rec5, the run of
record), with every flagged, GENERATOR-FILL and UNMEASURED-NAME row triaged. 205a90fd19b8 is the address checker of record
after 08:00Z (the row owner's relay of 2026-10-31; read-only copy CKDIR/versions/205a90fd19b8/). Before it the gate ran
0d24592683b6 (the version of record from 23:46Z); the comparison of the two on the same run is below.

## Command

    gates/flag-gate-A.sh WORK LIB OUT/pac        (run by checks/run-gates.sh; records/run-gates.txt has its exit status and time)

- `gates/flag-gate-A.sh` runs the record pass (`gates/pac-A.sh`: one default pass, `--paired-only --summary --donors-from
  DONORS --cache OUT/pac/rec.cache --fail-on-flags`, every input pinned by sha256, exit 5 on a mismatch), `gates/triage-A.py`
  over every row, and the three controls. Script sha256 (records/flag-gate.txt line 2): pac-A.sh cf205cb0cdd8,
  flag-gate-A.sh 1624404302eb, triage-A.py ce9ec163a04c.
- Checker: CKDIR/versions/205a90fd19b8/port_addr_check.py, sha256 205a90fd19b8; `checker files: 6 of 6 in
  versions/205a90fd19b8.SHA256SUMS OK` (port_addr_check.py, scan_literals.py, inputs_used.py,
  identity-quotients/qscan.py and imgquant.json, insn-targets/insn_targets.py). Images: src fuzz_grant.asan c2c7559b29bd
  (twin 57c26f993615), dst fuzz_transport.asan e89be137db17 (twin 86efc3a80314). Inputs (records/flag-gate.txt line 5):
  WORK/stage tree cb94de36d3c6, WORK/stage-out tree 3df9dee2b44d (492 files each), port_core 83f5203d2a2f, LIB/A/AB13.v
  1fb1a9636438, AF0m.v 5dfdd0e65356, AD2j.v f32f53f83a52 (T3r's cut start-up layer), overrides.tsv 50a44ad70d1b (the run read e796f27baba3; the two
  differ in one comment line), the 14
  patches WORK/patches.log names.
- Adapted from libdiginet/fuzz_decode's image-A core record (D9): its gates/pac-A.sh, flag-gate-A.sh, triage-A.py (sha256 e6f5f0468baa, bbc099633d6d, 77f73f67f443;
  internal records). For the run of record,
  triage-A.py gained measured rules (P-BSSZR, P-GHUNK, P-LINEPAIR, N-IMGSPAN and the patch-aware override cross-check) and
  its CZONE rule changed with the decision (below); flag-gate-A.sh lists every patch the run applied and names its outputs
  by the checker sha; both scripts take every host path from a named variable.

## Result (quoted from records/flag-gate.txt)

    FLAG-CLASSES 575d398c6022	27 classes count as findings (--list-flag-classes prints them)
    FLAGGED 465 rows in 9 classes: DIFFERENT-SYMBOL=15 GEOMETRY-CHANGED=10 KIND-CHANGED=9 NON-ADDRESS-CHANGED=175 SAME-VALUE-DIFFERENT-OBJECT=20 STALE-DONOR-CODE-POINTER=3 UNPAIRED-PORTED=149 UNPAIRED-SOURCE=68 UNRESOLVED=16
    UNMEASURED 1 rows in 1 classes: UNMEASURED-NAME=1 (measured by nothing: neither a finding nor a pass)
    checker <file> rc=4 (sha256 205a90fd19b8)
    checker files: 6 of 6 in versions/205a90fd19b8.SHA256SUMS OK
    GENERATOR-FILL 7 (reported, not counted)
    triage-A.py rc=0: 465 flagged rows + 7 GENERATOR-FILL: 472 explained, 0 UNEXPLAINED
    1 UNMEASURED-NAME rows (reported, measured by nothing): 1 explained, 0 UNEXPLAINED
    classification of the flagged + GENERATOR-FILL rows: OK-explained 437, TOOL-LIMIT 35, REAL 0, UNEXPLAINED 0
    controls: PASS (each plant: exactly one flagged row added to the unplanted control's rows and none removed, ...)

The per-row table is records/gate-205a90-triage-rows.tsv (raw_line, verdict, src_file, src_line, dst_line, sentence, idx,
kind, src_value, dst_value, reason, class, known, detail; 473 rows: the 472 above and the 1 UNMEASURED-NAME row, class
OK-explained 438 = 437 + 1, TOOL-LIMIT 35); records/gate-205a90-TRIAGE.md has the per-reason tables; records/rec-triage.out
the counts by reason and the region layout line (`donor (33, 24, 28), unit (54, 44, 49) (LIB/A/AD2j.v), N-REGCNT rows 50:
recomputed`).

Addendum (08:4xZ): records/PAC-NAMEDIFF.md diffs the named-symbol rows of the two checkers on this run for the fail-open
the checker's owner reported for 205a90fd19b8: 54 rows that 0d24592683b6 flagged (DIFFERENT-SYMBOL 48, UNMEASURED-NAME 6)
pass as SAME-SYMBOL under 205a90fd19b8, and in all 54 the stated function is a different function from the one at the
value (A/AB1w.v labels the released donor carries; the donor's and the port's values name the same symbols, so the
relocation is right).

## The two classes NON-ADDRESS-CHANGED and STALE-DONOR-CODE-POINTER: findings new against 0d24592683b6

Both checkers ran on the same run (work-rec5): 0d24592683b6 with the same scripts in the earlier gate run, 205a90fd19b8
here. Rows compared by class, file, lines and values (the two gate-*-triage-rows.tsv):

| class | 0d24592683b6 | 205a90fd19b8 | new in 205a90fd19b8 | gone |
|---|---:|---:|---:|---:|
| NON-ADDRESS-CHANGED | 174 | 175 | 1 | 0 |
| STALE-DONOR-CODE-POINTER | 10 | 3 | 0 | 7 |

The one new finding, read from the cell's use:

| file:line (donor -> stage-out) | value | the cell's use | verdict |
|---|---|---|---|
| A/AD1g.v:1276 -> 1277 | 0x5ea000 -> 0x606000 | `Lemma static_img_chk : forallb (fun r : Z * Z => (0x10000 <=? fst r) && (fst r + snd r <=? 0x10000 + 0x606000))%bool (Tfib_owned_static ++ Tfib_zero_shadow) = true.`: every owned or zero-shadow range of the start-up AF0m.v lies in [IMG_LO, IMG_LO + SPAN). The value is the image span: 0x616000 - 0x10000 = 0x606000 (fuzz_transport.asan's page-up last PT_LOAD end 0x6153d0, its first PT_LOAD vaddr); the donor's 0x5fa000 - 0x10000 = 0x5ea000. 205a90fd19b8's size-name slot rule flags a size that changed; this size must change with the image (rule N-IMGSPAN) | RIGHT (the image span; the lemma is checked by the build) |

The other 174 NON-ADDRESS-CHANGED rows are the rows 0d24592683b6 also flagged, with the same reasons (N-FMTPTR 113, N-REGCNT
45, P-BSSZR 4, FMTWIN 3, N-CELLPATCH 2, N-IAL 2, N-TOT 2, N-AD1o-TOP 1, N-DEPOT 1, N-INST 1); the 3 STALE-DONOR-CODE-POINTER
rows are SDCP-SIZE (262144 = 0x40000, an mmap length), each a row 0d24592683b6 also flagged.

## Controls (records/flag-gate.txt)

| control | change to a copy of stage-out (checked with --include A/AF0l.v) | result |
|---|---|---|
| plant 1 | `pc_wrap_memcpy` = 0x93734 (fuzz_transport's abort; the file holds 0x523ac) | `STALE-DONOR-CODE-POINTER=1` added (1 added, 0 removed), rc 4, triage UNEXPLAINED |
| plant 2 | `pc_wrap_memcpy` = 0x523b0 (pc_asan_memcpy's value in the same sentence) | the same |
| unplanted | none | `UNPAIRED-PORTED=1` only (the class-5 arm key, P-AF0L); the pair not flagged; triage rc 0 |

## Rules changed for the run of record, each with its measurement

- K-CZONE (9 rows, A/AFhn, AFix x2, AFjb x2, AFju x2, AFkm, AFkz): accepts the dst value only when it equals kLowShadowBeg
  (read from stage-out Reusable/YG0f.v) + IMG_TOP / 8 (read from the image), map_facts SM1 `kLowShadowBeg + TFIB_IMG_END /
  8 <= SMv` is present in stage-out A/AFjm.v, and the highest shadow end of the image's 40 registered globals (0x800b663c,
  read from asan_globals) is at or below it: 0x7fff7000 + 0x616000 / 8 = 0x800b9c00 (METHOD.md item 1). In this run the
  checker classes all 9 rows UNRESOLVED (a dry run had KIND-CHANGED); the rule takes both classes.
- P-BSSZR (20 rows, A/AD1o.v and A/AD25.v): the dst line is a line bss-zero-range.patch added (patches.log names the file),
  and the dst value is an end, the start + 0x20 or a quotient by 8 of exactly one zero-shadow piece that the patch writes
  in that file as `(lo, hi - lo)` and that is an entry of LIB/A/AF0m.v Tfib_zero_shadow (25 pieces): [0x5f31e0, 0x616000)
  in A/AD1o.v, [0xa9340, 0x5df0b8) in A/AD25.v (METHOD.md item 2).
- P-GHUNK (10 rows): a numeral below the image base 0x10000 (no address of either image) on a line a G patch added
  (UNPAIRED-PORTED: the out-window count 0 of `ajournal_gx ... G 0 []` at A/ACfn.v:56 and A/AD1w.v:100; 0, 2, 64 of
  `0 <= a < 2 ^ 64` at A/AD1r.v:229 and :301; 0xd0 = 208 of `(usp - 208)` at A/AD1r.v:340), or on a line a G patch
  deleted whose replacement keeps the value (UNPAIRED-SOURCE: A/AD1r.v:330 `(usp - 208)`, the same sentence with memS and
  Hag added; similarity >= 0.8). The rule reads the added and deleted lines from EV/g-*.patch and the files from
  WORK/patches.log.
- P-LINEPAIR (4 rows, A/AFet.v): the lines right after afet-cost.patch's two hunks (`... rewrite (C152 (0xa970a + Z.of_nat
  k)) ...`, donor lines 295 and 484, stage-out 296 and 485), which the patch does not change but whose sentence the checker
  no longer aligns, because the patch changed the sentence before them. Paired by line (port_core's provenance line puts
  donor line L at stage-out line L + 1): the two lines are the same text with the numerals masked, and at the same position
  the donor's 0xa184a and the port's 0xa970a are each `__asan::instance+0x372` in their own image (twin symtabs).
- N-IMGSPAN (1 row): the image span, above.
- The override cross-check: an override row whose donor line and value match a row must have written the dst value; a row
  that port_core reports `removed by --patch` in WORK/overrides.tsv (22 rows, the A/AD1o / A/AD25 zero-shadow rows) is
  accepted only through P-BSSZR, and no other rule may then explain it.

## TOOL-LIMIT rows (35): the dst value is right, measured; the checker's reading is contradicted by the images

| reason | rows | the checker's reading, and what the images give |
|---|---:|---|
| SV-MMAP | 18 | an mmap flags word (MAP_* bits, remainder 0) read as `internal_alloc_placeholder` + off |
| G-6128 | 9 | 6128 = kPage + kSecRz - kChunkHeaderSize, an offset from the mmap base, read as load2.memhi - .got.lo of fuzz_grant |
| DS-AB1W-LABEL | 3 | `tfib_[AE]_<x>` row names read as symbol names; they are labels the released donor carries from cgif_file_fuzzer's AB1w; src and dst values hold the same symbol labels in their own symtab |
| SDCP-SIZE | 3 | 262144 = 0x40000 = kUserMapSize, an mmap length, read as a code pointer |
| SV-HWCAP | 2 | 0x20112D, a set of AT_HWCAP ISA bits, read as theDepot + off |

Against 0d24592683b6 on the same run (92 TOOL-LIMIT rows): DS-AB1W-LABEL 51 -> 3, SDCP-SIZE 10 -> 3, SV-RODATA-BOUND 2 -> 0;
205a90fd19b8 no longer flags those cells.

## Known items, each with its reason (records/gate-205a90-triage-rows.tsv, column known)

| item | rows | reason |
|---|---:|---|
| CZONE 0x800b9c00 | 9 | K-CZONE |
| A/AD1o.v / A/AD25.v zero-shadow pieces | 20 | P-BSSZR |
| the G patches (harness globals) | 10 | P-GHUNK |
| lines next to afet-cost.patch, paired by line | 4 | P-LINEPAIR |
| the image span (A/AD1g.v static_img_chk) | 1 | N-IMGSPAN |
| A/AFem.v TOT_range 127008 = 31 + 1 + 31 * DEPOT_MAX | 2 | N-TOT |
| tfib_rodata_hi 0x22b4c, the .rodata end | 1 | U-RODATA-HI |
| the dead arm removed from A/AD1g.v | 3 | PATCH-DEADARM |
| region counts (IMG_E, IMG_B, PM_tailL and others) | 50 | N-REGCNT: mapped from the donor's IMG_REGIONS layout (N 33, R_A5a at 24, R_A7b at 28) to LIB/A/AD2j.v's (N 54, R_A5a_1 at 44, R_A7b at 49), T3r's cut file at the pin |

There is no REAL row: every dst value is fuzz_transport's own value of the quantity the src value names in fuzz_grant's
image, or this unit's own value with the measurement above.
