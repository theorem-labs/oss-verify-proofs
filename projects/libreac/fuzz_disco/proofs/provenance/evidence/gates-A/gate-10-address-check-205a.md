# Gate 10 — address checker port_addr_check 205a90fd19b8, image A (fuzz_disco.asan), on the series tree

Kind: measurement; proves no function. `port_addr_check` 205a90fd19b8 was installed after 0d24592683b6. Gates 1, 6 and 9
stand unchanged. This gate runs 205a90fd19b8 and 0d24592683b6 with gate 1's command and file set over the SERIES tree
(the base plus the unit owner's code fixes), compares the two versions row by row on that one tree, triages every
flagged row of 205a90fd19b8 and every row whose verdict moved, and runs gate 1's planted control and the checker owner's
planted size on 205a90fd19b8.

## Command (run.sh `addr205a`, every path a variable; no host path)

```
port_addr_check.py --git $HUB --donors-from $DONORS --summary --fail-on-flags \
  --src $CGIF_REF:proofs/cgif/cgif_file_fuzzer/lib --dst $SERIES:proofs/libreac/fuzz_disco/lib \
  --paired-only --map A/=A/ --map =Reusable/ \
  --src-image A=$CGIF_BIN.asan --src-image B=$CGIF_BIN.asan-ubsan --src-image P=$CGIF_BIN.plain --src-image U=$CGIF_BIN.ubsan \
  --dst-image A=$PIN_A:$TWIN_A --dst-image B=$PINS/fuzz_disco.asan-ubsan:$TWINS/fuzz_disco.asan-ubsan \
  --dst-image P=$PINS/fuzz_disco.plain:$TWINS/fuzz_disco.plain --dst-image U=$PINS/fuzz_disco.ubsan:$TWINS/fuzz_disco.ubsan \
  --assign '**=auto' --include 'A/**' --cache $OUT/addr205a/cache --out $OUT/addr205a/pac-A.tsv
```

The same command with `$PAC0D24`, `--cache $OUT/addr205a/cache0d24` and `--out $OUT/addr205a/pac0d24-A.tsv` gives the
0d24592683b6 table on the same tree. The arguments are those of gates 1, 6 and 9 with ONE change: `--dst` names the
series tree `$SERIES` = d57e4e79e469316d9e26c20fd6bb5ff3a086dd55, not the base. Both runs started from an empty cache.
cgif's four pins are the ones its harness.yaml names (sha256 7093581aab04 / 1c29845fe605 / 19dedd1bc682 / 44a34d2e23b6).

## Tools (cited by name + sha256, not copied)

`port_addr_check.py` sha256 `205a90fd19b85ab3b9f1910ff13f144c1d72a28fe393209e1106a3b26fcdcb69`, run from its versioned
directory; the SHA256SUMS beside that directory lists six files (port_addr_check.py, scan_literals.py, inputs_used.py,
insn-targets/insn_targets.py, identity-quotients/qscan.py and imgquant.json) and `sha256sum -c` passes for all six. Its
finding classes (`--list-flag-classes`, 27 classes, FLAG-CLASSES 575d398c6022) are byte-equal to 0d24592683b6's. The
0d24592683b6 run uses the file of gate 9 (sha256 `0d24592683b610123346567302caf1bf97e5ac9354cf05799dc7cfc21dc0f4fa`).

Its owner lists one measured change against 0d24592683b6 (by way of 9873fe3cf51b, which was withdrawn and never
installed): a page-aligned value is read as a SIZE only in a closed list of size-role slots (`syscall-arg`,
`arith-operand`, `bound`, `declared-field`, `size-name`; the row's note names the slot), every other slot keeps its
address reading, and the size reading is taken before the symbol match, so a size moved as a consistent relocation
(onto the same offset inside the same-named symbol) is NON-ADDRESS-CHANGED where 0d24592683b6 read it SAME-SYMBOL. It
also carries 9873fe3cf51b's changes: a cache fallback for read-only directories, INSN-SAME-AT-TARGET, `--accept-added`,
name variants of one object, and KIND-CHANGED only with the kind on both sides. The limits its owner lists for this
version are in the MANIFEST role of this file.

## The series tree

lib/A of `$SERIES` differs from lib/A of the base in 14 files (29 lines replaced in place, so every line number is the
base's): the unit owner's fixes of the counts gates 6 and 8 record (`AB1v.v:14` 16403 -> 16102, `AE34.v:22` 435 -> 383,
`AE34.v:26` 38 -> 36), the TOT bound `AFem.v:130` / `:208` 127070 -> 127008, the bound `AE7d.v:78` 0x14b740 ->
0x148680, the allocator model's check labels in `AFeu.v`, `AFft.v`, `AFfy.v`, `AFfz.v`, `AFg2.v`, `AFi3.v`, `AFk0.v`
(replaced by tags 1 .. 14), a proof step in `AD1g.v:1070`, and the `timeout 30` of a tactic's first arm removed in
`ACeg.v` and `Prog/YC81.v`. The triage reads the series files (`git archive $SERIES`, run.sh `addr205a`).

## Verdict

205a90fd19b8: exit 4 (findings present). Scope: 395 files paired, 206808 numerals. `FLAGGED 12515 rows in 12
classes`; `UNMEASURED 3365` (UNPAIRED-FILE-UNMEASURED). 0d24592683b6 on the same tree: exit 4, `FLAGGED 12526 rows in
12 classes`. Images as in gate 9: A `5e39150dd810`, B `cee6f04ad3d4`, P `04988e3ab313`, U `56121de6ba4c`; cgif A
`7093581aab04`, B `1c29845fe605`, P `19dedd1bc682`, U `44a34d2e23b6`.

| class | 205a90fd19b8, series | 0d24592683b6, series | 0d24592683b6, base (gate 9) |
|---|---|---|---|
| UNPAIRED-PORTED | 7697 | 7697 | 7697 |
| UNPAIRED-SOURCE | 2963 | 2963 | 2959 |
| NON-ADDRESS-CHANGED | 1394 | 1390 | 1386 |
| DIFFERENT-SYMBOL | 210 | 212 | 212 |
| UNRESOLVED | 114 | 114 | 114 |
| KIND-CHANGED | 103 | 105 | 105 |
| GEOMETRY-CHANGED | 15 | 15 | 15 |
| SAME-VALUE-DIFFERENT-OBJECT | 8 | 12 | 11 |
| STALE-DONOR-ROUNDED | 4 | 4 | 4 |
| STALE-DONOR-CODE-POINTER | 3 | 10 | 10 |
| NO-COUNTERPART | 3 | 3 | 3 |
| IMAGE-EXTENT-CHANGED | 1 | 1 | 1 |
| **flagged** | **12515 in 12 classes** | **12526 in 12 classes** | **12517 in 12 classes** |

Passing classes that differ between the two versions on the series tree: NON-ADDRESS-SAME 172391 / 172067, SAME-SYMBOL
8503 / 8783, SAME-GEOMETRY 4899 / 4925, ROUND-CONSTANT-SAME 54 / 61. UNMEASURED-NAME is 0 rows in both runs.

## Difference from 0d24592683b6 (same tree, same file set and arguments)

`addr/run_diff.py $OUT/addr205a/pac0d24-A.tsv $OUT/addr205a/pac-A.tsv` (run.sh `addr205a/diff`; rows paired by their
identity: file, line, sentence, index, kind and both values). 206808 rows on each side, every identity on both sides.
**374 rows differ: 328 verdicts moved, 46 rows differ in their notes or resolutions only.**

| verdict move | rows | values |
|---|---|---|
| SAME-SYMBOL -> NON-ADDRESS-SAME | 280 | 0x10000 |
| SAME-GEOMETRY -> NON-ADDRESS-SAME | 24 | 0x20000 |
| ROUND-CONSTANT-SAME -> NON-ADDRESS-SAME | 7 | 0x30000, 0x9f000, 0x100000 |
| STALE-DONOR-CODE-POINTER -> NON-ADDRESS-SAME | 7 | 0x40000 |
| SAME-VALUE-DIFFERENT-OBJECT -> NON-ADDRESS-SAME | 4 | 0x200000, 0x109000, 0x209000 |
| KIND-CHANGED -> NON-ADDRESS-SAME | 2 | 0x40000 |
| DIFFERENT-SYMBOL -> NON-ADDRESS-CHANGED | 2 | 0x30000 |
| SAME-GEOMETRY -> NON-ADDRESS-CHANGED | 2 | 0x6f000, 0x5ee000 |

Four rows move into a finding (NON-ADDRESS-CHANGED), 13 move out of one, 311 move from one pass to another. No row
moves into a flag in a generic slot: the three generic register slots that hold the allocator granule (`A/AFk8.v:56`,
`A/AFk9.v:28`, `A/AFk9.v:54`, `pin .. (SLit 262144)`, the cost the owner accepts for this version) are
STALE-DONOR-CODE-POINTER on both versions. Every moved row is read below; the numeral was opened on its line and its
value measured where it is an image quantity.

### The four rows that move into a finding: none is a size the port kept from cgif

| file:line | 0d24592683b6 -> 205a90fd19b8 | numeral (port / donor) | reading |
|---|---|---|---|
| `A/AB13.v:84` (2 rows) | DIFFERENT-SYMBOL -> NON-ADDRESS-CHANGED | 196608 = 0x30000 / 0x9d000 | the low of segment 1 [0x30000, 0x9f000) of the A pin (PT_LOAD 2, vaddr 0x30eac rounded down) in that segment's membership test `(196608 <=? x) && (x + 1 <=? 196608 + 454656)`. The donor numeral it is paired with is cgif's segment-2 low 643072 = 0x9d000 from cgif's next sentence: the port has one sentence more before it (`unfold YImgTop.IMG_TOP in Hx`), the shift gate 1's hand table records. cgif's own segment-1 test states 196608 too. The pin's value, not moved |
| `A/AB13.v:144` | SAME-GEOMETRY -> NON-ADDRESS-CHANGED | 454656 = 0x6f000 / 0x6d000 | the size of segment 1 of the A pin, [0x30000, 0x9f000) (measured); cgif's segment 1 is [0x30000, 0x9d000), size 0x6d000. The target's own size; the checker's `expected 0x6d000` is cgif's |
| `A/AD1g.v:1277` | SAME-GEOMETRY -> NON-ADDRESS-CHANGED | 0x5ee000 / 0x5eb000 | the image span IMG_TOP - kImgLo = 0x5fe000 - 0x10000 of the A pin in Lemma static_img_chk; cgif's is 0x5fb000 - 0x10000 = 0x5eb000 |

In each the port states the A pin's own geometry and the donor states cgif's; 205a90fd19b8 reads a geometry value in a
bound or size-name slot as an image-independent size and expects the donor's. **No row of this run flags a size that
the proof code kept from cgif: 0 DEFECT.**

### The 13 rows that move out of a finding

Gate 9 triaged each of them by a measured rule, and 205a90fd19b8 now reads each as a size:

- the allocator granule 262144 = kUserMapSize (MAP-SIZE) as the length register a1 of an mmap call (a2 = 3, a3 the
  flags; the checker's note: a syscall-arg slot): `A/AFk8.v:97`, `:101`, `A/AFkn.v:776`, `:1065`, `:1073`, `:1081`,
  `:1216` (STALE-DONOR-CODE-POINTER) and `A/AFkn.v:1225`, `:1234` (KIND-CHANGED);
- FS_FROFF 0x109000 / 0x209000 = kFakeFramesOff + (CID << kStackSizeLog) (FAKESTACK-OFFSET): `A/AF0r.v:41`,
  `A/AF0t.v:42`;
- the bound 0x200000 of Lemma entD_ro (LOOSE-BOUND): `A/AE30.v:1395`, `A/AE6k.v:1388`.

### The 311 rows that move from one pass to another (all to NON-ADDRESS-SAME, the value equal on both sides)

- **0x10000** (280 rows, from SAME-SYMBOL). 0x10000 is kImgLo of `Reusable/YG0f.v`, the low of the A pin's first
  page-rounded segment (measured; cgif's first segment starts there too), and 2^16. Read at each occurrence:
  - the image low, the low end of an image address range (`0x10000 <= a < IMG_TOP`, `(0x10000 <=? fst r)`, the shadow
    of [kImgLo, IMG_TOP) `65536 / 8`), 64 rows: `A/AB13.v:147`, `ACeg.v:81`, `AD1f.v:210`, `AD1g.v:473`,
    `AD1j.v:116`, `AD1o.v:22`, `AD1r.v:207`, `AD1u.v:99`, `:101`, `AD1y.v:149`, `:191`, `AD2b.v:27`, `AD2d.v:133`,
    `AD2g.v:23`, `AD2k.v:71`, `:83`, `:93`, `AE6x.v:93`, `AFev.v:431`, `AFf4.v:340`, `:355` (2), `:531`, `AFfy.v:118`,
    `:170`, `:171`, `:175` (2), `:246`, `AFg0.v:155`, `AFg1.v:552`, `:605`, `:606`, `:610` (2), `:674`, `:725`,
    `AFg3.v:287`, `:327`, `AFg4.v:275`, `AFg5.v:507`, `AFg6.v:717`, `AFg7.v:159`, `AFhn.v:62`, `:420`, `AFic.v:128`,
    `:382`, `AFix.v:295`, `:299`, `AFjb.v:299`, `:303`, `AFju.v:574`, `:582`, `:620`, `AFjy.v:831`, `:913`, `:1595`,
    `AFk1.v:767`, `AFk2.v:623`, `:653`, `AFkm.v:620`, `:1307`, `AFkz.v:424`, `:899`; with 11 rows of the segment tests
    `A/AB13.v:83` (2), `:103` (2), `:124`, `:130` (2), `:141` (2) and `A/AD1g.v:1277` (2), and the start-up files
    `A/AD1k.v:228`, `A/AD2i.v:75`;
  - a 64 KiB window, below the user stack pointer (`usp - 65536 <= a < usp`, a stack-relative region low -65536) or
    win_check's read window, 67 rows: `A/AD1r.v:128` (2), `:561` (2), `:620`, `:704`, `:756`, `:814`, `:925`, `:968`,
    `AD1v.v:45`, `:58`, `:325`, `:336`, `AD1w.v:169`, `AD1x.v:104`, `AD1y.v:45`, `:50`, `:77`, `:105`, `:229` (2),
    `:293`, `:318`, `AD1z.v:240`, `:274`, `:301`, `AD21.v:33`, `AD23.v:193`, `:356`, `:482`, `:543`, `:567`,
    `AD25.v:107`, `:196`, `:343`, `:579`, `:750`, `AD26.v:79` (2), `:186`, `AD27.v:213`, `:228`, `:315`, `:363`,
    `:459`, `:636`, `:706`, `:774`, `AD28.v:115`, `:123`, `:226`, `:246`, `AD29.v:156`, `:219`, `AD2a.v:129`,
    `AD2c.v:138`, `AD2d.v:286`, `:367`, `AD2e.v:277`, `:432`, `:525`, `:578`, `:585`, `AD2f.v:285`, `AD2g.v:112`,
    `AD2h.v:58`;
  - an alignment or granule of an address (`SB mod 65536 = 0`, `q * 65536`, the stack top rounded to 64 KiB
    `u eSp1 + 65536`), 64 rows: `A/AD1e.v:232`, `AD1g.v:388`, `:392`, `:407`, `:412` (2), `:414`, `:415` (2),
    `:420` (3), `:423`, `:425` (3), `:968`, `:1116`, `:1155`, `AFfc.v:113`, `AFfi.v:107`, `AFfr.v:104`, `AFg6.v:92`,
    `AFgk.v:192`, `:221`, `AFgs.v:195`, `:226`, `AFgu.v:101`, `AFgx.v:159`, `AFhc.v:123`, `:140`, `AFhl.v:228`,
    `AFjm.v:259`, `AFk5.v:183`, `:210`, `:223` (2), `:538`, `:543` (2), `:562`, `:566`, `:568`, `:570`, `:572`,
    `:573`, `AFkm.v:1090`, `:1098`, `:1217`, `:1219`, `:1240`, `:1241`, `:1410` (2), `:1421`, `:1422`, `:1460` (2),
    `AFkn.v:780`, `:1887`, `AFko.v:147`, `:174`, `:187` (2);
  - a size bound or length of the program or the allocator model (buffer capacity `65536 <= cap <= 2 ^ 26`, request
    length `1 <= want <= 65536`, a malloc / read length register `SLit 65536`, kMaxSize of `Reusable/YG00.v`), 33 rows:
    `A/AD1r.v:587`, `:1031`, `AD1t.v:48`, `:71`, `AD1v.v:162`, `:174`, `:183`, `:349`, `AD1w.v:49`, `:228`,
    `AD1z.v:21` (2), `:130`, `:160`, `:168`, `:412`, `AD20.v:129`, `AD23.v:131`, `:314`, `AD25.v:105`, `:314`, `:391`,
    `:478`, `:554`, `:710`, `AD2g.v:96`, `:132`, `AFf9.v:376`, `AFho.v:13`, `AFis.v:307`, `:312`, `:327`, `:354`;
  - the weight of byte 2 in a little-endian word (`b0 + 256 * b1 + 65536 * b2 + ..`), 27 rows: `A/AF0x.v:448`,
    `AFem.v:48`, `:52` (2), `:54` (2), `:56`, `:57`, `:59`, `:67`, `AFff.v:143`, `:152`, `:157`, `:158`, `:159` (2),
    `:160` (2), `:164`, `:175`, `:176`, `:187`, `:189`, `:191`, `AFfg.v:143`, `:171`, `:202`;
  - the bound of a 16-bit value (`0 <= v < 65536`), 12 rows: `A/AFel.v:181`, `:188`, `:195` (2), `:204` (2) (these
    two lines also bound `nb + 16 * 65536`), `AFfc.v:254`, `AFfr.v:134`, `AFgi.v:282`, `AFgm.v:272`, `AFgs.v:230`,
    `AFgx.v:126`.
- **0x20000** (24 rows, from SAME-GEOMETRY): 131072 = kPtrArrayCommit of `Reusable/YG00.v` (the secondary allocator's
  pointer-array commit: the region `[QSv, QSv + 131072)`, the mmap length a1 with `a7 = 222`, the eager-memory step),
  23 rows: `A/AFjt.v:591`, `:599` (2), `:600`, `:606`, `:718`, `:719`, `:720`, `:800`, `:802`, `:804`, `:805`, `:815`,
  `AFjz.v:1016`, `:1080`, `AFk0.v:1004`, `:1065`, `:1124`, `:1148`, `:1232`, `:1240`, `:1319`, `:1337`; and
  `A/AB13.v:132`, 131072 = the size of segment 0 [0x10000, 0x30000) of the A pin in its membership test.
- **0x30000, 0x9f000** (6 rows, from ROUND-CONSTANT-SAME): the lows of segments 1 and 2 of the A pin in their
  membership tests, `A/AB13.v:104` (2), `:142` (2) and `:85` (2).
- **0x100000** (1 row, from ROUND-CONSTANT-SAME): `A/AFem.v:208` `0 <= bkt < 1048576`, the stack depot's bucket count
  d_tab_words = 2 ^ 20 (`Reusable/YG0f.v`; bkt indexes the buckets, `S2 = TFIB_DEPOT + 4 * bkt`).

### The named-symbol fail-open of 205a90fd19b8 (the checker owner's notice after installation)

A function-table cell whose name is a different function than the one at its value can read SAME-SYMBOL with no
marker when one name contains the other. On this tree **no row reads DIFFERENT-SYMBOL or UNMEASURED-NAME on
0d24592683b6 and SAME-SYMBOL on 205a90fd19b8**: no row moves into SAME-SYMBOL at all (the moves above), UNMEASURED-NAME
is 0 rows in both runs, and run.sh `addr205a/named` checks the diff for such a move. The cells of that shape are
lib/A/AB1w.v's; addr_triage.py measures every one of them by exact name against the A pin's twin (2570 of 2570
`tfib_A_` / `tfib_E_` cells equal the start / end of the twin's function of that name, whatever the checker's verdict):
`tfib_A___asan_register_globals` is 0x3f518 = `__asan_register_globals` (`__asan_register_elf_globals` is 0x40900) and
`tfib_A___interceptor_strlen` is 0x42a54 = `__interceptor_strlen` (`__interceptor_trampoline_strlen` is 0x429c4).

## Per-row triage

`addr/addr_triage.py` over the series files with `addr/hand-triage-series.tsv`, the moved rows given with `--also`
(run.sh `addr205a/triage`): **12515 flagged, 12515 triaged, 12515 right, 0 DEFECT**, 76 hand rows matching 79 flagged
rows; **328 moved rows (4 findings, 324 not findings), 328 triaged, 328 right, 0 DEFECT**. By class: STARTUP 6785,
SYMTAB 2504, NO-PORTED-VALUE 1366, IMAGE-BYTES 1124, KERNEL 182, SMALL-QUANTITY 181, AE3I 148, MAP-SIZE 65, IDENT 48,
SHADOW-SET 30, SEGMENT-TABLE 22, IMAGE-SPAN 21, DERIVED 9, AF0M-CELL 8, REGION-COUNT 6, SYMBOL 6, SEGMENT-GEOMETRY 4,
COUNT-BOUND 2, DECODE 2, SIZE 1, TEXT-COUNT 1. On this tree a KERNEL row is inside a fail-loud vm_compute / fetch_word
fact of the series tree, so the series build checks it.

The rules added to addr_triage.py read only rows whose note carries 205a90fd19b8's size-slot reading, so on the tables
of gates 1, 6 and 9 the per-row triage is byte-equal to the version before them (cmp). Each measures its fact first:

| rule | rows | measured fact |
|---|---|---|
| SEGMENT-GEOMETRY | 4 findings + 18 moved passes | the value is the low, size or end of a page-rounded segment of the A pin, in that segment's own membership test on the line, or the image low / span in Lemma static_img_chk |
| IMAGE-LOW, WINDOW-64K, ALIGN-64K, SIZE-BOUND-64K, BYTES-2^16, RANGE-16BIT | 267 moved passes | the value is 0x10000 = kImgLo of `Reusable/YG0f.v` = the low of the pin's first page-rounded segment, equal on both sides; its use is read at each occurrence on the line by the patterns the script lists |
| NAMED-SIZE | 23 moved passes | the value is the value of exactly one named Z constant of `Reusable/YG00.v`, `YG0f.v`, `YG01.v` (here kPtrArrayCommit = 131072) |

`addr/hand-triage-series.tsv` is gate 1's hand table without the three rows that do not apply to the series tree
(`A/AB13.v:84` DIFFERENT-SYMBOL twice, which SEGMENT-GEOMETRY now measures as NON-ADDRESS-CHANGED rows, and
`A/AB1v.v:14` with 16403) and with four rows of the series tree that no rule covers:

| file:line | verdict | class | check and reading |
|---|---|---|---|
| `A/AB1v.v:14` | GEOMETRY-CHANGED 16403 -> 16102 | TEXT-COUNT | the series fix of gate 6's DEFECT row: (.text end - 0x8f310) / 4 = (0x9eea8 - 0x8f310) / 4 = 16102, the file's own rule, measured from the pin's section table; the checker's expected 16104 runs 8 bytes past .text |
| `A/AFem.v:130`, `:208` | NON-ADDRESS-CHANGED 127070 -> 127008 | COUNT-BOUND | TOT = length ly_tr0 + 1 + depot_frames S <= 31 + 1 + 31 * 4096 = 127008, from lo_tr0 (`Reusable/YG0f.v`, length ly_tr0 <= 31), depot_frames_bound (31 per trace) and depot_len_bound (DEPOT_MAX = 4096, `Reusable/YG01.v`); the lemma is proved from those three. cgif's 127070 is a count bound an earlier relocation moved as an address; the series tree no longer carries it |
| `A/AFem.v:208` | NON-ADDRESS-SAME 0x100000 (moved) | TABLE-BOUND | d_tab_words = 2 ^ 20 = 1048576 (`Reusable/YG0f.v`), the depot's bucket count, which bounds bkt |

## Planted controls

- **Gate 1's plant (must fire).** A copy of the series tree's `lib/A/AE2k.v` with `FF_mask` moved from `0x103b8` to
  `0x30eac` (`_start`, a code symbol), re-run over that one file on 205a90fd19b8: exit 4, `FLAGGED 19 rows in 3
  classes`, and the row reads `DIFFERENT-SYMBOL 0x103a0 -> 0x30eac`, `expected 0x103b8`. Recorded `FIRED`.
- **The checker owner's plant**, a size moved as a consistent relocation (its round_fa granule 0x40000 -> 0x4051c). The
  same file here, `lib/A/Bz/A/R_prim_defs.v:34` (`round_fa x := ((x + 0x3ffff) / 0x40000) * 0x40000`), pairs with no
  cgif file (UNPAIRED-FILE-UNMEASURED: nothing in it is checked), so the plant cannot be placed there. The nearest
  equivalents in paired files, each the numeral set to where an address relocation would move it:
  - **G**, the same granule: 262144 as the `/` operand of `A/AFkm.v:611` (`change (262144 / 8) with 32768`) set to
    0x410d4. cgif's 0x40000 is `UnpoisonBeforeMain`+0x80 (cgif 0x3ff80), and the A pin's `UnpoisonBeforeMain` is
    0x41054. 205a90fd19b8: exit 4, `NON-ADDRESS-CHANGED`, "a size in a arith-operand slot that CHANGED ... expected
    0x40000", `FIRED`. 0d24592683b6 on the same copy: SAME-SYMBOL, "both sides are _ZL18UnpoisonBeforeMainv+0x80".
  - **B**, a power-of-two bound: 0x200000 of `A/AE30.v:1395` (Lemma entD_ro) set to 0x2030c0 (cgif's 0x200000 is
    `theDepot`+0x78128; the A pin's `theDepot` is 0x18af98). 205a90fd19b8: exit 4, `NON-ADDRESS-CHANGED` "in a bound
    slot", `FIRED`. 0d24592683b6: SAME-SYMBOL (`theDepot`+0x78128 on both sides), exit 0, 0 findings.

  On 0d24592683b6 both plants pass, which is the hole 205a90fd19b8 closes.

## Re-run

run.sh `addr205a` re-run into a second, empty output directory (the same pins and tools by sha256, new empty caches):
every verdict line PASS / FIRED (`pac-A`, `pac0d24-A`, `diff`, `named`, `triage`, the plant `FIRED`, `plantG-205a`
and `plantB-205a` `FIRED`, `plantG-0d24` and `plantB-0d24` PASS as SAME-SYMBOL), and all seven tables row-identical to
the first runs (comment lines, which name the run's own paths, aside; sha256 of the non-comment lines, first 16 hex):
205a90fd19b8 `122d9fac38e8e428`, 0d24592683b6 `c628d6423fdc9f33`, gate 1's plant `950d48e4e28ab8d7`, plant G
`de1580f9ffb061eb` / `1e7e22f6bec127da`, plant B `8a503b6e2848cbaa` / `bfdcedeed3707c46` (205a90fd19b8 / 0d24592683b6).
The moved-row list and the per-row triage table are byte-equal to the first run's (cmp).
