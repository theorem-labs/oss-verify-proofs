# G11: the address checker 205a90fd19b8 over the image B files, on the series tree (gate record)

Proves no function (kind: measurement). Run 2026-10-31 (`run.sh g11`) on the series tree `d57e4e79e469` (run.sh:
`SERIES`): the series base b1afc3e80791 with the unit's later fixes (among them YE34.v:20 and :24, ruled in G9). Its
owner installed port_addr_check 205a90fd19b8 at 2026-10-31 08:00Z. 0d24592683b6 is run again here on the same tree,
so that the two versions are compared on one tree. The G10 (0d24592683b6 on the series base), G7 and G1 records stand
beside this one, unchanged.

## Tool
port_addr_check.py, sha256 `205a90fd19b85ab3b9f1910ff13f144c1d72a28fe393209e1106a3b26fcdcb69`, run from its version
directory. Before the runs, run.sh checks it, 0d24592683b6 and the five files beside each against the shas of their
SHA256SUMS (the five are the same files for both versions: inputs_used.py `3ed6c0c79f05...`, scan_literals.py
`f0ec1e108ff8...`, insn-targets/insn_targets.py `efdf3951d4bb...`, identity-quotients/qscan.py `7baa52331b8c...`,
identity-quotients/imgquant.json `7bd088dd7fed...`). Its `--list-flag-classes` output is byte-equal to
0d24592683b6's (27 classes; `FLAG-CLASSES 575d398c6022` in all four summaries).

Its change against 0d24592683b6, as its owner records it: it carries the six changes of 9873fe3cf51b (never
installed: a default cache directory, INSN-SAME-AT-TARGET, a size reading of page-aligned values, name-variant code
cells, `--accept-added`, a one-side coincidence read NON-ADDRESS-SAME), and makes the size reading SLOT-GATED: a
page-aligned value is a size only in a closed list of slots (syscall-arg, arith-operand, bound, declared-field,
size-name), read before the symbol key, and a size whose value changed is NON-ADDRESS-CHANGED.

## Commands
(1) The gate: G1's command with the tool replaced and the series tree as `--dst`, every other argument the same:
```
python3 "$PAC205" --git "$GIT" --donors-from "$DONORS" --summary --fail-on-flags \
  --src c8557374ad2e:proofs/cgif/cgif_file_fuzzer/lib --dst d57e4e79e469:proofs/libreac/fuzz_disco/lib \
  --paired-only --map A/=A/ --map =Reusable/ \
  --src-image A="$CGIF_BIN/cgif_file_fuzzer.asan" --src-image B="$CGIF_BIN/cgif_file_fuzzer.asan-ubsan" \
  --src-image P="$CGIF_BIN/cgif_file_fuzzer.plain" --src-image U="$CGIF_BIN/cgif_file_fuzzer.ubsan" \
  --dst-image A="$PIN_DIR/fuzz_disco.asan" --dst-image B="$PIN_DIR/fuzz_disco.asan-ubsan" \
  --dst-image P="$PIN_DIR/fuzz_disco.plain" --dst-image U="$PIN_DIR/fuzz_disco.ubsan" \
  --assign '**=auto' --include 'Y*.v' --cache "$WORK/g11/cache" --out "$WORK/g11/pac205-Y.tsv"
```
(2) The same with each `--dst-image K="$PIN_DIR/fuzz_disco.<build>:$TWIN_DIR/fuzz_disco.<build>"` (the unstripped
twins' `.symtab`), cache `$WORK/g11/cache-t`. (3) and (4): 0d24592683b6 (`"$PAC0D"`) with the arguments of (1) and
(2), caches `cache-0d` and `cache-0dt`. run.sh starts the four at once. Every cache starts empty: (1) and (3) hits 0,
misses 8; (2) and (4) hits 0, misses 4.

## Result (about 11 min for the four): rc 4 each; count files paired 836; 397415 numerals

| finding class | 0d24592683b6 on the base (G10) | 0d24592683b6 (3) | 205a90fd19b8 (1) | 0d24592683b6 PIN:TWIN (4) | 205a90fd19b8 PIN:TWIN (2) |
|---|---|---|---|---|---|
| UNPAIRED-PORTED | 16038 | 16038 | 16038 | 16038 | 16038 |
| UNPAIRED-SOURCE | 7282 | 7291 | 7291 | 7291 | 7291 |
| NON-ADDRESS-CHANGED | 2595 | 2597 | 2604 | 2595 | 2602 |
| KIND-CHANGED | 954 | 954 | 949 | 956 | 951 |
| DIFFERENT-SYMBOL | 415 | 415 | 415 | 436 | 436 |
| UNRESOLVED | 190 | 190 | 190 | 170 | 170 |
| SAME-VALUE-DIFFERENT-OBJECT | 55 | 55 | 51 | 55 | 51 |
| STALE-DONOR-CODE-POINTER | 26 | 26 | 19 | 26 | 19 |
| STALE-DONOR-DATA-POINTER | 5 | 5 | 5 | 5 | 5 |
| STALE-DONOR-ROUNDED | 4 | 4 | 4 | 4 | 4 |
| GEOMETRY-CHANGED | 3 | 3 | 3 | 3 | 3 |
| IMAGE-EXTENT-CHANGED | 2 | 2 | 2 | 2 | 2 |
| NO-COUNTERPART | 2 | 2 | 2 | 2 | 2 |
| INSN-CHANGED | 1 | 1 | 1 | 1 | 1 |
| FLAGGED (classes) | 27572 (14) | 27583 (14) | 27574 (14) | 27584 (14) | 27575 (14) |

`UNMEASURED`: (1) and (3) 2925 rows in 2 classes (UNMEASURED-NAME 1, UNPAIRED-FILE-UNMEASURED 2924); (2) and (4)
2924 rows (UNPAIRED-FILE-UNMEASURED).

## Diff against 0d24592683b6 on the same tree (g11_triage.py, row by row)
Rows are keyed by (src_file, src_line, dst_file, dst_line, sentence, idx, kind, src_value, dst_value) and
occurrence; both versions give the same 397415 keys. (1) against (3) and (2) against (4) give the same **715 rows that
differ**: 98 in the note only (NON-ADDRESS-SAME in both; 205a90fd19b8 adds its size-slot note) and **617 in the
verdict**:

| verdict move | rows | rule (G11-rows.tsv) | the numerals, read on their lines |
|---|---|---|---|
| SAME-SYMBOL -> NON-ADDRESS-SAME | 548 | UNCHANGED-PASS | 65536 in both trees; 0d24592683b6 read it as PT_LOAD 0's address, 0x10000 in all four pins and all four cgif pins. Roles: the image base 112, a 2^16 factor of a positional weight 108, the 64 KiB stack window 73, a 64 KiB alignment modulus 64, the read loop's input capacity 41, a read / write chunk bound 36, allocator model bounds 32, the shadow scale 65536 / 8 31, a 16-bit value range 26, the GIF code-table modulus 14, a 64 KiB size threshold 9, a 64 KiB chunk stride 2 |
| SAME-GEOMETRY -> NON-ADDRESS-SAME | 29 | UNCHANGED-PASS 25, CAPACITY-DOUBLING 4 | 131072 = seg0 size of pins A and B (and of cgif's): the 128 KiB pointer-array mmap length and the region it maps 23, seg0 of image B in YB13.v:138 1, `2 * 131072` and `67108864 <=? 131072` in YO01.v:47 / :48 (images A, B) 4; 5619712 = seg3 size of image B (and of cgif's) in YB13.v:94 1 |
| ROUND-CONSTANT-SAME -> NON-ADDRESS-SAME | 22 | UNCHANGED-PASS | 131072, a 128 KiB request / buffer length bound 15 (images P, U: there 0x20000 is also the fuzz_disco pin's PT_LOAD 2 / 1 end, cgif's is 0x1f000, so the numeral is the length); 196608 = 0x30000, seg1's start in image B (both trees), YB13.v:90 / :110 / :148 6; 1048576, a hash bucket bound, YFem.v:207 1 |
| STALE-DONOR-CODE-POINTER -> NON-ADDRESS-SAME | 7 | ALLOC-MAP-SIZE | 262144, the mmap length a1 at the ecall in internal_mmap (a7 = 222): YFk8.v:96, :100, YFkn.v:765, :1054, :1062, :1070, :1205 (G10 took them by the same rule) |
| SAME-VALUE-DIFFERENT-OBJECT -> NON-ADDRESS-SAME | 4 | FAKESTACK-OFFSET 2, LOOSE-ENTRY-BOUND 2 | YF0r.v:38 FS_FROFF 0x109000, YF0t.v:39 FS_FROFF 0x209000; YE30.v:1393, YE6k.v:1387 entD_ro bound 0x200000 |
| KIND-CHANGED -> NON-ADDRESS-CHANGED | 5 | SAME-G1-RULE | image P, YN0c.v:670, YN0e.v:133, :442, YN0g.v:320, :567: `bv_unsigned a + 131072 <= 0x10000 \/ 0x52000 <= bv_unsigned a`. 0x10000 is the plain image's base, an address bound (cgif's line: `<= 0x1f000 \/ 0x51000 <=`, its own PT_LOAD 2 end); 205a90fd19b8 reads the bound slot as a size and expects cgif's 0x1f000. g1_triage.py gives each the same rule on both tables (HAND: the plain image extent [0x10000, 0x52000), plain pin PT_LOADs) |
| SAME-GEOMETRY -> NON-ADDRESS-CHANGED | 2 | TARGET-GEOMETRY | YB13.v:150 `x - 196608 <? 458752`: 458752 = 0x70000 = seg1 size of the image B pin (PT_LOAD 1 from 0x30000, end 0x9f248 -> 0xa0000); cgif's 446464 = 0x6d000 = cgif's seg1 size. YD1g.v:1277 `fst r + snd r <=? YImgTop.IMG_LO + 0x5ee000`: 0x5ee000 = image span of the image B pin (0x5fe000 - 0x10000); cgif's 0x5eb000 = cgif's span. The port holds the target's own quantity; 205a90fd19b8 expects cgif's |

No finding becomes a pass except the 11 rows of the fourth and fifth lines, each by its G10 rule; the 2 new findings
and the 5 renamed ones are NON-ADDRESS-CHANGED readings of right target values.

Named-symbol check (205a90fd19b8's name-variant cells can read a cell that names another function SAME-SYMBOL):
rows DIFFERENT-SYMBOL or UNMEASURED-NAME under 0d24592683b6 and SAME-SYMBOL under 205a90fd19b8: **0** in (1)/(3) and
**0** in (2)/(4) (g11_triage.py would leave such a row UNTRIAGED); no row of YB1w.v differs between the versions at
all, so its tfib_* cells keep 0d24592683b6's verdicts.

## Triage: 0 untriaged, 0 defects
- `g1_triage.py` (this directory, `--lib` = the series tree) on the four tables: UNTRIAGED 19 (1), 20 (2), 28 (3),
  29 (4), so it exits 1 there; every other flagged row has its G1 rule, and on (1) and (3) those rows differ only in
  the class name of the 5 YN0 rows above.
- `g11_triage.py` (this directory) writes `G11-rows.tsv` (1465 rows: per run the 715 changed rows, part `diff`, and
  the flagged rows g1_triage.py leaves untriaged whose verdict did not move, part `flagged`) and exits 0:

| rule | (1) vs (3) | (2) vs (4) | measured |
|---|---|---|---|
| NOTE-ONLY | 98 | 98 | the verdict is unchanged; the detail gives the note text removed and added |
| UNCHANGED-PASS | 595 | 595 | value equal on both sides, both passes; the quantity 0d24592683b6 named first, measured on the row's fuzz_disco pin, is this value (cgif's beside it), or 0d24592683b6 read ROUND-CONSTANT-SAME; the detail gives 205a90fd19b8's slot, the numeral's role and the text |
| ALLOC-MAP-SIZE | 7 + 13 | 7 + 13 | G10's rule; the 13 part `flagged`: YG00.v:13, :15, YG06.v:351, :352 (2), :353, YG0h.v:318, :559, YG0i.v:207, :222 (KIND-CHANGED) and YFk8.v:55, YFk9.v:26, :52 (STALE-DONOR-CODE-POINTER: a generic register slot `pin (runto ..) 19%bv (SLit 262144)`, which 205a90fd19b8 keeps as an address by design) |
| CAPACITY-DOUBLING | 4 + 2 | 4 + 2 | G10's rule (YO01 RPX_closed, Qed) |
| FAKESTACK-OFFSET | 2 | 2 | G10's rule |
| LOOSE-ENTRY-BOUND | 2 | 2 | G10's rule |
| SAME-G1-RULE | 5 | 5 | the rule and detail g1_triage.py gives the row on both tables |
| TARGET-GEOMETRY | 2 | 2 | `size <q>` of 0d24592683b6's reading: the port's value is q of the fuzz_disco pin, the donor's is q of cgif's pin |
| FOOTPRINT-LENGTH | 1 | 1 | G10's rule (YO0f.v:1102) |
| JAL-SAME-CALLEE | 1 | 1 | G10's rule (YN3i.v:302) |
| SIZE0-END-NEXT-CELL | 0 | 1 | G10's rule (YH03.v:18, the twin's named-symbol rule) |

Defect test: every row 205a90fd19b8 flags in a class 0d24592683b6 did not give it is a NON-ADDRESS-CHANGED size
reading; in each the port's value is the target's measured quantity (TARGET-GEOMETRY) or the plain image's base
(SAME-G1-RULE). No flagged row holds a size kept from, or moved off, cgif where fuzz_disco's value differs.

## Planted controls
Each plant is a copy of one file of the series tree, run with `--dst <dir holding that copy> --include <file>` and the
images and cache of (1) (205a90fd19b8) or (3) (0d24592683b6).

| plant | file:line, change | 205a90fd19b8 | 0d24592683b6 |
|---|---|---|---|
| G1's | YE23.v:474 `Z_to_bv 64 6277920` -> `6277936` | rc 4, FLAGGED 19 (the file flags 18), NON-ADDRESS-CHANGED 0x5f9920 -> 0x5fcb30: fired | the same |
| its owner's (a granule moved as an address): rf-sys | YFkn.v:765 `sr_get (ss_regs ss) 11%bv = SLit 262144` -> `266524` (the mmap length, a7 = 222 in the sentence) | NON-ADDRESS-CHANGED (FLAGGED 1; the file flags 0): fired | SAME-SYMBOL: passes |
| rf-arith | YD2n.v:247 `.. / 262144)` -> `/ 266524)` | NON-ADDRESS-CHANGED on images A and B (FLAGGED 2): fired | image B SAME-SYMBOL: passes; image A NON-ADDRESS-CHANGED |
| rf-name | YG00.v:13 `Definition kUserMapSize : Z := 262144.` -> `266524` | image B SAME-SYMBOL: passes; image A NON-ADDRESS-CHANGED (FLAGGED 2, as unplanted) | the same |
| kept donor geometry: geo-bound | YB13.v:150 `<? 458752` -> cgif's `446464` | NON-ADDRESS-SAME: passes (FLAGGED 2; the file flags 3) | NON-ADDRESS-SAME: passes (FLAGGED 2, as unplanted) |
| geo-name | YD1g.v:1277 `+ 0x5ee000` -> cgif's `+ 0x5eb000` | NON-ADDRESS-SAME: passes (FLAGGED 7; the file flags 8) | NON-ADDRESS-SAME: passes (FLAGGED 7, as unplanted) |

The owner's plant moved round_fa's granule 0x40000 to 0x4051c, the same offset inside the same-named symbol. Here
266524 = 0x4111c = UnpoisonBeforeMain + 0x50 in the image B pin, and cgif's 0x40000 is cgif's UnpoisonBeforeMain +
0x50 (the twins' `.symtab`): the same consistent move. 205a90fd19b8 closes it in the syscall-arg and arith-operand
slots. It does not close it at `kUserMapSize`: its size-name pattern (port_addr_check.py line 224, `SIZE_NAME`) is
upper-case only, so a camel-case size name stays an address name (its owner's Limits (e)); the plant is caught there
only because image A's UnpoisonBeforeMain sits at another offset. The geometry plants are the converse of the two
TARGET-GEOMETRY rows: neither version judges these slots against the target's own geometry; G8 (roundconst v2) reads
kept donor geometry by value.

## Limits of this checker, as its owner lists them (its version record: the 205a90fd19b8 entry and Limits)
1. A SAME-SYMBOL match on an anonymous or local symbol (`.str*`, `.L*`, a bare section offset) checks no target
   bytes. Here 3 rows read a bare `.bss` offset (YB01.v:15 twice, YB03.v:13), the same under 0d24592683b6: hand-off
   state words, which YB1m's startup_cert checks in the kernel (G1, HANDOFF-STATE).
2. GENERATOR-FILL can report as fill a cell the tool could check absolutely (a `.got` cell against its GOT word):
   115 GENERATOR-FILL rows here (REPORTED; YI0z.v 90, YCej.v 16, others 9), the same under 0d24592683b6.
3. The addend of `q * G + G` is in no size-role slot, so an addend moved as an address reads SAME-SYMBOL.
4. FAIL-OPEN from the name-variant cells: a cell whose stated name is another function than the one at its value
   passes SAME-SYMBOL when one name contains the other, with no marker (0 rows move to SAME-SYMBOL here: above).
5. The size slots miss the granule argument of round_up-like functions and camel-case size names (rf-name above).
6. The list of 9873fe3cf51b stands: a relocated numeric quotient in `change (..) with N` can pass SAME-SYMBOL; rows an
   earlier version paired are unpaired (lost coverage); the auto image choice is not deterministic for two files of
   another unit; its harness has no donor-on-donor control; a start cell can read as the previous object's end; a kept
   donor count is not caught (G9 recomputes the counts); a code-pointer cell accepts another symbol when the value
   equals the pin word; moves by address are caught only inside `.got`; SAME-CONTENT counts where neither side names a
   symbol; the named-symbol rule is absolute only against the image's own `.symtab` (command (2) lifts it); second
   tier: mmap flags outside a flag slot, a 13-bit branch immediate read as a `.got` quantity, the AT_HWCAP range.
7. Address versus size is decided by name and context, and a NON-ADDRESS numeral is compared by value only; an
   in-range decimal is an address only as a symbol start, boundary, GOT slot, xref, jump-table cell, call return site
   or decimal copy of a hex code address of the same file; a donor object no symbolised build carries, or an END whose
   preceding object the donors cannot name, is UNRESOLVED; SLID-TO-NEIGHBOUR covers windows of at most 0x100 bytes;
   instruction words are compared modulo relocation immediates; `--assign '**=auto'` marks a tie between the two ASan
   images AMBIGUOUS.
8. Measured here, not in its list: a geometry quantity in a bound or size-name slot is compared with the donor's
   value, so the target's right value flags (YB13.v:150, YD1g.v:1277) and a kept donor value passes (geo-bound,
   geo-name).
