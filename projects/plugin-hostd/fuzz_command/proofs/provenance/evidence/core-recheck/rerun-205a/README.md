# Re-run of the value gates RA and RB on port_addr_check 205a90fd19b8

rule 24: no function proved (kind: measurement). No .v file is changed by this record. The gates RA and RB of
`../gate/GATE.md` and their planted controls PA / PB were run again on the inputs of `../rerun-0d24/README.md`, with
the tool version of record from 2026-10-31 08:00Z, and compared with 0d24592683b6 verdict by verdict.

## Result

0 new findings. Every row whose verdict changed was measured (`changed-RA.tsv`, `changed-RB.tsv`). One changed row
is a wrong value in our tree, and it was already recorded: lib/B/YE6k.v:1388 holds 0x1ffb80, the right value is
0x200000 (`../code-values.tsv`, fixed on the series head). 205a keeps it flagged and now names 0x200000 as the
expected value. No row that 0d24 read SAME-SYMBOL is NON-ADDRESS-CHANGED under 205a: on these gates, no size was
moved as if it were an address. The 8 new NON-ADDRESS-CHANGED flags are correct values of our own image (the
geometry false-flag class the tool owner named at 08:03Z). The planted `.got` moves are still flagged
(SLID-TO-NEIGHBOUR), and 8 of 8 plants fire.

| gate | files paired | rows examined (numerals) | same verdict | changed | newly flagged | flag cleared | flag class changed | non-finding class changed | FLAGGED 0d24 -> 205a |
|---|---|---|---|---|---|---|---|---|---|
| RA (image A core) | 389 | 212053 | 211704 | 349 | 4 | 57 | 0 | 288 | 25117 -> 25064 |
| RB (image B core) | 389 | 212121 | 211772 | 349 | 4 | 56 | 1 | 288 | 25169 -> 25117 |

## The tool

port_addr_check.py sha256 205a90fd19b85ab3b9f1910ff13f144c1d72a28fe393209e1106a3b26fcdcb69, run from the tool owner's
read-only versioned copy of 205a90fd19b8 with its helper modules; `sha256sum -c` of that copy's SHA256SUMS: 6 OK. The
identity runs used the versioned copy of 0d24592683b6 (port_addr_check.py sha256
0d24592683b610123346567302caf1bf97e5ac9354cf05799dc7cfc21dc0f4fa); `sha256sum -c` of its SHA256SUMS: 6 OK.
The two SHA256SUMS files differ only in the port_addr_check.py line; the 5 helper modules are byte-equal.
`--list-flag-classes` prints the same 27 classes under both versions (`flagclasses-0d24.txt` = `flagclasses-205a.txt`,
sha256 191b74b7661b), and every summary here says FLAG-CLASSES 575d398c6022, as the record's do.

The changes from 0d24 in the tool's code (diff of the two files): the closed list of size-role slots (syscall-arg,
arith-operand, bound, declared-field, size-name), read before the symbol-key override; INSN-SAME-AT-TARGET (no row
here); the libc / sanitizer spellings of a function-table label (`name_variants`); an image quantity on one side
against an unchanged non-address on the other reads NON-ADDRESS-SAME. `--accept-added` is not given. The cache rule
changed, and `--cache cache` is given, as before. Each summary has two more note lines (the cache directory and the
size-role slot list).

## The inputs are the inputs of record

- Trees: `git archive` extracts of c8557374ad2e:proofs/cgif/cgif_file_fuzzer/lib (`$DONOR`) and repository tree (git
  tree 1c3596a429a4; internal record):proofs/plugin-hostd/fuzz_command/lib (`$OURS`). `scripts/verify_tree.py` hashed
  each extracted file as a git blob and compared it with `git ls-tree -r` of the same ref: donor 2468 of 2468 blob-equal,
  ours 4881 of 4881, 0 missing, 0 extra, 0 .v files with a CR byte. The tool read the same .v files as the record: src
  files read 728 / 2467, after `--include` 724 / 1449; dst files read 1316 / 1278, after `--dst-include` 391 / 390
  (RA / RB).
- Images: cgif.A.pin 7093581aab040cfd94ed56f83bf44a37e6ec3c34db39cc57bf467e2949e870f0 (589640 bytes), cgif.A.twin
  488e39500746294ebe16fb1333e50c52e2339671de22f7768a37232aaeb05ad1, cgif.B.pin
  1c29845fe6058de6e1dbf3f6ec6abd566ea612d76b65ea5435d7ff77c63e08ef (590264), cgif.B.twin
  ce511d541cdabbe3c8df3f672dc517e8b5a7edd37b280a7483043b438de0adf7, cmd.A.pin
  c0661b96b5bd458ba489f91a4693b6a8acd6c0f74d5e20798ed78e937f858bb9 (634904), cmd.A.twin
  68db792d5fa79d84aff962832b8860777b5da99be208f85fc20e427c7697e30d, cmd.B.pin
  bbe55d24d0965b89b7fe2ae4d7d8f984d83fba09ca3caab96b10d6c1a1ffab16 (633720), cmd.B.twin
  658cefbe806b535ba1fbe5a37c8efe02099fc39c326f300e9b1c969d479df401: the 12-hex prefixes and sizes of `../gate/GATE.md`
  and of the INPUTS USED blocks.
- Donor set `$BIN`: the pinned donor binaries themselves, read only (their SHA256SUMS sha256
  c5f896249572b3d288ccb18b8a38475c584b19a413453c2491274304631c63d5, dated 2026-10-26 01:53Z); `sha256sum -c
  SHA256SUMS`: 112 OK. The three projects the tool takes hold no other ELF with a `.debug` beside it.
- pyelftools 0.33 (the tool's one third-party module), Python 3.12.3.
- Plants: `../gate/mkplants.py` on the ours extract; plants.tsv sha256 050f8402a3e9, the record's.

## Identity check: 0d24592683b6 on these inputs reproduces the record

`identity.txt` (`scripts/identity.py`): for RA, RB, PA-base, PA-plant, PB-base and PB-plant, the FLAGGED line is
byte-equal to the record's line in `../rerun-0d24/flagged.txt`, the exit code is 4, and the sha256 of the full.tsv rows
without the `#` header block equals the record's: 75ce43de2a88 / 3eaa28b5e816 (RA / RB, `../rerun-0d24/counts-R?.txt`),
3fa30f18fd6e / 300217d64754 / 4b5de3d05022 / d8d989781ce9 (the plant runs, `../rerun-0d24/plants.txt`). With host
paths written as `$...` names (`scripts/norm_summary.py`), each `summary-<run>-0d24.txt` is byte-equal to the record's
`../rerun-0d24/summary-<run>.txt`. 6 of 6 runs equal the record.

## Verdict by verdict

The record's `scripts/diff_rows.py` (byte-equal to `../rerun-0d24/scripts/diff_rows.py`) matches each 205a row with
the 0d24 row on the same numeral (image, source file and line, ported file and line, sentence, index, source value,
ported value). Every row matched: 0 unmatched on either side, in all six run pairs (`counts-RA.txt`, `counts-RB.txt`,
`plants.txt`).

## Every changed row, measured

`scripts/triage_205a.py` measures each changed row by its group and writes one line per row in the columns of
`../rerun-0d24/changed-R?.tsv`: file:line, sentence, both verdicts, our value, the value the tool expects, the triage,
the measurement, and the tool's 205a note. 0 rows are OPEN.

| group | rows (RA + RB) | change | measurement | triage |
|---|---|---|---|---|
| the value 0x10000 (65536) in 78 files per gate, e.g. lib/A/AB13.v, AD1g.v, AFem.v | 281 + 281 | SAME-SYMBOL -> NON-ADDRESS-SAME | 0x10000 on both sides in every row: 153 in a bound slot (`0x10000 <= a`, `x + 1 <=? 65536 + 143360`), 125 as an arith operand (`mod 65536`, `65536 * byteZ ..`), 3 in a size-name slot. 0x10000 is also the first PT_LOAD p_vaddr of all four pins, so the address reading and the size reading give the same value. These are the rows whose 0d24 pass rested on a SAME-SYMBOL reading of a size: none moved. | no flag, value unchanged |
| function table lib/A/AB1w.v lines 75-76, 81-85, 87-95, 98-100, 102, 109, 111-114, 148-149; lib/B/YB1w.v lines 76-77, 82-86, 88-96, 99-101, 103, 110, 112-115, 149-150 | 48 + 48 from DIFFERENT-SYMBOL; 6 + 6 from UNMEASURED-NAME (A lines 92, 98, 111; B lines 93, 99, 112) | DIFFERENT-SYMBOL / UNMEASURED-NAME -> SAME-SYMBOL | Read against the twins, for the fail-open the tool owner named at 08:31Z ("Function-table cells" below). For each of the 54 + 54 cells, our value starts (tfib_A_) or ends (tfib_E_) the same FUNC of our twin as the donor's value does in the donor twin. 50 + 50 are interceptor trampolines `__interceptor_trampoline_<label>`; 4 + 4 are `__asan_(un)register_elf_globals`. None of the 54 names occurs in a .v file of the repository tree (git tree 1c3596a429a4) outside AB1w.v / YB1w.v, except in other units' own tables (`table-names-grep.txt`). | OK: same function as the donor's cell, unread |
| lib/A/AB13.v:87, :131, :143, AD1g.v:1282; lib/B/YB13.v:88, :132, :144, YD1g.v:1283 | 4 + 4 | SAME-GEOMETRY -> NON-ADDRESS-CHANGED (expects the donor's value) | Image quantities of our own pin, not moved sizes ("NON-ADDRESS-CHANGED rows" below). | OK |
| lib/A/AFk8.v:97, :101, AFkn.v:773, :1062, :1070, :1078, :1213; lib/B/YFk8.v:98, :102, YFkn.v:774, :1063, :1071, :1079, :1214 | 7 + 7 | STALE-DONOR-CODE-POINTER -> NON-ADDRESS-SAME | 262144 (0x40000) on both sides, the map length of the record's maplen group. 205a reads it in a syscall-arg slot (x11 with a7 = 222 in the same sentence) or as an arith operand. Pins: the register pinned at 0x39630 (A) / 0x3967c (B) in SizeClassAllocator64::PopulateFreeArray is the one `lui x19, 0x40` loads at 0x39620 / 0x3966c; at 0x372c0 / 0x3730c in EnsureFreeArraySpace the function loads `lui 0x40` and its mask `lui 0xfffc0`. | OK |
| lib/A/AE6k.v:1387, AE30.v:1393; lib/B/YE30.v:1394 | 2 + 1 | SAME-VALUE-DIFFERENT-OBJECT -> NON-ADDRESS-SAME | 0x200000 on both sides, the bound of `assert (Hrange : 0 <= start /\ start + length <= 0x200000)` over icpt_rodata. The largest start + length is 0xb1db8 (lib/A/AE2y.v) / 0xb1938 (lib/B/YE2y.v), and each proof ends Qed. | OK |
| lib/A/AFem.v:194; lib/B/YFem.v:195 | 1 + 1 | ROUND-CONSTANT-SAME -> NON-ADDRESS-SAME | 0x100000 on both sides: `0 <= bkt < 1048576`, a bucket bound (2^20) in a precondition. | no flag, value unchanged |
| lib/B/YE6k.v:1388 | 0 + 1 | DIFFERENT-SYMBOL -> NON-ADDRESS-CHANGED (expects 0x200000) | `assert (Hrange : .. <= 0x1ffb80)`. The donor and the A twin lib/A/AE6k.v:1387 state 0x200000. 0x1ffb80 is 0x200000 moved by the image-B relay as if it were an address (theDepot delta -0x480). Both values bound the icpt_rodata entries (largest end 0xb1938), so the proof closes. | FINDING, already recorded: `../code-values.tsv` (0x1ffb80 -> 0x200000), `../sweep/findings.code.tsv`, `../triage-B/extra-findings.tsv`. The unit as this series ships it holds 0x200000 at this line. |

### NON-ADDRESS-CHANGED rows (every one that changed)

Our pins' PT_LOAD tables (vaddr, memsz): cmd.A.pin 0x10000 0x22340; 0x33340 0x713bc; 0xa5700 0x2900; 0xa8108 0x55dd70.
cmd.B.pin 0x10000 0x2238c; 0x3338c 0x70ecc; 0xa5258 0x1da8; 0xa7c68 0x55dd90. Rounded to pages:

| row | our value | quantity of our pin | donor value = donor pin's quantity | in the proof |
|---|---|---|---|---|
| lib/A/AB13.v:87 `x - 688128 <? 5627904` | 0x55e000 | seg3 0xa8000..0x606000, size 0x55e000 | 0x55c000 (cgif.A.pin seg3 0x9f000..0x5fb000) | the length of Asan_seg_bytes_003, which `tfib_len3` states as 5627904 by vm_compute |
| lib/A/AB13.v:131 `x - 65536 <? 143360` | 0x23000 | seg0 0x10000..0x33000 | 0x20000 | `tfib_len0` = 143360 |
| lib/A/AB13.v:143 `x - 208896 <? 466944` | 0x72000 | seg1 0x33000..0xa5000 | 0x6d000 | `tfib_len1` = 466944 |
| lib/A/AD1g.v:1282 `fst r + snd r <=? 0x10000 + 0x5f6000` | 0x5f6000 | image span 0x10000..0x606000 (= tfib_img_hi - tfib_img_lo of AB1w.v) | 0x5eb000 | static_img_chk, vm_compute |
| lib/B/YB13.v:88 `x - 684032 <? 5632000` | 0x55f000 | seg3 0xa7000..0x606000 | 0x55c000 (cgif.B.pin) | `tfib_len3` = 5632000 |
| lib/B/YB13.v:132 | 0x23000 | seg0 0x10000..0x33000 | 0x20000 | `tfib_len0` = 143360 |
| lib/B/YB13.v:144 | 0x72000 | seg1 0x33000..0xa5000 | 0x6d000 | `tfib_len1` = 466944 |
| lib/B/YD1g.v:1283 | 0x5f6000 | image span 0x10000..0x606000 | 0x5eb000 | static_img_chk |

Each value is our own image's page-rounded segment or span. The donor's value is the donor image's. The value 205a
expects (the donor's) would be wrong for our image. These rows are the false-flag class the tool owner named at
08:03Z (a correct image-geometry value in a bound slot reads NON-ADDRESS-CHANGED instead of SAME-GEOMETRY). They are
not findings. The ninth NON-ADDRESS-CHANGED change is lib/B/YE6k.v:1388, above.

### STALE-DONOR-CODE-POINTER rows (every one under 205a)

205a flags 7 per gate, all with the same verdict under 0d24 (`sdcp-RA.tsv`, `sdcp-RB.tsv`). No row is newly flagged
in this class. Each one was read by hand against the image:

- lib/A/AFk8.v:56, AFk9.v:28, :54; lib/B/YFk8.v:57, YFk9.v:29, :55: `pin (runto PC ..) 19%bv / 18%bv (SLit 262144)`,
  a generic register slot. This is the accepted cost of 205a for a power of two. 262144 is the map length (the pin
  readings above), not a code pointer, so it is a correct value.
- lib/A/AB1w.v:292-293, lib/B/YB1w.v:293-294 (tfib_A_internal_strcmp / internal_strncmp): our value starts the FUNC of
  that name in our twin (`_ZN11__sanitizer15internal_strcmpEPKcS1_` at 0x69b2c A / 0x69b78 B;
  `..16internal_strncmp..` at 0x69b70 / 0x69bbc). The donor's value starts internal_strchr / internal_strcmp: the
  donor's label names another function, and our row names its own (`../gen-states/README.md`, ROW-FUNC). Correct
  value.
- lib/A/AF0m.v:239-240, lib/B/YF0m.v:240-241 (`z8 (ANum CELL) VALUE` of Tfib_const_abs): the 8 pin bytes at the
  REAL slot (0xa8110 / 0xa8118 A, 0xa7c70 / 0xa7c78 B: real_strlen / real_strndup) equal our value (strlen / strndup).
  The donor's row is cgif's REAL(fclose) / REAL(fopen) slot. Correct value (`../gen-cells/README.md`).

### Function-table cells (the fail-open the tool owner named at 08:31Z)

These are the cells whose 0d24 verdict was DIFFERENT-SYMBOL or UNMEASURED-NAME and whose 205a verdict is SAME-SYMBOL:
54 per gate (27 table lines, an A cell and an E cell on each). Each line of `changed-R?.tsv` gives the FUNC our value
starts or ends, the donor's, and the FUNCs of our twin spelled as the label itself. Reading:

- 50 + 50 cells `tfib_A_<f>` / `tfib_E_<f>` with f = strlen, strnlen, strcmp, strchr, memcmp, memchr, frexpl, read,
  fwrite, time, gmtime_r, vprintf, vfprintf, vsnprintf, clock_gettime, wcrtomb, wctomb, pthread_attr_getstack,
  sem_timedwait, pthread_setcancelstate, send, sendto, sigaltstack, memset, memcpy. Each value is the start / end of
  `__interceptor_trampoline_<f>` (also `__wrap_<f>`), in our twin and, at the donor's value, in the donor twin. Our
  twin also has musl's plain `<f>` (for example `strlen` at 0x9f3cc A). The table gives that body its own row,
  `tfib_A_musl_<f>` (lib/A/AB1w.v:533 `tfib_A_musl_strlen := 0x9f3cc`), so `tfib_A_<f>` is the trampoline by the
  table's own convention. Correct value.
- 4 + 4 cells tfib_A/E_asan_register_globals and tfib_A/E_asan_unregister_globals (lib/A/AB1w.v:75-76,
  lib/B/YB1w.v:76-77). Our values are the start and end of `__asan_register_elf_globals` (0x4306c..0x430d8 A,
  0x430b8..0x43124 B) and `__asan_unregister_elf_globals` (0x430d8..0x43140 A, 0x43124..0x4318c B). `__asan_register_globals`
  (0x41c84..0x42aa0 A, 0x41cd0..0x42aec B) and `__asan_unregister_globals` are covered by the rows before them,
  tfib_*_asan_register_globals_impl_RegisterGlobal_loop and tfib_*_asan_unregister_globals_impl. The donor's table
  (c8557374ad2e lib/A/AB1w.v:68-71) has the same layout: its `tfib_A_asan_register_globals` is 0x3f82c, the start of
  `__asan_register_elf_globals` in cgif.A.twin. The label is the donor's short name for the ELF-globals entry point,
  and our values name the same function in our image. The label is imprecise. The value is not wrong, and no proof
  reads the cell.

Result for this group: 0 cells name a function other than the donor's cell's function, and 0 cells are read outside the
two table files.

## Planted controls PA / PB (`plants.txt`)

The plants of record, made again by `../gate/mkplants.py` (plants.tsv sha256 050f8402a3e9), each run under both
versions. Under 205a90fd19b8 (`scripts/plants_205a.py`):

| plant | A | B |
|---|---|---|
| stale donor code pointer (AB1v.v:15 / YB1v.v:15) | STALE-DONOR-CODE-POINTER | STALE-DONOR-CODE-POINTER |
| `.got` cell moved to the next GOT word (ACeg.v:21 0xa6448 -> 0xa6450 / YCeg.v:22 0xa5fa8 -> 0xa5fb0) | SLID-TO-NEIGHBOUR, expected 0xa6448 | SLID-TO-NEIGHBOUR, expected 0xa5fa8 |
| model constant moved by a code delta (AE6k.v:1387 / YE30.v:1394 0x200000 -> 0x20051c) | NON-ADDRESS-CHANGED, expected 0x200000 (was DIFFERENT-SYMBOL) | NON-ADDRESS-CHANGED, expected 0x200000 |
| stale donor data pointer (AE7d.v:35 / YE7d.v:36) | STALE-DONOR-DATA-POINTER | STALE-DONOR-DATA-POINTER |

8 of 8 plants fire. Between each base and plant run, 0 rows outside the plant lines change verdict. In each base
copy, two rows change from 0d24: the 0x200000 bound (SAME-VALUE-DIFFERENT-OBJECT -> NON-ADDRESS-SAME, the flag
clears) and ACeg.v:74 / YCeg.v:75 0x10000 (SAME-SYMBOL -> NON-ADDRESS-SAME). The class-B plant now reads as a size
that changed, and the tool names the unit's own value as the expected value.

## Additional measurement: values outside 205a's closed slot list

205a reads a page-aligned value as a size only in its closed list of slots. `scripts/moved_pages.py` lists every 205a
SAME-SYMBOL row whose donor value is page-aligned and whose ported value differs (`moved-pages-R?.tsv`): 74 (RA) / 76
(RB). None has a power-of-two donor value. 61 / 61 are image extents (EXTENT, e.g. image.top 0x5fb000 -> 0x606000),
each equal to the named quantity of our pin and the donor's to the donor pin's. 13 / 15 name the same symbol + offset
on both sides with a ported value that is not page-aligned: addresses that moved with their symbol, not sizes. 74 / 76
OK, 0 OPEN. These verdicts are the same under 0d24.

## Findings

0 new. In the changed rows, 1 is a wrong value in our tree: lib/B/YE6k.v:1388 0x1ffb80, right value 0x200000. It was
already recorded and is fixed on the series head.

## Not re-run

RU (lib/Reusable), the relay view RAB, the runs of `../rt-reusable/`, `../triage-B/`, `../d9e0/` and the donor-on-donor
controls CA / CB were not in this re-run's scope. They stand as recorded.

## Reproducing

The work directory `$W` holds `img/` (the eight image copies), `tree/donor` and `tree/ours`
(`git archive <ref>:<path> | tar -x`), `plant/` (`python3 ../gate/mkplants.py $W/tree/ours $W/plant`), `runs/`. `W=$W PAC=.. BIN=..
scripts/drive_seq.sh 0d24592683b6` and then the same with `205a90fd19b8` run the six runs of each version one at a
time at nice 19, each through the record's `scripts/run_gate.sh` (byte-equal to `../rerun-0d24/scripts/run_gate.sh`),
with `PAC` the directory of the tool owner's versioned copies and `BIN` the pinned donor binaries. The identity check
is `scripts/identity.py $W/runs ../rerun-0d24 identity.txt`. Per run R, `scripts/diff_rows.py runs/R-0d24/full.tsv
runs/R-205a/full.tsv flagclasses-205a.txt OUT` writes counts and changed rows. Per gate G, `scripts/triage_205a.py G
OUT/changed.tsv runs/G-205a/full.tsv $W/tree/ours $W/tree/donor $W/img changed-G.tsv sdcp-G.tsv flagclasses-205a.txt`
measures them (exit 0: no row OPEN). Then `scripts/plants_205a.py $W/runs $W/plant/plants.tsv flagclasses-205a.txt`
and `scripts/moved_pages.py G runs/G-205a/full.tsv $W/img moved-pages-G.tsv`. `table-names-grep.txt` is `git grep -l
-w -F -f table-names.txt <tree> -- '*.v'` over the repository tree (git tree 1c3596a429a4; internal record).
`summary-<run>.txt` (205a) and `summary-<run>-0d24.txt` are the runs' summaries, with local paths written `$IMG`,
`$BIN`, `$DONOR`, `$OURS`, `$PLANT`. The two fixed lines of the tool's output are restated as in `../gate/`
(`scripts/norm_summary.py`). Every count is unchanged. Runs: 0d24 09:23:48Z-09:41:07Z, 205a 09:42:01Z-09:59:20Z,
2026-10-31.
