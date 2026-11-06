# Re-run of the value gates RA and RB on port_addr_check 0d24592683b6

rule 24: no function proved (kind: measurement). No .v file is changed by this record. The gates RA and RB of
`../gate/GATE.md` and their planted controls PA / PB were run again, on the inputs of record, with the tool version
installed after them, and compared with the version of record verdict by verdict.

## Result

0 findings. Every row whose verdict changed was measured (`changed-RA.tsv`, `changed-RB.tsv`): none is a wrong value
in our tree. Every row flagged by the runs of record keeps its verdict. The planted `.got` move, which the version of
record passed, is now flagged.

| gate | files paired | rows examined (numerals) | same verdict | changed | newly flagged | flag cleared | flag class changed | non-finding class changed | FLAGGED 3d2e -> 0d24 |
|---|---|---|---|---|---|---|---|---|---|
| RA (image A core) | 389 | 212053 | 211979 | 74 | 63 | 0 | 0 | 11 | 25054 -> 25117 |
| RB (image B core) | 389 | 212121 | 212048 | 73 | 62 | 0 | 0 | 11 | 25107 -> 25169 |

## The tool

port_addr_check.py sha256 0d24592683b610123346567302caf1bf97e5ac9354cf05799dc7cfc21dc0f4fa (installed 2026-10-30
23:46Z), run from its owner's versioned copy with its helper modules; each of the copy's 6 files was checked against
its SHA256SUMS (6 OK). Only port_addr_check.py differs from 3d2eee813cce; the 5 helper modules are byte-equal.
`--list-flag-classes` prints the same 27 classes under both versions, and every summary here says FLAG-CLASSES
575d398c6022, as the runs of record do.

## The inputs are the inputs of record

- Trees: `git archive` extracts of c8557374ad2e:proofs/cgif/cgif_file_fuzzer/lib (`$DONOR`) and
  repository tree (git tree 1c3596a429a4; internal record):proofs/plugin-hostd/fuzz_command/lib (`$OURS`), the two refs the runs of record read through `--git`.
  The tool reads the same .v files from them: src files read 728 / 2467, after `--include` 724 / 1449; dst files read
  1316 / 1278, after `--dst-include` 391 / 390 (RA / RB), as recorded. No .v file of either extract holds a CR byte, so
  the tool's path reader (text mode) and its git reader give the same text.
- Images: the four pins and their unstripped twins of `../gate/GATE.md`, with the sha256 and byte sizes the INPUTS
  USED blocks state.
- Donor set `$BIN`: a byte copy of the pinned donor set, every file checked against its SHA256SUMS (0 not OK).
- The tool's one third-party module, pyelftools, at version 0.33.
- Identity measured: the same inputs run with 3d2eee813cce reproduce the record. The FLAGGED lines of RA, RB, PA-base,
  PA-plant, PB-base and PB-plant are byte-equal to line 1 of `../gate/flagged-<run>.txt`; full.tsv has 212083 / 212151
  lines, as recorded; `summary-RA-3d2e.txt` and `summary-RB-3d2e.txt` equal `../gate/summary-RA.txt` and
  `-RB.txt` except line 1 (the command: local extracts instead of `--git` refs) and lines 4-5 (the two refs); the plant
  summaries equal `../gate/summary-P*.txt` except lines 1 and 4. The full.tsv sha256 differ from the record's
  (4a709c0abb3b / 989144f32040) because the file's `#` header holds the command line; the rows without that header
  are in `counts-RA.txt` / `counts-RB.txt` (3d2e: cbda41f5619b / 7bdcf729e496; 0d24: 75ce43de2a88 / 3eaa28b5e816).

## Verdict by verdict

`scripts/diff_rows.py` matches each row of a gate's 0d24 run with the row of its 3d2e run on the same numeral (image,
source file and line, ported file and line, sentence, index in the sentence, source value, ported value). Every row
matched: 0 unmatched on either side, in both gates (`counts-RA.txt`, `counts-RB.txt`, with the transition table).

## Every changed row, measured

`scripts/triage_changed.py` measures each changed row by its group and writes one line per row: file:line, sentence,
both verdicts, our value, the value the tool expects, the triage and the measurement, and the tool's own note.

| group | rows (RA + RB) | change | measurement | triage |
|---|---|---|---|---|
| function table lib/A/AB1w.v lines 75-76, 81-85, 87-91, 93-95, 99-100, 102, 109, 112-114, 148-149, 174, 439; lib/B/YB1w.v lines 76-77, 82-86, 88-92, 94-96, 100-101, 103, 110, 113-115, 149-150, 175, 440 | 51 + 51 | SAME-SYMBOL -> DIFFERENT-SYMBOL | The table (written from our images by the unit's generator, `../gen-states/`) has two rows for an intercepted libc function: `tfib_A_<f>` / `tfib_E_<f>` are the start and end of the 4-byte interceptor trampoline the program calls, and `tfib_A_musl_<f>` / `tfib_E_musl_<f>` are musl's body. The tool now reads the label as the symbol name `<f>`. Per row: our value names the same object as the donor's cell (start cells: the same symbol + offset; end cells: the end of the same object) in 51 of 51; the value the tool expects is the value of another row of the same table in 36 of 51 (29 of them a `musl_` row); 0 files of lib/ name the cell outside the two table files. `git grep -w` over every .v file of repository tree (git tree 1c3596a429a4; internal record) finds the 30 changed names, in this unit, only in AB1w.v and YB1w.v, and in no file of projects/ or theories/ (other units' hits are their own tables). | OK: unread cells that keep the donor's object |
| lib/A/AB1w.v lines 21, 92, 98, 111; lib/B/YB1w.v lines 22, 93, 99, 112 | 7 + 7 | SAME-SYMBOL -> UNMEASURED-NAME | not a finding class (the tool cannot tell which of two spellings the label means) | no flag |
| lib/A/AE6k.v:1387, lib/A/AE30.v:1393; lib/B/YE30.v:1394 | 2 + 1 | ROUND-CONSTANT-SAME -> SAME-VALUE-DIFFERENT-OBJECT (expects 0x20b0c0) | 0x200000 is a bound, not an address: `assert (Hrange : 0 <= start /\ start + length <= 0x200000)` over every entry of icpt_rodata, closed entry by entry by lia, proof ended by Qed. The largest start + length is 0xb1db8 (lib/A/AE2y.v) and 0xb1938 (lib/B/YE2y.v). It is the value the record's code row lib/B/YE6k.v:1388 restores. | OK |
| lib/A/AFk8.v:56, :97, :101, AFk9.v:28, :54, AFkn.v:773, :1062, :1070, :1078, :1213; lib/B/YFk8.v:57, :98, :102, YFk9.v:29, :55, YFkn.v:774, :1063, :1071, :1079, :1214 | 10 + 10 | ROUND-CONSTANT-SAME -> STALE-DONOR-CODE-POINTER (expects 0x43840 A, 0x4385c B) | 262144 (0x40000) is a map length, not a code pointer. Pins: the register pinned at pc 0x39630 (A) / 0x3967c (B) in SizeClassAllocator64::PopulateFreeArray, and at 0x372c0 (A) / 0x3730c (B) in EnsureFreeArraySpace, holds a size rounded up to 0x40000: each of these functions loads `lui 0x40` (0x40000) and `lui 0xfffc0` (its mask) in our image (the pcs are in the .tsv). Register equations: x11 = 262144 with x12 = 3 (PROT_READ, PROT_WRITE) or 0 (PROT_NONE), the length argument of the map call. | OK |
| lib/A/AF0m.v:136, AFgi.v:108, AFgm.v:96, AFgn.v:71; lib/B/YF0m.v:137, YFgi.v:109, YFgm.v:97, YFgn.v:72 | 4 + 4 | ROUND-CONSTANT-SAME -> SAME-SYMBOL | not a finding class | no flag |

## Planted controls PA / PB (`plants.txt`)

The plants of record (`../gate/plants.tsv`), made again by `../gate/mkplants.py` from the same extract (plants.tsv
sha256 050f8402a3e9, the record's), each run under both versions. Under 0d24592683b6 the planted `.got` moves
(lib/A/ACeg.v:21 0xa6448 -> 0xa6450, lib/B/YCeg.v:22 0xa5fa8 -> 0xa5fb0) read SLID-TO-NEIGHBOUR with expected
0xa6448 / 0xa5fa8, the unit's own values; under 3d2eee813cce they read SAME-SYMBOL-ROUNDED, the "FAIL" of
`../gate/GATE.md`. The three other plant classes keep their verdicts. In each base copy one row changes: the bound
0x200000 of the table above (lib/A/AE6k.v:1387, lib/B/YE30.v:1394), which is also the site of the class-B plant, whose
planted value stays flagged (DIFFERENT-SYMBOL) under both versions. Result: 4 of 4 plant classes fire.

## Limits: what 0d24592683b6 changes against 3d2eee813cce

Source: the tool owner's registry entry for 0d24592683b6 (seven measured changes, each with its regression rows and
its plant; 471 regression rows). Against the limits of 3d2eee813cce that `../REPORT.md` names:

- SAME-CONTENT across two symbols: removed (change 4: both content branches require that neither side names a
  symbol). No SAME-CONTENT row changed on RA or RB (14 each).
- jal INSN-SAME by opcode + rd: removed (change 6: a control-transfer word the decoder cannot place, whose two values
  differ, is INSN-CHANGED). No INSN-SAME row changed.
- ROUND-CONSTANT-SAME: narrowed, not removed (change 1: a kept page-round value in a geometry slot is judged against
  the target's own quantity; change 2: a value inside a named symbol is no round constant). RA keeps 38 such rows
  (was 54), RB 38 (was 53).
- PREDICT MAPS-STRING: removed where the source names a symbol (change 5). The gates do not run PREDICT mode.
- The named-symbol rule depends on the donor: removed where the target's symbols are its own (change 3); RA and RB
  give our unstripped twins, so it applies to them. Where a target's symbols are recovered, the donor must still
  agree.
- A `.got` cell moved to the next 16-aligned GOT word: removed (change 7), measured here by the plants.
- Still a limit: a by-address move onto an unrelated cell reads SAME (no change names it); `../sweep/` covers it.

## Not re-run

RU (lib/Reusable), the relay view RAB, the runtime and lib/Reusable runs of `../rt-reusable/` and the donor-on-donor
controls CA / CB stand as recorded with 3d2eee813cce.

## Reproducing

`$W` is the work directory on the build VM: `pac/<version>/` (the tool's versioned copies), `img/` (the eight image
copies, named as in the INPUTS USED blocks), `bin/` (`$BIN`), `tree/donor` and `tree/ours` (the two extracts),
`pylib/` (pyelftools 0.33), `runs/`. `scripts/drive.sh` runs the four gate runs and `scripts/drive_plants.sh` the
eight plant runs, each through `scripts/run_gate.sh`, which refuses a tool whose sha256 does not start with the
version asked. Then, per gate G: `scripts/diff_rows.py runs/G-3d2e/full.tsv runs/G-0d24/full.tsv FLAGCLASSES OUT`
(FLAGCLASSES = the output of `--list-flag-classes`) writes OUT/counts.txt (here `counts-G.txt`) and OUT/changed.tsv,
and `scripts/triage_changed.py G OUT/changed.tsv $W/tree/ours $W/img changed-G.tsv` measures the changed rows. The
same diff_rows.py call on each plant run pair gives `plants.txt`: its first six count lines and its changed rows
(file:line, both verdicts, value, the tool's note). drive.sh and
drive_plants.sh ran with the work directory written in (sha256 e731972d7888 and a6ea4a2d0891); the copies here read it
from `$W`, find run_gate.sh beside them and mkplants.py in `../gate/`, and run the same commands. In the summaries the host paths read
`$IMG`, `$BIN`, `$DONOR`, `$OURS`, `$PLANT`, and two fixed lines of the tool's output are restated as in `../gate/`
(`../internal-texts.md`): the note line that names the tool's documentation file reads "see the tool's documentation
file", and the attribution of the file-pairing note reads "(the tool author's note)". Every count is unchanged.
