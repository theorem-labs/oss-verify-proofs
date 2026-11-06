# Symbol + offset sweep of fuzz_command's relocated core (plugin-hostd/fuzz_command)

rule 24: no function proved. Read-only check; no `.v` file changed.

## What it checks

A relocated numeral that names an object must equal TARGET(S) + o, where S + o is the DONOR value read in the
donor's unstripped twin symtab. The value gate (port_addr_check 3d2eee813cce) compares values; a value moved onto an
unrelated cell (for example a `.got` word) can still read SAME there. This sweep reads every PAIRED row of the gate
runs again, by symbol + offset:

- `sweep.py` (sha256 2b829e945031): row selection, resolution, status. Its docstring states the rules.
- `triage.py` with `hand.tsv` (fb2bbc5eb9db): a measured reason for every non-SAME row. The copy that ran (sha256
  305bb2c723d56a2247fc5e9f2d38b422e708f76a40a39e1fc767d6916856b7a0, the version `controls.txt` and `findings.code.tsv`
  name) wrote `mismatches.tsv`, `adjacent.tsv` and the triage of the controls (the texts restated in the two tables since
  are in `../internal-texts.md`). The shipped `triage.py` (8215c493c6cb) is that file with its 8 default paths (on lines
  781-785, 857, 864) written as REPORT.md's placeholders `$W`, `$DONOR`, `$OURS` (sha256 2bcb4cd07b86) and then three
  texts restated (`../internal-texts.md`); no other code differs.
- `run.sh`, `all.sh` (83b0135d1e02): the commands (`bash all.sh`). The run.sh that ran has sha256
  04017c07448442a8e81db9e02df39c88b10fdf41b10f95c86836955d5fdcd0f1; the shipped `run.sh` (b9edf66b0604) is that file
  with its 4 default paths (lines 8-10, 12) written with the placeholder `$W`.

Row selection: both values present; kind `ident` skipped (an identifier suffix, never relocated: src = dst on every
row); instruction words skipped (src_class INSN, a literal typed `bv 32`); the donor value must lie in a PT_LOAD of
the donor; NONADDR rows whose reason is a size / count by NAME are skipped unless the value is a donor symbol start.
A jump-table word (src_class JTREL) is resolved by its target (table base from the gate + the word).

Resolution (pyelftools, twin symtab, pin bytes): the smallest covering sized OBJECT / FUNC, start aliases, the ends
of sized symbols, else the nearest preceding symbol of the same section; section and PT_LOAD bounds; for `.got` the
slot and the 64-bit word the pin holds there. A symbol is keyed by its name, or `file:name` for a name several
symbols share.

Status: SAME (same key + offset, or exactly ours(S) + o); SAME-SYMBOL-OFFSET-DIFFERS; DIFFERENT-SYMBOL;
LANDS-IN-GOT (ours in `.got` and the donor not, or two GOT slots with different pointees); NO-SYMBOL (a side with no
covering symbol and no symbol start).

## Runs and images

| run | donor files -> our files | donor image (pin / twin) | our image (pin / twin) |
|---|---|---|---|
| RA | cgif lib/A -> lib/A | cgif_file_fuzzer.asan 7093581aab04 / 488e39500746 | fuzz_command.asan c0661b96b5bd / 68db792d5fa7 |
| RB | cgif lib root Y -> lib/B | cgif_file_fuzzer.asan-ubsan 1c29845fe605 / ce511d541cda | fuzz_command.asan-ubsan bbe55d24d096 / 658cefbe806b |
| RU | cgif lib root Y -> lib/Reusable | as RB | as RB |
| RUP | cgif lib root Y -> lib/Reusable | cgif_file_fuzzer.plain 19dedd1bc682 / 6ab540c43108 | fuzz_command.plain a20873dc7f0e / fbe3a48ad296 |
| RtCgifA | cgif lib/A files -> lib/A/Rt | as RA | as RA |
| RtCgifB | cgif lib root Y files -> lib/B/Rt | as RB | as RB |
| RtDisco | fuzz_disco lib/A/Rt -> lib/A/Rt | fuzz_disco.asan 5e39150dd810 / ec656cf105cb | as RA |
| RtGrant | fuzz_grant lib/A/Rt -> lib/A/Rt | fuzz_grant.asan c2c7559b29bd / 57c26f993615 | as RA |
| RtPreset | fuzz_preset lib/A -> lib/A/Rt | fuzz_preset.asan d83eb25dbf0d / f0d2e8d40c7e | as RA |
| RtRelay | our lib/A/Rt -> our lib/B/Rt | fuzz_command.asan c0661b96b5bd / 68db792d5fa7 | as RB |

`src` / `dst` in the TSVs are file:line relative to the run's directories in this table. Every run was made by
port_addr_check 3d2eee813cce; sweep.py checks that each run's header names the images it resolves in. In addition
the RU pairs are resolved in the plain images (`work/rows.RU-P.tsv`): lib/Reusable's 425 pre-port `.v` files (of its
565, the ones added 2026-10-27 in 84b1ffc6d7d; 421 directly in lib/Reusable, 4 in its sub-directories R/ and Z/)
describe the plain build. Scope of findings (owner's ruling): port_core outputs only, i.e. lib/A/A*.v, lib/B/Y*.v, lib/Reusable's
140 files added by the port (commit 6b559e1f018; list in `work/portera.files`) and the Rt relocations. Rows of the
pre-port Reusable files are in `adjacent.tsv` as OUT-OF-SCOPE-PREPORT, with their measurements.

## Rows checked, per run and status (rows.tsv)

| run | checked | SAME | SAME-SYMBOL-OFFSET-DIFFERS | DIFFERENT-SYMBOL | LANDS-IN-GOT | NO-SYMBOL |
|---|---|---|---|---|---|---|
| RA | 10914 | 8996 | 698 | 567 | 1 | 652 |
| RB | 10913 | 8975 | 717 | 565 | 1 | 655 |
| RU | 1350 | 410 | 274 | 51 | 0 | 615 |
| RUP | 1094 | 840 | 44 | 148 | 0 | 62 |
| RtCgifA | 213 | 175 | 1 | 36 | 0 | 1 |
| RtCgifB | 213 | 175 | 1 | 36 | 0 | 1 |
| RtDisco | 288 | 223 | 9 | 36 | 0 | 20 |
| RtGrant | 212 | 171 | 3 | 38 | 0 | 0 |
| RtPreset | 27 | 23 | 3 | 0 | 0 | 1 |
| RtRelay | 1760 | 1441 | 209 | 5 | 0 | 105 |
| total | 26984 | 21429 | 1959 | 1482 | 2 | 2112 |

RU: 286 rows in files added by the port (183 non-SAME), 1064 in pre-port files (757 non-SAME). RUP: 171 in files added
by the port (68 non-SAME), 923 in pre-port files (186 non-SAME). Rows not checked, per reason and run: `rows.skipped.tsv`.

## Triage of the non-SAME rows (mismatches.tsv: 4612 rows in scope)

Every in-scope row has a measured reason; none is left OPEN. Rules (triage.py docstring; the first that measures
wins):

| rule | rows | what was measured |
|---|---|---|
| CONST | 1490 | the same numeral on both sides and no symbol start / small data object in the donor; its text use is a quantity (mapping or zero-run length, range bound, fuel, flag word decomposed into MAP_* bits, a named model constant of lib/Reusable/YG00.v, arithmetic) |
| INSN | 784 | an instruction encoding passed as a number (its rd / rs1 fields are the two register arguments before it) or an immediate of a word the line decodes |
| STR | 642 | both values in a NUL-terminated .rodata string, same text, same offset (pin bytes) |
| DERIVED | 412 | the same image quantity on both sides (PT_LOAD / section / image bounds, their differences, / 8, / 4, shadow) |
| GENSET | 381 | generated file: ours' symbol + offset also occurs in the donor's same definition (another order) |
| XREF | 343 | unnamed data that the same code (auipc pair at S+o, decoded from the pins) references on both sides |
| GENERATED | 200 | generated file (header names its generator, from our image): positional pairing of two different tables; ours names an object of our image |
| HAND | 159 OK, 1 FINDING | read by hand, measurement in hand.tsv |
| IMAGE | 68 | RUP rows of files added by the port (ASan model files): not plain-build files; judged in RU |
| LABEL | 38 | a check-site label (mcheck / spin / FCheck): in the two asan twins both values are the same symbol + offset |
| CELL | 37 | a cell whose stated content equals our pin's bytes at its address |
| NAMED | 22 | a table row `tfib_A_f` / `tfib_E_f` equals the start / end of f in our symtab |
| REGION | 13 | a chunk (start, length) of a region of our generated AD2j.v / YD2j.v |
| ARITH | 12 | `change (E) with N` / `replace (E) with (F)` holds on the line's own numbers |
| END | 6 | the end of a same-named symbol whose size differs |
| BYTES | 2 | the 16 bytes at both values are equal (pin) |
| AUIPC | 2 | the intermediate value of the auipc at the same symbol + offset |

Generated files (AB01 AB03 AF0m AD2j AE3i ACej AB1w and Y twins) were checked by the same rule: rows where ours is
the start / end of the function the definition names (NAMED), a reordering (GENSET), a cell checked against our
bytes (CELL) or an image quantity (DERIVED) are measured as such; the 200 GENERATED rows are judged by provenance.

## FINDINGs

One, code (findings.code.tsv), reported at once to the check's owner (STOP rule: a proof reads it):

- lib/B/YE6k.v:1388 `assert (Hrange : ... <= 0x1ffb80)`: old 0x1ffb80, new 0x200000 (class B, a model constant moved
  by a relocation delta). The donor YE6k.v:1392 and our A twin lib/A/AE6k.v:1387 have 0x200000; theDepot is 0x192f98
  in twin 68db792d5fa7 and 0x192b18 in twin 658cefbe806b, and 0x200000 - 0x480 = 0x1ffb80. The proof still closes;
  no claim changes.

No comment FINDING: the gate rows hold proof numerals only (port_addr_check strips comments).

Out of scope (adjacent.tsv, 943 rows of runs RU and RUP): lib/Reusable's pre-port files, measured in the plain
images. 64 pairs (each in both runs) are measured wrong (NAMED, all in lib/Reusable/YH03.v: cgif plain-build
function names and values kept or shifted, e.g. src0_E_LLVMFuzzerTestOneInput 0x130b0 where our plain twin has
LLVMFuzzerTestOneInput [0x14048, 0x14374)); 156 rows have no rule. That file is regenerated separately.

## Controls (controls.txt): PASS

On the planted copies (runs PA-plant / PB-plant and their bases): every planted address (stale code pointer, `.got`
cell moved to the next word, stale data pointer) is a non-SAME row whose base row is SAME; the planted model
constant is non-SAME and left OPEN by the triage, while its unchanged base row is cleared (CONST). No triage rule
clears a plant (8 of 8 OPEN); every base row is cleared (6 of 6).

## Files

rows.tsv, rows.skipped.tsv (sweep), mismatches.tsv (triage, in scope), adjacent.tsv (pre-port, out of scope),
findings.code.tsv, controls.txt, sweep.py, triage.py, hand.tsv, run.sh, all.sh; work/ctl (control rows and triage),
work/rows.RU-P.tsv (RU resolved in the plain images), work/portera.files, work/img (the plain images, local copies),
work/notes (copies of the lanes' notes, read-only).
