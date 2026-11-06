# port_core re-check of plugin-hostd/fuzz_command's relocated core

rule 24: no function proved (kind: measurement; a re-check of relocated proof files against the unit's pinned images).
No .v file is changed by this record. Checked tree: plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record) (the unit's series head; it holds the merged tree
781f46bc05cd plus later commits, see INVENTORY.md). All paths below are relative to the unit's proof root.

## The ruling this record answers (method owner, 2026-10-30)

port_core outputs whose inputs can be re-run: port_core d9e0589898fd --dry on those inputs, the stage-out compared by
sha256, every differing row classed provenance-only / patched / VALUE. Outputs whose inputs are lost, and as the CHECK OF
RECORD over lib/A/A*.v and lib/B/Y*.v: (1) the pin-keyed value gate port_addr_check 3d2eee813cce with its controls
firing and its registered limits named; (2) the roundconst gate v2 32b39f3b34e9; (3) a recompute from our images of every
image-derived count. Any flagged row is triaged with a measured reason; a wrong value in proof code is listed for a code
commit (`code-values.tsv`), a wrong value in comment text becomes a measured row (`measured-rows.tsv`). Two named limits of
every relocation tool and gate were added the same evening and are covered here: a .got cell mapped to the wrong GOT word
(class A), a model constant that looks like an address moved (class B), and a by-address move onto an unrelated cell.

## Result

FINDINGS: 5 code rows, 0 comment rows. All five are class B (a model constant moved as an address); all five statements
stay TRUE (each is a weaker bound that its proof still closes, Qed), so no claim and no release-check result changes.
Proofs read the first four. They are listed with their measurement in `code-values.tsv`:

| file:line | old | new | read by |
|---|---|---|---|
| lib/A/AFjm.v:428 (map_zoneN) | 2148223601 | 2148236288 | proofs (21 walk files, lib/A/AFk1.v sm_bounds) |
| lib/A/AFk1.v:696 (sm_bounds) | 2148223601 | 2148236288 | proofs |
| lib/B/YFjm.v:429 (map_zoneN) | 2148223601 | 2148236288 | proofs |
| lib/B/YFk1.v:697 (sm_bounds) | 2148223601 | 2148236288 | proofs |
| lib/B/YE6k.v:1388 (assert in entD_ro's proof) | 0x1ffb80 | 0x200000 | that proof only |

2148236288 = 0x7fff7000 (kLowShadowBeg) + 0x606000 / 8 (both images end on page 0x606000): the numeric form of the
neighbouring lemma map_zone's own bound. 0x1ffb80 is the 2 MiB bound of the A twin and the donor, moved by the image-B
relay by theDepot's A -> B delta (-0x480).

No other row of any check below is a defect. One more value was examined on request: the TOT bound 634974 (lib/A/AFem.v:116,
:194; lib/B/YFem.v:117, :195; the atom range in lib/A/AFek.v:34 and lib/B/YFek.v:35). It is TRUE for this unit's model
(TOT_range is Qed by lia from lo_tr0 <= 31, depot_inv_frames <= 31 per entry and DEPOT_CAP = 20480) and is not a
relocation value: both port_core runs on our inputs write the donor's 127070 there, and 634974 is the donor's shape
(1 + 31 * nD_max + 62) rescaled by hand to our depot size. The exact bound from the same definitions is
31 + 1 + 31 * 20480 = 634912; whether to tighten it is a choice, not a defect.

## The checks, their counts and their controls

| part | what | rows / items | result | controls | directory |
|---|---|---|---|---|---|
| value gate RA | port_addr_check 3d2eee813cce, cgif lib/A -> our lib/A/A*.v, key A | 389 files, 212053 numerals, 25054 flagged | all 25054 triaged: 2204 no ported value, 1534 kernel-checked proof steps, 62 kernel-checked facts (mechanical pass), 807 hand-measured (805 OK, 2 FINDING), 20447 in the 7 generated files (all OK) | donor-on-donor CA; 4 planted classes (3 fire; .got class does not: limit 3) | `gate/`, `triage-A/`, `gen-cells/`, `gen-states/` |
| value gate RB | cgif root Y*.v -> our lib/B/Y*.v, key B | 389 files, 212121 numerals, 25107 flagged | all triaged: 3809 mechanical, 809 hand-measured (807 OK, 2 FINDING), 20489 generated (all OK); the YE6k.v:1388 FINDING sits in a mechanically settled proof step and was found by the relay scan and the symbol sweep | donor-on-donor CB; 4 planted classes (as RA) | `gate/`, `triage-B/`, `gen-cells/`, `gen-states/` |
| relay view RAB | our lib/A (image A) -> our lib/B (image B) | 4483 flagged (3833 UNRESOLVED from one key for two builds) | 86 relay rows measured (STALE-DONOR / SAME-VALUE / quotient / changed values): all OK; generated-file rows covered by the whole-file measurements | - | `triage-B/rab-rows.tsv` |
| generated files | AF0m AE3i AD2j AB01 AB03 ACej AB1w and Y twins, written from our images by the unit's generators | 40936 flagged rows; plus EVERY numeral of AF0m/AE3i/AD2j (24338) and of AB01/AB03 (52722) and their twins | all OK (cells = image bytes, shadow = recomputed from the 180 descriptors, chunks / runs recomputed, rows = FUNC symbols, traces re-generated) | perturbation (value + 4, donor value, neighbour row); 230 planted .got moves refused | `gen-cells/`, `gen-states/` |
| false-EQUAL classes | every SAME-CONTENT, INSN-SAME (jal: opcode + rd only) and ROUND-CONSTANT-SAME row of RA, RB, RU | 3867 rows | all OK (string identity; word = image bytes at its pc, jal / branch targets decoded and equal by donor symbol + offset; role measured) | planted wrong jal, wrong j, wrong string: flagged | `false-equal/` |
| .got cells | every numeral inside .got in lib/A/A*.v, lib/B/Y*.v, lib/A/Rt, lib/B/Rt, lib/Reusable (1612 files) | 858 cells | all OK: pointee = donor pointee (520 of 520 paired), = definition name, = stated word | the two planted GOT moves flagged, base not; perturbation | `got-codeptr/` |
| codeptr 12348302dfd2 | 13 start-up / table files per image, paired with cgif's | A 25 findings, B 26 | all 102 rows (findings + limit rows) settled by role and measured | codeptr's own controls PASS (must-find paired, must-not-flag) | `got-codeptr/codeptr*` |
| symbol + offset sweep | every address-valued paired numeral: donor symbol + offset vs ours (RA, RB, RU, Rt runs) | 26984 rows | 4612 not SAME, all measured: 4611 OK, 1 FINDING (YE6k.v:1388) | planted code / data pointer and GOT move: non-SAME; constant plant kept open | `sweep/` |
| roundconst v2 32b39f3b34e9 | on the full rows of RA, RB, RU (and RU on the plain images), normal and --moved | 12585 non-SAME rows | all OK (none a kept donor quantity) | 13 of 13: donor-on-donor 0; kept PT_LOAD lengths, word counts, small table length flagged by v2 (missed by v1); gap control SAME | `roundconst/` |
| count recompute | every image-derived count and section / segment bound in lib/A/A*.v, lib/B/Y*.v, lib/A/Rt, lib/B/Rt, lib/Reusable | 12462 candidates | 2633 recomputed, all SAME; 9829 not image-derived (reason per row) | value + 4 refused on every SAME row | `counts/` |
| d9e0 --dry diff | runs A1 (377 files) and A2 (14 files) re-run, stage-out vs the old stage-out vs our file | 4446 differing rows | 3213 generated slots (by design), 562 patched, 408 provenance-only, 179 refused by d9e0, 51 other, 26 generated, 4 VALUE (our value right in each), 3 not in tree | value + 4 / donor value | `d9e0/` |
| runtime and lib/Reusable | Rt files relocated from cgif / fuzz_grant / fuzz_disco / fuzz_preset donors (each with its own pinned image), our lib/A/Rt -> lib/B/Rt, lib/Reusable (key B and the plain images) | 8252 flagged rows | all settled: 6735 OK; 1517 in the 425 lib/Reusable files of the plain build added before the port (not port_core outputs) | donor-on-donor per donor image, 0 flags | `rt-reusable/` |

## Re-run of RA and RB on port_addr_check 0d24592683b6 (`rerun-0d24/`)

The version installed after these runs, port_addr_check 0d24592683b6 (sha256
0d24592683b610123346567302caf1bf97e5ac9354cf05799dc7cfc21dc0f4fa), was run once on the inputs of RA and RB, and
3d2eee813cce again on the same inputs. The 3d2eee813cce runs reproduce every recorded count and FLAGGED line, so the
two versions are compared on the inputs of record. Rows examined: RA 389 files, 212053 numerals; RB 389 files, 212121
numerals; every row matched one to one between the two versions.

| gate | same verdict | changed | newly flagged | flag cleared | other class changed | FLAGGED 3d2e -> 0d24 |
|---|---|---|---|---|---|---|
| RA | 211979 | 74 | 63 | 0 | 11 (not finding classes) | 25054 -> 25117 |
| RB | 212048 | 73 | 62 | 0 | 11 (not finding classes) | 25107 -> 25169 |

The changed rows, each measured in `rerun-0d24/changed-RA.tsv` and `changed-RB.tsv`; 0 findings:

- lib/A/AB1w.v:75-76, :81-85, :87-91, :93-95, :99-100, :102, :109, :112-114, :148-149, :174, :439 and lib/B/YB1w.v:76-77,
  :82-86, :88-92, :94-96, :100-101, :103, :110, :113-115, :149-150, :175, :440 (51 + 51, SAME-SYMBOL -> DIFFERENT-SYMBOL):
  interceptor-trampoline cells of the generated function table. Each names the same object as the donor's cell, and
  no proof file names them. OK.
- lib/A/AE6k.v:1387, lib/A/AE30.v:1393, lib/B/YE30.v:1394 (2 + 1, -> SAME-VALUE-DIFFERENT-OBJECT): 0x200000 is the
  bound on the region ends of icpt_rodata (largest 0xb1db8 A, 0xb1938 B), not an address. OK.
- lib/A/AFk8.v:56, :97, :101, AFk9.v:28, :54, AFkn.v:773, :1062, :1070, :1078, :1213 and lib/B/YFk8.v:57, :98, :102,
  YFk9.v:29, :55, YFkn.v:774, :1063, :1071, :1079, :1214 (10 + 10, -> STALE-DONOR-CODE-POINTER): 262144 is a map length
  rounded up to 0x40000 by our images' allocator code (`lui 0x40` and its mask in the pinned functions), not a code
  pointer. OK.
- lib/A/AB1w.v:21, :92, :98, :111 and lib/B/YB1w.v:22, :93, :99, :112 (7 + 7, -> UNMEASURED-NAME); lib/A/AF0m.v:136,
  AFgi.v:108, AFgm.v:96, AFgn.v:71 and lib/B/YF0m.v:137, YFgi.v:109, YFgm.v:97, YFgn.v:72 (4 + 4, ROUND-CONSTANT-SAME ->
  SAME-SYMBOL): not finding classes.

The planted controls PA / PB, run again under both versions: under 0d24592683b6 the planted `.got` move is flagged
(SLID-TO-NEIGHBOUR, expected the unit's value), so 4 of 4 plant classes fire.

## Limits of the tools, named

- port_addr_check 3d2eee813cce: false-EQUAL on SAME-CONTENT across two symbols, jal INSN-SAME (opcode + rd only),
  ROUND-CONSTANT-SAME, PREDICT MAPS-STRING; the named-symbol rule depends on the donor (a cell the donor already had wrong
  passes, e.g. cgif's tfib_rodata_hi, which is not cgif's .rodata end: ours is our .rodata end, 0x246a4 A / 0x246e4 B);
  a .got cell moved to the next 16-aligned GOT word reads SAME-SYMBOL-ROUNDED (measured here by a plant); a by-address
  move onto an unrelated cell reads SAME. Each is covered by a part above (false-equal, got, sweep, counts).
- port_addr_check 0d24592683b6 (the re-run of RA, RB, PA and PB, `rerun-0d24/`), by its owner's registry entry, removes
  five of these: SAME-CONTENT across two symbols, jal INSN-SAME, PREDICT MAPS-STRING (where the source names a symbol),
  the donor-relative named-symbol rule (where the target's symbols are its own, as in RA and RB) and the .got rounding
  (measured here: the planted .got moves now read SLID-TO-NEIGHBOUR). It narrows ROUND-CONSTANT-SAME (a kept page-round
  value in a geometry slot, a value inside a named symbol, are no longer round constants). A by-address move onto an
  unrelated cell still reads SAME.
- roundconst v2: a kept small donor value that is also a right target quantity reads SAME; an unnamed run that does not
  pair is not checked; function sizes are not quantities. Covered by the count recompute.
- codeptr 12348302dfd2: its CELL rule accepts a different symbol when the value equals the pin word. Covered by the GOT
  check and the sweep.
- Rows settled by role only (a register number, a variable index, a page size) show that the numeral is not an address
  or an image quantity, not that its value is right; such values sit in proof steps that the kernel checks.
- Comment numerals: the gate and the sweep read proof text without comments. The d9e0 diff found no row where both
  port_core runs agree and our file differs only in a comment. Stale donor numerals in comments are the series' comment
  scrub step's work; this record adds no measured row. Line 4 of the B files lib/B/YE3i.v and lib/B/YD2j.v is the A twin's
  notice line (it names the ASan build and holds the A image's values, which are right for that build); line 5 states the
  B values.

## Older runs on this tree, superseded

port_addr_check was run on this core twice before this record, with older versions (`gate/GATE.md`, last table). Both
miss classes 3d2eee813cce covers; this record's runs supersede them.

## Reproducing

Tool copies of record: port_addr_check 3d2eee813cce (the registry's `tools/port_addr_check/3d2eee813cce/`, byte-equal to
its owner's `audit-tools/versions/3d2eee813cce/`, which the runs used; no later version was registered when these runs were
made, so its five named limits stand and are covered above; the later 0d24592683b6 re-ran RA and RB on the same inputs,
`rerun-0d24/README.md`, which also says how to reproduce that re-run); roundconst
`tools/roundconst-gate/32b39f3b34e9/roundconst.py`; codeptr `tools/codeptr/12348302dfd2/codeptr.py`; port_core: the file
`port_core.py`, sha256 d9e0589898fd12f83fd76e086a3d7ddf3d1a43a7008dd59a73f442bff30388aa, path
`tools/pg-reloc/d9e0589898fd/port_core.py` in the commit of the proofs repository whose tree is repository tree (git tree 0f4cc1fc13e5; internal record); record copy port_core.py (sha256 d9e0589898fd; internal record)
(the registry holds no copy of this version). `d9e0/runs/run.sh` refuses a port_core.py whose sha256 does not start
d9e0589898fd, and the 12 other files that the version line of `d9e0/runs/A1.log` and `A2.log` names are under the same
directory of that commit, each with the sha256 the line gives. Trees: `git archive` of c8557374ad2e (donor cgif_file_fuzzer lib),
plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record) (checked) and 781f46bc05cd (merged). Images: the four pins of `inventory.tsv`'s runs and their unstripped twins
(sha256 in `gate/GATE.md`). The scripts of each part are in its directory; host paths in them and in the run logs are
written as placeholders: `$W` = the work directory of this check; `$IMG` = its image copies; `$RUN` = its gate runs;
`$PLANT` = its planted copies; `$OURS` / `$MERGED` / `$DONOR` = `git archive` extracts of the checked commit, of the
merged tree and of the donor commit; `$PAC` / `$RC2` / `$CODEPTR` / `$D9E0` = the tool copies of record; `$HUB` = a clone
of the proofs repository; `$BIN` = the pinned donor image set. The parts' own work directories are named after this
record's sub-directories (triage-A, gen-cells, ...). In `d9e0/runs/A1.log` and `A2.log`, `$ADDRMAP` and `$ADDRMOVE` are
the file names, in `$D9E0`, of port_core d9e0589898fd's vendored address-map writer (sha256
4d51ec1c0069a242e4923a4eea37dc66f9f9aa0e4cbfeb0d9c8f8778954b893c) and address mover (sha256
2d846496640d126854e14d94fab4e22858af2642d4cba2b4ea8e4f750ef85f82). The text sanitizer that wrote these placeholders is
not shipped, nor is its host-side table; `internal-texts.md` gives the sanitizer's internal record entry and every other
text of this slice that was restated or moved. Three row tables are split by image into `.A.tsv` / `.B.tsv` files for
the repository's 5 MiB file cap (`MANIFEST.md` says which).
