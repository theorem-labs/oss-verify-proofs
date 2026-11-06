# fuzz_wire kit relocation: gate record on the series tree

Tool: port_addr_check.py, sha256 prefix 3d2eee813cce (it keys each image by its build letter: P = plain, U = ubsan).
Donor: proofs/libreac/fuzz_decode/lib at 25e3d17bdb5059606131377a3722d585415ab5d6. Images (pins, sha256 prefix):
decode plain 556b61e63c44, decode ubsan ff70f30e22dc; fuzz_wire plain c8763dfc4e81, fuzz_wire ubsan 6e91fe0b5555.
Tree checked: this unit's lib/ at the series head, after the code commits 21a12f93ff3 (FILE-sink restatement), 5dc55e235e5 (YH03 cells),
8b420399cf8c (review fixes), 167c590ef1b8 (YK1a self-test constants) and a8248a48a2c5 (YH03 keeps the three true stdio cells).

Command (arguments in angle brackets are local paths):

    port_addr_check.py --git <hub clone> --src 25e3d17bdb50:proofs/libreac/fuzz_decode/lib --dst <this unit's lib>
      --src-image P=<decode plain pin>:<twin> --src-image U=<decode ubsan pin>:<twin>
      --dst-image P=<fuzz_wire plain pin>:<twin> --dst-image U=<fuzz_wire ubsan pin>:<twin>
      --assign 'U/**=U' --assign '**=P' --paired-only --fail-on-flags --summary --only-flags --out gate.tsv
      --include <each .v file the relocation script (../k2/k2_relocate.py) writes for this unit>

Result: exit 4. `count files paired: 1108`. `FLAG-CLASSES 575d398c6022	27 classes count as findings (--list-flag-classes prints them)`. `UNMEASURED named-symbol 0 / 90 cells	UNMEASURED-NAME 0 rows	UNPAIRED-FILE-UNMEASURED 122 rows`. `UNMEASURED 122 rows in 1 classes: UNPAIRED-FILE-UNMEASURED=122 (measured by nothing: neither a finding nor a pass)`. `FLAGGED 816 rows in 4 classes: DIFFERENT-SYMBOL=2 NON-ADDRESS-CHANGED=8 UNPAIRED-PORTED=62 UNPAIRED-SOURCE=744`.
Flagged rows by class: DIFFERENT-SYMBOL 2, NON-ADDRESS-CHANGED 8, UNPAIRED-FILE-UNMEASURED 122, UNPAIRED-PORTED 62, UNPAIRED-SOURCE 744.

Each flagged class, with its measured reason (plain and U alike):

| rows | class | file:line | reason |
|---|---|---|---|
| 62 | UNPAIRED-PORTED | Reusable/YI14.v, Reusable/YL03.v (U the same) | the FILE-sink restatement (21a12f93ff3): its option-typed lines have no donor line; they are not relocations. |
| 744 | UNPAIRED-SOURCE | Reusable/YI14.v, YL03.v, YH03.v; FrameAPI.v:33, :62 (U the same) | donor lines the restatement replaced; the 5 YH03 cells 5dc55e235e5 deleted (no reader); the donor YH03 definitions the unit does not use; `ms_calloc B` is `None` (the plain and UBSan images have no symbol named `calloc`; musl's __libc_calloc is linked). |
| 2 | DIFFERENT-SYMBOL | Reusable/YH03.v (U the same) src0_A_stdio_seek | the relocation of record sets this code cell BY NAME to this unit's __stdio_seek; the tool expects the donor's symbol + offset (__stdio_write+0x164), and the donor's value was not __stdio_seek. |
| 8 | NON-ADDRESS-CHANGED | FrameAPI.v:14/15, Reusable/YL0k.v:183 (0xb8 -> 0xa0); Reusable/YN3f.v:283, :343 (U the same) | the RELRO list length from the section headers (.init_array up to the stack-guard .got slot = 0xa0 in both builds); the jal immediates of instruction words read from this unit's image (each word is a fetch_word fact proved in the same file, which compiles). |
| 122 (reported, not flagged) | UNPAIRED-FILE-UNMEASURED | one row per file | files of this unit's lib/ that the relocation script does not write (the unit's own walks, specs and harness files, and the new YI5cSat.v, whose 2 rows go with its deletion by 05336ebfc612: 120 at the series head): no donor counterpart, so not relocations; the gate measures no numeral in them. |
No row is a relocation error. Verbatim tool output: the internal record of the series (named in the pull request body), file gate/gate.tsv, sha256 65995893cb56e260876517654a3afce9e53c1ff81b7ab110ab014b8980318671; run log: the internal record of the series (named in the pull request body), file gate/gate-run.log, sha256 ca1b72ac64c4bf552c7a4cff445dfcc0ea5d68d5d5f59ad6a701d360b5baa929.

## Re-run on port_addr_check 0d24592683b6

The same command and inputs on port_addr_check.py sha256 prefix 0d24592683b6 (the version that fixes the limits of
3d2eee813cce), on the same series tree: exit 4, `FLAG-CLASSES 575d398c6022`, `UNMEASURED named-symbol 0 / 90 cells`.

| version | flagged rows |
|---|---|
| 3d2eee813cce | `FLAGGED 816 rows in 4 classes: DIFFERENT-SYMBOL=2 NON-ADDRESS-CHANGED=8 UNPAIRED-PORTED=62 UNPAIRED-SOURCE=744` |
| 0d24592683b6 | `FLAGGED 816 rows in 4 classes: DIFFERENT-SYMBOL=2 NON-ADDRESS-CHANGED=8 UNPAIRED-PORTED=62 UNPAIRED-SOURCE=744` |

No row changed class.
No row is in a value class (GEOMETRY-CHANGED, STALE-DONOR-CODE-POINTER, SLID-TO-NEIGHBOUR; the 2 DIFFERENT-SYMBOL
rows are the src0_A_stdio_seek rows explained above). Verbatim output: the internal record of the series (named in the
pull request body), file gate/gate-0d24.tsv, sha256 4c9c23a23f2ef748f148cc5d0f7e802f29c6a136cf7dc81f20c155225b86c5cd; run log gate/gate-run-0d24.log, sha256 bb2bdad1ea16b3c18666d51758b91343f51d11f4f47946fab21fa0cefe873691.

## Re-run on the series head after the shared restatements (RECORD.md items 6 and 8)

The same command, inputs and checker (port_addr_check.py sha256 prefix 0d24592683b6) on the series head bbe1bbba6aeb,
where lib/Lib/Acfg.v (4f4da94a3b6a) and lib/Reusable/R/Cfg.v (b96006e5d59f) are the shared clean-room restatements, taken byte-equal by
sha: exit 4. `count files paired: 1108`. `FLAG-CLASSES 575d398c6022 27 classes count as findings (--list-flag-classes prints them)`. `UNMEASURED named-symbol 0 / 90 cells  UNMEASURED-NAME 0 rows  UNPAIRED-FILE-UNMEASURED 120 rows`. `FLAGGED 852 rows in 5 classes: DIFFERENT-SYMBOL=2 GEOMETRY-CHANGED=1 NON-ADDRESS-CHANGED=8 UNPAIRED-PORTED=79 UNPAIRED-SOURCE=762`.

Against the set above: 32 rows more, 0 rows fewer, and every added row is in one of the two restated files:

| rows | class | file | reason |
|---|---|---|---|
| 13 | UNPAIRED-SOURCE | Lib/Acfg.v (donor lines 488-525, 545) | numerals in the proof scripts of vm_base_ok_step and vm_find_base_complete in the donor's file; the restatement rewrote those proofs (its statements and definitions are the delivered text), so the donor lines have no aligned line. |
| 3 | UNPAIRED-SOURCE | Reusable/R/Cfg.v (donor lines 66, 71, 129) | the same, in the proofs of acfg_family_off_222, acfg_family_off_226 and refusal_spurious_of_grant. |
| 1 | GEOMETRY-CHANGED | Lib/Acfg.v:520 (vm_base_ok_step, sentence 49) | a proof-script numeral paired with a different one of the rewritten proof (0x1000 / 0x40); no address. |
| 10 | UNPAIRED-PORTED | Lib/Acfg.v (refusal_b_214 / 216 / 222 / 226, vm_base_ok_step) | numerals of the rewritten proofs (the lemma-name numbers 0xd6 .. 0xe2, page and alignment constants). |
| 5 | UNPAIRED-PORTED | Lib/Acfg.v (cr2_refusal_b_at, cr2_vm_base_ok_iff) | the statements of two helper lemmas the restatement adds; no donor counterpart. |

None of these files is the relocation script's output any more, and no row is a relocation of an image value. From this
head on, this run's flagged set is the gate's expected set: the internal record of the series (named in the pull request
body), file gate/gate-restated.tsv, sha256 c7782f55743435cb16a418b6207744061776c556309d2f053366821b27aef2ba; run log gate/gate-restated-run.log, sha256 bb436fcd280d6a3c172ba3f95893b3d0eea391b5c6d7f7636280f89f4c0828ca.
