# provenance/evidence/yh03-v64: the YH03 address tables under the YH03 tools v6.4 (read-only)

Both address tables, lib/Reusable/YH03.v (plain image) and lib/U/Reusable/YH03.v (ubsan image), were checked with the YH03
tools v6.4: yh03check fb3bfbc1eea8 and yh03regen 1254e5c96a44 (registry tools/yh03check/fb3bfbc1eea8/). No file changed: the
tables were already correct. Inputs: the pinned images (sha256 = projects/libreac/fuzz_decode/harness.yaml), their unstripped
twins, the twins' nm listing, and the unit's proofs directory. No run used --accept.

Commands (PINNED_DIR / TWIN_DIR: the directories of the pinned images and of their unstripped twins):

    yh03check.py --pinned PINNED_DIR/fuzz_decode.<b> --pins projects/libreac/fuzz_decode/harness.yaml --side <b> TWIN_DIR/fuzz_decode.<b> <YH03.v>
    yh03check.py ... --other-side <the other YH03.v> --proofs proofs/libreac/fuzz_decode ...      (plain; readers of copied cells)
    yh03regen.py --pinned PINNED_DIR/fuzz_decode.<b> --pins ... --side <b> --elf PINNED_DIR/fuzz_decode.<b> --syms-elf TWIN_DIR/fuzz_decode.<b> --proofs proofs/libreac/fuzz_decode --unchecked-ok <nm listing> <YH03.v>   (no --write)

Results (files beside this one):
- yh03check, both images: `# self-test: 223 known answers OK (yh03regen 163 + yh03check 60)`; exit 0; 18 of 18 section cells
  equal the image's section headers; 103 rows, 0 not OK; D cells by symbol 41 OK, 0 BAD; fe_getround OK-BY-LOAD; the
  got_DYNAMIC_reserved cell OK-GOT0; 'not checked by any rule: src0_debruijn_len, src0_vmlock'.
- yh03regen --proofs without --write, both images: `# self-test: 163 known answers OK`; exit 0; no ABSENT cell (classes:
  KEEP 155, KEEP-SIZE0 2, KEEP-SPAN 3, NOSYM 44, KEEP-BY-LOAD 1, KEEP-GOT0 1, UNCHECKED 2); the file is unchanged. The 2
  UNCHECKED string cells (str, str_2: no slug) have no reader.
- One definition per line: `grep -cE "Definition [a-z0-9]+_D_.*Definition [a-z0-9]+_D_"` prints 0 for both files
  (two-D-per-line.grep.txt).
- The two cells no rule checks, measured by hand: src0_debruijn_len (32, 32) has 0 readers (git grep -w over the unit).
  src0_vmlock (None, None) is read (YH02.v:24 MSyms ms_vmlock; YV00.v; the Hvml hypotheses of YN0g.v / YN0h.v), and None is
  right: in both images __vm_wait is musl's `dummy` (the symbols __vm_wait and dummy at 0x16030 plain / 0x16660 ubsan, size 4,
  bytes 67 80 00 00, a bare return), and the image has no vmlock symbol, so the routine reads no lock word.

## Cell-parse coverage (2026-10-31)

An independent cell-parse count, 2026-10-31, read decode's four cell tables at this series. It counted every declaration
with comments removed (any keyword, any layout) and applied the tools' own regexes to the raw text. Per table,
declarations : one-line cells : tool read : not read:
- lib/Reusable/YH03.v: 325 : 323 : 323 : 2 (read by yh03check: 101 A/E rows, 202 cells, + 103 D + 18 section);
- lib/U/Reusable/YH03.v: 325 : 323 : 323 : 2 (the same);
- lib/A/AB1w.v: 823 : 771 : 771 : 52 (read by the v5.2.1 tfib run after the removals: `771 named cells`);
- lib/B/YB1w.v: 811 : 759 : 759 : 52 (the same run: `759 named cells`).

Every declaration is a one-line `Definition` with no comment before its name, so no cell is skipped in silence: no
cell has a hidden shape (no Example, Let, Fact or Lemma ... Defined, no cell split over lines), and the tools read no
name from inside a comment.

The definitions not read as cells:
- YH03, 2 per table (yh03check names both as not checked by any rule, above):
  - src0_vmlock := None: TRUE. Readers: YH02.v:24 (a constructor argument), YV00.v, and the `src0_vmlock = Some v ->
    ...` hypotheses of YN0g, YN0h, YN0k, YN0l, YN0m, YN0n, YN0o and YN1f (each also as `_cf`), in both builds; with None
    they are vacuous. The pinned images hold no vmlock object, and __vm_wait is a 4-byte `ret` (word 0x00008067).
  - src0_debruijn_len := 32: TRUE (the table at src0_D_debruijn32 is a 32-byte permutation of 0..31); 0 readers
    (YH02.v passes the literal 32, not the name).
- AB1w / YB1w, 52 per table: the section bounds tfib_<sec>_lo / tfib_<sec>_hi, tfib_img_lo / tfib_img_hi, tfib_entry,
  tfib_gp and the tfib_at_* atable fields. Each has 0 readers: `git grep -w` over the unit outside provenance/ finds
  each name only in the two tables (measured again here: 52 of 52 in each table). The count's verdicts against
  the pinned image: 51 per table TRUE (the section bounds equal the image's section headers; tfib_entry and
  tfib_at_a_entry are e_entry; tfib_gp is __global_pointer$; tfib_at_ph_* are img_lo + e_phoff / e_phentsize /
  e_phnum; every other tfib_at_* equals atable --fields on that image; tfib_img_lo / tfib_img_hi are 0x10000 / 0x5f6000,
  computed from both images' loaded segments with IMG_LO_val), and tfib_at_stops_more, below.

Removal list, next series:
- lib/A/AB1w.v and lib/B/YB1w.v tfib_at_stops_more — lists 12 of atable's 13 self-loops (missing
  SealedRepairReservation+0xc0), unread; removed in the next series. Measured here with atable --fields (start-up set
  8cd71d3a4bb) on the pinned images 5973b76807d8 (A) and 5d05689fd5b1 (B): lib/A/AB1w.v lists 12 addresses, each one
  of atable's 13 self-loops, and lacks 0x6ddc0; lib/B/YB1w.v lists 12 and lacks 0x6de0c. Both are
  `_ZN11__sanitizerL23SealedRepairReservationEmm+0xc0`, the self-loop atable appends after its stop list. A missing
  entry can only make a start-up check fail, so the count judged the cell sound; it is unread either way.

## From the former slice MANIFEST.md

This README replaces the slice MANIFEST.md (2026-10-31); the file list and sha256 of every file are in provenance/evidence/MANIFEST.md.

The MANIFEST.md had the title of this README and no other prose. What each file is, where the text above does not
say it:

- `check-fb3bfbc1eea8.plain.summary.txt`: yh03check summary lines (plain)
- `check-fb3bfbc1eea8.ubsan.summary.txt`: yh03check summary lines (ubsan)
- `check-fb3bfbc1eea8.plain.proofs.summary.txt`: yh03check summary lines with the readers run (plain)
- `regen-1254e5c96a44.plain.proofs.summary.txt`: yh03regen --proofs summary lines, no --write (plain)
- `regen-1254e5c96a44.ubsan.proofs.summary.txt`: yh03regen --proofs summary lines, no --write (ubsan)
- `NOSYM.md`: the 44 NOSYM cells of each table, read against the unit's pins: what each is judged by and what was
  found
- `nosym-plain.tsv`: the per-cell table of lib/Reusable/YH03.v: value, class, expected, found, verdict, readers
- `nosym-ubsan.tsv`: the per-cell table of lib/U/Reusable/YH03.v, the same columns
- `nosym-readers.tsv`: the readers of each NOSYM cell outside the two YH03.v (git grep -w over the unit)
- `nosym-refs.plain.out`: the code of the plain twin that forms the addresses whose rule needs it
- `nosym-refs.ubsan.out`: the same for the ubsan twin
- `nosym_table.py`: judges every NOSYM cell by the rule its name states (const / got / table / object)
- `refs.py`: which code of an image forms a given address, through the comparison kit's own target pass
- `run.sh`: the whole check: yh03check on both files, the readers, the judgement, the references
