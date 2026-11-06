# kit-rerun: the exposure scans of cmpkit 86da41d3ef68 on the records made on cmpkit 4bbd3a74be89

cmpkit 86da41d3ef68 (tools/cmpkit/86da41d3ef68 at the tools commit 98e50c029045) supersedes cmpkit 4bbd3a74be89. Its
README ("For lanes that compared on 4bbd3a74be89 (or older): what needs a re-run") gives two scans:
- `luiscan.py` 9ae61e4a0e01: rule 8 exposure. `exposure` 0 for a function in both images means rule 8 leaves the old
  verdict unchanged.
- `ambiscan.py` 9f61b4cee422: a by-name compare that took the lowest-address copy of a name that several functions
  carry. A TOTAL of 0 ambiguous hits means no such compare.

`run.sh` beside this file runs both scans on each record. As a control, it also runs the record's compares under
strictcmp3.py 65688e94214a and compares old against new with `diffcheck.py` (word verdict, counts, accepted targets,
differing targets). Each log lies beside its record. The twin proofs are in `twins.log`. Paths in this file are relative
to `provenance/evidence/kit-rerun/`.

| record | scan log | luiscan | ambiscan | strictcmp3 control |
|---|---|---|---|---|
| `A/kit-rerun-4bbd3a74be89/` (7 pairs, donor twin : decode A twin) | `A/kit-rerun-4bbd3a74be89.scans-86da41d3ef68.log` | exposure 0 in both images, 7 of 7 | 0 ambiguous hits (the 15 out/ files of the re-run: 7 names; the whole directory: every file) | 7 of 7 keys SAME |
| `B/fncmp.cmpkit-4bbd3a74be89.log` (8 functions, symtwin and donor twin : decode B twin) | `B/fncmp.cmpkit-4bbd3a74be89.scans-86da41d3ef68.log` | exposure 0 in all three images, 8 of 8 | 0 ambiguous hits for S : E and T : E (8 names) | 16 of 16 keys SAME |
| `cmpkit-4bbd3a74be89/settled.tsv` (Allocate +0xdc S:E and T:E, PoisonShadow +0x48c S:E) | `cmpkit-4bbd3a74be89/settled.scans-86da41d3ef68.log` | exposure 0 in all three images, 2 of 2 | 0 ambiguous hits; it reads no name here (see below) | 3 of 3 settled rows are the same kit difference |

All three records: scans clear. No row is exposed, so no row was re-run, and no verdict changes.

- **lui values through every ALU op (the KIT LIMIT).** luiscan follows a lui value through addi, load, store and jalr
  only, so its `memfed 0` is not proof. Every lui of the three records has been hand-traced through every ALU op:
  - the A record, by its author: `A/kit-rerun-4bbd3a74be89/LUI-HANDTRACE.md`, 18 rows per image, 4 (a), 14 (b);
  - the B record and the settled rows: `B/LUI-HANDTRACE-B.md`, 19 rows per pair, 5 (a), 14 (b). The 18 rows shared
    with A have byte-identical ROW lines; the 19th is TryMemCpy +0x34, a stored poison pattern.

  No address depends on a lui value.
- **lui-in-section:** none. `insec` and `memfed` are 0 for every function in every image, so strictcmp3 forms no lui
  address target in these records (OPEN LIMIT 1 has no row here).
- **lui-const (registry notice: a `lui-const (dataflow)` row is no evidence when the lui value meets a register-register
  or logical ALU op):** no output of the three records holds `lui-const`, and luiscan's `luiconst` column is 0 in every
  image. The command and its counts are in `luiconst-search.out`. There is no such row to hand-check.
- **MemToShadow:** no record compares `_ZN6__asanL11MemToShadowEm`, by name or by address. Every compared name has one
  sized FUNC copy per image (luiscan `--fns` lists one row per name and image; strictcmp3 refuses a name with several
  copies, and it refused none). The A record's by-address re-run of its 7 pairs is
  `A/kit-rerun-4bbd3a74be89/out/nmcount.out`: every by-address verdict equals the by-name one.
- **Base-relative switch tables (OPEN LIMIT 4):** no record claims or relies on a jump or switch table.
- **The settled rows:** strictcmp3 reports exactly the differing targets that `settled.tsv` settles, with the same
  kinds:
  - Allocate +0xdc: `data-differs`, the bounded-index table of OPEN LIMIT 5.
  - PoisonShadow +0x48c S:E: `got-tls`. The symtwin has no STT_TLS symbol. On the donor twin, strictcmp3 accepts the
    row as `gotval ... fake_stack_tls+0x1@tls`.

  The combined verdict column reads `DIFFERENT-target` for these rows, as the old target-differ column did. Their
  settlements in `settled.tsv` still apply unchanged.
- **ambiscan on settled.tsv:** ambiscan takes a row's first field as its function name. In `settled.tsv` that field is
  the pair, so the scan reads no name there. The two functions of the settled rows are covered three other ways:
  ambiscan reads them in the B record (the same pairs, 0 ambiguous hits); luiscan `--fns` finds one copy in each image;
  and strictcmp3 compares them by name without a refusal.
- **The A record's own scan:** the record's author ran the same two scans
  (`A/kit-rerun-4bbd3a74be89/SCANS-86da41d3ef68.md` and its 3 outputs). This run agrees with it:
  - its luiscan ROW and TOTAL lines are byte-identical to `out/luiscan-86da41d3ef68.out`;
  - its ambiscan TOTAL line over the same 15 files is byte-identical to `out/ambiscan-86da41d3ef68.out`.

  This run also reproduced the author's lui trace: the ROW lines of `B/luitrace-pair-TE-86da41d3ef68.out` for the 18
  shared rows are byte-identical to those of `out/luitrace-pair-86da41d3ef68.out`.
