# Cited paths outside provenance/evidence/

Some files in this directory cite paths that are not in `provenance/evidence/`. This file tells where each
of these paths is. The files that cite them are not changed. Paths are relative to `proofs/libreac/fuzz_boxreg/`.

| Cited as | Cited by | Where it is |
| --- | --- | --- |
| `proofs/libreac/fuzz_boxreg/provenance/core-reloc/ab1w` | `NOTES.md` line 198 | prover-only (on the series branch; not shipped): `provenance/core-reloc/ab1w/`. It holds the same files as this directory, byte for byte (this file excepted). |
| `../flags/ab1w.tsv` | `NOTES.md` line 239 | relative to `provenance/core-reloc/ab1w/`, where this record was first written: prover-only (on the series branch; not shipped): `provenance/core-reloc/flags/ab1w.tsv`. The same bytes: `ab1w.tsv` (sha256 a06731dd1f26; internal record). |

The sysconf +0xe8 row of RERUN-cmpkit-4bbd3a74be89.md writes the toolchain image's musl sysroot path as a description (scanner rule, 2026-10-31), and its lines 465, 641, 642 and 665 name the toolchain's source repository by its role, without its name or its commit (private-data owner ruling, 2026-10-31); every other byte is as copied.

## Cell-parse coverage (2026-10-31)

An independent cell-parse count, 2026-10-31, read the unit's two tfib tables, lib/A/AB1w.v and lib/B/AB1w.v, at this
series. It counted every declaration with comments removed (any keyword, any layout) and applied the tools' own regexes
to the raw text. Per table, declarations : one-line cells : tool read : not read:
- lib/A/AB1w.v: 924 : 873 : 873 : 51 (read by the v5.2.1 tfib run after the removals: `873 named cells`; this file has
  no tfib_text_hi);
- lib/B/AB1w.v: 925 : 873 : 873 : 52 (the same run: `873 named cells`).

Every declaration is a one-line `Definition` with no comment before its name, so no cell is skipped in silence: no
cell has a hidden shape (no Example, Let, Fact or Lemma ... Defined, no cell split over lines), and the tools read no
name from inside a comment.

The definitions not read as cells, 51 in lib/A/AB1w.v and 52 in lib/B/AB1w.v: the section bounds tfib_<sec>_lo /
tfib_<sec>_hi, tfib_img_lo / tfib_img_hi, tfib_entry, tfib_gp and the tfib_at_* atable fields. Each has 0 readers:
`git grep -w` over the unit outside provenance/ finds each name only in the two tables, apart from tfib_data_rel_ro_lo
and tfib_got_hi, which the header comment of lib/A/Prog/BoxImg.v and of lib/B/Prog/BoxBImg.v names as the bounds of
the read-only range (measured again here). The count's verdicts against the pinned image: 50 (A) and 51 (B) TRUE (the
section bounds equal the image's section headers; tfib_entry and tfib_at_a_entry are e_entry; tfib_gp is
__global_pointer$; tfib_at_ph_* are img_lo + e_phoff / e_phentsize / e_phnum; every other tfib_at_* equals atable
--fields on that image; tfib_img_lo / tfib_img_hi are 0x10000 / YImgTop.IMG_TOP = 0x5f6000), and tfib_at_stops_more,
below.

Removal list, next series:
- tfib_at_stops_more — lists 12 of atable's 13 self-loops (missing SealedRepairReservation+0xc0), unread; removed in the next series

Measured again here with atable --fields (start-up set 8cd71d3a4bb) on the pinned images eacfa20547ad (A) and
7620eb05e0ad (B): lib/A/AB1w.v lists 12 addresses, each one of atable's 13 self-loops, and lacks 0x6dca8;
lib/B/AB1w.v lists 12 and lacks 0x6dd08. Both are `_ZN11__sanitizerL23SealedRepairReservationEmm+0xc0`, the
self-loop atable appends after its stop list. A missing entry can only make a start-up check fail, so the count
judged the cell sound; it is unread either way.
