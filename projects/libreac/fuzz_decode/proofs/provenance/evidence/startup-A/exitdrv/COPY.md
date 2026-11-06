# COPY.md: the exit-driver record of image A, copied from the working directory

Until commit `8529e243afd7`, `lib/A/AD1y.v` and `lib/A/AE23.v` said in header line 5 that every numeral they hold is
named in `provenance/startup-gen/A/exitdrv/EXITDRV.md`. That directory is a working directory: it is not shipped, so
the citation had no target in the shipped tree; since that commit line 5 cites this directory's `EXITDRV.md`
(`README.md`, "Where the headers point"). This directory holds that record, `EXITDRV.md`, and the four run outputs
that were beside it. Two of the five files are byte-identical to the original. In `EXITDRV.md`, `exitdrv.run2.out` and
`gate.drvivs.txt`, a named token is put in where the original names a host path, a worker, an internal
tool, a lane, or a path into a worker's own work directory. Nothing else differs. `copycheck.py` beside this file
proves it from the original's bytes in git. `README.md` states the record's one erratum (image B) and where the lib
headers point.

## 1. The original

- Commit `fadeeb148437a4303c8c69628e82fb04c844c523`, directory
  `proofs/libreac/fuzz_decode/provenance/startup-gen/A/exitdrv/`. The five copied files are unchanged since they were
  added: `EXITDRV.md`, `exitdrv.run2.out` and the drvivs gate output by `aefd8c038286`, the two ae37data outputs by
  `b161fd4d9777` (the later `469e6875cc0a` changes only exitdrv.py there).
- Four copies keep their original's name. The drvivs gate output is shipped as `gate.drvivs.txt`: its original's name
  holds a lane name. copycheck.py finds each copy's original by its bytes, not by its name: the one file of that
  directory that, with the copy's spans put in, is the copy. Section 4 names it by its file sha256.
- The verbatim originals of the three token copies are also kept in the internal records ref, commit
  `594fa9d1d7218d06b07214e8bfa929a5d06483a4`: `exitdrv/A/EXITDRV.md` (sha256
  `337cd4a543e524427f97317c58e593077da71c65186ba04ddd41b09402f15c6f`), `exitdrv/A/exitdrv.run2.out` (sha256
  `2dec73eee925572cc0676e3e83ac1e60da78ca513ecaf1f29cbcd65b8e618679`) and `exitdrv/A/gate.drvivs.txt` (sha256
  `0cc0ff1c22f6d08b97aab50dbb9cc4f0cbd5ca0496e4bb88c71cbe00c62e6fc6`). They are the same bytes as the files of that
  directory that copycheck.py reads from git.
- Copied (5 files):
  - `EXITDRV.md`: the record. It gives, for every numeral of AE23 / AD1y and of their image-B twins YE23 / YD1y, the
    cgif value, the decode value and the source (section 5), and the controls and the reasons (sections 1 to 4).
  - `exitdrv.run2.out`: the stdout of exitdrv.py revision 2, the run that wrote the four files (numeral table with
    the seven `DEC` rows of the decimal literals, and the CONTROLS).
  - `ae37data.af0m-run4.out`, `ae37data.af0m-run5.out`: ae37data.py on AF0m runs 4 and 5 (the exit cells and the ODR
    region against AF0m's constant cells; run 4 has one MISS, run 5 none).
  - `gate.drvivs.txt`: drvivs.py, DRV_IVS of `lib/A/AD1y.v` against AF0m run 4's owned entries (0 overlaps) and its
    control on run 3 (the 2 atexit overlaps).
- Not copied: the scripts `exitdrv.py`, `ae37data.py` and `drvivs.py`. They are writers, not records, and stay in the
  working directory.
- Section 4 gives the file sha256 of each copied file's original at that commit, beside the sha256 of the file as
  shipped here.

## 2. What changed, and the proof

74 spans in 3 of the 5 files are changed. Each span is one whole token of the original (a WORKDIR span is the
directory part of a path; the `/` and the file name after it stay). A token replaces it, in UPPER_CASE, as
`provenance/evidence/kit-rerun/A/kit-rerun-4bbd3a74be89/COPY.md` does. The other 2 files are byte-identical to the
original. No span holds a newline, so every line keeps its number, and no line is added or removed.

| token | class | spans | what it stands for |
|---|---|---|---|
| `HUB` | PATH | 1 | the hub clone (a directory) from which the record's writer read the donor at `c8557374ad2e` (`EXITDRV.md` line 5) |
| `OWNER_WORKER` | NAME | 2 | the worker session that wrote the record and owned the decode start-up files |
| `PORTER_WORKER` | NAME | 4 | the worker session that ported AF0m / AD2l (the porter) |
| `MAP_TOOL` | TOOL | 50 | the internal address-map tool that wrote `map.cgif2decode.asan.json`, the `ELFMAP_A` input of exitdrv.py (`../inputs/map.cgif2decode.asan.json`: its `tool` field held the same text, and the same token replaces it there); `MAP_TOOL+symtab` in the source column of `exitdrv.run2.out` (47 rows) is a data address moved by that map and named in the unstripped twin's `.symtab` |
| `MAP_KIT` | TOOL | 1 | the internal tool kit that holds MAP_TOOL |
| `LANE_1` | LANE | 1 | the lane (session) of the record's writer that wrote revision 1 (`EXITDRV.md` line 3) |
| `LANE_2` | LANE | 2 | the lane (session) that made revision 2, the DRV_IVS fix (`EXITDRV.md` line 17), and ran the drvivs gate (`gate.drvivs.txt` line 1) |
| `LANE_3` | LANE | 1 | the lane (pipeline) that built the pinned original images (`EXITDRV.md` line 30) |
| `WORKDIR` | WORKDIR | 7 | a directory of the record's writer's own work tree, the only token that stands for more than one text: where the run's outputs and exitdrv.py were (lines 7, 24), where the pins and the unstripped twins were linked (lines 33, 35), the binmatch directory (line 37), the map input's directory (line 40) and drvivs.py's directory (line 105) |
| `WORKDIR_NOTE_1` | WORKFILE | 2 | a note of that work tree, the decode-binary certificate notes, cited for its findings F1 and F2 (lines 60, 225) |
| `WORKDIR_NOTE_2` | WORKFILE | 2 | the work tree's inputs note, cited for its section 3, the rename table (lines 206, 221) |
| `WORKDIR_LOG` | WORKFILE | 1 | the log of the first build (line 17) |

`EXITDRV.md` has 26 spans (HUB 1, OWNER_WORKER 2, PORTER_WORKER 4, MAP_TOOL 3, MAP_KIT 1, LANE_1 1, LANE_2 1, LANE_3 1,
WORKDIR 7, WORKDIR_NOTE_1 2, WORKDIR_NOTE_2 2, WORKDIR_LOG 1), `exitdrv.run2.out` 47 (MAP_TOOL) and
`gate.drvivs.txt` 1 (LANE_2). Dates are kept as the original has them, and so is the donor's branch name.

`COPY.diff` is the diff original -> copy. It has one hunk per changed line. The `-` line is the original line with
every removed span shown as `<redacted>`. The `+` line is the copy's line. The removed text is not in this tree.
`copy-edits.tsv` lists every span: file, line, byte offset, length, the sha256 of the removed bytes, the class and the
token. With the original's files, it is enough to rebuild the copy. `SHA256SUMS` lists every file here but itself.

`python3 copycheck.py <hub clone> --scanner <scanner of record>` reads the original from git and checks the following.
The checker's docstring gives the details.
- Every listed span is a whole token of its class, and no removed span holds a number (no `0x...` value, no run of
  three or more digits, no run of eight or more hex digits; the build log's compact date-time stamp is the one allowed
  run of digits).
- Each token always replaces the same text, WORKDIR aside, and each removed text always gets the same token.
- The original with the spans replaced is the copy, byte for byte; a file with no span is the original, byte for byte.
- No removed text is left anywhere in this directory as a whole token.
- `COPY.diff`, the file table below and `SHA256SUMS` match the files. copycheck.py writes COPY.diff (`--write-diff`)
  and the file table (`--write-table`) itself, and without those options checks them line for line.
- The scanner of record exits 0 on this directory with no blocking hit, and every blocking hit it finds in the
  original lies inside a replaced span. The LANE, WORKDIR and WORKFILE spans hold no scanner hit: they were found by
  reading.

Its output on this tree (scanner of record: `binscan_of_record.sh`, scanner `0609a660961e`, exceptions
`2fe8196d9738`):

```
$ python3 copycheck.py <hub clone> --scanner <scanner of record>
copycheck: original fadeeb148437 proofs/libreac/fuzz_decode/provenance/startup-gen/A/exitdrv: 5 files copied (EXITDRV.md, ae37data.af0m-run4.out, ae37data.af0m-run5.out, exitdrv.run2.out, gate.drvivs.txt); 74 spans in 3 files {'LANE': 4, 'NAME': 6, 'PATH': 1, 'TOOL': 51, 'WORKDIR': 7, 'WORKFILE': 5}; every other byte identical; COPY.diff, COPY.md file table and SHA256SUMS match
copycheck: scanner on the 11 files here: exit 0, 0 blocking hits; listed, non-blocking, per file: {}
copycheck: scanner on the original: 64 blocking hits, every one inside a replaced span (0 listed, non-blocking); 58 of 74 spans hold a hit; spans that hold none, by class: {'LANE': 4, 'WORKDIR': 7, 'WORKFILE': 5}
```

No number, verdict, count or row changed. Every table row, value, address and sha256 of the original is in the copy
unchanged, the one wrong row included (`README.md`, "Erratum").

## 3. What the record covers

The record covers both images: section 5 has a decode.asan column (image A: `lib/A/AE23.v`, `lib/A/AD1y.v`) and a
decode.asan-ubsan column (image B: `lib/B/YE23.v`, `lib/B/YD1y.v`). Its section 0 lists the four `.v` outputs of the
run by sha256; `lib/A/AE23.v` and `lib/A/AD1y.v` are the later re-emission of `469e6875cc0a` (the startup-A
README.md, "Identity"). Revision 2's note says the seven decimal literals are table rows `DEC` in section 5; section
5 has no `DEC` row, and the seven rows are in `exitdrv.run2.out` (its last block before the `SEG` rows).

## 4. Files (the manifest of this directory)

Every file here except this one and `SHA256SUMS` (each names the other's sha256), with the sha256 of its bytes as
shipped. For a copied file, the file sha256 of its original at commit `fadeeb148437` (the first 12 hex digits; a file
that is not a copy has `-`), and the number of replaced spans. `python3 copycheck.py <hub clone> --write-table` wrote
this table from the originals in git and the files here, and copycheck.py checks every row.

| file | original file sha256 (12 hex) | sha256 as shipped | spans |
|---|---|---|---|
| `COPY.diff` | - | `7ed74886805dfcedcf13236c1d9286a8457656bf504da53846bc48235d7061bf` | 0 |
| `EXITDRV.md` | `337cd4a543e5` | `25ddc26fb32cb9b34c3f30b97be458b723f089af0eec37a548ad51582c3d7cf9` | 26 |
| `README.md` | - | `d8592ce7eb8c72e83bf4e20e855a8fe20d4f98231cf939689d69243c1948b3fc` | 0 |
| `ae37data.af0m-run4.out` | `2e0e3db7f7c7` | `2e0e3db7f7c753da6e50d6080c10e1d796aab51aadadc07e86941c6256e66aa0` | 0 |
| `ae37data.af0m-run5.out` | `e69e6aae9aa2` | `e69e6aae9aa2fd78b43e740218c2ea0599590e19ded619303a925834a170e679` | 0 |
| `copy-edits.tsv` | - | `19329cca732d96e7d3c0399a91dfbc6ac84bea587c87217097ab7190a208a235` | 0 |
| `copycheck.py` | - | `f143fc4f14cadf4e4d7bb234276c7a54a7ecd17b0a1c4f13614131de1aa74c7c` | 0 |
| `exitdrv.run2.out` | `2dec73eee925` | `24a4e1bdf3c74e45de9635a465f286df217302e93a2a7919b05cc83308bf2d42` | 47 |
| `gate.drvivs.txt` | `0cc0ff1c22f6` | `9263dd1298aab8803701058a7a4ff202e3a6ed6ddf7c6714d3fae72e1a79b56e` | 1 |
