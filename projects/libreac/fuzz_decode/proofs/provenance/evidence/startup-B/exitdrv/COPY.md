# COPY.md: the exit-driver record of image B, copied from the working directory

Until commit `8529e243afd7`, `lib/B/YD1y.v` and `lib/B/YE23.v` said in header line 5 that every numeral they hold is
named in a record they cited by its path in the start-up writer's work directory, which the shipped tree does not hold;
since that commit line 5 cites this directory's `EXITDRV.md` (`README.md`, "Where the headers point"). This directory
holds that record, `EXITDRV.md`, and `exitdrv.run2.out`, the stdout of the run that wrote both files. In both, a named
token is put in where the original names a host path, a worker, an internal tool, a lane, or a path into a worker's
own work directory. Nothing else differs. `copycheck.py` beside this file proves it from the original's bytes in git.
`README.md` states the record's one erratum (image B) and where the lib headers point.

## 1. The record the image-B headers cite

- Until `8529e243afd7`, header line 5 of `lib/B/YD1y.v` and `lib/B/YE23.v` named the record by a path in the writer's
  work directory, and line 1 named its writer exitdrv.py by a path in the same work directory. There, the record
  `EXITDRV.md` has sha256
  `337cd4a543e524427f97317c58e593077da71c65186ba04ddd41b09402f15c6f`: the bytes of
  `proofs/libreac/fuzz_decode/provenance/startup-gen/A/exitdrv/EXITDRV.md` at commit
  `fadeeb148437a4303c8c69628e82fb04c844c523`. The run's stdout
  `exitdrv.run2.out` beside it has the bytes of `exitdrv.run2.out` in the same git directory (sha256
  `2dec73eee925572cc0676e3e83ac1e60da78ca513ecaf1f29cbcd65b8e618679`). copycheck.py reads both from git.
- The two work-directory files are also kept verbatim in the internal records ref, commit
  `594fa9d1d7218d06b07214e8bfa929a5d06483a4`: `exitdrv/B/EXITDRV.md` (sha256
  `337cd4a543e524427f97317c58e593077da71c65186ba04ddd41b09402f15c6f`) and `exitdrv/B/exitdrv.run2.out` (sha256
  `2dec73eee925572cc0676e3e83ac1e60da78ca513ecaf1f29cbcd65b8e618679`).
- Why this file is the record the headers cite (measured):
  - its section 0 lists the run's outputs by sha256, among them `YD1y.v`
    `93fd1d70a816cd79097696e18f21b847e39989a320c0baa9c206de383ae44b30` and `YE23.v`
    `66092be4b040bddccbd60ffb1327cb631db5f6e1e5b046d2b28008c2f97032b6`; the `YD1y.v` and `YE23.v` beside it in the work
    directory have exactly these sha256;
  - lines 1-5 (the header) of those two outputs are byte-equal to lines 1-5 of `lib/B/YD1y.v` and `lib/B/YE23.v` at
    `fadeeb148437`; the other lines that differ are the hand edits that `../README.md` lists by commit;
  - every numeral value of `lib/B/YD1y.v` (13 distinct values) and of `lib/B/YE23.v` (56) at `fadeeb148437` that
    cgif's `lib/YD1y.v` / `lib/YE23.v` at `c8557374ad2e` does not hold is named in it as a hex value, the bounds
    `0x5d39c0` / `0x5d39c3` of the third window's cut in `lib/B/YD1y.v` included (section 3, XW2 of B).
- The record covers both images (section 5: a decode.asan column for image A, a decode.asan-ubsan column for image B).
  So the two files here are the same token copies as `../../startup-A/exitdrv/EXITDRV.md` and
  `../../startup-A/exitdrv/exitdrv.run2.out`: the same bytes, from the same spans. `copycheck.py` is the same file as
  there; `COPY.diff` and `copy-edits.tsv` are image A's without the rows of `gate.drvivs.txt`, which is not
  here; this COPY.md, `README.md` and `SHA256SUMS` are this directory's own.
- Section 3 gives the file sha256 of each copied file's original at `fadeeb148437`, beside the sha256 of the file as
  shipped here.

## 2. What changed, and the proof

73 spans in the 2 files are changed. Each span is one whole token of the original (a WORKDIR span is the directory
part of a path; the `/` and the file name after it stay). A token replaces it, in UPPER_CASE, as
`provenance/evidence/kit-rerun/A/kit-rerun-4bbd3a74be89/COPY.md` does. No span holds a newline, so every line keeps its
number, and no line is added or removed.

| token | class | spans | what it stands for |
|---|---|---|---|
| `HUB` | PATH | 1 | the hub clone (a directory) from which the record's writer read the donor at `c8557374ad2e` (`EXITDRV.md` line 5) |
| `OWNER_WORKER` | NAME | 2 | the worker session that wrote the record and owned the decode start-up files |
| `PORTER_WORKER` | NAME | 4 | the worker session that ported AF0m / AD2l (the porter) |
| `MAP_TOOL` | TOOL | 50 | the internal address-map tool that wrote `map.cgif2decode.asan.json`, the `ELFMAP_A` input of exitdrv.py (`../../startup-A/inputs/map.cgif2decode.asan.json`: its `tool` field held the same text, and the same token replaces it there); `MAP_TOOL+symtab` in the source column of `exitdrv.run2.out` (47 rows) is a data address moved by that map and named in the unstripped twin's `.symtab` |
| `MAP_KIT` | TOOL | 1 | the internal tool kit that holds MAP_TOOL |
| `LANE_1` | LANE | 1 | the lane (session) of the record's writer that wrote revision 1 (`EXITDRV.md` line 3) |
| `LANE_2` | LANE | 1 | the lane (session) that made revision 2, the DRV_IVS fix (`EXITDRV.md` line 17) |
| `LANE_3` | LANE | 1 | the lane (pipeline) that built the pinned original images (`EXITDRV.md` line 30) |
| `WORKDIR` | WORKDIR | 7 | a directory of the record's writer's own work tree, the only token that stands for more than one text: where the run's outputs and exitdrv.py were (lines 7, 24), where the pins and the unstripped twins were linked (lines 33, 35), the binmatch directory (line 37), the map input's directory (line 40) and drvivs.py's directory (line 105) |
| `WORKDIR_NOTE_1` | WORKFILE | 2 | a note of that work tree, the decode-binary certificate notes, cited for its findings F1 and F2 (lines 60, 225) |
| `WORKDIR_NOTE_2` | WORKFILE | 2 | the work tree's inputs note, cited for its section 3, the rename table (lines 206, 221) |
| `WORKDIR_LOG` | WORKFILE | 1 | the log of the first build (line 17) |

`EXITDRV.md` has 26 spans (HUB 1, OWNER_WORKER 2, PORTER_WORKER 4, MAP_TOOL 3, MAP_KIT 1, LANE_1 1, LANE_2 1, LANE_3 1,
WORKDIR 7, WORKDIR_NOTE_1 2, WORKDIR_NOTE_2 2, WORKDIR_LOG 1) and `exitdrv.run2.out` 47 (MAP_TOOL). Dates are kept as
the original has them, and so is the donor's branch name.

`COPY.diff` is the diff original -> copy (one hunk per changed line; the `-` line shows every removed span as
`<redacted>`). `copy-edits.tsv` lists every span: file, line, byte offset, length, the sha256 of the removed bytes, the
class and the token. `SHA256SUMS` lists every file here but itself. `copycheck.py`'s docstring gives its checks; they
are those of `../../startup-A/exitdrv/COPY.md` section 2. Its output on this tree (scanner of record:
`binscan_of_record.sh`, scanner `0609a660961e`, exceptions `2fe8196d9738`):

```
$ python3 copycheck.py <hub clone> --scanner <scanner of record>
copycheck: original fadeeb148437 proofs/libreac/fuzz_decode/provenance/startup-gen/A/exitdrv: 2 files copied (EXITDRV.md, exitdrv.run2.out); 73 spans in 2 files {'LANE': 3, 'NAME': 6, 'PATH': 1, 'TOOL': 51, 'WORKDIR': 7, 'WORKFILE': 5}; every other byte identical; COPY.diff, COPY.md file table and SHA256SUMS match
copycheck: scanner on the 8 files here: exit 0, 0 blocking hits; listed, non-blocking, per file: {}
copycheck: scanner on the original: 64 blocking hits, every one inside a replaced span (0 listed, non-blocking); 58 of 73 spans hold a hit; spans that hold none, by class: {'LANE': 3, 'WORKDIR': 7, 'WORKFILE': 5}
```

No number, verdict, count or row changed. Every table row, value, address and sha256 of the original is in the copy
unchanged, the one wrong row included (`README.md`, "Erratum").

## 3. Files (the manifest of this directory)

Every file here except this one and `SHA256SUMS` (each names the other's sha256), with the sha256 of its bytes as
shipped. For a copied file, the file sha256 of its original at commit `fadeeb148437` (the first 12 hex digits; a file
that is not a copy has `-`), and the number of replaced spans. `python3 copycheck.py <hub clone> --write-table` wrote
this table from the originals in git and the files here, and copycheck.py checks every row.

| file | original file sha256 (12 hex) | sha256 as shipped | spans |
|---|---|---|---|
| `COPY.diff` | - | `88deff6e22607231096e214c0d0efcd34123fcca8049662e194692222c80196d` | 0 |
| `EXITDRV.md` | `337cd4a543e5` | `25ddc26fb32cb9b34c3f30b97be458b723f089af0eec37a548ad51582c3d7cf9` | 26 |
| `README.md` | - | `0ade8911a3c66275c4e0da380d6f33293ffeca08d5866f35ed2fcff639311639` | 0 |
| `copy-edits.tsv` | - | `91d9a7055a1b1fb085a3c394e7cf71aff8438cc50b7d291d47dea17e1f68c6a5` | 0 |
| `copycheck.py` | - | `f143fc4f14cadf4e4d7bb234276c7a54a7ecd17b0a1c4f13614131de1aa74c7c` | 0 |
| `exitdrv.run2.out` | `2dec73eee925` | `24a4e1bdf3c74e45de9635a465f286df217302e93a2a7919b05cc83308bf2d42` | 47 |
