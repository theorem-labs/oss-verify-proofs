This README replaces the slice MANIFEST.md (2026-10-31); the file list and sha256 of every file are in provenance/evidence/MANIFEST.md.

# provenance/evidence/startup-A: inputs of the image-A start-up writers, and the exit-driver record

Each input under `inputs/` is read by a writer of record under `provenance/startup-gen/A/` and was not in git before.
The bytes are the bytes that writer read, except one cleaned copy (below), which only `inputs/scrub_input.py` wrote.

## Cleaned copy

exitdrv.py's third input (`ELFMAP_A` of exitdrv.py, a work-tree path in the tool; the committed copy is
`inputs/map.cgif2decode.asan.json`; original sha256
`0d19cf8f15812964ac5eeb87a2917a705286cb9075997f31b9032a89c669d160`) fails the scanner in three string values: `tool` and
the two image paths `old.path` / `new.path`. exitdrv.py reads only its `runs` key. The committed copy replaces those three
values with tokens and copies every other byte:

    python3 inputs/scrub_input.py json ORIGINAL inputs/map.cgif2decode.asan.json \
      --sha256 0d19cf8f15812964ac5eeb87a2917a705286cb9075997f31b9032a89c669d160 --scanner <ossv-binscan> \
      --field tool MAP_TOOL --field old.path CGIF_ASAN_IMAGE --field new.path DECODE_ASAN_IMAGE

The diff original -> copy is `inputs/map.cgif2decode.asan.json.scrub.diff` (lines 2, 5 and 155; each removed span shown as
`<redacted>`). The image sha256 values in `old.sha256` / `new.sha256` are unchanged: the cgif asan image
(`7093581a...`) and decode's pinned `bin/fuzz_decode/fuzz_decode.asan` (`5973b768...`).

Identity: exitdrv.py (`provenance/startup-gen/A/exitdrv/exitdrv.py`, sha256
`663779408ab9ab9b4fec433db59086e8fd4764ea19e69dc8f1d42f843c3c8695`) was run twice in the same layout, once with the
original and once with the copy as `ELFMAP_A` (the binmatch files below; the pinned images and unstripped twins read from
the image path, sha256 `5973b768...` / `5d05689f...` and `4cb0a852...` / `6744989b...`). Every output is byte-identical:

| output | sha256 (original run = copy run) |
|---|---|
| `AE23.v` (-> `lib/A/AE23.v`) | `ebcddeaf8f37b568082c1272ae5b6c90b89e52ec00587c9bbb9b29c9bdc79cbd` |
| `AD1y.v` (-> `lib/A/AD1y.v`) | `17198b77590c00ac80a7f1c3fd6132f4e0c253b2a3c18366b6e595af3c0a04de` |
| `YE23.v` | `1520ab6f4101c325b2630d9cd1bf9c178b6ebe005fa741d66e80e995df15edb3` |
| `YD1y.v` | `5ef83a69f16381545591065c9a1c958afe80ed405e80e02af95839a13a2fb8ab` |
| stdout (numeral table + CONTROLS) | `dcc5099ce6d190f4a6959a5103064b748d62038042b82bd174261ee2d387b132` |

The run's outputs are as listed. The shipped `lib/A/AE23.v` and `lib/A/AD1y.v` now differ from them in lines 1 and 5
only: those two lines were rewritten by `exitdrv_header.py` `08ee0e66ac66` (`tools/exitdrv/c4a86fa61d82`, of record) in
commit `8529e243afd7`. Shipped sha256: `lib/A/AE23.v` `dce3579f18cef805b63d37e55a35fffade94e02faeb6536ef734b19288ba9742`,
`lib/A/AD1y.v` `709ab7c919a1c52454460a93c7b4ebe3eacf60029f95e2f1ec2116035e3cc62a` (and, from the same commit,
`lib/B/YE23.v` `401c846d5a2baaf224ac3397df69b3e1f92d6a0c6727a1ce9112cb52f19a3429`, `lib/B/YD1y.v`
`bb4b6649a4cfd651008fc82bbddcbf557e97725b9736b516b4e6494248eda2c0`: `../startup-B/README.md`). With the run output
as ORIG, `python3 exitdrv_header.py --check <run output> <shipped> --record provenance/evidence/startup-A/exitdrv/EXITDRV.md`
returns 0 for each: "check passed: ... = this version's header + 143137 body bytes" (AE23.v) and "+ 24568 body
bytes" (AD1y.v).

`lib/B/YE23.v` and `lib/B/YD1y.v` are not taken from this run: they were edited by hand after the tool ran.

## exitdrv/: the record the AD1y / AE23 headers cite

`lib/A/AD1y.v` and `lib/A/AE23.v` say in header line 5 that every numeral is named in
`provenance/evidence/startup-A/exitdrv/EXITDRV.md`, this slice's `exitdrv/EXITDRV.md`. Until `8529e243afd7` they cited
`provenance/startup-gen/A/exitdrv/EXITDRV.md`, a file of the working directory, which the shipped tree does not hold.
`exitdrv/` holds that record and the four run outputs that were beside it, copied from
`provenance/startup-gen/A/exitdrv/` at `fadeeb148437`: `ae37data.af0m-run4.out` and `ae37data.af0m-run5.out` byte for
byte; `EXITDRV.md`, `exitdrv.run2.out` and the drvivs gate output (shipped as `gate.drvivs.txt`, a name with no lane
name in it) as token copies, with a named token where the original names a host path, a worker, an internal tool, a
lane, or a path into a worker's own work directory (74 spans, no number in any). `exitdrv/COPY.md` says what each
token stands for, gives the file sha256 of each file's original,
and cites the verbatim originals in the internal records ref; `exitdrv/copycheck.py` proves the copies from the
originals in git (`python3 exitdrv/copycheck.py <hub clone> --scanner <scanner of record>`); `exitdrv/SHA256SUMS` lists
the directory. The writers (exitdrv.py, ae37data.py, drvivs.py) stay in the working directory.

`exitdrv/README.md` says that the same record covers both images, and states the record's one erratum, for image B
(`../startup-B/README.md`, "exitdrv/"): record row DEC 0x5f9920 -> 0x5f49e0 (buf, 8) for image B is WRONG; the
shipped YE23 uses STDOUT_BUFA = 0x5f49e8 (lib/B/YE3m.v:34, since b5a5f994474f), and the B pin holds 0x5f49e8 at
__stdout_FILE+0x58 (measured by the command in `exitdrv/README.md`). The row's image-A value, 0x5f4468, is what the A
pin holds there. The copies keep the row as the source has it. Since `8529e243afd7` (header-only rewrite, see the
run's outputs above) the 4 lib headers cite the record here and in `../startup-B/exitdrv/`; before, they cited the old
record locations (`lib/A`: the prover-only working directory; `lib/B`: the start-up writer's work directory).

## Files

What each file is, where no other text of this slice says it (the file list with the sha256 of every file is in
`provenance/evidence/MANIFEST.md`):

- `inputs/binmatch.cgif.asan.json`: `BINMATCH['A']` of `provenance/startup-gen/A/exitdrv/exitdrv.py` (a work-tree path
  in the tool; the committed copy is this file): the identical cgif-asan functions that move side-A code pcs; with
  `ELFMAP_A` it regenerates `lib/A/AE23.v` and `lib/A/AD1y.v`
- `inputs/binmatch.cgif.asan-ubsan.json`: `BINMATCH['B']` of `provenance/startup-gen/A/exitdrv/exitdrv.py` (a work-tree
  path in the tool; the committed copy is this file): loaded on every run (side-B code map); needed to regenerate
  `lib/A/AE23.v` and `lib/A/AD1y.v`
- `inputs/atable.py`: `ATABLE` of `provenance/startup-gen/A/prep.sh` (the frozen atable emitter; reads the pinned image,
  its unstripped twin and, for the cgif control, cgif's `A/AB1w.v` at `c8557374ad2e`): writes the body of
  `lib/A/AB12.v`, which `provenance/startup-gen/A/run.py` heads
- `inputs/map.cgif2decode.asan.json`: `ELFMAP_A` of `provenance/startup-gen/A/exitdrv/exitdrv.py` (a work-tree path in
  the tool; the committed copy is this file), the CLEANED COPY of the original (see "Cleaned copy" above): the asan cgif
  -> decode data runs that move side-A data addresses; with the two binmatch files it regenerates `lib/A/AE23.v` and
  `lib/A/AD1y.v`
- `inputs/scrub_input.py`: the scrub writer: replaces named spans with tokens, writes the copy and its redacted diff,
  and refuses its own output when the scanner reports any hit in either or a removed span remains

The files of `exitdrv/` are described in `exitdrv/COPY.md` (each file, its original and its spans) and
`exitdrv/README.md`.
