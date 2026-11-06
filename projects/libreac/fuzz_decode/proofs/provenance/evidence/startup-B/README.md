This README replaces the slice MANIFEST.md (2026-10-31); the file list and sha256 of every file are in provenance/evidence/MANIFEST.md.

# provenance/evidence/startup-B: inputs of the image-B start-up writers, and the exit-driver record

Each input under `inputs/` is read by a writer of record under `provenance/startup-gen/B/` and was not in git before.
The bytes are the bytes that writer read, except two cleaned copies (below), which only `inputs/scrub_input.py` wrote; the
pass-2 copy is kept in two parts that `cat` joins (below).

`lib/B/YF0m.v` (af0m, `provenance/startup-gen/B/run_gen2.sh`) stays unchanged: the 26 `--add` arguments of the af0m run
that wrote it have no recorded order, so it cannot be regenerated. The pass-2 log and the nm listing that run also read
are now here.

`lib/B/YB12.v` (atable, `provenance/startup-gen/B/run_gen.sh` step 2 with `mk_hdr12.py`, then step 3) stays unchanged: the
run (control `YB12: EQUAL` on cgif; `gen/YB12.v` `5df6a75e1044b150fe2eeb8208d18143ab189eb9c22145e9eb693715ddd3267b`,
`lib-B/YB12.v` `569fc9ef5bb65daa9622b78b00a102fcbd1dc1f84529707207c356fdf692b3cf`) differs from the committed file in line 21
only: the tool writes `Definition TFIB_TEXT_N : nat := 106159.`, the file has `106303`, the declared one-line change of
commit `3f139df4e82a` (`provenance/startup-gen/B/GATES-decB.md`, "TFIB_TEXT_N 106303 earned"). Line 4, which `mk_hdr12.py`
writes, is the same in both, so it keeps the image's host directory name: owed (a defect of `mk_hdr12.py`'s text).

`lib/B/YD1y.v` and `lib/B/YE23.v` (exitdrv, `provenance/startup-gen/A/exitdrv/exitdrv.py` `663779408ab9`, which writes both
sides; run as `../startup-A/README.md` states, outputs `YD1y.v` `5ef83a69f163...` and `YE23.v` `1520ab6f4101...`) are
not regenerated: the run differs from them beyond the header. Each differing line of the files as committed before
`8529e243afd7`, with the commit that wrote it (blame at `9841b5ca99b6`, the tree commit `b7730c7823ac` took them from by
path):

- `YD1y.v` 1 and 5 (header), 16-17 (Require lines split to lib.B), 23 and 42 (`DRV_IVS` / `DRVW_cases`: the third window
  cut at `0x5d39c0..0x5d39c3`), 69 (`TfibSyms`): `b9d6a97ebe5c`.
- `YE23.v` 1 and 5 (header), 23 (Require lib.B), 451 and 453 (`TfibSyms`): `b9d6a97ebe5c`; 358-359, 363-364, 480, 485, 535,
  568, 573, 623, 656, 661, 674, 713, 804, 835-837, 1033-1035, 1231-1233, 1431-1433 (image B's named constants for donor
  values, `def_eq`): `b5a5f994474f`; 487, 575, 663 (tactic repair): `aefc59507a23`.

Since `469e6875cc0a` exitdrv.py's header lines 1 and 5 name no worker. In the shipped files they name none since commit
`8529e243afd7`: only lines 1 and 5 were rewritten there, every other byte kept, by `exitdrv_header.py`
`08ee0e66ac66` (`tools/exitdrv/c4a86fa61d82`, of record), from the files as committed before it (`lib/B/YD1y.v`
`b9a96875fb935460ea98cd36736124e2a55d08364547c4050d0f54ba008b3fd3`, `lib/B/YE23.v`
`cc18ca5b91f3b0c8751a926077c04aab927efb22e6966cd747974fd7fca32b1f`). Shipped sha256: `lib/B/YD1y.v`
`bb4b6649a4cfd651008fc82bbddcbf557e97725b9736b516b4e6494248eda2c0`, `lib/B/YE23.v`
`401c846d5a2baaf224ac3397df69b3e1f92d6a0c6727a1ce9112cb52f19a3429`. With the file as committed before it as ORIG,
`python3 exitdrv_header.py --check <committed before> <shipped> --record provenance/evidence/startup-B/exitdrv/EXITDRV.md`
returns 0 for each: "check passed: ... = this version's header + 24896 body bytes" (YD1y.v) and "+ 142773 body bytes"
(YE23.v).

## Cleaned copies

The collector logs `runs/B/pass2b.log` (original sha256 `437ed1cfc104428d7d6506a8c04ce705ab43ebd260883cad635cf259a7cac067`)
and `runs/B/pass1.log` (original sha256 `3ed1def61a5609898682fef1921977acc2756e8c9cd58ca4844766b855a22e1b`) fail the scanner
on line 1 only: its `rjob:` field names an internal build job. The committed copies replace that field with the token `RJOB`
and copy every other byte:

    python3 inputs/scrub_input.py text ORIGINAL pass2b.log \
      --sha256 437ed1cfc104428d7d6506a8c04ce705ab43ebd260883cad635cf259a7cac067 --scanner <ossv-binscan> --line-field 1 'rjob: ' RJOB
    python3 inputs/scrub_input.py text ORIGINAL inputs/pass1.log \
      --sha256 3ed1def61a5609898682fef1921977acc2756e8c9cd58ca4844766b855a22e1b --scanner <ossv-binscan> --line-field 1 'rjob: ' RJOB

The cleaned pass-2 copy (6739063 bytes) is over the lint cap of 5 MiB (`tools/oft/lint.py` `MAX_BYTES`, 5242880 bytes),
so it is kept as two plain-text parts, cut at the end of its line 306 (owner ruling 2026-10-31). `inputs/split_pass2b.py`
wrote them; it refuses, and writes nothing, unless the sha256 of the two parts together is that of the copy:

    python3 inputs/split_pass2b.py pass2b.log inputs/pass2b.log.part1 inputs/pass2b.log.part2

`inputs/pass2b.log.part1` is lines 1-306 (3931204 bytes), `inputs/pass2b.log.part2` lines 307-311 (2807859 bytes).
`cat inputs/pass2b.log.part1 inputs/pass2b.log.part2 > pass2b.log` gives the copy back, sha256
`5592b5596ceccd1e4c58af1bd0376fbc48f9bacbaa772b8869a3fb31607a7dbc`: the bytes `provenance/startup-gen/B/run_gen.sh` reads as
`in/runB/pass2b.log`.

The diffs original -> copy are `inputs/pass2b.log.scrub.diff` (its copy: the two parts joined) and
`inputs/pass1.log.scrub.diff` (line 1 each; the removed span shown as `<redacted>`). `inputs/scrub_input.py` is the same
file as `../startup-A/inputs/scrub_input.py`.

Identity: `provenance/startup-gen/B/run_gen.sh` steps 1 (YB01: hsform `hs`; YB03: hsform `js`) and 3 (reqfix) for those
two files ran four times, with hsform.py `b1d794ec6122` and its af0m.py `98d4aadc6ed2` / pins.py `88e69cd871f8` (the tool
files of the released run), reqfix.py `81bc7dbf9243`, the donor `YB01.v` / `YB03.v` at `c8557374ad2e`, the nm listing
below, and the pinned image `5d05689f...` with its unstripped twin `6744989b...` read from the image path (about 4.1 GB for
`hs`). The released run's `--modified` texts with the original logs give its known answers (`gen/YB01.v` `2714ad3e37f7`,
`gen/YB03.v` `05d8ddd12043`) and, after reqfix, the released `lib/B/YB01.v` / `lib/B/YB03.v` byte for byte. With each of
the first two `--modified` texts, every output from the copies is byte-identical to the output from the originals. The
last column is the run from the copies with the `--modified` texts of the current `run_gen.sh`, which name the pinned
original and not the image's host directory. With the texts "without the worker name" the same run gives that column's
`lib-B` files byte for byte, and the current `lib-B` files differ from those in line 4 only:

| output | released `--modified` text: original run = copy run | `--modified` text without the worker name: original run = copy run | current `--modified` text: copy run |
|---|---|---|---|
| `gen/YB01.v` | `2714ad3e37f7b267feb1d5b6c9d02a50ea4235b9f930449d3411ad192dce170b` | `96e22b5a888e019107c958501c066a62af23067784f3d8e409c963f8151773a3` | `7ed4173060e1d00b80e673792e27ff285a1b7f8c2baeacf0b7d7bdf4526501f9` |
| `gen/YB03.v` | `05d8ddd120433f0552d8c6159a35b2afa351c4df62779694173702f794a8310b` | `675d377a1927f89206b1e073580695d1fdcad6d07a922de25ff55f1a1dddbabc` | `c552c649c86297e3f714a1971afbf44e9a5bd8ec76a03544768a04bc3e562a3c` |
| `lib-B/YB01.v` | `34b88b003c3f7c3f2272f0a784ce577345e599fe8c5875af55bcca07b99d86e6` (the released file) | `e2ee98f833c4bd17fc04f102f236243d0c1b01ef70bd3d6b045d118a396fc0e9` | `3008225332af853436a553107285a3860b51f9497ad5ad3bf7b1a36fb5a31b4d` (-> `lib/B/YB01.v`) |
| `lib-B/YB03.v` | `43f8f556a24f8b524dfbdd93097448981a7b58ae21cf11db6f652094d79f6bc5` (the released file) | `dcd47b98a9dbbf56da816cd706cb2f5851120c8ff8ddbe2ccf5456bc5e558899` | `574fc0acc2bb0635ffc27a9c0de4bc7b17315d578eff647b210a6e726d954c77` (-> `lib/B/YB03.v`) |
| `pass2b.log.hs.json` (hsform's report) | `ebd8914644cdc769cbd98137a7fa674d903dbb3c57b6504673cd742ea85707ba` | `ebd8914644cdc769cbd98137a7fa674d903dbb3c57b6504673cd742ea85707ba` | `ebd8914644cdc769cbd98137a7fa674d903dbb3c57b6504673cd742ea85707ba` |
| hsform `hs` stdout | `712b77c7fc26807f4467cacbb69cf023bf2ab34adca02d211c2b723fbcdbf003` | `712b77c7fc26807f4467cacbb69cf023bf2ab34adca02d211c2b723fbcdbf003` | `712b77c7fc26807f4467cacbb69cf023bf2ab34adca02d211c2b723fbcdbf003` |
| hsform `js` stdout | `7e9519a2418a850e1e56a43abc256cf514ca23ae94d258e1ac56d60a281071f9` | `7e9519a2418a850e1e56a43abc256cf514ca23ae94d258e1ac56d60a281071f9` | `7e9519a2418a850e1e56a43abc256cf514ca23ae94d258e1ac56d60a281071f9` |

## lib/B/YB13.v: its writer runB13.py

The writer of record of `lib/B/YB13.v`, runB13.py (sha256 `29041197f9c84177ac61f325c28898d026dc35924c6aa0819a513a226b20f165`,
`gen13/runB13.py` in `provenance/startup-gen/B/SHA256.lib-B.txt`), was not in git. Its bytes hold host paths and worker
names, so it is committed as `provenance/startup-gen/B/yb13/runB13.py`, where `yb13/run_yb13.sh` runs it, with these edits
only: it reads the three images from the work dir (`img/`, which `run_yb13.sh` fills and checks by sha256), not from host
paths, and its pin checks print the file name only; it imports gen.py from `provenance/startup-gen/A/` (sha256
`6ccd419c977f`, checked; unchanged), not from its own directory; its docstring and the YB13 notice name no worker, and the
target is "the pinned original"; its `Read from` line has the pins.py form, without the image's host directory.
`run_yb13.sh` takes the donor text from the checkout, the images from `$IMG` / `$TWIN` / `$CG`, and gives reqfix
(`ad1k64/reqfix.py` `81bc7dbf9243`) the module names of `lib/B` / `lib/Reusable` at `5607400a019c`, as `run_gen.sh` step 3
does.

Identity: the original runB13.py, with only its cgif image path changed to a copy of the same bytes (`1c29845f...`), and
reqfix (with the run's own module lists and with the `5607400a019c` lists alike) give the previous `lib/B/YB13.v`
(`ca859c2d6df9f5381cc958b77e36f4f2161f340706feeae9c0d59bd02ce05d7c`) byte for byte. `run_yb13.sh` from an empty work dir:
all checks pass, `out/YB13.v` `d43c730f4909b33b7b1dbf5a5422bb5ed6c04349a4964193ba1eacf3aa22f257`, `lib-B/YB13.v`
`7d6117f61f3431cec16bc8d6358c0e0c40feb31d8e0b522bcb167187d64df299` (-> `lib/B/YB13.v`), which differs from the previous
file in lines 4 and 5 only.

    WORK=<empty work dir> IMG=<bin/fuzz_decode/fuzz_decode.asan-ubsan> TWIN=<its unstripped twin> \
      CG=<cgif_file_fuzzer.asan-ubsan> bash provenance/startup-gen/B/yb13/run_yb13.sh

## exitdrv/: the record the YD1y / YE23 headers cite

`lib/B/YD1y.v` and `lib/B/YE23.v` say in header line 5 that every numeral is named in
`provenance/evidence/startup-B/exitdrv/EXITDRV.md`, this slice's `exitdrv/EXITDRV.md`. Until `8529e243afd7` they cited
the record by its path in the start-up writer's work directory, never in git. That file is the record: its sha256
`337cd4a543e524427f97317c58e593077da71c65186ba04ddd41b09402f15c6f` is that of
`provenance/startup-gen/A/exitdrv/EXITDRV.md` at `fadeeb148437` (one record for both images); its section 0 lists
the run's `YD1y.v` / `YE23.v` by the sha256 of the `YD1y.v` / `YE23.v` beside it in the work directory, whose header
lines 1-5 were byte-equal to those of `lib/B/YD1y.v` / `lib/B/YE23.v` before `8529e243afd7`; and it names, as a hex
value, every numeral value of `lib/B/YD1y.v` (13) and `lib/B/YE23.v` (56) that cgif's `lib/YD1y.v` / `lib/YE23.v` at
`c8557374ad2e` does
not hold. `exitdrv/` holds it and the run's stdout `exitdrv.run2.out` as token copies, the same bytes as
`../startup-A/exitdrv/EXITDRV.md` and `../startup-A/exitdrv/exitdrv.run2.out` (73 spans: a host path, two worker
names, an internal tool and its kit, three lanes, and paths into the writer's own work directory; no number in any).
`exitdrv/COPY.md` gives the measurements, the tokens, the file sha256 of each file's original, and the verbatim
originals in the internal records ref; `exitdrv/copycheck.py` proves the copies from the originals in git
(`python3 exitdrv/copycheck.py <hub clone> --scanner <scanner of record>`); `exitdrv/SHA256SUMS` lists the directory.

Erratum (also in `exitdrv/README.md`, with the measuring command): record row DEC 0x5f9920 -> 0x5f49e0 (buf, 8) for
image B is WRONG; the shipped YE23 uses STDOUT_BUFA = 0x5f49e8 (lib/B/YE3m.v:34, since b5a5f994474f), and the B pin
holds 0x5f49e8 at __stdout_FILE+0x58 (measured: `exitdrv/README.md`'s command on the pin `5d05689fd5b1...` at
`0x9da00` prints `['0x5f49e8']`; on the A pin `5973b76807d8...` at `0x9d458` it prints `['0x5f4468']`, the row's A
value). The row is line 81 of `exitdrv/exitdrv.run2.out`; the copies keep it as the source has it. The shipped value's
derivation: `lib/B/YE3m.v:34` is `Definition STDOUT_BUFA : Z := 0x5f49e8.` (written by `3eb6dc398951`, the B core
relocation), and `b5a5f994474f` replaced YE23's unrelocated cgif values by B's named constants (its message: "YE23
held seven cgif values (... STDOUT_BUFA 6265120 ...) -> B's named constants (B: ... STDOUT_BUFA 0x5f49e8 ...)").

Since `8529e243afd7` (header-only rewrite, see "`lib/B/YD1y.v` and `lib/B/YE23.v`" above) the 4 lib headers cite the
record here and in `../startup-A/exitdrv/`; before, they cited the old record locations (`lib/B`: the record's path in
the start-up writer's work directory; `lib/A`: the prover-only working directory).

## Files

What each file is, where no other text of this slice says it (the file list with the sha256 of every file is in
`provenance/evidence/MANIFEST.md`):

- `inputs/decode.asan-ubsan.nm.txt`: `--names` (`in/decode.asan-ubsan.nm.txt`; the unstripped twin's `.symtab` in nm
  form) of `provenance/startup-gen/B/run_gen.sh` (hsform `hs` / `js`: `lib/B/YB01.v`, `lib/B/YB03.v`) and `run_gen2.sh`
  (af0m: `lib/B/YF0m.v`); also read by `run_gates.sh`, `run_gates2.sh` and `yb13/run_gates_yb13.sh`
- `inputs/pass2b.log.part1`, `inputs/pass2b.log.part2`: the CLEANED COPY of the collector's pass-2 log `runs/B/pass2b.log`
  in two parts (see "Cleaned copies" above): `cat inputs/pass2b.log.part1 inputs/pass2b.log.part2 > pass2b.log` gives
  sha256 `5592b5596cec...`, `in/runB/pass2b.log` of `provenance/startup-gen/B/run_gen.sh` (hsform `hs`: `lib/B/YB01.v`)
- `inputs/split_pass2b.py`: the script that wrote the two parts (see "Cleaned copies" above)
- `inputs/pass1.log`: the CLEANED COPY of the collector's pass-1 log `runs/B/pass1.log` (see "Cleaned copies" above):
  `in/runB/pass1.log` of `provenance/startup-gen/B/run_gen.sh` (hsform `js`: `lib/B/YB03.v`)

The files of `exitdrv/` are described in `exitdrv/COPY.md` (each file, its original and its spans) and
`exitdrv/README.md`.
