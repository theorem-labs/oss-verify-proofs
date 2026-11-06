# libdiginet/fuzz_transport, image A: the start-up layer (lib/A), how it was made and how to remake it

rule 24: no function proved
proves no function (kind: start-up data layer: generated facts files, no walk)

The 19 files of `lib/A` below are generated start-up DATA: the collected hand-off states, the start-up plan, the tables
and the certificate's facts. No file here proves a function; the tools move numerals, read the pinned image's bytes
and gate what they wrote.

## What was generated

| file | step | sha256 |
|---|---|---|
| lib/A/AB01.v | col | a204cb2896218acc5c266fb0beda6877eb7bed42c8e786bb319772d6f6b50522 |
| lib/A/AB03.v | col | 729a5325dbb5fffd51acf16bc2485cae624dedbbdd7589411f80cd7f75ecb035 |
| lib/A/AB05.v | col | 9d0e858b9a9a730ad54aba73fd3f235967fb60c339a84e1b03b847baf1f856c0 |
| lib/A/AB12.v | start | 15cef867238aaab3af46dd0fab0d533370c7861a06ac378b5fc2eea8a233b6f6 |
| lib/A/AB13.v | gen | 1fb1a963643891c7e57656712b71bc85b33e6d6357e49a46f8b88e9a14f35bc0 |
| lib/A/AB1h.v | gen | e50529dd0e93cdf150341120e8601985c62bbd12af8bc5f20161adf4292cad48 |
| lib/A/AB1k.v | gen | 5b0a8e8688924967f6c900b985b24a007d8b6e8576dfe5827949d5b12d280638 |
| lib/A/AB1l.v | col | 26df9cd85e924e95ec62bb19dcf688de33dc608b44a41e731d61f6b8be7a6b86 |
| lib/A/AB1m.v | col | 21f12acd8c61e56483bbbb159d837480e7a39c3240ec60cdd2c0461b90de0c41 |
| lib/A/AB1v.v | gen | 2de7f12d30d92bf73bf531d56bfd7bd25bfabcb4531fd6bdfec35f07f792631d |
| lib/A/ACej.v | acej | 8d2386fce4a87856293b84668753c86af357d316e02b4a5a404dcdc3dc57267f |
| lib/A/AD1k.v | start | 31b55909ff5e4819e699065118ba733a6fc81dedbe02244878c68ed0d19f6fd9 |
| lib/A/AD1y.v | exitdrv | b4c78341e1dca05400742056752db7ef751b7475b299dfe45ce1016bc431bdba |
| lib/A/AD2i.v | start | 621a1b4e7cb277d66c40887b31a1fd75d259353c7dbf7e451f57275b35f9c51a |
| lib/A/AD2j.v | start | f32f53f83a52adddaded3dca24ac3c2bfd63c17ce5573671a74a334111bfebfd |
| lib/A/AE23.v | exitdrv | d05bca94aa65317dbc2e32ce6e13f479ae92358fb6eba0d503dec35c68093491 |
| lib/A/AE37.v | start | 8cdacdbdec565b727c71a6f957b1d5b88c63c9499dbb2a2db265a34eb8e271d8 |
| lib/A/AE3i.v | start | 02b2b0111bd4ae845d1ad5b82dcfd6f2203610b804f952bd247f2cdac7ad46c9 |
| lib/A/AF0m.v | start | 5dfdd0e65356936fa0e4a30fc0ccd17c084886e917940512c4d95b181b9105c1 |

They follow the layout and the names of libreac/fuzz_decode's released start-up files of the same names. Every module
the 19 files Require is in this unit's lib (`missing_requires.py (sha256 d2dbfb9ba11a; internal record)`: 19 files
read, 118 unit modules present, 0 missing), and the kit's build gate Gp builds the 19 and every lib/A file that
Requires one of them.

## The kit is an internal record

This tree ships four files: this README, `regen.sh`, `site.env.example` and `KIT-MANIFEST`. The kit that made the 19 files
and remakes them (its scripts, gates, tables, the record of its generic fixes, the CONTROL files that quote each
step's controls, and the records of its runs) is not here: it is an internal record, on the internal records ref,
file for file. `KIT-MANIFEST` names every kit file (401) by its records path, its sha256, its mode and its path in the
kit. A record file is cited by its content only: `<name> (sha256 <first 12 hex digits>; internal record)`, for
example the kit's own driver `regen.sh (sha256 c7dd67f9a008; internal record)`; `KIT-MANIFEST` gives the full sha256 of
each.

At the release this directory moved from provenance/startup-gen/A/ to provenance/evidence/startup-gen/A/ (the
release's lint allows provenance/evidence/, not provenance/startup-gen/), and its kit list from `MANIFEST` to
`KIT-MANIFEST` (the evidence index's checker reads every file named MANIFEST under provenance/evidence/ as an
index of that directory). The list's bytes are unchanged. `regen.sh` changed in two places only: the unit
directory is one level further up, and the list's name. The runs this README cites ran it at the old place, with
the old name.

The 19 files cite every record the same way, never by a path: AD1y and AE23 their writer and their numeral table
(`exitdrv.py (sha256 64187f0d3029; internal record)`, `numerals.md (sha256 4f09954a8fdd; internal record)`: every
numeral of AD1y and AE23, with its cgif value and its source), ACej its assembler, its rows file and its checker
(`acej.py (sha256 5db4ca1babf0; internal record)`, `libdiginet__fuzz_transport.rows (sha256 3824dd4d0ddb; internal
record)`, `xcheck_pcs.py (sha256 ff6151d17c42; internal record)`), AE37 the rule its numerals follow (`ae37data.py
(sha256 f16b8b1d6935; internal record)`), and AB05 the two tools whose names the release scanner refuses as `a Theorem
Labs tool (sha256 2d846496640d; internal record)` and `a Theorem Labs tool (sha256 4d51ec1c0069; internal record)`.
Every repository path a comment of the 19 names opens in the shipped tree (the kit's gate Go, with no kit fallback).

## Remaking the layer after a re-pin

One command. Give the new pinned files and a fresh output directory; every per-unit value is derived from them.

    SITE=<this host's site file, outside the tree; see site.env.example> \
    TARGET=libdiginet/fuzz_transport \
    IMAGE=<dir>/libdiginet/result/bin/fuzz_transport/fuzz_transport.asan \
    TWIN=<dir>/libdiginet/unstripped/fuzz_transport/fuzz_transport.asan \
    UBSAN=<dir>/libdiginet/result/bin/fuzz_transport/fuzz_transport.asan-ubsan \
    BIN_REF=<the commit whose index/binaries.tsv and projects/libdiginet/fuzz_transport/ pin the new images> \
    OUT=<a fresh directory on local disk> MONTH=<YYYY-MM> \
      bash regen.sh

The `drivers` step first fetches every `KIT-MANIFEST` row from the internal records ref (SITE: `RECORDS_REPO`,
`RECORDS_REF`) into `$WORK/kit` and refuses the run when a file is missing or its sha256 is not the one `KIT-MANIFEST`
gives, whatever commit it came from; two controls show it (a `KIT-MANIFEST` with one sha256 digit changed, and one naming a
records path the ref does not hold, are each refused with nothing fetched). The kit then runs from `$WORK/kit`, with
the unit's `lib/` beside it: the 19 files go to this unit's `lib/A` (or `LIB`). A later run of single steps
(`bash regen.sh col`) reuses the kit that a `drivers` step of the same `WORK` fetched for this `KIT-MANIFEST`; the steps
after it read what it wrote.

### The pinned build: the layout every step reads

The `pins` step refuses, before anything runs, a pin set laid out otherwise (`derive/pin_layout.py (sha256
4ce1f50e9e62; internal record)` names what it found and the line below it expected):

    <dir>/libdiginet/result/bin/fuzz_transport/fuzz_transport.asan          IMAGE
    <dir>/libdiginet/result/bin/fuzz_transport/fuzz_transport.asan-ubsan    UBSAN
    <dir>/libdiginet/unstripped/fuzz_transport/fuzz_transport.asan          TWIN (names only from it)
    <dir>/libdiginet/result/SHA256SUMS                                      optional: the build's own sums

(`<dir>/libdiginet/bin` and `<dir>/libdiginet/unstripped` are symlinks to `result/bin` and `result/unstripped`, as in
the pipeline's own tree; IMAGE and TWIN may be given through them, or straight under `result/`.) The `libdiginet/`
component is required: the acej header names each file by its path below it, so give IMAGE under `result/bin/` and
TWIN through `unstripped/`, as the runs of record did (a TWIN under `result/unstripped/` changes that one comment line
of ACej). Copy a build's whole `result/` directory with its two links; do not flatten it.

THE PINS OF RECORD are BIN_REF's own `index/binaries.tsv`: IMAGE and UBSAN must equal its rows, and every later step
reads the unit's rows there, never a written value. The index has no row for the unstripped TWIN: its authority is its
own bytes (`derive/twin_check.py (sha256 018e02a265db; internal record)`: every PT_LOAD and `.text` equal to the pinned
IMAGE's). A `result/SHA256SUMS` is never the authority: if present it must agree with the index and with the files.
No commit is written in this tree: the kit pins the repository commits it reads (the donors' released libs, the
control units' pins, the image-A core of record) in its own regen.sh's defaults block, and a re-pin changes BIN_REF and
the three paths only.

What the steps need: `col` and gate Gp need the build VM, a cgif donor worktree built once so its workspace exists,
and the unit's own build workspace on the new base (SITE: `VM`, `DONOR_WT`, `UNIT_WS`, `GP_WS`, `GP_WT`); the rest runs
on local disk. A run that reuses the collector's four build logs (`REUSE_PASS1`, `REUSE_PROBEF`, `REUSE_PASS2`,
`REUSE_CERT`, each `<log>:<sha256>`) runs nothing on the VM. `GATE_VM=` (set and empty) runs every gate but the two
that need the VM (Gp is then WAITING, Gm's m4 NOT RUN), so the `gates` step then FAILS, naming those two.

## The steps and the tool versions of each

`regen.sh` runs, in order, each step after its own control, and exits non-zero on the first failed control or step;
its last line is then `RESULT: steps ... FAIL: <the step and why>`. The `gates` step writes one row per gate (rc,
result, control result: `gates/logs/table.md` of the run) and then judges every row and every control by the pass
rules (`pass_rules.tsv (sha256 b8c11ed219e2; internal record)`: per gate, the rc values that mean PASS, each with its
reason; codeptr passes on rc 2 and port_addr_check on rc 4 only under the conditions their own docstrings give). It
FAILS when any gate or control fails its rule or did not run, naming each one (`GATES FAILED: ...`). The kit files
are cited by sha256 (all of them in `KIT-MANIFEST`); the other tools are files the kit fetches by sha256 before any step
reads them: `vendor.tsv (sha256 ba16f698863c; internal record)` names 82 registered tool files, and `records.tsv
(sha256 e2a3784d271e; internal record)` the tool copies registered nowhere and the collector control's pinned inputs.
No diff is applied to a shared driver: the decode start-up writer took every generic fix of this unit into their own
driver set, which the `drivers` step checks file for file (each fix with its controls in `PATCHES.md (sha256
d2cb81726094; internal record)`). Every start-up tool runs through the start-up set of record,
`startup-set-2026-10-30d.tsv (sha256 bde970239064)`.

| step | writes | kit files (internal record) | other tools |
|---|---|---|---|
| drivers | - | `regen.sh` c7dd67f9a008, `driver_check.py` d0d0551288f7, `fetch_vendor.py` 5b6b9ed1d902, `literal_check.py` 4ab6401d8434 | - |
| pins | - | `pin_layout.py` 4ce1f50e9e62, `twin_check.py` 018e02a265db | - |
| derive | the core's pin rows | `core_pins.py` 4a08f996db8e | - |
| core | the relocated core bases and their ELF map | `core/run.sh` 8826adc6d799, `run_core.sh` eb00a8efd514 | `port_core.py (sha256 0e4e065eab9f; internal record)`, the ELF map tool (sha256 4d51ec1c0069; internal record) |
| col | AB01 AB03 AB05 AB1l AB1m | `run_col.sh` 6b5b7a80e2a3, `emit_col.py` f87e5fdf20d0, `colhelp.py` 8f71bf230d5f | the remap tool (sha256 2d846496640d; internal record), `colrun.py` 59778df6f00b, `replyscratch.py` cf47e327b300, `itabranges.py` 6bd6b8036747, `rvelf.py` 23152d9ca11c (each internal record), the set's `ColA.v` d198e5a14160 |
| gen | AB13 AB1h AB1k AB1v | `gen/run.sh` 9ee922f62994, `run.py` 91d0af289d42, `gen.py` 32cf4c01c088, `codeptr_gate.py` 7fe9facf18fd | the start-up set |
| acej | ACej | `acej_conf.py` 5a91fad8249d, `derive/run.sh` be9feb84d4e5, `acej/run.sh` 0007efd75f41, `rows.py` c4efb5e00b75, `xcheck_pcs.py` ff6151d17c42 | `acej.py` 5db4ca1babf0, `gen_traces.py` a78026af1ae2 (each internal record) |
| exitdrv | AE23 AD1y | `exitdrv_tables.py` ee531e1a08fd, `exitdrv.py` 64187f0d3029, `exitdrv/run.sh` 83d71b4604dd | - |
| start | AF0m AB12 AE3i AE37 AD2i AD2j AD1k | `run_all.sh` e632261a8599, `ae37gen.py` 9e99e6da19ce | `prep_owned.py` 9d548aaca227, `imglib.py` b97cae013d52, `ae37data.py` f16b8b1d6935 (each internal record), the start-up set |
| place | the 19 into lib/A | `place.py` cb605b020b7c | - |
| gates | the gate log, its table and its verdict | `run_gates.sh` 15591d40870f, `verdict.py` 5dcd2e2f112f, `pass_rules.tsv` b8c11ed219e2, `t3gates.py` 4a24c186f9f7, `paths.py` f2d9ffd43596, `hygiene.py` 3b2a3a684d1a, `build_gate.sh` b867cbf3afcf | `port_addr_check.py` efa19b81e92b, `decscan.py` d36f0a6ddc6c, `elfdiff` 3f1a4862903f (each internal record), `global_settings.py` 439f8e3bd463, `kimg_overlap` 5db341e3cd62 / acfd7418176d |
| record | the run's records, for the internal records ref | `record.py` aca4f9ff7bd5, `records_ref.py` 13e170cb5cae, `kit_manifest.py` a8419e0f540f | - |

Methods of record: `core` is libdiginet/fuzz_decode's core driver (port_core's dry run) with the unit's lists; `start`
is libdiginet/fuzz_decode's start chain; `col` is reac-repacer/fuzz_uci's collector made target-parametric; `gen` is
fuzz_uci's generator in fuzz_frame's libdiginet port; `acej` is libdiginet/fuzz_decode's acej driver; `exitdrv` is
libdiginet/fuzz_decode's exitdrv driver with the unit's three table rows derived from the image; the gates are
fuzz_uci image B's gate set plus fuzz_frame's image-A gates. The `drivers` step checks every shared driver file of the
kit against the decode start-up writer's commit of record, byte for byte; no shared driver carries a diff.

## The runs of record

- The clean end-to-end run of the kit before the comment fix, with the real collector on the build VM, said
  `RESULT: steps drivers pins derive core col gen acej exitdrv start place gates record PASS` (its log
  `regen.20261031T111926Z.log (sha256 91e9ad08df56; internal record)`), because its gates step did not yet judge the
  gates. Its 19 files equal that day's lib/A byte for byte, apart from the collector-log sha256 that AB01, AB1m and AF0m
  cite (a real collector run writes new log bytes; lib/A keeps the citations of the logs it was made from). Judged by
  the pass rules from its gate logs (`verdict.out (sha256 a9531eb03850; internal record)`) it FAILS on one gate: Go
  (cited paths) rc 1, `ACej.v:17: the comment cites provenance/startup-gen/A/acej/acej.py, which does not resolve`;
  its other 18 gates and 41 control results pass their rules.
- The comment fix of AB05, ACej, AD1y, AE23 and AE37 (comment lines only; the other 14 files and every line of code
  unchanged, AF0m included) was written by this kit's own steps, with the collector's four build logs reused
  (`pass1.log (sha256 7e289bbd1a71; internal record)`, `probef.log (sha256 999fafcb714f; internal record)`, `pass2.log
  (sha256 d96720c54ad7; internal record)`, `cert.log (sha256 755cd85c89d0; internal record)`) and `GATE_VM=`
  (`regen.20261031T161245Z.log (sha256 4324a815b6b1; internal record)`), then, on the decode start-up writer's current
  driver set, `RESULT: steps drivers exitdrv record PASS` with AD1y and AE23 byte-equal
  (`regen.20261031T164401Z.log (sha256 26586bd12285; internal record)`). Those runs left Gp WAITING and Gm's m4 NOT RUN.
- The gates step on these files, with the pass rules, the collector's logs reused and the build VM given (Gp's core:
  the image-A core's integration line), then the record step: `RESULT: steps gates record PASS`
  (`regen.20261031T173339Z.log (sha256 979059741471; internal record)`), its verdict `GATES PASS: all 19 rows and 41
  control results pass their rule (gates/pass_rules.tsv)` (`verdict.out (sha256 c67dc2cf040d; internal record)`): Gp
  `PASS: all 371 target(s) build`, m4 stmtcheck rc 0, Go 19 files, 12 cited paths, 0 that do not resolve. The
  verdict's control: the same step, gate Go alone, on a copy of the outputs whose AD1y.v holds a planted comment citing
  a path that does not exist, exits 1 with `RESULT: steps gates FAIL: ... GATES FAILED: 1 item(s): row o (o cited
  paths) (rc 1: ...)` (`regen.20261031T173313Z.log (sha256 f3d7b819abed; internal record)`).
- The end-to-end run of record, exactly as this README says, on this tree with the kit before the last re-pin: a fresh
  output directory, the kit fetched by `KIT-MANIFEST`, the real collector on the build VM, Gp included, 17:54:58Z to
  20:44:15Z: `RESULT: steps drivers pins derive core col gen acej exitdrv start place gates record PASS` and `GATES
  PASS: all 19 rows and 41 control results pass their rule` (`regen.20261031T175531Z.log (sha256 6eaecd811c10;
  internal record)`; Gp `PASS: all 371 target(s) build`). Its 19 files equal lib/A: 16 byte for byte, and AB01, AF0m
  and AB1m apart from the collector-log sha256 they cite (`compare.out (sha256 347ac89e72ea; internal record)`).
- The kit re-pinned to the decode start-up writer's driver set that took the last fix (no diff left on any shared
  driver): `RESULT: steps drivers start exitdrv PASS` with the collector's logs reused (`regen.20261031T204823Z.log
  (sha256 1b47c97615b1; internal record)`); the seven start files and AD1y, AE23 equal the run of record's (AF0m
  apart from the collector-log sha256 it cites; it equals lib/A).

## The controls

Every step reproduces a file that already exists before it writes the unit's: the collector reproduces fuzz_uci's five
committed files from fuzz_uci's pinned inputs; `gen` reproduces cgif's four released files on cgif's image and
fuzz_frame's four committed files; `acej` re-emits cgif's released ACej / YCej byte for byte and reproduces
fuzz_grant's released universe; `exitdrv` reproduces the donor's and fuzz_uci's reference copies and is checked by
seven planted values that must each be caught; the gates run their cgif control before the unit's run. Each step's
CONTROL file quotes its command, its control lines and its gate lines (`start/CONTROL.md` 291e73c2d1de,
`col/CONTROL.md` f0a905a4ce0c, `gen/CONTROL.md` ae12c93cb0ae, `acej/CONTROL.md` ee98f85644bd, `exitdrv/CONTROL.md`
c993d3939181, `gates/CONTROL.md` 53e09a50d439, `derive/CONTROL.md` e63eeef3d520; each internal record).

## Host locations and names

No file of this tree names a host location, a workspace, a repository branch, a tool repository or a worker. Each
host location and workspace is a variable of the SITE file, an env file outside the tree (`site.env.example` lists
every one with what it is); `regen.sh` refuses a SITE that leaves one unset or sets one it does not know, naming it,
and its `drivers` step shows a SITE without `RECORDS_REF` refused. The same step runs the release scanner of record
(SITE: `SCANNER`; `regen.sh` pins it by the sha256 of its directory's SHA256SUMS) over this tree, after the scanner's
own positive control, and requires no uncleared hit; then a copy of this tree whose README names a worker of the
roster (SITE: `ROSTER`) must be flagged.
