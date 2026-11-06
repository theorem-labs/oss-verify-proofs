# libdiginet/fuzz_transport, image B: the start-up layer (lib/B), how it was made and how to remake it

rule 24: no function proved
proves no function (kind: start-up data layer: generated facts files, no walk)

The 19 files of `lib/B` below are generated start-up DATA for image B (the asan-ubsan build): the collected hand-off
states, the start-up plan, the tables and the certificate's facts. No file here proves a function; the tools move
numerals, read the pinned image's bytes and gate what they wrote.

## What was generated

| file | step | sha256 |
|---|---|---|
| lib/B/YB01.v | collector | f6913544c543e6f39f531f1d7e72505ea602ed1cfd5ed1e5e502e3f5eb7e7c9b |
| lib/B/YB03.v | collector | bc398352236fe8cf13024cd16912813e3a27a3b60b6fc63ec42284882a91b25b |
| lib/B/YB05.v | yb05 | e0b9c37dc01d5306eeb44a49284234f348dfc8a2a07af9f9ab6058e81d657343 |
| lib/B/YB12.v | rest | dd88a2312bd242d6af4cccc0a6a910736a6552f86fec8b4da6b1912378c02125 |
| lib/B/YB13.v | data1 | 5b26b60889249d358e5c41bdb3585fcfad94ebe60c5e9a9b79eb6b4672ab1d6d |
| lib/B/YB1h.v | data1 | 3aad3747569aef83d44b581333d74c0119dd826359d5d212a110cbd802c404bd |
| lib/B/YB1k.v | data1 | c4debc34842bf3bdd1591f5b62b09482fc65168529ad7d94ca84ada6ec7afb53 |
| lib/B/YB1l.v | data1 | 6f40f1652081ff6b0fc1cfd717ac78e41bd6287644187ac0885822063d21c0e0 |
| lib/B/YB1m.v | yb1m | 3798355d6877d5fd7691bb91a7f1fc4317a6e3fb15a898e3aaef6e3e5dd464da |
| lib/B/YB1v.v | data1 | 00ba4a17bb4a8222ecde924bf8719e25d2e233d77ade6283c345ca981907a3a9 |
| lib/B/YCej.v | acej | bf3107109c72c4ed0237363de194c2ee3239f913a6e95daf32f47d54c6df65e5 |
| lib/B/YD1k.v | rest | 40ef4f87b6abaa6ff43fd279506a9d5e572af0595f32e658089af452bc74d675 |
| lib/B/YD1y.v | exitdrv | f0c80bacb4776a77bb0b6aee135277f352666db52c927738a084f53b6316b1fd |
| lib/B/YD2i.v | rest | 0ab2d5dc33111b890b1a163426a7b8bb6da394b6e4067b7207d0d543a1589f2c |
| lib/B/YD2j.v | rest | 731ec11ec87764ed52fe95a57af8d833786020b75b9f5bc750dc7af162fc63c4 |
| lib/B/YE23.v | exitdrv | a5e52ea24efba1ab653e2a8be0583e5a7c93ac992e6f9d9ecf9eca3921abf5d5 |
| lib/B/YE37.v | exitdrv | 41fa97ea24f9300247106948cc8f6cdccbd360c6585e12ed361e6e8dc837c161 |
| lib/B/YE3i.v | rest | 1b5a13680420f0be40be196adfab652d910c864b441e8de9895d83d76de76b4a |
| lib/B/YF0m.v | yf0m | 35d10c8cbfc1433ed545bad27cfdfa3184bdb243f749a78025873db388d964c0 |

Each file's `(* Read from:` line names the pinned image B (sha256 41113a03c82f) and its unstripped twin (sha256
e217cb0a84f1). They follow the layout and the names of libreac/fuzz_grant's released image-B start-up files of the same
names, and each file's Require set equals its fuzz_grant twin's: the kit's gate G18a, `19 files EQUAL and gen =
nsB(raw), 0 not, 0 without a raw file` (`regen.gates.log (sha256 e0e7191fc5d8; internal record)`).

## The kit is an internal record

This tree ships four files: this README, `regen.sh`, `site.env.example` and `KIT-MANIFEST`. The kit that made the 19 files
and remakes them (its scripts, gates, tables and the sub-records of each stage) and the records of its runs are not
here: they are an internal record, on the internal records ref, file for file. `KIT-MANIFEST` names every kit file (178: the
159 CODE and 19 DOC files of the record's own class table `KIT.tsv`) by its records path, its sha256, its mode and its
path in the kit; the record's run outputs and logs (its RUN files) stay on the records ref and are not fetched. A record
file is cited by its content only: `<name> (sha256 <first 12 hex digits>; internal record)`, for example the kit's own
driver `regen.sh (sha256 acd10e399226; internal record)`; `KIT-MANIFEST` gives the full sha256 of each kit file, and
`KIT.tsv` that of each run file.

At the release this directory moved from provenance/startup-gen/B/ to provenance/evidence/startup-gen/B/ (the
release's lint allows provenance/evidence/, not provenance/startup-gen/), and its kit list from `MANIFEST` to
`KIT-MANIFEST` (the evidence index's checker reads every file named MANIFEST under provenance/evidence/ as an
index of that directory). The list's bytes are unchanged. `regen.sh` changed in two places only: the unit
directory is one level further up, and the list's name. The runs this README cites ran it at the old place, with
the old name.

The 19 files cite every record the same way, never by a path: YB01 and YB03 their collector logs (`pass2.B.log (sha256
32c44072a43b; internal record)`, `pass1.B.log (sha256 bb76bcf4e755; internal record)`), YB05 the two tools of the ASan
kit that relocate the donor plan (`a Theorem Labs tool (sha256 4d51ec1c0069; internal record)`, the ELF map tool, and `a
Theorem Labs tool (sha256 2d846496640d; internal record)`, the remap tool: the record's `LT-INPUTS.md (sha256
a1fe44985694; internal record)` names both), YCej its generator, its assembler, its checker and its override writer
(`gen_traces.py (sha256 a78026af1ae2; internal record)`, `acej.py (sha256 5db4ca1babf0; internal record)`,
`xcheck_pcs.py (sha256 aea1f2f6192d; internal record)`, `closure.py (sha256 09360e41bbe8; internal record)`), and YD1y,
YE23 and YE37 their writer (`gen_exitB.py (sha256 99d42401e998; internal record)`). No comment of the 19 names a path of
this tree that does not exist.

## Remaking the layer after a re-pin

One command. Give the four pinned files and a fresh output directory; every per-unit value is derived from them.

    SITE=<this host's site file, outside the tree; see site.env.example> \
    UBSAN=<path of fuzz_transport.asan-ubsan, the image-B pin> \
    UBSAN_TWIN=<path of its unstripped twin> \
    IMAGE=<path of fuzz_transport.asan, the image-A pin> \
    TWIN=<path of its unstripped twin> \
    OUT=<a fresh directory on local disk> \
      bash regen.sh

The `drivers` step fetches every `KIT-MANIFEST` row from the internal records ref (SITE: `RECORDS_REPO`, `RECORDS_REF`) into
`$WORK/kit` and refuses the run when a file is missing or its sha256 is not the one `KIT-MANIFEST` gives, whatever commit it
came from; two controls show it (a `KIT-MANIFEST` with one sha256 digit changed, and one naming a records path the ref does
not hold, are each refused with nothing fetched). A SITE without `RECORDS_REF` is refused, naming it. The `kit` step
lays the kit out as a lane (`kit_unpack.sh (sha256 efea945fa36b; internal record)`: the CODE files of `KIT.tsv`, and the
41 CODE files `CITED-NOT-COPIED.txt` names by commit, path and sha256, fetched and checked) and checks every pin of it
(`kit_verify.py (sha256 838dbc22ac1a; internal record)`). The `run` step runs the kit's `regen.sh (sha256 acd10e399226;
internal record)` on the four files; `bash regen.sh run <stage>` resumes at a stage.

### The pinned build: what the kit reads

The kit's regen.sh checks the four files against their sha256 before anything runs, then stages copies of them into the
layout its stages read the project and unit names from, `<scratch>/pins/libdiginet/result/{bin,unstripped}/
fuzz_transport/`, and checks each copy again; the given paths may lie anywhere. THE PINS OF RECORD are the facts
commit's own `index/binaries.tsv`: the kit derives the facts commit from the cold bases table (SITE `TRANSB_BASETSV`) as
the newest row whose index pins both given images (`pinindex.sh (sha256 82ebe43944cf; internal record)`) and refuses the
run when none does; a scratch pin table (`OSSV_PIN_TABLES`) is refused. Image A's AF0m for these pins (the pair input of
YF0m's pin line; this unit's lib/A/AF0m.v, sha256 5dfdd0e65356) is SITE `TRANSB_PAIRA_FROM`, checked by sha256
(`paira.sh (sha256 0b38fdf9e2cd; internal record)`). No commit is written in this tree: the kit pins the repository
commits it reads (the donor lib, the start-up set, the control units' records) in its own files.

What the stages need: the collector's builds, af0m and hsform's heavy mode run on a build VM, which the kit's env.sh
template (`env.sh (sha256 833b42c2bc24; internal record)`) names; the build check needs the build launcher and the cold
bases table; the rest runs on local disk under a 2 GB address-space cap that the kit's regen.sh sets for every process
of the run.

## The steps and the tool versions of each

The kit's regen.sh runs, in order, prep, facts, portcore, collector, yb05, data1, acej, yf0m, exitdrv, rest, yb1m, ns,
stamp, gates, build, each after its own controls; it stops at the first failing stage and names it. Every start-up tool
runs through the start-up set of record, `startup-set-2026-10-30d.tsv (sha256 bde970239064)` (`SHA256.control-inputs.txt
(sha256 7140b6e6701b; internal record)`). The kit files are cited by sha256 (all of them in `KIT-MANIFEST`); the other tools
are the files `kit_unpack.sh` fetches by commit and sha256 (`CITED-NOT-COPIED.txt (sha256 584c48127655; internal
record)`) or the start-up set:

| step | writes | kit files (internal record) | other tools |
|---|---|---|---|
| prep, facts | the local inputs; the image facts (`work/facts.env`) | `regen.sh` acd10e399226, `facts.py` 84a57fe0b1b3, `elfinfo.py` 05596908ca59 | - |
| portcore | the image-B core stage-out the later stages read | `run_port_core.sh` 18f3f77ef690 | `port_core.py (sha256 0e4e065eab9f; internal record)` |
| collector | YB01 YB03 | `run_collector.sh` 5b584badf23f, `run_hsform.sh` 1736f2a96c75, `pass2sum.py` 43ae2e94be10 | the ELF map tool (sha256 4d51ec1c0069; internal record), the remap tool (sha256 2d846496640d; internal record), the start-up set |
| yb05 | YB05 | `mk_yb05_transport.py` 711f14e5e118 | - |
| data1 | YB13 YB1h YB1k YB1l YB1v | `data1/run.sh` 763aab2c56e1, `transb_yb13.py` f5df0e6b2307, `transport_ab1hk_drive.py` b6e7f622d293 | `boxb1.py (sha256 68b5819b2776; internal record)` |
| acej | YCej | `acej/run.sh` f59b870b7995, `mktext.py` c5037adc53cc, `acej.py` 5db4ca1babf0, `closure.py` 09360e41bbe8, `xcheck_pcs.py` aea1f2f6192d | `gen_traces.py (sha256 a78026af1ae2; internal record)`, the start-up set |
| yf0m | YF0m | `run_af0mB.sh` f06ee27038ca, `relocownTransportB.py` b2a38e949496, `fsconst.py` b079dcdd1a8d | the start-up set |
| exitdrv | YE23 YD1y YE37 | `exitdrv/run.sh` 29bf864d21db, `gen_exitB.py` 99d42401e998 | - |
| rest | YB12 YD2i YD2j YD1k YE3i | `run_restB.sh` bf3103f4478c, `hull.sh` 3c41926881ca | the start-up set |
| yb1m | YB1m | `mk_yb1m.sh` 5c8802de34a2 | `boxb1.py (sha256 68b5819b2776; internal record)` |
| ns, stamp | the module paths, the pin lines | `run_lead_ns.sh` 0d1566cd7983, `nsB.py` 128db325f7d0, `stamp.sh` fc5c4656c86d, `pairstamp.sh` ec4463520e33, `paira.sh` 0b38fdf9e2cd | the start-up set |
| gates | the gate and control tables and their verdict | `gates/run_gates.sh` 0b518935f5f9, `verdict_B.py` d7a7da654403, `pass_rules_B.tsv` 0f46881ffcbe, `recite_check.py` 9aad58843ec6 | - |
| build | the build check of the 19 | `run_build.sh` 7465d8bb1d12 | the build launcher (SITE `TRANSB_CBTOOL`) |

Method of record: fuzz_lock's image-B start-up set, its writers copied with only the unit's pins and names changed;
where fuzz_transport differs, the record lists the difference with its measurement (`GATES-transportB.md (sha256
c04590c8a4e9; internal record)`, working record `NOTES.md (sha256 21c832ba8161; internal record)`).

## The runs of record

- The gate run of record on these pins: `CONTROLS: 97 ok, 0 BAD`, `GATES: 117 ok, 0 BAD (...); this run: 0 BAD, 0
  MISSING-input lines; MISSING in WK/gen: none; MISSING in WK/raw: none`, `run_gates: ALL STEPS OK` (`regen.gates.log
  (sha256 e0e7191fc5d8; internal record)`; its tables `CONTROLS.rc (sha256 c5053599900e; internal record)`, 97 rows, and
  `GATES.rc (sha256 19ff4b1321d7; internal record)`, 117 rows, every row `ok`). Its pin table is the facts commit's own
  `index/binaries.tsv` (sha256 aebeac715ec1), and `facts.env AGREES with this measurement (16 of 16 FB_* values the
  gates read)`.
- The build check on the integration base with the image-B core: `cb: rc=0 ... (19 targets compiled, 0 restored from the
  cache, 0 failed, 36 warnings)`, its .vo check `0 .vo failed` (`cb.build.asanb.recite.log (sha256 9db9e8cc019c;
  internal record)`, `cb.build-run.asanb.recite.log (sha256 8a71e931a510; internal record)`).
- The citation rewrite by the writers (the six files whose comments cited a record by its path re-made by their own
  writers, never edited): `recite_check: 19 files compared, 6 changed (YB01 YB03 YCej YD1y YE23 YE37), 11 changed lines,
  code outside comments IDENTICAL in all; PASS` (`recite.check.log (sha256 0a0ef8e4252a; internal record)`); its
  control, a copy with one planted code change in YD2j, `FAIL (2)` (`recite.control.log (sha256 c08d2ba6b8a0; internal
  record)`).
- The files those runs read and wrote are listed by sha256 in `SHA256.lib-B.txt (sha256 e16e1b3b4dff; internal record)`:
  18 of them equal the table above byte for byte. The 19th, YB05, differs in one comment line only (its line 4 now cites
  the two ASan kit tools by content); with every Rocq comment removed (nested `(* *)`, strings kept), the old and the
  shipped YB05 are equal token for token.
- The shipped form itself (this tree's `regen.sh` from `drivers` through `run`) has no run of record. The kit's regen.sh
  ran from a lane, stage by stage, as above; a run from a kit fetched by this `KIT-MANIFEST`, and the release scanner over
  this tree, are still to be run.

## The controls

Each stage reproduces a file that already exists before it writes the unit's, on cgif's released files and fuzz_lock B's
committed files, and the gates run every control before the unit's run: 97 control rows of record, every one `ok`, 26 of
them a planted fault that must be caught and is (`CONTROLS.rc`, above). Each sub-record's report quotes its commands,
its controls and its gate lines (`REPORT.md (sha256 54932707fa06; internal record)` for acej, `REPORT.md (sha256
5e499b8e32b5; internal record)` for data1, `REPORT.md (sha256 d64cdb917f2f; internal record)` for exitdrv, `REPORT.md
(sha256 97b45c22f931; internal record)` and `CONTROLS.md (sha256 e9002183cadb; internal record)` for the gates).

## Host locations and names

No file of this tree names a host location, a workspace, a repository branch, a tool repository or a worker. Each host
location and workspace a run needs is a variable of the SITE file, an env file outside the tree (`site.env.example`
lists every one with what it is); `regen.sh` refuses a SITE that leaves one unset or sets one it does not list, naming
it. Its `drivers` step runs the release scanner of record over this tree (SITE `SCANNER`; pinned by the sha256 of its
directory's SHA256SUMS) after the scanner's own positive control and requires no uncleared hit; then a copy of this tree
whose README names a worker of the roster (SITE `ROSTER`) must be flagged.
