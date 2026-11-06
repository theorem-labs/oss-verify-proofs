# reac-repacer/fuzz_wire image B (asan-ubsan) start-up data set: evidence slice `startup-B`

The scripts, logs and gate inputs in this directory cite internal working commits by sha, byte for byte as they ran; those commits are not in the release history, and the unit's internal record keeps them reachable.

rule 24: proves no function (kind: start-up facts). This slice lets a reader re-derive every number of the 19 image-B
start-up files `proofs/reac-repacer/fuzz_wire/lib/B/{YB01,YB03,YB05,YB12,YB13,YB1h,YB1k,YB1l,YB1m,YB1v,YCej,YD1k,YD1y,YD2i,YD2j,YE23,YE37,YE3i,YF0m}.v`
from the pinned image (`fuzz_wire.asan-ubsan`, sha256 af4534831a4528320c7dc74ca3f64bb96e8232ed2e313f01126d10879f3417d6,
the value `projects/reac-repacer/fuzz_wire/harness.yaml` pins at commit 25e3d17bdb50) and the donor
`proofs/cgif/cgif_file_fuzzer/lib` at commit 25e3d17bdb50. Generation logs are not part of it; they stay with the lane's
provenance. Frozen tools are cited by sha256 and commit:path, never copied in.

## Environment the writers read
Every writer takes its paths from the environment, never from a literal: `W` (lane directory), `WK` (its work tree),
`UB` / `UBs` (the asan-ubsan pin and its unstripped twin), `UA` / `UAs` (the asan pin and twin), `CB` / `CA` (the donor's
asan-ubsan / asan pins), `DLIB` (the donor clone's lib), `DLIBC` (a clean export of the donor lib at 25e3d17bdb50), `TR`
(the unit's trunk clone), `LT` (local scratch), `FT` (the start-up tool set below, extracted), `FR3` (`bash $FT/frozen-run.sh
<the set's tsv>`), `HUB` (the git hub), `LR` (the fuzz_grant / fuzz_decode images used by controls), `S`
(the start-up tools directory holding colrun / itabranges / replyscratch / frozen-run.sh), `KIT` (the ASan comparison
kit), `MAPTOOL` / `RELOCTOOL` (the kit's image address-map tool and plan-relocation tool, sha256 4d51ec1c0069 /
2d846496640d), `PAC_CACHE` / `DONOR_BINS` (the relocation gate's address cache and the donor builds it reads), `OLD_SYMS`
(the donor image's symbol recovery cache), `VM` (the build host's name, never written into a kept file), and `scrub`
(the log writer's filter that writes any host path as the variable holding it).

## Files
| file | role |
|---|---|
| `GATES-wireB.md` | the gate record: generated set (sha256, how), tools (sha256), every gate with its control, the collector run table, findings, open points |
| `GATES-wireB.paths.tsv` | the relative paths of `GATES-wireB.md` under this unit's bases, one row each: its line, its base (named on that record's line 17; the one dead path, line 22, under none), the repository path it resolves to, and the file's sha256 where it has one; the paths of other units at the released commit a line names (lines 25, 115, 411, 425) are not listed |
| `tables/image-B.facts.txt` | the measured image facts (`tools/measureB.py` output): pin / twin sha256, PT_LOAD equality, sections, TFIB_TEXT_N, asan_globals (none), main, memset / memcpy, canary .got cell, interceptor ipc values, frame-pointer setters |
| `tables/YB13.slots.tsv` | YB13's per-value table: each donor image numeral, its fuzz_wire value, occurrences (`tools/wire_yb13.py --table`) |
| `tables/YF0m.owned-static.baseaudit.tsv` | YF0m's Tfib_owned_static derivation: each donor row, its class, its key, its fuzz_wire value (`tools/af0mB/relocownWireB.py`) |
| `tables/SHA256.lib-B.txt` | sha256 of the 19 committed files |
| `tools/measureB.py` | measures the image facts above |
| `tools/wire_ab1hk_drive.py` | drives gen_ab1hk.py (sha256 0f51cb9cdb18) for YB1h / YB1k / YB1l, and its cgif control |
| `tools/addhdr.py` | the undated modification notice and pin line for boxb1.py's YB1v / YB1m |
| `tools/wire_yb13.py` | YB13 by fuzz_decode's gen.py rules (gen_dec.py sha256 6ccd419c977f, cited) + segment 1's base; control and residue gate |
| `tools/mk_yb05_wire.py` | YB05: hsform's header of the donor plan + the plan the collector's pass 2 ran |
| `tools/af0mB/relocownWireB.py` | YF0m's base: Tfib_owned_static re-derived by name (fuzz_decode B's relocownB.py 4a866ee29181 with fuzz_wire paths and its n = 0 branch) |
| `tools/af0mB/addsWB.py` | af0m's --add cells, fuzz_decode B's list of record mapped by name |
| `tools/af0mB/ab01log_B.py` | writes cgif's released YB01 states in collector-log form for af0m's donor control |
| `tools/af0mB/run_af0mB.sh` | YF0m: af0m control on cgif, base, provisional YB12, af0m on fuzz_wire (every decision with its reason) |
| `tools/run_restW.sh` | YB12 (atable), YD2i / YD2j (gen_ad2), YD1k (gen_ad1k), YE3i (ae3i), each with its cgif control first, and the hull-bound gate |
| `tools/finalize.sh` | module paths (nsW.py), pins.py stamp (on a scratch copy that replaces the file only after textguard.py passes it), hdrcheck over the 19 |
| `tools/nsW.py` | module paths by port_core 0e4e065eab9f's rename_text in fuzz_grant B's lib/B layout (commit 4f87de75d67), the record renames over the CODE text only (a comment may state the rename mapping itself), the placement rule (per-image vs shared modules), and the header rule per file: dated Theorem Labs notices are undated in 18 files and kept in YF0m (`KEEP_DATED`: YF0m comes from af0m of the start-up set at commit f141794333162b); gates the Require set; refuses (exit 2, nothing written) a `--grant-twin` that is not a module name and any text textguard.py refuses |
| `tools/textguard.py` | the writers' refusal check (fail-closed on their inputs): host paths, worker / lane / workspace names by shape, named branches, host names, private addresses, dates and clock times (a notice head's month exempt); mk_yb05_wire.py, nsW.py, exitdrv/gen_exitW.py and finalize.sh's stamp step call it on the text they would write, and refuse (exit 2) before writing |
| `tools/trunk_missing.py` | the unit-lib modules the 19 Require that the trunk does not hold |
| `tools/elfinfo.py` | nm / section / program-header listings of the twin (pyelftools) |
| `tools/hdr.YB12.txt` | YB12's header lines |
| `acej/run.sh`, `acej/header-B.txt`, `acej/pins.sha256`, `acej/refs.sha256` | YCej and its universe json: gen_traces + the fuzz_decode emitter, with every control; the helpers it runs are cited in `pins.sha256` (fuzz_decode emitter acej.py at commit 1148f2311f82, ycej_json.py at commit 7eb81ddb186) |
| `exitdrv/gen_exitW.py`, `exitdrv/run.sh`, `exitdrv/run_binmatch_wireB.py`, `exitdrv/xcheck_portcore.py`, `exitdrv/trunk_requires.py` | YE23 / YD1y / YE37 by the exit-driver method, its controls and negative controls |
| `gates/run_gates.sh`, `gates/codeptr-decl.sh`, `gates/pac_table.py` | the gate run of record: every step with its wanted rc, the run's own exit status (1 when a step is UNEXPECTED) |
| `gates/GD.expect` | gate GD's expectations: the base commit and each of the 19 files' change class (equal / comment / require / code, with its commits, changed lines and reason); every GD WANT comes from it |
| `gates/mk_gdexpect.py` | writes `gates/GD.expect` from the trunk clone (base..HEAD): each file's commits, changed lines and class come from git and stripcmp, its reason from the script's table; no sha is typed by hand; refuses (exit 2) a changed file without a reason and any text textguard.py refuses |
| `gates/mk_results.py` | writes the `Gate run of record` section of `GATES-wireB.md` from the run log |

## Tools cited, not copied
The start-up tool set of record, by sha256 and not in the published tree except ColA.v (the main line holds it, since commit a4e873577f2c, at projects/libreac/fuzz_boxreg/proofs/provenance/evidence/startup-AB/inputs/set/frozen/ColA.v.frozen-d198e5a14160) (af0m 238598b380f1, atable 42e18a7eef50,
gen_ad2 979c52cd71c6, gen_ad1k 43a0cf0abc67, hsform a6de3be38c53, plantail f8aa639d5cc7, codeptr 12348302dfd2, pins
4778073f01be, keyset f050b43e480e, ifchk f5cde600cc18, universe 8510965be502, coq/ColA.v d198e5a14160); port_core.py
0e4e065eab9f, gen_traces.py a78026af1ae2 and resolve_code.py 81803218fe79 (by sha256; none is in the published
tree); the ASan comparison kit's image address-map tool 4d51ec1c0069 and plan-relocation tool 2d846496640d;
colrun.py 59778df6f00b, itabranges.py 6bd6b8036747, replyscratch.py cf47e327b300; ae3i.py 3cf49addef7e; gen_ab1hk.py
0f51cb9cdb18; boxb1.py 0fe1e96732e2; fuzz_decode's gen.py 6ccd419c977f; the gate tools listed with their sha256 in
`GATES-wireB.md`.

`provenance/evidence/MANIFEST.md` and the machine manifest `provenance/evidence/MANIFEST` (beside this slice) are
GENERATED, in one run, by their one writer, mk_top_manifest.py, the registered copy of record cited at commit
47ad23906df6 `tools/mk_top_manifest/3d332f497626/mk_top_manifest.py` (sha256
3d332f4976269a3664554725544ad098892cbff1b2d2b2590530e191192340cc) and run from there over `provenance/evidence/`.
