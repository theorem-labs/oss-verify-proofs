# provenance/evidence/startup-B: fuzz_uci image-B start-up set (lib/B, 19 files)

Written by scripts/mk_evidence.py; not edited by hand. What a reader needs to re-derive the numbers of lib/B/{YB01,YB03,YB05,YB12,YB13,YB1h,YB1k,YB1l,YB1m,YB1v,YCej,YD1k,YD1y,YD2i,YD2j,YE23,YE37,YE3i,YF0m}.v: the writers of record, the per-value tables and the gate record. Generation logs are not here.

Pipeline of every file: its writer (below) -> scripts/nsB.py (module paths + header rule) -> pins.py stamp (10 files) -> lib/B. Re-running the pipeline reproduces all 19 committed files byte for byte.

## Files

| file | kind | role |
|---|---|---|
| `env.example.sh` | config | every variable name the writers read, without values |
| `exitdrv/gen_exitB.py` | script | YE23.v / YD1y.v / YE37.v (exit-driver relocation; all 8 descriptor words in YE37); its controls first; writes tables/exitdrv-numerals.md |
| `exitdrv/run.sh` | script | the exit-driver run (binmatch, gen_exitB, controls, nsB) |
| `exitdrv/run_binmatch_uciB.py` | script | binmatch.py (cited) cgif -> fuzz_uci, the identical-function map gen_exitB reads |
| `gates/GATE-RECORD.md` | gate record | every gate's RESULT and summary lines, controls first |
| `scripts/acej/drv_check.py` | script | the 8 driver traces derived from the universe json |
| `scripts/acej/header-B.txt` | script | the header acej writes into YCej.v |
| `scripts/acej/run.sh` | script | YCej.v: gen_traces + acej (cited), controls, negative controls, members check, the universe json |
| `scripts/addhdr.py` | script | the modification notice and pin line of YB1v.v / YB1m.v (boxb1 output) |
| `scripts/af0mB/ab01log_B.py` | script | cgif's released YB01 states in log form (af0m control input) |
| `scripts/af0mB/addsB.py` | script | af0m --add cells mapped by name from decode B's list |
| `scripts/af0mB/relocownUciB.py` | script | the base's Tfib_owned_static re-derived by name (decode B's relocownB.py rule, cited); writes tables/af0m-base-audit.tsv |
| `scripts/af0mB/run_af0mB.sh` | script | YF0m.v: af0m (cited) on the derived base, its controls, refused-row decisions and --add cells, each with its reason |
| `scripts/core_check.py` | script | records from git that the layer is built in the image-B core: head, merge, build record, shared MANIFEST.md |
| `scripts/elfinfo.py` | script | nm / section / program-header listings of an ELF (pyelftools) |
| `scripts/gates/codeptr-decl.sh` | script | codeptr pass-2 declarations, each with its role in both images (1 --same, 18 --not-address) |
| `scripts/gates/decl_evidence.py` | script | evidence for each codeptr declaration |
| `scripts/gates/keyed_scan_uci.py` | script | keyed-table scan (stack classes) |
| `scripts/gates/pac_fill.py` | script | triage of every GENERATOR-FILL row |
| `scripts/gates/pac_moved.py` | script | row join of two port_addr_check runs on the same inputs: moved, new and gone rows |
| `scripts/gates/pac_table.py` | script | port_addr_check flag classes per file vs the control |
| `scripts/gates/plant_uciB.py` | script | planted control of the by-role check |
| `scripts/gates/recount_uci.py` | script | hand-off state recount (decode recount rule) |
| `scripts/gates/run_gates.sh` | script | every gate G0-G12, each control first |
| `scripts/gates/symname_check.py` | script | independent .symtab check of every symbol-named definition (<x>_(A|D|E)_<symbol>, src0_D_*) |
| `scripts/hdr.YB12.txt` | script | the header atable writes into YB12.v |
| `scripts/hdrfix.py` | script | the committed-header rule on comments (undated Theorem Labs notice, no agent / lane / branch names, no dates, no host paths); code untouched |
| `scripts/hdrscan.py` | script | counts host paths, agent / lane names, branch names and dates in comments |
| `scripts/mk_evidence.py` | script | this builder |
| `scripts/mk_yb05_uci.py` | script | YB05.v: hsform header + the plan the collected pass 2 ran |
| `scripts/nsB.py` | script | module paths of a generated file in the lib/B layout (port_core rename_text) + the header rule (hdrfix.py); the gate: Require (dir, module) set = fuzz_grant B's released twin |
| `scripts/run_restB.sh` | script | YB12 / YD2i / YD2j / YD1k / YE3i: atable, gen_ad2, gen_ad1k, ae3i (cited) with their cgif controls and the planted atable control |
| `scripts/stripcmp.py` | script | comment-stripped diff of two .v files (comments-only proof) |
| `scripts/trunk_missing.py` | script | Required modules the trunk lib does not hold (build check) |
| `scripts/uci_ab1hk_drive.py` | script | YB1h.v / YB1k.v / YB1l.v through gen_ab1hk.py (cited) |
| `scripts/ucib_env.py` | script | every machine-specific path the writers read, from the environment |
| `scripts/ucib_yb13.py` | script | YB13.v: image numerals by the donor's rules (decode gen.py slots + segment 1 base); control on cgif's image; --table writes tables/yb13.slots.tsv |
| `tables/YCej.universe.json` | table | the allocation-trace universe of YCej.v (ycej_json.py, cited); af0m reads DRV_TRACES from it |
| `tables/af0m-adds.txt` | table | YF0m --add cells: decode B's list mapped by name, each row's fate and reason |
| `tables/af0m-base-audit.tsv` | table | YF0m base: each donor Tfib_owned_static row, its key and its fuzz_uci row (class b kept / c regenerated / d dropped) |
| `tables/exitdrv-numerals.md` | table | YE23 / YD1y / YE37: every numeral, cgif value | kind | fuzz_uci value | source |
| `tables/pac-fill-triage.txt` | table | every GENERATOR-FILL row of port_addr_check cb0e067e3bae with its measured reason (0 unexplained) |
| `tables/yb13.slots.tsv` | table | YB13.v: cgif token -> fuzz_uci token per slot, occurrences |

## Cited tools (not shipped: their text carries host-path patterns and would fail the lint)

Fetch the exact copy with `git show <commit>:<path>`; the sha256 is of that copy.

| tool | sha256 | commit | path |
|---|---|---|---|
| af0m.py | `238598b380f12c8942be11b554b5cbabe6db724ef8332835efcdacc42626758a` | dbb5a97ad14 | `tools/startup-set/2026-10-30/af0m.py` |
| atable.py (YB12) | `42e18a7eef506163388497138ad3200ad030645746cfa60d10e955340f70caaf` | dbb5a97ad14 | `tools/startup-set/2026-10-30/atable.py` |
| atable.py (first generation, byte-equal output) | `2d236e51ad7061c3786e54cb24284f83c6811ffcd2e47af4f36251f8bc87a298` | 8cd71d3a4bb | `tools/startup-set/2026-10-29/atable.py` |
| gen_ad2.py | `979c52cd71c6968173cf1ec7d83d5873c0fd9d988875bbe131c0c5bf6bc53189` | dbb5a97ad14 | `tools/startup-set/2026-10-30/frozen/gen_ad2.py.frozen-979c52cd71c6` |
| gen_ad1k.py | `43a0cf0abc6741ea9d27bc19d47752bf26840e41ff73813733fd935bec3560d9` | dbb5a97ad14 | `tools/startup-set/2026-10-30/frozen/gen_ad1k.py.frozen-43a0cf0abc67` |
| hsform.py (YB01, YB03, YB05 header) | `a93ebaea058faaeb14d35b1cdec31d6b4bcbe508ced124ccb1cf47e91d14adec` | 8cd71d3a4bb | `tools/startup-set/2026-10-29/frozen/hsform.py.frozen-a93ebaea058f` |
| plantail.py | `f8aa639d5cc7a5bae8879bca935e2df53fd77ecb83cc180316ec466fd77251af` | dbb5a97ad14 | `tools/startup-set/2026-10-30/frozen/plantail.py.frozen-f8aa639d5cc7` |
| codeptr.py | `12348302dfd2e419748bc3ad20e67b246d21b576c9c6d7887a33854785e146dd` | dbb5a97ad14 | `tools/startup-set/2026-10-30/codeptr.py` |
| pins.py | `4778073f01be27d903d4afa8820ba6407c521e11d5de200e635a2a2346491498` | dbb5a97ad14 | `tools/startup-set/2026-10-30/frozen/pins.py.frozen-4778073f01be` |
| keyset.py | `f050b43e480e9b8294a81a0b80b680cbcbc1c4862735fa0b5e89175e5d88413c` | dbb5a97ad14 | `tools/startup-set/2026-10-30/frozen/keyset.py.frozen-f050b43e480e` |
| ifchk.py | `f5cde600cc1886bb65200495a69e1eb3afb936ea5512edb8c581edc0299847fb` | dbb5a97ad14 | `tools/startup-set/2026-10-30/frozen/ifchk.py.frozen-f5cde600cc18` |
| tr0.py | `14f49a0b2243b01acec98e3c65f5238f6031456174135661678bd073d9c4fb54` | dbb5a97ad14 | `tools/startup-set/2026-10-30/frozen/tr0.py.frozen-14f49a0b2243` |
| ColA.v (collector) | `d198e5a14160538277fcaf78fa92e581774b9e092ff389a00c4c1aed07315b79` | dbb5a97ad14 | `tools/startup-set/2026-10-30/coq/ColA.v` |
| ae3i.py | `3cf49addef7e85d818b17b66363b2d8cc7d5feb4b7163fd22d8c3be41acae7a0` | 7eb81ddb186 | `proofs/libreac/fuzz_decode/provenance/startup-gen/B/ae3i.py` |
| gen_ab1hk.py | `0f51cb9cdb183fe6820d9b0ea689a38a681622b858115f63dce9c0c6c54fa326` | 7eb81ddb186 | `proofs/libreac/fuzz_decode/provenance/startup-gen/B/gen_ab1hk.py` |
| boxb1.py | `0fe1e96732e222969b7e4ee4cd57dbc34c9e52779060ec2c8f1c7afebd3657e1` | 7eb81ddb186 | `proofs/libreac/fuzz_decode/provenance/startup-gen/B/boxb1.py` |
| port_core.py (pg-reloc 0e4e065eab9f) | `0e4e065eab9f9a6707caa60a74f2c4da6ea9459e6eab49da05a318dd5586042c` | 7f0e4b05267 | `tools/pg-reloc/0e4e065eab9f/port_core.py` |
| gen.py (decode, as gen_dec.py) | `6ccd419c977fbb4d40da7d36488ebc2021beefbe6991b9225a4fff648bae0200` | 1148f2311f82 | `proofs/libreac/fuzz_decode/provenance/startup-gen/A/gen.py` |
| relocownB.py (decode B) | `4a866ee291817dbac45078e6f406aaa8850261a03c2b921d150f8bf1b7ce1c0a` | 7eb81ddb186 | `proofs/libreac/fuzz_decode/provenance/startup-gen/B/af0m/relocownB.py` |
| colrun.py | `59778df6f00b34aca3e807ac76711522df70823f976da0fae923f2813b4faf31` | 534cebca43a | `proofs/reac-repacer/fuzz_uci/provenance/startup-gen/B/tools/colrun.py` |
| itabranges.py | `6bd6b803674730b67690bd1f97b79cd50199af8ee502a751b9c5b51e9561073e` | 534cebca43a | `proofs/reac-repacer/fuzz_uci/provenance/startup-gen/B/tools/itabranges.py` |
| replyscratch.py | `cf47e327b300f8ce93eaf8748b2242fffa67fb3d83b862a4c7bdc1b02a059b20` | 534cebca43a | `proofs/reac-repacer/fuzz_uci/provenance/startup-gen/B/tools/replyscratch.py` |
| kimg_overlap.py | `acfd7418176d7470a6b69896d10475e494a04fd263b8178246746e9bb931f42f` | 534cebca43a | `proofs/reac-repacer/fuzz_uci/provenance/startup-gen/B/gates/tools/kimg_overlap-acfd7418176d.py` |
| port_addr_check.py (16f8a030c869) | `16f8a030c869fb97eff621fc97728d6c446c4d5ee1b005a8fedc9fc5768dfcbf` | 7eb81ddb186 | `proofs/libreac/fuzz_decode/provenance/startup-gen/B/port_addr_check.py` |
| port_addr_check.py (cb0e067e3bae) | `cb0e067e3bae20e70d58a38a5e7d8ae7e8fdf05a6b1d273c4275b266db9f345d` | 534cebca43a | `proofs/reac-repacer/fuzz_uci/provenance/startup-gen/B/gates/tools/pac-cb0e/port_addr_check.py` |
| port_addr_check.py (e165063a0081) | `e165063a00810b376b9f65ef3da645c11eed0e22e6b50b2ae10db97ccc6b2d3b` | 33b974797adf | `proofs/reac-repacer/fuzz_uci/provenance/startup-gen/B/gates/tools/pac-e165/port_addr_check.py` |
| port_addr_check.py (efa19b81e92b, of record) | `efa19b81e92ba289e7c185d481faadf045ce7d52d092cc10642fec69924aba03` | bc04213653c8 | `proofs/reac-repacer/fuzz_uci/provenance/startup-gen/B/gates/tools/pac-efa1/port_addr_check.py` |
| global_settings.py (v10) | `439f8e3bd4637640d6d40fb668716c081c3ba202aa831f31f0120de0b4e39242` | 463af5742a39 | `tools/global_settings/439f8e3bd463/global_settings.py` |
| ownedcheck.py (352fb92f) | `352fb92f567b188247af554bf69ed8299ca2bdd30a26a08c97d28cf8f5cca7c5` | 534cebca43a | `proofs/reac-repacer/fuzz_uci/provenance/startup-gen/B/gates/tools/ownedcheck-352fb92f/ownedcheck.py` |
| shadowcheck.py (542898b2) | `542898b23954d1fc088d0f2624696eda5e7e4a637f5c430447c032c8138c4cb7` | 534cebca43a | `proofs/reac-repacer/fuzz_uci/provenance/startup-gen/B/gates/tools/shadowcheck-542898b2/shadowcheck.py` |
| classify.py (by-role check, unit uciB config) | `3df8cb1327d8acea8dd0bd79324a9354915e6e4d7ec2d477bd0561d3f2f003f1` | 534cebca43a | `proofs/reac-repacer/fuzz_uci/provenance/startup-gen/B/gates/tools/classify/classify.py` |
| lowbeg.py | `8413f30bc6daf99bc52d7e232f032e7cc58414bf90c1b55849001d7e4d23ee1e` | 534cebca43a | `proofs/reac-repacer/fuzz_uci/provenance/startup-gen/B/gates/tools/lowbeg.py` |
| acej.py | `5db4ca1babf0c593537907c71d0593f120ec40857d9e947709bf197687fdcf9e` | 7eb81ddb186 | `proofs/libreac/fuzz_decode/provenance/startup-gen/B/acej/acej.py` |
| ycej_json.py (decode B) | `c96a25b5daf982689b6e27d7eea6bb0dcf3bd60c37a81d5d5ad21c55e23d5973` | 7eb81ddb186 | `proofs/libreac/fuzz_decode/provenance/startup-gen/B/acej/ycej_json.py` |
| mk_top_manifest.py (writer of record of provenance/evidence/MANIFEST.md and MANIFEST) | `a0ba0eb66d6693325368f3dae7dec2e19ca4c3566de3cc51deec41d92227ba0a` | 4f2904dd062 | `tools/mk_top_manifest/a0ba0eb66d66/mk_top_manifest.py` |

## Checks run by the builder

44 files; oft lint private-data shapes (tools/oft/lint.py sha256 ee1df54a6188: HOST_PATH, PRIVATE_IP, PRIVATE_HOST_NAME, REPOSITORY_PATH, EMAIL, PRIVATE_KEY, TOKEN) plus /tmp and /mnt paths, build-machine names, Tailscale names, derived suffixes and binary content: 0 findings.
