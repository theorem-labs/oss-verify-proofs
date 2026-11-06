# Licence-header record of the generated start-up files

This statement replaces `headers_check.py`, its output `STARTUP-HEADERS.tsv` and the list `AF0m.body-removed.tsv`.
Each is kept, unchanged, in an internal record, cited below by path and sha256. The quoted donor comment
lines are in the record only. `AE23.body-removed.tsv`, `AE37.body-removed.tsv` and `AE3i.body-removed.tsv` stay in this
directory.

## Records

- headers_check.py: internal record, path startgen/headers_check.py, sha256 8c062f2be216d094daacd2f9177801a62692159e9abfdb7f73c78dc52536a48c
- STARTUP-HEADERS.tsv, its output: internal record, path startgen/STARTUP-HEADERS.tsv, sha256 56a9425c5666990bddc20f241afc55fe80d80e5c38c07bf65cda177cc2fdb1d9
- AF0m.body-removed.tsv, the body comment lines removed from AF0m's base before the generator ran: internal record, path startgen/AF0m.body-removed.tsv, sha256 83f14cbf2675cb88931eea2ab5c093c3f4733e5679dfa49307f585e6f8ebc91d

## Command and checks

`headers_check.py --repo REPO --ref 88154566652a --out STARTUP-HEADERS.tsv GEN.v=F[=BODY.tsv] [GEN.v=cgif:F ...]`,
with each donor read by `git show` (libreac/fuzz_pcap's `lib/A/F.v` at 88154566652a, or with `cgif:F`
cgif_file_fuzzer's `lib/A/F.v` at c8557374ad2e). For each generated file:

- it checks that lines 1-3 (Copyright, SPDX, the 'ported' notice) are byte-identical to the donor's, line 3 either
  exactly or with only the start-up tools' undating (`Theorem Labs, 2026-10: ` -> `Theorem Labs: `);
- it records the donor's top comment lines after line 3 that the generated file does not have (removed before the
  tool ran), the count of the tool's own header lines, the body comment lines removed before the tool (from BODY.tsv),
  and whether any removed line occurs in the Anthropic-derived cgif_file_fuzzer file of the same name at
  c8557374ad2e. It exits 1 on a failed header check or on a removed line found in that file.

## Result (STARTUP-HEADERS.tsv): 16 files, 0 FAIL

| file | donor at commit | header lines 1-3 | header lines removed | tool-written lines | body lines removed | removed lines in the cgif file |
|---|---|---|---|---|---|---|
| `reac-pw/fuzz_link/lib/A/AB01.v` | `proofs/libreac/fuzz_pcap/lib/A/AB01.v@88154566652a` | PASS (1-3 byte-identical to the donor; 3 undated by the tool) | 3 | 7 | 0 | no (0 of 3) |
| `reac-pw/fuzz_link/lib/A/AB03.v` | `proofs/libreac/fuzz_pcap/lib/A/AB03.v@88154566652a` | PASS (1-3 byte-identical to the donor; 3 undated by the tool) | 2 | 5 | 0 | no (0 of 2) |
| `reac-pw/fuzz_link/lib/A/AB05.v` | `proofs/libreac/fuzz_pcap/lib/A/AB05.v@88154566652a` | PASS (1-3 byte-identical to the donor) | 2 | 1 | 0 | no (0 of 2) |
| `reac-pw/fuzz_link/lib/A/AB12.v` | `proofs/libreac/fuzz_pcap/lib/A/AB12.v@88154566652a` | PASS (1-3 byte-identical to the donor; 3 undated by the tool) | 4 | 1 | 0 | no (0 of 4) |
| `reac-pw/fuzz_link/lib/A/AF0m.v` | `proofs/libreac/fuzz_pcap/lib/A/AF0m.v@88154566652a` | PASS (1-3 byte-identical to the donor; 3 undated by the tool) | 1 | 3 | 50 | no (0 of 51) |
| `reac-pw/fuzz_link/lib/A/AD2i.v` | `proofs/libreac/fuzz_pcap/lib/A/AD2i.v@88154566652a` | PASS (1-3 byte-identical to the donor) | 3 | 2 | 0 | no (0 of 3) |
| `reac-pw/fuzz_link/lib/A/AD2j.v` | `proofs/cgif/cgif_file_fuzzer/lib/A/AD2j.v@c8557374ad2e` | PASS (1-3 byte-identical to the donor; 3 undated by the tool) | 0 | 2 | 0 | no (0 of 0) |
| `reac-pw/fuzz_link/lib/A/AE3i.v` | `proofs/libreac/fuzz_pcap/lib/A/AE3i.v@88154566652a` | PASS (1-3 byte-identical to the donor) | 1 | 1 | 13 | no (0 of 14) |
| `reac-pw/fuzz_link/lib/A/ACej.v` | `proofs/libreac/fuzz_pcap/lib/A/ACej.v@88154566652a` | PASS (1-3 byte-identical to the donor; 3 undated by the tool) | 1 | 4 | 0 | no (0 of 1) |
| `reac-pw/fuzz_link/lib/A/AB1m.v` | `proofs/libreac/fuzz_pcap/lib/A/AB1m.v@88154566652a` | PASS (1-3 byte-identical to the donor) | 4 | 0 | 0 | no (0 of 4) |
| `reac-pw/fuzz_link/lib/A/AB1v.v` | `proofs/libreac/fuzz_pcap/lib/A/AB1v.v@88154566652a` | PASS (1-3 byte-identical to the donor) | 1 | 0 | 0 | no (0 of 1) |
| `reac-pw/fuzz_link/lib/A/AB1h.v` | `proofs/libreac/fuzz_pcap/lib/A/AB1h.v@88154566652a` | PASS (1-3 byte-identical to the donor) | 1 | 0 | 0 | no (0 of 1) |
| `reac-pw/fuzz_link/lib/A/AB1k.v` | `proofs/libreac/fuzz_pcap/lib/A/AB1k.v@88154566652a` | PASS (1-3 byte-identical to the donor) | 1 | 0 | 0 | no (0 of 1) |
| `reac-pw/fuzz_link/lib/A/AE23.v` | `proofs/libreac/fuzz_pcap/lib/A/AE23.v@88154566652a` | PASS (1-3 byte-identical to the donor) | 1 | 0 | 5 | no (0 of 6) |
| `reac-pw/fuzz_link/lib/A/AE37.v` | `proofs/libreac/fuzz_pcap/lib/A/AE37.v@88154566652a` | PASS (1-3 byte-identical to the donor) | 27 | 0 | 12 | no (0 of 39) |
| `<staged>/lib/A/AD1k.v` | `proofs/cgif/cgif_file_fuzzer/lib/A/AD1k.v@c8557374ad2e` | PASS (1-3 byte-identical to the donor; 3 undated by the tool) | 0 | 2 | 0 | no (0 of 0) |

`<staged>/` is the staged copy of the unit's `lib/` that held AD1k.v when the check ran.

The AD2i.v row is the check of the AD2i.v that the 2026-10-30d gen_ad2 run wrote (`RUNS.md`). That run copies the
donor's line 3 with its date, so the check finds lines 1-3 byte-identical without undating. The record's earlier
version of this file (internal record, path startgen/STARTUP-HEADERS.tsv, sha256
2f6ec5bda47d44a4aa45b64301194ea6107faf45a455c8979870f32d5dd633ab) differs only in that cell, which read "PASS (1-3
byte-identical to the donor; 3 undated by the tool)".

## AF0m.body-removed.tsv

51 lines of AF0m's base, none of them in cgif_file_fuzzer's `lib/A/AF0m.v` at c8557374ad2e: header line 4 (base line
4), the comments on the real_fmemopen row (base lines 292-294) and on the real_fread row (295-297), the
Tfib_owned_static per-entry notes (350-392) and the ts_junk comment (455).
