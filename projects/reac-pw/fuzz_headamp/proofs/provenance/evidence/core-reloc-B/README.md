# core-reloc-B: text kept out of this directory (the derivation of image B's ASan core; in-record paths keep the record's own names)

The files below are kept verbatim in an internal record, commit d257b0747438. Each row cites the file as: commit, path
inside the record, sha256.

## As-run files

Each is a tool's output or a script exactly as it ran. Its text names the hosts and work directories of the run, and a
rewrite would no longer be the bytes that ran, so it is not in this directory.

| file | record | what it is |
| --- | --- | --- |
| pac-B3.log | commit d257b0747438, path reloc-B3/pac-B3.log, sha256 de816ff8a5418c4ebfbc842e8d2f12903a573689ab9b63fc704310eaabda5b2b | the as-run summary output of port_addr_check 3d2eee813cce, lib/A -> lib/AU on image B (138 flagged rows; each read in port_addr_check-flags.tsv) |
| pac-ctrl-donor-vs-donor.log | commit d257b0747438, path reloc-B3/pac-ctrl-donor-vs-donor.log, sha256 a88fd87cbbe45e43f58bad2ed2840c63918f3b2c18c34554040e0699d42d5191 | the as-run summary output of the port_addr_check donor-vs-donor control (image A on both sides, 6 flagged rows) |
| pac-plant.log | commit d257b0747438, path reloc-B3/pac-plant.log, sha256 23d163b5cc6eab03b45e9da31d5b7495791ce7ad7cfbb2b8f1d57623aa315c52 | the as-run summary output of the port_addr_check plant control (144 flagged rows) |
| runs.sh | commit d257b0747438, path reloc-B3/runs.sh, sha256 db22edf582d8de5549b3ae70fb9353088a44dc1c78655c7e661e052c35830105 | the B3 runs of record as they ran (derive_y, alreloc, YCej traces, recompute_counts, roundconst-gate v2, port_addr_check, codeptr) |
| codeptr-run.txt | commit d257b0747438, path reloc-B3/codeptr-run.txt, sha256 c49cc99ad4cb572331b7307105830eb007c818a015cd89d72508dca498aa3176 | the as-run output of codeptr 12348302dfd2 over the 386 lib/AU files of image B (the findings are read in codeptr-findings.tsv) |

## Text before the scrub

Each file below is in this directory with only its internal names and host paths rewritten: a branch name became its
commit sha, a lane or host name was removed or became a role word, a host path became a tool registry path, a file
name or a sha256. Every number, address, verdict and count is unchanged. The text as it was before that rewrite is
kept in the internal record.

| file | record (text before the scrub) |
| --- | --- |
| codeptr-findings.tsv | commit d257b0747438, path reloc-B3/codeptr-findings.tsv, sha256 50156883f38384554e348235febad32e9c9368a6fadc43bc4de996e3d4be3148 |
| decisions.tsv | commit d257b0747438, path reloc-B3/decisions.tsv, sha256 c889f4123147226bca61dd09f7a3353040c098bc4ed520a998906992e3ceaefe |
| port_addr_check-flags.tsv | commit d257b0747438, path reloc-B3/port_addr_check-B3-flags.tsv, sha256 f0984894b5ec62d0f81f671ccd6fb67cbf76a851e0b6864bea3b9734be5e3949 |
| roundconst-v2-nonsame.tsv | commit d257b0747438, path reloc-B3/roundconst-v2-B3-nonsame.tsv, sha256 203d5cd8b8f68faed94e8fe3cf8db53d30deb288fae52f8eb8bf15f745155caa |
| untimed-build.txt | commit d257b0747438, path reloc-B3/untimed-build.txt, sha256 6bfb9c09c51908dda661f51298dc4319cd54e6b809f18f33616b23655fd8d453 |

## Cited outputs and logs

Files that a ledger here cites by name and sha256; they are not in the tree.

| file | record | what it is |
| --- | --- | --- |
| build-20261030T202228Z.log | commit d257b0747438, path reloc-B3/logs/build-20261030T202228Z.log, sha256 b67d3fd1c668d3f3fc2f3fbd407f9b238e06d81f02bdd6d63d024ad3991c6090 | the image-B untimed build log (cited in untimed-build.txt) |

## Rows superseded by later code commits

The ledgers keep the decision as it was made; these rows no longer describe the proof text.

| rows | was | now | why |
| --- | --- | --- | --- |
| decisions.tsv:148-149; codeptr-findings.tsv:10; class5-check.tsv:1409; agreed-sample.txt:3 | YFem.v:131 / :209 `TOT <= 127070` (restored byte-identical to lib/A) | `TOT <= 127008` | as image A: 31 + 1 + 31 * DEPOT_MAX (Definition TOT at lib/AU/YFem.v:101, DEPOT_MAX = 4096 at lib/Reusable/YG01.v:142); the aTOT atom range (YFek.v:37) stays `mkAF 2 131072 0` (memory cell max 127039: YFem.v:1249, tr_len :124) |
| image-derived-counts.tsv:31-32 (YD1g hull pages 1514) | YD1g.v:1072 arm `change 6201344 with (1514 * 4096)` | the arm is deleted | unreached text, as in image A |
