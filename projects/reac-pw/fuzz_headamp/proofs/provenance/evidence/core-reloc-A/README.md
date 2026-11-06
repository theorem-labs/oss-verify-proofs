# core-reloc-A: text kept out of this directory (the relocation of image A's ASan core; in-record paths keep the record's own names)

The files below are kept verbatim in an internal record, commit d257b0747438. Each row cites the file as: commit, path
inside the record, sha256.

## As-run files

Each is a tool's output or a script exactly as it ran. Its text names the hosts and work directories of the run, and a
rewrite would no longer be the bytes that ran, so it is not in this directory.

| file | record | what it is |
| --- | --- | --- |
| port_addr_check-run.txt | commit d257b0747438, path reloc-A3/port_addr_check-run.txt, sha256 2c88489abd6302f4b72747462ef702cc7fbb09e6fd3c2cda2b82067a3d801285 | the as-run output of port_addr_check 3d2eee813cce on image A (inputs used, counts); the run summarised in port_addr_check.tsv |

## Text before the scrub

Each file below is in this directory with only its internal names and host paths rewritten: a branch name became its
commit sha, a lane or host name was removed or became a role word, a host path became a tool registry path, a file
name or a sha256. Every number, address, verdict and count is unchanged. The text as it was before that rewrite is
kept in the internal record.

| file | record (text before the scrub) |
| --- | --- |
| class4-list.txt | commit d257b0747438, path reloc-A3/class4-list.txt, sha256 810db01881502c915caae50a82848a729030e34126aa4685a41b39304dceba86 |
| crosscheck-portcore.txt | commit d257b0747438, path reloc-A3/crosscheck-portcore.txt, sha256 00781d94c2d80c71952b9672e37bcdd00996a8d3febdb09027a38a7728e8bf21 |
| decisions-alreloc-a5c53bb2bed4.tsv | commit d257b0747438, path reloc-A3/decisions-alreloc-a5c53bb2bed4.tsv, sha256 3a97403eefaf5315114011212e32296a6be844e9fbd5de36c82a256130f3ee44 |
| image-derived-counts.tsv | commit d257b0747438, path reloc-A3/image-derived-counts.tsv, sha256 b3d0a45ee8e2c78687eb38c86c5dbf9b2186b478ff6237805f7b7308ae9d3a74 |
| measurements.txt | commit d257b0747438, path reloc-A3/measurements.txt, sha256 bdc070dcb46ef8d6fd380ce8392e59763b67cee85753c23b213e5b779f3ad3d8 |
| per-file.tsv | commit d257b0747438, path reloc-A3/per-file.tsv, sha256 bc90eb8a1acac46685551dfc81688763907dfc57aea3d74dc13bceb8dbcc9c8b |
| port_addr_check.tsv | commit d257b0747438, path reloc-A3/port_addr_check.tsv, sha256 1bc80aaac9100a8cb2ca726639aad6e3a1109e44c9f5da813a4df9b0c0babcb2 |
| portcore-d9e0589898fd-check.txt | commit d257b0747438, path reloc-A3/portcore-d9e0589898fd-check.txt, sha256 3add7cb554ec636b5c1eb761a89b540b1bc645e7920f5eec61330c89c0e342ae |
| roundconst-v2.tsv | commit d257b0747438, path reloc-A3/roundconst-v2.tsv, sha256 888224501f6012da2ce49fce47b40962d6830ce529d2d20c83d45d7dd9405494 |

## Cited outputs and logs

Files that a ledger here cites by name and sha256; they are not in the tree.

| file | record | what it is |
| --- | --- | --- |
| rc-dry4.tsv | commit d257b0747438, path reloc-A3/roundconst/rc-dry4.tsv, sha256 6aff986dad3b5eb0d3d575e2cde47a084898611af6b671efb850c3a92a013aa7 | roundconst.py 8ad299147f2e output, kept rows (cited in image-derived-counts.tsv) |
| mv-dry4.tsv | commit d257b0747438, path reloc-A3/roundconst/mv-dry4.tsv, sha256 9462e978b694e40e10f1329fab72a7c76e1b5123fbcb219cb14958cba86c5b86 | roundconst.py 8ad299147f2e output, moved rows (cited in image-derived-counts.tsv) |
| ctrl-dry4.tsv | commit d257b0747438, path reloc-A3/roundconst/ctrl-dry4.tsv, sha256 cd4909fc523eeae0ffe61f37f829960bd2694e98cb357f586c620fbe0eaed529 | roundconst.py 8ad299147f2e output, role-on-role control (cited in image-derived-counts.tsv) |
| build-20261030T193212Z.log | commit d257b0747438, path reloc-A3/logs/build-20261030T193212Z.log, sha256 05ff4a75149a69b148213bb9d045a698a6980954bb3cc6d7ef43ed1600544fce | the image-A untimed build log (cited in measurements.txt) |
| build-20261030T190938Z.log | commit d257b0747438, path reloc-A3/logs/build-20261030T190938Z.log, sha256 057ce2628f77699303234461ca05167ee622498b983e256766ff24c036f497fd | the A5 close-files build log (cited in measurements.txt) |

## Rows superseded by later code commits

The ledgers keep the decision as it was made; these rows no longer describe the proof text.

| rows | was | now | why |
| --- | --- | --- | --- |
| decisions-alreloc-a5c53bb2bed4.tsv:80; image-derived-counts.tsv (AD1g hull pages); roundconst-v2.tsv:6 plant A | AD1g.v:1070 arm `change 6201344 with (1514 * 4096)` (relocated 1512 -> 1514) | the arm is deleted; the first `apply Z_mod_mult` stays | no goal reaches the arm (`repeat split` and `try lia` close every goal first) |
| decisions-alreloc-a5c53bb2bed4.tsv:660-661; codeptr-findings.tsv:108; agreed-sample.txt:3 | AFem.v TOT_range and the conjunct at :208, `TOT <= 127070` (kept as a kit bound) | `TOT <= 127008` | 127008 = 31 + 1 + 31 * DEPOT_MAX from `Definition TOT` (lib/A/AFem.v:100), lo_tr0 (lib/Reusable/YG0f.v:447), DEPOT_MAX = 4096 (lib/Reusable/YG01.v:142); 127070 = 0x1f05e was the donor's relocated .rodata address. The aTOT atom range (AFek.v:36) stays `mkAF 2 131072 0`: the atom denotes TOT (AFem.v:227, :252, proved at :410) and the memory cell takes at most 127008 + 30 + 1 = 127039 at exit (AFem.v:1248, tr_len :123) |
