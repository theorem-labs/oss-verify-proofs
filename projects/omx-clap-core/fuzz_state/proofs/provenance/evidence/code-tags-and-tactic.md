# fuzz_state code-value records: allocator-model labels, a dead tactic arm

## Allocator-model labels are tags 1..14, not addresses

The 14 label literals read from lib/Reusable/YG00.v were replaced by the tags 1..14 with model_tags.py (sha256 74926eaca9e0; its later version 42be517f5220 makes the same rewrite): 201364->1 201376->2 202260->3 209280->4 210276->5 212388->6 213516->7 219184->8 221048->9 222820->10 391236->11 449860->12 460508->13 469488->14. `--check` first: 0 refused, census equal (156 code occurrences in 48 files). After the write, the zero-remaining command
`git grep -n -w -E '201364|201376|202260|209280|210276|212388|213516|219184|221048|222820|391236|449860|460508|469488' -- ':(glob)proofs/omx-clap-core/fuzz_state/**/*.v' ':(glob,exclude)proofs/omx-clap-core/fuzz_state/**/provenance/**'`
prints 19 lines (26 occurrences), all inside comments; 0 code lines.

## Dead second arm with a stale page count

lib/A/AD1g.v:1071 and lib/B/YD1g.v:1069 (shipped tree): `apply Z_mod_mult || (change 6213632 with (1482 * 4096); apply Z_mod_mult)` -> `apply Z_mod_mult` (the first arm is the one that runs; 1482 was the donor's page count). After the change, over the whole unit: `git grep -nE 'change [0-9]+ with \([0-9]+ \* 4096\); apply Z_mod_mult'` = 0 lines and `git grep -n '1482 \* 4096'` = 0 lines.

