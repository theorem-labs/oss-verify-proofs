# Inventory: which files of the core came from port_core, with which inputs, and the route of the re-check

Unit: plugin-hostd/fuzz_command. Checked tree: plugin-hostd/fuzz_command tree (git tree 86ee7833f146; internal record) (the unit's series head), which holds the merged tree
781f46bc05cd plus comment and proof commits (75 lib/A/A*.v, 82 lib/B/Y*.v, 2 lib/A/Rt, 22 lib/B/Rt and 5 lib/Reusable
files differ from 781f46bc05cd; `inventory.tsv` gives both sha256 per file). The merged tree's history holds the unit as
one commit, so the runs below were found from the working notes of the lanes that made the core, and identified by the
hashes of their inputs and outputs.

`inventory.tsv` (written by `scripts/mk_inventory.py`) lists every `.v` file directly in lib/A (A*.v), lib/B (Y*.v),
lib/A/Rt, lib/B/Rt and lib/Reusable (for lib/Reusable 561 of its 565 `.v` files: its 4 files in the sub-directories R/
and Z/, all 4 added before the port, are not listed) with its set, its route, its sha256 at the checked commit and at
781f46bc05cd, the sha256 of the run output it came from (where a run made it) and the provenance line of its own header.

## The port_core runs

| set | tool | inputs | outputs in this tree | inputs re-runnable? |
|---|---|---|---|---|
| A1, the core run | port_core.py, untagged copy, git blob bebe64d6f526 (sha256 4c73f44961b0) | donor proofs/cgif/cgif_file_fuzzer/lib at c8557374ad2e; file list of 377 A/ files (sha256 78c62f014f0c); old image cgif_file_fuzzer.asan 7093581aab04 with old-program block 80490:86bcc; target image fuzz_command.asan c0661b96b5bd with its function names (its tables name our symbols; the d9e0 re-run uses the unstripped twin 68db792d5fa7); renames TfibSyms=CmdSyms, TfibB=CmdB, TfibB_syms=CmdB_syms, TfibB_ok=CmdB_ok; no --override row | 375 lib/A/A*.v (the run also wrote A/AF0r.v and A/AF0s.v, which this tree does not hold: their walks moved to lib/A/Rt); 7 of the 375 were regenerated later from image A by the unit's generators (AB01, AB03, AF0m, AD2j, AE3i, ACej, AB1w) | YES. Donor identified: all 377 staged files equal the donor files at c8557374ad2e under the module-path change and the four renames (byte for byte, 377 of 377). Images and file list present with the sha256 above. The run's own output (stage-out, 377 files) is kept, so the new tool's output can be compared with it. |
| A2, the runtime-intrinsics run | the same blob bebe64d6f526 | the same donor, images and renames; 14 A/ files (AE2q, AE2r, AE6k .. AE6v; list sha256 26c0a89fc046); 48 hand values applied after the run (table sha256 051708bebbfa) | 14 lib/A/A*.v | YES, as A1; its stage-out (14 files) is kept. |
| run 1, the first core run | an earlier untagged port_core copy, not identifiable (it ran before the copy of record above was written) | the same donor and images; 609-line file list (sha256 389e8e984b69) | its 377 A/ outputs were replaced by run A1; its 121 lib/Reusable copies: 90 are in this tree byte for byte, 31 were edited later; 107 lib/Reusable files it kept were already in the target | NO (tool version lost) |

Other files of the core that a relocation made, and how:

| set | how it was made | files |
|---|---|---|
| image B core, lib/B/Y*.v | not by port_core: derived from this unit's image-A files by a relay tool (a2b.py sha256 3a7e74c983e1 + relay.py 7843a38021b5, hand overrides table 1b6fb2df3df9; its own gates cellscan.py 38796ee773f8 and stalescan.py 0bf89609cf54), values read again from fuzz_command.asan-ubsan bbe55d24d096; the B start-up set (YB*) collected for image B | 357 relayed twins, 5 of them regenerated from image B; 26 start-up / other files |
| lib/A/Rt relocations | runtime files whose header names a donor file and moved addresses (cgif AE7d/AE7e/AE7f -> Strnlen*, AE38 -> RtSIstrlen, AFfm -> RtSM7Fm, AE37 -> RtDtorExit; fuzz_grant's Rt/Strcmp* -> RtStrcmp*; others) | 15 |
| lib/B/Rt | B twins of lib/A/Rt files (reloc_rt.py over the relay tool) and donor relocations | 22 + 22 |
| lib/Reusable | 425 of its 565 `.v` files were added before the port (2026-10-27 in 84b1ffc6d7d, the plain build's proofs; 421 directly in lib/Reusable, 4 in its sub-directories R/ and Z/) and are not port_core outputs; the other 140 came with the ASan core (2026-10-30 in 6b559e1f018): run 1's copies, files run 1 kept, other copies of the donor's shared model files; numerals unchanged except the image values set by hand (image end 0x606000 in YCbq, YCe5, YG0f) | 140 files added by the port; 405 of all 565 have a donor file at the same path (401 of the 561 that `inventory.tsv` lists) |

## Route per set (the method owner's ruling of 2026-10-30 19:10Z, amended 19:13Z)

| set | route | where |
|---|---|---|
| A1, A2 | (1) the pin-keyed value gate port_addr_check 3d2eee813cce over lib/A/A*.v, check of record, controls firing; (2) port_core d9e0589898fd --dry on the same inputs, its stage-out compared by sha256 with the run's own stage-out and with this tree, every differing row classified | `gate/`, `d9e0/` |
| image B core | value gate over lib/B/Y*.v (check of record) and the relay view (this unit's lib/A -> lib/B) | `gate/` |
| run 1 outputs, lib/Reusable, lib/A/Rt and lib/B/Rt relocations | value gate on the donor pairing | `rt-reusable/` |
| all sets | the roundconst gate v2 32b39f3b34e9 on the value gate's full rows; a recompute from our images of every image-derived count; the GOT-cell check; codeptr 12348302dfd2 on the files it covers; the donor symbol + offset sweep | `roundconst/`, `counts/`, `got/`, `codeptr/`, `sweep/` |
