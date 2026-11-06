# Image A's relocation (asan build): what is in this directory and what is kept in the series' internal record

Route letters in the file names below name relocation RUNS, not people or lanes: F6 is the run that made image A's core commit 1, and C3, C4, C5, C6, C7, C8a and C8 are the runs that made core commits 3, 4, 5, 6, 7, 8a and 8 (the record's INVOCATIONS.txt has one block per run, headed F6, F7 (commit 2), C3S, C4R, C5R, C6R, C7R, C8aR and the commit-8 run).

The image-A core lane made this directory. The core of reac-pw/fuzz_segconf image A, lib/A, was relocated from plugin-hostd/fuzz_command, released at ossv/recipes 501c0d516c69. The tool was port_core 7a74e72920e6 (commit b25bb893cdb, tools/pg-reloc/7a74e72920e6, the registered tag).

## In this directory
- `donor-table.tsv`: the donor of each relocated lib/A file and why. This is the lane's record, not a tool input, so its text names roles and commit shas.
- `files-C3.txt`, `files-C4.txt`, `files-C5.txt`, `files-C6.txt`, `files-C7.txt`, `files-C8a.txt`, `files-C8.txt`, `files-F6.txt`: each run's `--files` list, byte for byte as the runs read them.
- `atom-ranges-AFek.tsv`: lib/A/AFek.v's DF_fixed atom ranges (core commit 7) checked against the unit's own stated ranges, both ends and the alignment per atom: the core lane's check of that file; `atom-ranges-AFek-c8.tsv`, the same check at core commit 8.
- `REGEN-STARTUP.txt`: the generated start-up files regenerated in core commit 8, the changed inputs and the controls, citing the scripts kept in the internal record by commit and path.

## Kept in the series' internal record, not in this tree
These files are run inputs or as-run text. Their bytes are the evidence, so they are kept, byte for byte, on the series' internal record ref, at commit c175c43cd063000b5a5f0e7932c730e55217c577, under `reloc-A3seg/`, with the sha256 below, rather than reworded (that commit holds every file below; commits 1aa71a935196bb9c6369e6bacd3862d1bf7e37b1, e5f9ba36d67a2ad88d52314013aa8a1b3d7b6611 and e190098a9b3155149c3e4a543826ab6cd8f68087 hold the versions before core commits 8, 8a and 7). The pull request body names that ref. An `--override` TSV or a `--patch` file is port_core's input: rewording its reason column would change a run input, and a reworded input is no longer the input that produced the tree. The run script, the invocation log and the scan script and its output are as-run text.

| file | sha256 | what it is |
|---|---|---|
| `run.sh` | 6e44c3f337e0829793b99e9e15599877f136b62cb6263d96e5e273aef1567d65 | the command line each route ran |
| `INVOCATIONS.txt` | fc8a644af5af259ed79c5fe868b2b502919bb825a1934b289a8a370d8130a60b | the runs of record, commit by commit (F6, C3, C4, C5, C6, C7, C8a, C8), with the tool versions line |
| `overrides-command.tsv` | d693a7f3e7a99396432c1cb8ad6a8028987ea41d4e5669782cd71062fd5a52d2 | `--override` rows of the command route, each decided against fuzz_segconf.asan's bytes, with its reason |
| `overrides-C4.tsv` | 07cd372c5081b625f61058d85e0dbf8b0363020ea56a5dfc8fcc57d5ef068a37 | `--override` rows of commit 4 |
| `overrides-C6.tsv` | d55c4b9994e51b856a96f64ea43329d017172d864e27f560133f107ffc54a9c7 | `--override` rows of commit 6 |
| `overrides-C7.tsv` | ef2111edd4f4c1c94282d72dc7ee61ddc4c60ca78c996976fca0f82c5139e495 | `--override` rows of commit 7 |
| `overrides-C8a.tsv` | 4e53d335ad2db179ef33da61287f69c303f4f8ee727a1a6d33b91a4a79e275ad | `--override` rows of commit 8a |
| `overrides-C8.tsv` | 8103e2f271b2095295271897e6a9c4722bc530fd7e12e94be94c4415dbd28359 | `--override` rows of commit 8 |
| `patches-command.patch` | af6333c74ae568e09e9a4c86e8ff1ec093583ea46acbeed38ada95cc49aee747 | `--patch` hunks of the command route |
| `patches-command-c3.patch` | 22501150880f6f48d7f9671640c3692a19e5809256e7b5be6143a88d41f32490 | `--patch` hunks of commit 3 |
| `patches-C4.patch` | fb20e7e26d8f63c1cf439191bfc0dd17648ab7dfe0d7d06529222c678c48d46c | `--patch` hunks of commit 4 |
| `patches-C7.patch` | 619b7a4ac6d5f9f65654b8b3240edaddecad6fb60b4fe29b32523ba969ed8269 | `--patch` hunks of commit 7 |
| `patches-C8.patch` | 375bf3b510db3c96d0d99f7477ba651e5ba234b8637e926f575a434f066e3671 | `--patch` hunks of commit 8 |
| `romscan/romranges_seg.py` | 11831fb9aebeba2add6f1e548a33aead93d424142158af4ded3d8b1487979e10 | the read-only-range scan of the image (fuzz_command's ROM-range scanner of record, with segconf's image and walk lists) |
| `romscan/romranges_seg.out` | fe1e7b661f0c0ea807c1f4765db355afb977a35ca9d75a6cb573ec94d1eab340 | its output, from which lib/A/Rt/RtDefs.v's RT_ROM_RANGES table was regenerated |

A grep of these records for `port_core_refused_` finds the marker only on REMOVED (`-`) lines: `port_core_refused_3fdb8` and `port_core_refused_40244` at patches-C7.patch:87 and patches-command.patch:532; `port_core_refused_5e3c40`, `_5e3c43`, `_5e3c80`, `_a7088` and `_9ef40` at patches-C8.patch:454, 529, 538, 539 and patches-command.patch:990, 1065, 1074, 1075. Those hunks delete port_core's refusal markers from the relocated text, so the names are evidence of the fix, not a refusal left in the proof tree.

The binaries the runs read, by sha256:
- fuzz_command.asan, the donor's pin: c0661b96b5bd458ba489f91a4693b6a8acd6c0f74d5e20798ed78e937f858bb9
- fuzz_scene.asan: 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026
- fuzz_decode.asan: 5973b76807d8d2e14b82dc6afde70a2c882923658406aeca43681719cb4e8036
- fuzz_knock.asan: 61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118
- fuzz_segconf.asan, the target's pin: 48c5355bdacbc5ba2e0a9ff843627969cb5d2913316654369904b549fc904ef8
