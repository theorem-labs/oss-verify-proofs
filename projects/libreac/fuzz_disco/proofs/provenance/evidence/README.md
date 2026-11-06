# libreac/fuzz_disco: evidence

Each subdirectory is one slice of the evidence for this unit's proofs; its MANIFEST names every file of the slice with its sha256 and its role, and its run.sh, where there is one, re-runs it. MANIFEST in this directory names every file of the tree.

Slice names: `A` is image A, the ASan build `fuzz_disco.asan` (its proofs are under lib/A/); `Y` is image B, the ASan+UBSan build
`fuzz_disco.asan-ubsan` (its proofs are the files of lib/Reusable/ whose names begin with `Y`). `core-A` / `core-Y`: the runtime and
allocator core of each image; `startup-A` / `startup-Y`: the start-up data of each image; `image-facts`: program listings and
read-only ranges of both images; `g9-gxa`: gate 9 (same code up to relocation) for the GXA layer, the relocated formatted-output and
memory-interceptor proofs (`fm_snprintf_gxa` and its callees); `yh03`: the address tables lib/Reusable/YH03.v and
lib/U/Reusable/YH03.v of the plain and ubsan builds; `gates-A` / `gates-Y`: gate records re-run against each image's pin;
`gates-tree`: whole-tree records.

The commit ids in the run records of this directory (TSV records, logs and tool output, kept byte for byte) name internal working commits; they are kept in an internal record and are not reachable from the public history.
