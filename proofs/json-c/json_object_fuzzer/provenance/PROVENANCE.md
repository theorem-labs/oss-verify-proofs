# How the binaries of `json-c/json_object_fuzzer` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `recipe/` (`recipe/MANIFEST.tsv` lists them) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/json-c/json-c at `d17ad9d1863ebbf39993706140bf67847b7add0f` |
| OSS-Fuzz project | https://github.com/google/oss-fuzz `projects/json-c` at `bd2ce21991a9` |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/json_object_fuzzer.cc` from https://github.com/json-c/json-c `fuzz/json_object_fuzzer.cc` at `d17ad9d1863e`; unmodified; licence MIT |
| Recipe | `recipe.tar.zst` of release `v2026.10.0-src` (sha256 `0339bf3221b15cd39513d46abe99062bac9cce874ed7ba5947753f75b6219ae5`), target `json-c-json_object_fuzzer` |
| Build system | cmake |
| Patches to the library | none |
| Compiler | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Static AddressSanitizer | https://github.com/theorem-labs/static-asan at `b05061352064fa2be1813ac5429149f3de5f057d` (the published source of the compiler image's static AddressSanitizer: its toolchain/ and patches/ are those the image was built from, with comments and patch descriptions edited for publication (toolchain-src.tar.zst holds this commit). Building it gives the image's libclang_rt.builtins.a and musl libc.a byte for byte; its libclang_rt.asan.a and asan_cxx.a differ from the image's only in DWARF line tables, which --strip-all removes from the binaries) |
| Source code | not required by the licences; the upstream source is `json-c-src.tar.zst` of release `v2026.10.0-src` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `json_object_fuzzer.plain` | 337856 | `6602e319562d93c51ab98df97b7fdf9de14be19926d8524d6a362c715a071689` |
| asan | `json_object_fuzzer.asan` | 891608 | `0dd699476a57230bab3b47edf64b937d879850d45cc638063e82c12f195fde65` |
| ubsan | `json_object_fuzzer.ubsan` | 345416 | `e7d8fcbde19dab042dd43fba460c3d78545a07575c62d08da0a71bc2be7b3149` |
| asan-ubsan | `json_object_fuzzer.asan-ubsan` | 901560 | `533de695c92b6308a90ae37f5e80dd6c049e2ce3ea3c4588fd49c2cffe8e543d` |

## Licences

| component | licence | texts |
|---|---|---|
| json-c | MIT | LICENSES/json-c-COPYING, LICENSES/json-c-file-copyright-notice.txt |
| lookup3 hashlittle (Bob Jenkins), in json-c linkhash.c | LicenseRef-lookup3-public-domain | LICENSES/json-c-lookup3-notice.txt |
| musl libc (static) | MIT | LICENSES/musl-COPYRIGHT |
| LLVM runtimes: compiler-rt builtins; in ASan builds the sanitizer runtime and libunwind; libc++/libc++abi in C++ programs | Apache-2.0 WITH LLVM-exception | LICENSES/llvm-compiler-rt-LICENSE.TXT, LICENSES/llvm-libunwind-LICENSE.TXT, LICENSES/llvm-libcxx-LICENSE.TXT, LICENSES/llvm-libcxxabi-LICENSE.TXT |
| static-asan patches compiled into the ASan runtime and musl | MIT | LICENSES/static-asan-LICENSE |
| Theorem Labs file-input driver and build recipe (recipe/src/, recipe/targets/*/plugin.c) | MIT | LICENSES/oss-fuzz-theorems-LICENSE |

## Rebuild

- rebuilt from this recipe and the source assets on a separate machine: plain identical, asan identical, ubsan identical, asan-ubsan identical

## The proofs' licence

The proof files of this entry point were made from final-anthropic-opensource-formal-verification-proofs-package-2026-10-21 (sha256 4c6c152f61ce538e439b9d2adef439f4dbe1a2d446767d84ac7c3946d7c6687a), libraries/json-c/proofs/submission-1, libraries/openssl-b/proofs/submission-1 and libraries/pupnp/proofs/submission-1 and are under Apache-2.0 OR MIT, at the recipient's option: the licence texts and the notice are `LICENSES/anthropic-proofs-LICENSE`, `LICENSES/anthropic-proofs-LICENSE-MIT` and `LICENSES/anthropic-proofs-NOTICE` in the repository's top directory; each changed file carries one line under its licence header saying so. The proofs of ubsan_agrees were written in this repository: the package has no complete proof of them.

## Compiler and linker flags

As written in the recipe; a library's own build system adds its flags after these (e.g. CMake Release appends -O3 -DNDEBUG), see the pin and recipes.sh.

```
recipe/tools/build-body.sh:58: OFT_NO_BUILTIN_ALLOC="-fno-builtin-malloc -fno-builtin-calloc -fno-builtin-realloc -fno-builtin-reallocarray -fno-builtin-free -fno-builtin-aligned_alloc -fno-builtin-posix_memalign -fno-builtin-memalign -fno-builtin-valloc -fno-builtin-strdup -fno-builtin-strndup"
recipe/tools/build-body.sh:59: BASE_CFLAGS="-march=rv64g -mabi=lp64d -Os -g -ffunction-sections -fdata-sections -fno-stack-protector -fno-plt -Wdate-time $OFT_NO_BUILTIN_ALLOC"
recipe/tools/build-body.sh:65: SAN=""
recipe/tools/build-body.sh:560: SAN="-fsanitize=address"
recipe/tools/build-body.sh:577: SAN="-fsanitize=address -fsanitize=undefined -fno-sanitize-recover=all -fsanitize-trap=all -fno-sanitize=function"
recipe/tools/build-body.sh:586: SAN="-fsanitize=undefined -fno-sanitize-recover=all -fsanitize-trap=all -fno-sanitize=function"
recipe/tools/build-body.sh:590: SAN=""
recipe/tools/build-body.sh:618: CFLAGS="$BASE_CFLAGS $SAN -fmacro-prefix-map=$LIBROOT/=/work/build/lib/FLAVOUR/"
recipe/tools/build-body.sh:431: 'clang --config=/opt/asan-static/musl.cfg'
recipe/tools/build-body.sh:441: 'clang++ --config=/opt/asan-static/musl.cfg -stdlib=libc++'
recipe/tools/build-body.sh:478: SEALED_CFG=/opt/asan-static/asan-musl-sealed.cfg
recipe/tools/build-body.sh:1019: SILENT_LD=""
recipe/tools/build-body.sh:1021: SILENT_LD="-Wl,--defsym=__sanitizer_silent_reports=1"
recipe/tools/build-body.sh:1027: SILENT_LD=""
recipe/tools/build-body.sh:1049: "$CC" $BASE_CFLAGS -static -no-pie -Wl,--gc-sections ${OFT_STRIP--Wl,--strip-all} \
recipe/tools/build-body.sh:1054: "$CC" $BASE_CFLAGS -static -no-pie -Wl,--gc-sections ${OFT_STRIP--Wl,--strip-all} \
recipe/targets/json-c-json_object_fuzzer/pin:41: LIB_CFLAGS=""
```

