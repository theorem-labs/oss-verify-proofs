# How the binaries of `boost-beast/http_request` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `recipe/` (`recipe/MANIFEST.tsv` lists them) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/boostorg/boost at `4daa5786d7c5dad39df0429cb078165b3134a06f` |
| OSS-Fuzz project | https://github.com/google/oss-fuzz `projects/boost-beast` at `bd2ce21991a9` |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | not recorded from https://github.com/boostorg/boost `libs/beast/test/fuzz/http_request.cpp` at `4daa5786d7c5`; unmodified; licence BSL-1.0 |
| Recipe | `recipe.tar.zst` of release `v2026.10.0-src` (sha256 `0339bf3221b15cd39513d46abe99062bac9cce874ed7ba5947753f75b6219ae5`), target `boost-beast` |
| Build system | cmake |
| Patches to the library | none |
| Compiler | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Static AddressSanitizer | https://github.com/theorem-labs/static-asan at `b05061352064fa2be1813ac5429149f3de5f057d` (the published source of the compiler image's static AddressSanitizer: its toolchain/ and patches/ are those the image was built from, with comments and patch descriptions edited for publication (toolchain-src.tar.zst holds this commit). Building it gives the image's libclang_rt.builtins.a and musl libc.a byte for byte; its libclang_rt.asan.a and asan_cxx.a differ from the image's only in DWARF line tables, which --strip-all removes from the binaries) |
| Source code | not required by the licences; the upstream source is `boost-beast-src.tar.zst` of release `v2026.10.0-src` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `http_request.plain` | 451128 | `ee1ab1db14ab9038dc12e038cec22ce7457ed46ff2bee387c5ca4f890f5c6e92` |
| asan | `http_request.asan` | 1127528 | `136b42a5e2c6e19859bc9f48488d3c2c4ff8d832d65ca5ea8dc687642d67f558` |
| ubsan | `http_request.ubsan` | 468320 | `8509479229b8e96781911e79d2e68a15eed815c8e649f8c181b833b655ac5f25` |
| asan-ubsan | `http_request.asan-ubsan` | 1144744 | `620298a9edf2a53c792e6e76fafc224efb20879bb224a66714d6d56523677647` |

## Licences

| component | licence | texts |
|---|---|---|
| Boost (superproject 4daa5786) | BSL-1.0 | LICENSES/boost-LICENSE_1_0.txt |
| musl libc (static) | MIT | LICENSES/musl-COPYRIGHT |
| LLVM runtimes: compiler-rt builtins; in ASan builds the sanitizer runtime and libunwind; libc++/libc++abi in C++ programs | Apache-2.0 WITH LLVM-exception | LICENSES/llvm-compiler-rt-LICENSE.TXT, LICENSES/llvm-libunwind-LICENSE.TXT, LICENSES/llvm-libcxx-LICENSE.TXT, LICENSES/llvm-libcxxabi-LICENSE.TXT |
| static-asan patches compiled into the ASan runtime and musl | MIT | LICENSES/static-asan-LICENSE |
| Theorem Labs file-input driver and build recipe (recipe/src/, recipe/targets/*/plugin.c) | MIT | LICENSES/oss-fuzz-theorems-LICENSE |

## Rebuild

- rebuilt from this recipe and the source assets on a separate machine: plain identical, asan identical, ubsan identical, asan-ubsan identical

## The proofs' licence

The proof files of this entry point were made from final-anthropic-opensource-formal-verification-proofs-package-2026-10-21 (sha256 4c6c152f61ce538e439b9d2adef439f4dbe1a2d446767d84ac7c3946d7c6687a), libraries/boost-beast/proofs/submission-1, libraries/bzip2/proofs/submission-1, libraries/openssl-a/proofs/submission-2, libraries/jsoncons/proofs/submission-4, libraries/msgpack-c/proofs/submission-1, libraries/jsoncons/proofs/submission-6, libraries/jsoncons/proofs/submission-1 and libraries/varnish/proofs/submission-1 and are under Apache-2.0 OR MIT, at the recipient's option: the licence texts and the notice are `LICENSES/anthropic-proofs-LICENSE`, `LICENSES/anthropic-proofs-LICENSE-MIT` and `LICENSES/anthropic-proofs-NOTICE` in the repository's top directory; each changed file carries one line under its licence header saying so. The proofs of asan_agreement_decidable, asan_disagrees_at_most, asan_ubsan_agreement_decidable, asan_ubsan_disagrees_at_most, ubsan_agreement_decidable and ubsan_disagrees_at_most were written in this repository: they use lib/ConstAccept.v, a program that accepts every input, to decide where the builds agree and to bound their disagreement at 0.

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
recipe/targets/boost-beast/pin:41: LIB_CFLAGS=""
recipe/targets/boost-beast/pin:53: OFT_HARNESS_CFLAGS="$(for d in "$BUILDDIR"/src/libs/*/include "$BUILDDIR"/src/libs/*/*/include; do [ -d "$d" ] && printf "%s" "-isystem $d "; done) -H"
```

