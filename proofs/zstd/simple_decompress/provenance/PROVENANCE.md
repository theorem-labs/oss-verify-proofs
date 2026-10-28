# How the binaries of `zstd/simple_decompress` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `recipe/` (`recipe/MANIFEST.tsv` lists them) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/facebook/zstd at `82d322c4973d9e2968d94047a40892bc6d9a9bdf` |
| OSS-Fuzz project | https://github.com/google/oss-fuzz `projects/zstd` at `bd2ce21991a9` |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/simple_decompress.c` from https://github.com/facebook/zstd `tests/fuzz/simple_decompress.c` at `82d322c4973d`; unmodified; licence BSD-3-Clause OR GPL-2.0-only |
| Recipe | `recipe.tar.zst` of release `v2026.10.0-src` (sha256 `0339bf3221b15cd39513d46abe99062bac9cce874ed7ba5947753f75b6219ae5`), target `zstd-simple_decompress` |
| Build system | cmake |
| Patches to the library | none |
| Compiler | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Static AddressSanitizer | https://github.com/theorem-labs/static-asan at `b05061352064fa2be1813ac5429149f3de5f057d` (the published source of the compiler image's static AddressSanitizer: its toolchain/ and patches/ are those the image was built from, with comments and patch descriptions edited for publication (toolchain-src.tar.zst holds this commit). Building it gives the image's libclang_rt.builtins.a and musl libc.a byte for byte; its libclang_rt.asan.a and asan_cxx.a differ from the image's only in DWARF line tables, which --strip-all removes from the binaries) |
| Source code | https://github.com/theorem-labs/oss-verify-proofs/releases/tag/v2026.10.0-src: `zstd-src.tar.zst`, `zstd-src.MANIFEST.tsv`; https://github.com/theorem-labs/oss-verify-proofs/releases/tag/v2026.10.0-src: `recipe.tar.zst`; https://github.com/theorem-labs/oss-verify-proofs/releases/tag/sources-v1: `toolchain-src.tar.zst` (sha256 fc550b7b1a49c82e52d4fa8d042a275900e8871b283575571fc0331cfed028d5) |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `simple_decompress.plain` | 128144 | `915a2df41813d9b88edf3031572374cbd2ce35f51e6ce468dd861581d0957259` |
| asan | `simple_decompress.asan` | 760920 | `2fe237f03d25d3b87f98345d47c9ec85b7dda4e03df09d22737e70bc1c2011d6` |
| ubsan | `simple_decompress.ubsan` | 153040 | `3fbf52afb023d60725cf556e72be258989fc613304af31cb10cc174eab5a8d33` |
| asan-ubsan | `simple_decompress.asan-ubsan` | 778808 | `66560e8fa69ce14e0f18a516d85955ab7edf845aa3771b4622827854b180501d` |

## Licences

| component | licence | texts |
|---|---|---|
| Zstandard | BSD-3-Clause OR GPL-2.0-only | LICENSES/zstd-LICENSE, LICENSES/zstd-COPYING |
| musl libc (static) | MIT | LICENSES/musl-COPYRIGHT |
| LLVM runtimes: compiler-rt builtins; in ASan builds the sanitizer runtime and libunwind; libc++/libc++abi in C++ programs | Apache-2.0 WITH LLVM-exception | LICENSES/llvm-compiler-rt-LICENSE.TXT, LICENSES/llvm-libunwind-LICENSE.TXT, LICENSES/llvm-libcxx-LICENSE.TXT, LICENSES/llvm-libcxxabi-LICENSE.TXT |
| static-asan patches compiled into the ASan runtime and musl | MIT | LICENSES/static-asan-LICENSE |
| Theorem Labs file-input driver and build recipe (recipe/src/, recipe/targets/*/plugin.c) | MIT | LICENSES/oss-fuzz-theorems-LICENSE |

## Rebuild

- rebuilt from this recipe and the source assets on a separate machine: plain identical, asan identical, ubsan identical, asan-ubsan identical

## The proofs' licence

The proof files of this entry point were made from final-anthropic-opensource-formal-verification-proofs-package-2026-10-21 (sha256 4c6c152f61ce538e439b9d2adef439f4dbe1a2d446767d84ac7c3946d7c6687a), libraries/zstd/proofs/submission-1, libraries/zstd/model-editions/allocation-edition.patch, libraries/jsoncons/proofs/submission-7, libraries/openssl-b/proofs/submission-1 and libraries/openssl-a/proofs/submission-1 and are under Apache-2.0 OR MIT, at the recipient's option: the licence texts and the notice are `LICENSES/anthropic-proofs-LICENSE`, `LICENSES/anthropic-proofs-LICENSE-MIT` and `LICENSES/anthropic-proofs-NOTICE` in the repository's top directory; each changed file carries one line under its licence header saying so. The proofs of asan_agrees and ubsan_agrees were written in this repository: the package has no complete proof of them.

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
recipe/targets/zstd-simple_decompress/pin:40: LIB_CFLAGS=""
```

