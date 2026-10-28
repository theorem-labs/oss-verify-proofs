# How the binaries of `jsoncons/fuzz_json_cursor` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `recipe/` (`recipe/MANIFEST.tsv` lists them) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/danielaparker/jsoncons at `af497a1c1ea9043f4ad8d799617b7d00d6676153` |
| OSS-Fuzz project | https://github.com/google/oss-fuzz `projects/jsoncons` at `bd2ce21991a9` |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/fuzz_json_cursor.cpp` from https://github.com/danielaparker/jsoncons `fuzzers/fuzz_json_cursor.cpp` at `af497a1c1ea9`; unmodified; licence BSL-1.0 |
| Recipe | `recipe.tar.zst` of release `v2026.10.0-src` (sha256 `0339bf3221b15cd39513d46abe99062bac9cce874ed7ba5947753f75b6219ae5`), target `jsoncons-fuzz_json_cursor` |
| Build system | custom |
| Patches to the library | none |
| Compiler | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Static AddressSanitizer | https://github.com/theorem-labs/static-asan at `b05061352064fa2be1813ac5429149f3de5f057d` (the published source of the compiler image's static AddressSanitizer: its toolchain/ and patches/ are those the image was built from, with comments and patch descriptions edited for publication (toolchain-src.tar.zst holds this commit). Building it gives the image's libclang_rt.builtins.a and musl libc.a byte for byte; its libclang_rt.asan.a and asan_cxx.a differ from the image's only in DWARF line tables, which --strip-all removes from the binaries) |
| Source code | not required by the licences; the upstream source is `jsoncons-src.tar.zst` of release `v2026.10.0-src` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `fuzz_json_cursor.plain` | 722160 | `5d51157cdd8b5d3b57e12809abb2313b01a4c5b13f62b44d4e10cefc00f396fb` |
| asan | `fuzz_json_cursor.asan` | 1337752 | `b10619d64077178941cc940f9fb007e23fd11671ae47908413c90b7b3d7c7a3f` |
| ubsan | `fuzz_json_cursor.ubsan` | 729920 | `4a4ec58f139ede2e32ed06316ac93d00c5ed010e7d4ea4d84e50b538498766c1` |
| asan-ubsan | `fuzz_json_cursor.asan-ubsan` | 1342680 | `ced784bdd6c1fd5c344b24cd103543bcfdd510fe4e3a4e1372c4624bc1314b8a` |

## Licences

| component | licence | texts |
|---|---|---|
| jsoncons | BSL-1.0 | LICENSES/jsoncons-LICENSE, LICENSES/jsoncons-unicode-ConvertUTF-notice.txt |
| Grisu3 (Florian Loitsch), in jsoncons include/jsoncons/detail/grisu3.hpp | MIT | LICENSES/jsoncons-grisu3-MIT-notice.txt |
| decode_half, adapted from RFC 7049 Appendix D, in jsoncons include/jsoncons/config/compiler_support.hpp | BSD-3-Clause | LICENSES/jsoncons-rfc7049-decode_half-notice.txt |
| musl libc (static) | MIT | LICENSES/musl-COPYRIGHT |
| LLVM runtimes: compiler-rt builtins; in ASan builds the sanitizer runtime and libunwind; libc++/libc++abi in C++ programs | Apache-2.0 WITH LLVM-exception | LICENSES/llvm-compiler-rt-LICENSE.TXT, LICENSES/llvm-libunwind-LICENSE.TXT, LICENSES/llvm-libcxx-LICENSE.TXT, LICENSES/llvm-libcxxabi-LICENSE.TXT |
| static-asan patches compiled into the ASan runtime and musl | MIT | LICENSES/static-asan-LICENSE |
| Theorem Labs file-input driver and build recipe (recipe/src/, recipe/targets/*/plugin.c) | MIT | LICENSES/oss-fuzz-theorems-LICENSE |

## Rebuild

- rebuilt from this recipe and the source assets on a separate machine: plain identical, asan identical, ubsan identical, asan-ubsan identical

## The proofs' licence

The proof files of this entry point were made from final-anthropic-opensource-formal-verification-proofs-package-2026-10-21 (sha256 4c6c152f61ce538e439b9d2adef439f4dbe1a2d446767d84ac7c3946d7c6687a), libraries/jsoncons/proofs/submission-3 and are under Apache-2.0 OR MIT, at the recipient's option: the licence texts and the notice are `LICENSES/anthropic-proofs-LICENSE`, `LICENSES/anthropic-proofs-LICENSE-MIT` and `LICENSES/anthropic-proofs-NOTICE` in the repository's top directory; each changed file carries one line under its licence header saying so. The proofs of asan_agreement_decidable, asan_disagrees_at_most, asan_ubsan_agreement_decidable and asan_ubsan_disagrees_at_most were written in this repository: they use lib/ConstAccept.v, a program that accepts every input, to decide where the builds agree and to bound their disagreement at 0. The proofs of ubsan_agrees were written in this repository: the package has no complete proof of them.

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
recipe/targets/jsoncons-fuzz_json_cursor/pin:41: LIB_CFLAGS=""
```

