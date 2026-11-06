# How the binaries of `zlib/checksum_fuzzer` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `recipe/` (`recipe/MANIFEST.tsv` lists them) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/madler/zlib at `51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf` |
| OSS-Fuzz project | https://github.com/google/oss-fuzz `projects/zlib` at `bd2ce21991a9` |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/checksum_fuzzer.c` from https://github.com/google/oss-fuzz `projects/zlib/checksum_fuzzer.c` at `bd2ce21991a9`; unmodified; licence Apache-2.0 |
| Recipe | `recipe.tar.zst` of release `v2026.10.0-src` (sha256 `0339bf3221b15cd39513d46abe99062bac9cce874ed7ba5947753f75b6219ae5`), target `zlib-checksum_fuzzer` |
| Build system | cmake |
| Patches to the library | none |
| Compiler | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Static AddressSanitizer | https://github.com/theorem-labs/static-asan at `b05061352064fa2be1813ac5429149f3de5f057d` (the published source of the compiler image's static AddressSanitizer: its toolchain/ and patches/ are those the image was built from, with comments and patch descriptions edited for publication (toolchain-src.tar.zst holds this commit). Building it gives the image's libclang_rt.builtins.a and musl libc.a byte for byte; its libclang_rt.asan.a and asan_cxx.a differ from the image's only in DWARF line tables, which --strip-all removes from the binaries) |
| Source code | not required by the licences; the upstream source is `zlib-src.tar.zst` of release `v2026.10.0-src` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `checksum_fuzzer.plain` | 52880 | `4f04e95082d3e0baa9d55c72288945d99e64bb7503e39c0e644f4b38a7781af2` |
| asan | `checksum_fuzzer.asan` | 571640 | `60b2389f5b431e1dcd8da721010b42685da22e709d0caf41422eebcccf43084a` |
| ubsan | `checksum_fuzzer.ubsan` | 53520 | `5e80c9b8ebfbbfc3d24e8cc2d4e15d4e1780e758982b2305b85cbf61981fcd63` |
| asan-ubsan | `checksum_fuzzer.asan-ubsan` | 571896 | `dcce41d931b687f7ca2c8fae8b61748ae6e7d870e849ee2b91bb669b7e02d47c` |

## Licences

| component | licence | texts |
|---|---|---|
| zlib | Zlib | LICENSES/zlib-LICENSE |
| OSS-Fuzz harness | Apache-2.0 | LICENSES/oss-fuzz-LICENSE |
| musl libc (static) | MIT | LICENSES/musl-COPYRIGHT |
| LLVM runtimes: compiler-rt builtins; in ASan builds the sanitizer runtime and libunwind; libc++/libc++abi in C++ programs | Apache-2.0 WITH LLVM-exception | LICENSES/llvm-compiler-rt-LICENSE.TXT, LICENSES/llvm-libunwind-LICENSE.TXT, LICENSES/llvm-libcxx-LICENSE.TXT, LICENSES/llvm-libcxxabi-LICENSE.TXT |
| static-asan patches compiled into the ASan runtime and musl | MIT | LICENSES/static-asan-LICENSE |
| Theorem Labs file-input driver and build recipe (recipe/src/, recipe/targets/*/plugin.c) | MIT | LICENSES/oss-fuzz-theorems-LICENSE |

## Rebuild

- rebuilt from this recipe and the source assets on a separate machine: plain identical, asan identical, ubsan identical, asan-ubsan identical

## The proofs' licence

The proof files of this entry point were contributed by Rares Buhai in https://github.com/theorem-labs/oss-verify-proofs/pull/3 (commit 1e39b0fbb06ac789e9fc93f7fe923e9688d79912), written with an AI coding agent. 369 of its 407 library files carry Anthropic's licence header: they were made from the library files of the cgif and Varnish proofs of release 2026.10.0, at commit 98e995d4daced70a0a4aa2c810854b88720735f1 of https://github.com/theorem-labs/oss-verify-proofs (the parent of the contributed commit), and those came from final-anthropic-opensource-formal-verification-proofs-package-2026-10-21 (sha256 4c6c152f61ce538e439b9d2adef439f4dbe1a2d446767d84ac7c3946d7c6687a), and are under Apache-2.0 OR MIT, at the recipient's option: the licence texts and the notice are `LICENSES/anthropic-proofs-LICENSE`, `LICENSES/anthropic-proofs-LICENSE-MIT` and `LICENSES/anthropic-proofs-NOTICE` in the repository's top directory; each changed file carries one line under its licence header saying so, and the 11 that are byte for byte their source carry none. The other files the contributor wrote, and they are under the repository's MIT licence (`LICENSE`).

The proof `plain_halts_may_fail` and the 218 files of `lib/MayFail/` were contributed by Rares Buhai in https://github.com/theorem-labs/oss-verify-proofs/pull/7 (commit c6257b072eba3bea2f5e69b5d26285b662c379cc, whose parent is 1045cd75d83eacd942040cb611c98305f33dea59 of that repository), also written with an AI coding agent. `lib/MayFail/` is a may-fail runtime copy of this harness's own `lib/` files of the same names: 208 of its 218 files carry the Anthropic licence header of the `lib/` file each was made from, with one more line saying what changed in it (197 say only that its module paths changed; 10 also name the may-fail change they carry; `ZImage.v` also names the doc comment it expanded), and the other 10 are MIT files of this repository, under `LICENSE`. The binaries, the recipe and the statement are unchanged, so nothing else of this record changes.

Where the library comes from:

- `lib/Checksum/`: generic proof tactics, the CRC algebra and the frame of the certificates come from the Varnish proof (`proofs/varnish/esi_parse_fuzzer/lib`). `CrcGenInner.v` and `CrcCombinedGenInner.v` are made from its `V_crc32.v` for zlib's instruction layout and register allocation, `CrcLib.v` changes the address of the x2n table, and `BWorld.v` keeps only the generic budget definitions of its `BWorld.v`. `CrcGenModel.v` is a new mathematical model.
- `lib/Reusable/`: generic lemmas and binary-specific certificates from the cgif proof (`proofs/cgif/cgif_file_fuzzer/lib` and `proofs/cgif/cgif_rgb_fuzzer/lib`). Each certificate is checked against zlib's own binary, not taken on trust from cgif's.
- `lib/ZImage.v`: the image setup of the cgif proof, for zlib's plain binary.
- `lib/MayFail/`: the may-fail runtime copy of this harness's `lib/` files of the same names, from pull request 7. Most of its files differ from the `lib/` file they were made from only in their module paths and the layout of their imports; the ones that also change proof content say so in a line under their licence header (e.g. `Reusable/YK0v.v`, which drops the forced-refusal implication for a modelled mmap error).

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
recipe/targets/zlib-checksum_fuzzer/pin:40: LIB_CFLAGS=""
```

