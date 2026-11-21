# How the binaries of `zlib/checksum_fuzzer` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `port/` (the OSS Verify port's files for the project and the manifest its `oss-verify check --twice` wrote, less its host keys and the local ids of its docker images, and with the full path in the toolchain image of each file its uninstrumented lists name, from the same run's link records) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/madler/zlib at `99623ef7097352da7993ba614161fd6a311e046e` (1.4) |
| OSS-Fuzz project | https://github.com/google/oss-fuzz `projects/zlib` at `bd2ce21991a9` |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/checksum_fuzzer.c` from https://github.com/google/oss-fuzz `projects/zlib/checksum_fuzzer.c` at `fadbcdfb9e96`; unmodified; licence Apache-2.0 |
| Port | theorem-labs/oss-verify `projects/zlib` at `23e806fe4e4217abcc7fab4419f665f5277a602c`; archive `zlib-port.tar.zst` (sha256 `14f04792d8797c4e96dd7a7326100e52ae4a0dddb340cba86124f09c457c87c0`) |
| Build system | cmake (projects/zlib/build.sh of the port: oft_build_cmake) |
| Patches | `zlib-checksum_fuzzer.0001-inflate-memerr-totals.patch` (the harness of checksum_fuzzer), `zlib-gzio_fuzzer.0001-inflate-memerr-totals.patch` (the harness of gzio_fuzzer), `zlib-gzio_fuzzer.0002-gzseek-after-pushback.patch` (the harness of gzio_fuzzer), `zlib-compress_fuzzer.0001-oss-fuzz-16582.patch` (the harness of compress_fuzzer), `zlib-gzio_fuzzer.0003-oss-fuzz-16316.patch` (the harness of gzio_fuzzer), `zlib-gzio_fuzzer.0004-oss-fuzz-16411.patch` (the harness of gzio_fuzzer), `zlib-minigzip_fuzzer.0002-oss-fuzz-16428.patch` (the harness of minigzip_fuzzer), `zlib-minigzip_fuzzer.0003-oss-fuzz-16429.patch` (the harness of minigzip_fuzzer), as the port's `series` lists them (`port.patches`) |
| Compilers | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Source code | `zlib-src.tar.zst`, `zlib-src.MANIFEST.tsv`, `zlib-port.tar.zst` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `checksum_fuzzer.plain` | 52952 | `abc3576b38eb0fc9760857226677d99b5d66abee1b84c42deb4781f400479c89` |
| ubsan | `checksum_fuzzer.ubsan` | 53600 | `866ba01cec70255526f6761b7096d5d68cc88bc4db2ca390b9ea36e03c7f3cbe` |
| asan | `checksum_fuzzer.asan` | 571720 | `62426eb4a7377f606239b3c81835781ee47d51fa8908f157b576d8feb25b3bc0` |
| asan-ubsan | `checksum_fuzzer.asan-ubsan` | 571992 | `dc471b184b729329f65a81fbd1a728c929bb01adae0780df3b9c3c90226980c6` |

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

- the port's second build (port/manifest.yaml, rebuild: kind same-host, result identical) gave all 44 binaries of the 11 harnesses the SHA-256s of the first, these four among them

## The proofs' licence

0 of this entry point's 0 library files carry Anthropic's licence header: they are under Apache-2.0 OR MIT, at the recipient's option: the licence texts and the notice are `LICENSES/anthropic-proofs-LICENSE`, `LICENSES/anthropic-proofs-LICENSE-MIT` and `LICENSES/anthropic-proofs-NOTICE` in the repository's top directory; each changed file carries one line under its licence header saying so, and the 0 that are byte for byte their source carry none. The other files were written for this repository, and they are under the repository's MIT licence (`LICENSE`).
