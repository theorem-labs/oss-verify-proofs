# How the binaries of `zlib/zlib_uncompress3_fuzzer` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `port/` (the OSS Verify port's files for the project and the manifest its `oss-verify check --twice` wrote, less its host keys and the local ids of its docker images, and with the full path in the toolchain image of each file its uninstrumented lists name, from the same run's link records) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/madler/zlib at `99623ef7097352da7993ba614161fd6a311e046e` (1.4) |
| OSS-Fuzz project | https://github.com/google/oss-fuzz `projects/zlib` at `bd2ce21991a9` |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/zlib_uncompress3_fuzzer.cc` from https://github.com/google/oss-fuzz `projects/zlib/zlib_uncompress3_fuzzer.cc` at `fadbcdfb9e96`; unmodified; licence Apache-2.0 |
| Port | theorem-labs/oss-verify `projects/zlib` at `23e806fe4e4217abcc7fab4419f665f5277a602c`; archive `zlib-port.tar.zst` (sha256 `14f04792d8797c4e96dd7a7326100e52ae4a0dddb340cba86124f09c457c87c0`) |
| Build system | cmake (projects/zlib/build.sh of the port: oft_build_cmake) |
| Patches | `zlib-checksum_fuzzer.0001-inflate-memerr-totals.patch` (the harness of checksum_fuzzer), `zlib-gzio_fuzzer.0001-inflate-memerr-totals.patch` (the harness of gzio_fuzzer), `zlib-gzio_fuzzer.0002-gzseek-after-pushback.patch` (the harness of gzio_fuzzer), `zlib-compress_fuzzer.0001-oss-fuzz-16582.patch` (the harness of compress_fuzzer), `zlib-gzio_fuzzer.0003-oss-fuzz-16316.patch` (the harness of gzio_fuzzer), `zlib-gzio_fuzzer.0004-oss-fuzz-16411.patch` (the harness of gzio_fuzzer), `zlib-minigzip_fuzzer.0002-oss-fuzz-16428.patch` (the harness of minigzip_fuzzer), `zlib-minigzip_fuzzer.0003-oss-fuzz-16429.patch` (the harness of minigzip_fuzzer), as the port's `series` lists them (`port.patches`) |
| Compilers | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Source code | `zlib-src.tar.zst`, `zlib-src.MANIFEST.tsv`, `zlib-port.tar.zst` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `zlib_uncompress3_fuzzer.plain` | 66496 | `e6d12458a570ee80f478a4f70f9524150bc0af59c3dcea16d41e03c3a3bab63b` |
| ubsan | `zlib_uncompress3_fuzzer.ubsan` | 71384 | `0c9724f87f4ffc95c2c4205e7394429ba3aa1a94cfa66a24339212f97ef55e59` |
| asan | `zlib_uncompress3_fuzzer.asan` | 797032 | `5e190bd28da1f0d5d813b1e21807abbc93f3871581f4ce54708f4f91efeaf399` |
| asan-ubsan | `zlib_uncompress3_fuzzer.asan-ubsan` | 802456 | `9655c7cfc427eccd3a286f1b6a00071977d28adb1e578d8df2060df83a9d319e` |

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

3430 of this entry point's 3991 library files carry Anthropic's licence header: they are under Apache-2.0 OR MIT, at the recipient's option: the licence texts and the notice are `LICENSES/anthropic-proofs-LICENSE`, `LICENSES/anthropic-proofs-LICENSE-MIT` and `LICENSES/anthropic-proofs-NOTICE` in the repository's top directory; each changed file carries one line under its licence header saying so, and the 0 that are byte for byte their source carry none. The proof files whose first line says that they state or restate instruction words of the task's compiled program carry that line in place of a licence header: those instruction words are object code of the components in the Licences table above, and the licences of those components apply to them (`LICENSES/anthropic-proofs-NOTICE`, class 3). The other files were written for this repository, and they are under the repository's MIT licence (`LICENSE`).
