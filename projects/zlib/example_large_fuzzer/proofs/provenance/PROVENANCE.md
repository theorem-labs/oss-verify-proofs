# How the binaries of `zlib/example_large_fuzzer` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `port/` (the OSS Verify port's files for the project and the manifest its `oss-verify check --twice` wrote, less its host keys and the local ids of its docker images, and with the full path in the toolchain image of each file its uninstrumented lists name, from the same run's link records) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/madler/zlib at `99623ef7097352da7993ba614161fd6a311e046e` (1.4) |
| OSS-Fuzz project | https://github.com/google/oss-fuzz `projects/zlib` at `bd2ce21991a9` |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/example_large_fuzzer.c` from https://github.com/google/oss-fuzz `projects/zlib/example_large_fuzzer.c` at `fadbcdfb9e96`; unmodified; licence Apache-2.0 |
| Port | theorem-labs/oss-verify `projects/zlib` at `23e806fe4e4217abcc7fab4419f665f5277a602c`; archive `zlib-port.tar.zst` (sha256 `14f04792d8797c4e96dd7a7326100e52ae4a0dddb340cba86124f09c457c87c0`) |
| Build system | cmake (projects/zlib/build.sh of the port: oft_build_cmake) |
| Patches | `zlib-checksum_fuzzer.0001-inflate-memerr-totals.patch` (the harness of checksum_fuzzer), `zlib-gzio_fuzzer.0001-inflate-memerr-totals.patch` (the harness of gzio_fuzzer), `zlib-gzio_fuzzer.0002-gzseek-after-pushback.patch` (the harness of gzio_fuzzer), `zlib-compress_fuzzer.0001-oss-fuzz-16582.patch` (the harness of compress_fuzzer), `zlib-gzio_fuzzer.0003-oss-fuzz-16316.patch` (the harness of gzio_fuzzer), `zlib-gzio_fuzzer.0004-oss-fuzz-16411.patch` (the harness of gzio_fuzzer), `zlib-minigzip_fuzzer.0002-oss-fuzz-16428.patch` (the harness of minigzip_fuzzer), `zlib-minigzip_fuzzer.0003-oss-fuzz-16429.patch` (the harness of minigzip_fuzzer), as the port's `series` lists them (`port.patches`) |
| Compilers | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Source code | `zlib-src.tar.zst`, `zlib-src.MANIFEST.tsv`, `zlib-port.tar.zst` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `example_large_fuzzer.plain` | 97144 | `bcd66bcb935c115db45af21ece9341796b945bdb91ae0c3c1e6fadc560bf20a7` |
| ubsan | `example_large_fuzzer.ubsan` | 109464 | `0874dae378a1e926c028ba964259847f8b4a115c6dc1829aeed6e44c78016a9c` |
| asan | `example_large_fuzzer.asan` | 715736 | `0078b0aa21ff1f2365fd26f4f0d42b0608156f2942fc5ef8402d88d87f02350d` |
| asan-ubsan | `example_large_fuzzer.asan-ubsan` | 726712 | `8c0ee648d88b5bbc5ec93f902c29b81c824c5b011a5743834bcabf9cc5b48534` |

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

1493 of this entry point's 1529 library files carry Anthropic's licence header: they are under Apache-2.0 OR MIT, at the recipient's option: the licence texts and the notice are `LICENSES/anthropic-proofs-LICENSE`, `LICENSES/anthropic-proofs-LICENSE-MIT` and `LICENSES/anthropic-proofs-NOTICE` in the repository's top directory; each changed file carries one line under its licence header saying so, and the 0 that are byte for byte their source carry none. The other files were written for this repository, and they are under the repository's MIT licence (`LICENSE`).
