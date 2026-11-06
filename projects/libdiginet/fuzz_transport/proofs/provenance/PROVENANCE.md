# How the binaries of `libdiginet/fuzz_transport` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `port/` (the OSS Verify port's files for the project and the manifest its `tools/check --twice` wrote) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/FreeMixer/libdiginet at `835f336ccb7abac683681c5791a5715041c71e32` (0.1.1) |
| OSS-Fuzz project | none |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/fuzz_transport.c` from https://github.com/FreeMixer/libdiginet `fuzz/fuzz_transport.c` at `835f336ccb7a`; modified; licence GPL-3.0-or-later |
| Port | `theorem-labs/oss-verify` `projects/libdiginet` at `63e86d975329c21192e679e40fc77bb61203baaf`, with `tools/` and `infra/` of main at `ef32d395512d92ae354ce9b63217e28d42a4b9b9`; archive `libdiginet-port.tar.zst` (sha256 `578f66fcccb01c26b3c78f0b939145e28387b8be9ef5a10cc69af572a15233dd`) |
| Build system | build.sh (clang, ar; libdiginet's Makefile is not used) |
| Patches to the library | none |
| Compilers | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Source code | `libdiginet-src.tar.zst`, `libdiginet-src.MANIFEST.tsv`, `libdiginet-port.tar.zst` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `fuzz_transport.plain` | 64568 | `bb20ce415827592a9ab28fd0bd5b242215eb3ff03b629e12a4723cc6f44ace56` |
| ubsan | `fuzz_transport.ubsan` | 67496 | `af7b86991906e2fd59d929595aaaf239f5f5805109f480ef9ef99e286a97840d` |
| asan | `fuzz_transport.asan` | 616792 | `e89be137db17b720e0310addc2dcc601998945478a9102e6a9850b0566106350` |
| asan-ubsan | `fuzz_transport.asan-ubsan` | 615864 | `41113a03c82fde8282db830ab5f4fbe376e392a38d22670b8cb8c9f02969ece4` |

## Licences

| component | licence | texts |
|---|---|---|
| libdiginet | GPL-3.0-or-later | LICENSES/libdiginet-LICENSE |
| musl libc (static) | MIT | LICENSES/musl-COPYRIGHT |
| LLVM runtimes: compiler-rt builtins; in ASan builds the sanitizer runtime and libunwind | Apache-2.0 WITH LLVM-exception | LICENSES/llvm-compiler-rt-LICENSE.TXT, LICENSES/llvm-libunwind-LICENSE.TXT |
| static-asan patches compiled into the ASan runtime and musl | MIT | LICENSES/static-asan-LICENSE |
| the OSS Verify port's driver (infra/base-builder/driver/: cli.c, adapter.c and the headers they include, and the seals wrap_getenv.c, wrap_mkstemp.c and wrap_getpid.c), linked into every build | MIT OR Apache-2.0 | LICENSES/oss-verify-MIT.txt, LICENSES/oss-verify-LICENSE |

## Rebuild

- the port's projects/libdiginet/ at 63e86d97 with tools/ and infra/ of oss-verify's main at ef32d395 (the commit 12201191 port-commit makes of them; oss_verifier.modified: false), tools/check --twice libdiginet on the builder image: all 16 binaries of the 4 harnesses identical in the second build (port/manifest.yaml, rebuild.result identical), with these SHA-256s; the 12 binaries of fuzz_frame, fuzz_decode and fuzz_codec are the bytes the port at ef32d395 built
- libdiginet-bin.tar.zst and the source assets packed by tools/enroll/assets.py from those files; every member of libdiginet-src.tar.zst is a git blob of an upstream tree its MANIFEST names
