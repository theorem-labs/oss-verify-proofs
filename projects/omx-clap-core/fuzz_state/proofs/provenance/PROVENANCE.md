# How the binaries of `omx-clap-core/fuzz_state` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `port/` (the OSS Verify port's files for the project and the manifest its `tools/check --twice` wrote) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/FreeMixer/omx-clap-core at `246923f04ac0ff2adb189bb9280816670c05b36c` (0.20.1) |
| OSS-Fuzz project | none |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/fuzz_state.c` from https://github.com/FreeMixer/omx-clap-core `fuzz/fuzz_state.c` at `246923f04ac0`; unmodified; licence GPL-3.0-or-later |
| Port | `theorem-labs/oss-verify` `projects/omx-clap-core` at `5f067f673c4489bfe989de13bf17be68daf2b2df`, with `tools/` and `infra/` of main at `6aab4a04e1c104101e4f5e15bbbf210f05e15f11`; archive `omx-clap-core-port.tar.zst` (sha256 `793a877b3204973a0ea4dc4d30ed19a408f1cb03ba166417bb1e8ebb5b5fd1e4`) |
| Build system | build.sh (clang, ar; omx-clap-core's Makefile is not used) |
| Patches to the library | none |
| Compilers | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Source code | `omx-clap-core-src.tar.zst`, `omx-clap-core-src.MANIFEST.tsv`, `omx-clap-core-port.tar.zst` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `fuzz_state.plain` | 67840 | `c9703541c41a0194746aa9c67937071ad5dc1ab0df1cd3e774fdc3f7177aa016` |
| ubsan | `fuzz_state.ubsan` | 69608 | `6e4aa2cd877d4047a90a4eb004dbc39fd0b4a3c1bf0c4eba1da00d14dc4262f2` |
| asan | `fuzz_state.asan` | 597624 | `64b53ff86172bb07f93f146e67b81a0354bca88e0a580e93fb1da01406fb76e0` |
| asan-ubsan | `fuzz_state.asan-ubsan` | 598936 | `5ac5ce0954f87e2d050c481b7b0599cfd55ef554eadc008e51491f44c053d204` |

## Licences

| component | licence | texts |
|---|---|---|
| omx-clap-core | GPL-3.0-or-later | LICENSES/omx-clap-core-COPYING |
| musl libc (static) | MIT | LICENSES/musl-COPYRIGHT |
| LLVM runtimes: compiler-rt builtins; in ASan builds the sanitizer runtime and libunwind | Apache-2.0 WITH LLVM-exception | LICENSES/llvm-compiler-rt-LICENSE.TXT, LICENSES/llvm-libunwind-LICENSE.TXT |
| static-asan patches compiled into the ASan runtime and musl | MIT | LICENSES/static-asan-LICENSE |
| the OSS Verify port's driver (infra/base-builder/driver/: cli.c, adapter.c and the headers they include, and the seals wrap_getenv.c, wrap_mkstemp.c and wrap_getpid.c), linked into every build | MIT OR Apache-2.0 | LICENSES/oss-verify-MIT.txt, LICENSES/oss-verify-LICENSE |

## Rebuild

- the port's projects/omx-clap-core/ at 5f067f67 with tools/ and infra/ of oss-verify's main at 6aab4a04 (the commit 249cb279 port-commit makes of them; oss_verifier.modified: false), tools/check --twice omx-clap-core on the builder image: all 12 binaries of the 3 harnesses identical in the second build (port/manifest.yaml, rebuild.result identical), with these SHA-256s; the 8 binaries of fuzz_state and fuzz_manifest are the bytes the port at e29299ea built
- omx-clap-core-bin.tar.zst and the source assets packed by tools/enroll/assets.py from those files; every member of omx-clap-core-src.tar.zst is a git blob of an upstream tree its MANIFEST names
