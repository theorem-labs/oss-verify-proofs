# How the binaries of `reac-repacer/fuzz_uci` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `port/` (the OSS Verify port's files for the project and the manifest its `tools/check --twice` wrote) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/FreeREAC/reac-repacer at `3ac1cf1017c847fe2272fce7f2f93306f8a23b42` (0.2.3) |
| OSS-Fuzz project | none |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/fuzz_uci.c` from https://github.com/FreeREAC/reac-repacer `fuzz/fuzz_uci.c` at `3ac1cf1017c8`; unmodified; licence GPL-3.0-or-later |
| Port | `theorem-labs/oss-verify` `projects/reac-repacer` at `d897ff19667fd95fa86514cc2750b650b9845988`, with `tools/` and `infra/` of main at `d897ff19667fd95fa86514cc2750b650b9845988`; archive `reac-repacer-port.tar.zst` (sha256 `80ca55c825f6b09c902a3cd08dc8477365c30167f81e112dd481548f6dace6c1`) |
| Build system | build.sh (clang, ar; reac-repacer's Makefile and meson build are not used) |
| Patches to the library | none |
| Compilers | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Source code | `reac-repacer-src.tar.zst`, `reac-repacer-src.MANIFEST.tsv`, `reac-repacer-port.tar.zst` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `fuzz_uci.plain` | 44640 | `a6119aa7f1f281cacb63a767e0b5e6976b8f220542f6109c4fd2cecaf98ae5ac` |
| ubsan | `fuzz_uci.ubsan` | 44936 | `fa87ac3037db248a9ae80eb487b18990df08b26707cb501947d2831f6ccee58c` |
| asan | `fuzz_uci.asan` | 560936 | `6ea017c24525e6946fa06dc7e3075459ad2c5146d59af49873bf3c51a46e885d` |
| asan-ubsan | `fuzz_uci.asan-ubsan` | 561192 | `a1b86e424adde6f65d345459822690a6c21e9e606446b91b4ad25e9f3ef6e7fc` |

## Licences

| component | licence | texts |
|---|---|---|
| reac-repacer | GPL-3.0-or-later | LICENSES/reac-repacer-LICENSE |
| libreac | GPL-3.0-or-later | LICENSES/libreac-LICENSE |
| musl libc (static) | MIT | LICENSES/musl-COPYRIGHT |
| LLVM runtimes: compiler-rt builtins; in ASan builds the sanitizer runtime and libunwind | Apache-2.0 WITH LLVM-exception | LICENSES/llvm-compiler-rt-LICENSE.TXT, LICENSES/llvm-libunwind-LICENSE.TXT |
| static-asan patches compiled into the ASan runtime and musl | MIT | LICENSES/static-asan-LICENSE |
| the OSS Verify port's driver (infra/base-builder/driver/: cli.c, adapter.c and the headers they include, and the seals wrap_getenv.c, wrap_mkstemp.c and wrap_getpid.c), linked into every build | MIT OR Apache-2.0 | LICENSES/oss-verify-MIT.txt, LICENSES/oss-verify-LICENSE |

## Rebuild

- the port's projects/reac-repacer/ at d897ff19 with tools/ and infra/ of oss-verify's main at d897ff19 (the commit 35eedf6f port-commit makes of them; oss_verifier.modified: false), tools/check --twice reac-repacer on the builder image: all 16 binaries of the 4 harnesses identical in the second build (port/manifest.yaml, rebuild.result identical), with these SHA-256s
- reac-repacer-bin.tar.zst and the source assets packed by tools/enroll/assets.py from those files; every member of reac-repacer-src.tar.zst is a git blob of an upstream tree its MANIFEST names
