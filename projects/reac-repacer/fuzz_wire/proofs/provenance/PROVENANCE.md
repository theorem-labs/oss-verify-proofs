# How the binaries of `reac-repacer/fuzz_wire` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `port/` (the OSS Verify port's files for the project and the manifest its `tools/check --twice` wrote) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/FreeREAC/reac-repacer at `3ac1cf1017c847fe2272fce7f2f93306f8a23b42` (0.2.3) |
| OSS-Fuzz project | none |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/fuzz_wire.c` from https://github.com/FreeREAC/reac-repacer `fuzz/fuzz_wire.c` at `3ac1cf1017c8`; unmodified; licence GPL-3.0-or-later |
| Port | `theorem-labs/oss-verify` `projects/reac-repacer` at `d897ff19667fd95fa86514cc2750b650b9845988`, with `tools/` and `infra/` of main at `d897ff19667fd95fa86514cc2750b650b9845988`; archive `reac-repacer-port.tar.zst` (sha256 `80ca55c825f6b09c902a3cd08dc8477365c30167f81e112dd481548f6dace6c1`) |
| Build system | build.sh (clang, ar; reac-repacer's Makefile and meson build are not used) |
| Patches to the library | none |
| Compilers | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Source code | `reac-repacer-src.tar.zst`, `reac-repacer-src.MANIFEST.tsv`, `reac-repacer-port.tar.zst` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `fuzz_wire.plain` | 46664 | `c8763dfc4e813991f8c70c48a732a8c512a249766f972b609d969fbd16f7709d` |
| ubsan | `fuzz_wire.ubsan` | 47704 | `6e91fe0b5555ca208801070f2dbfa8ba841fef053c70afd71731c20c7aa7c532` |
| asan | `fuzz_wire.asan` | 566888 | `2f8f8697cd4f99bd15999cce4963a6fcc39b308444bd58e2bf526ec7c1ad5fa1` |
| asan-ubsan | `fuzz_wire.asan-ubsan` | 567032 | `af4534831a4528320c7dc74ca3f64bb96e8232ed2e313f01126d10879f3417d6` |

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
