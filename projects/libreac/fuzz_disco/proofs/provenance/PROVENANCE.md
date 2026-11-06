# How the binaries of `libreac/fuzz_disco` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `port/` (the OSS Verify port's files for the project and the manifest its `tools/check --twice` wrote) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/FreeREAC/libreac at `d16f3f4eba605ee2cb9e7a70bf72685f1b7b5d25` (1.9.0) |
| OSS-Fuzz project | none |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/fuzz_disco.c` from https://github.com/FreeREAC/libreac `fuzz/fuzz_disco.c` at `d16f3f4eba60`; unmodified; licence GPL-3.0-or-later |
| Port | `theorem-labs/oss-verify` `projects/libreac` at `6a4a32ac65b497b2f5d9d8990bb6f9aefbe54d16`, with `tools/` and `infra/` of main at `6a4a32ac65b497b2f5d9d8990bb6f9aefbe54d16`; archive `libreac-port.tar.zst` (sha256 `fc7075728374dee1d84d8ab20b04fe6ba27ab539b83f39ef8fe6533180c075d8`) |
| Build system | build.sh (clang, ar; libreac's Makefile is not used) |
| Patches to the library | none |
| Compilers | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Source code | `libreac-src.tar.zst`, `libreac-src.MANIFEST.tsv`, `libreac-port.tar.zst` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `fuzz_disco.plain` | 58944 | `04988e3ab31341965e44f0ca1bb0e5ed18fe6892e2c753df7a87bec197576f7c` |
| ubsan | `fuzz_disco.ubsan` | 60920 | `56121de6ba4cff85e0fa262e9783f384e35fb8642d057f7a3a4290bcc245b22e` |
| asan | `fuzz_disco.asan` | 602136 | `5e39150dd8104df969eb360f9cc29c4f92fe12326afd23783a679e4fb4809f46` |
| asan-ubsan | `fuzz_disco.asan-ubsan` | 603064 | `cee6f04ad3d4928e242405689ae058bb9e8b6533000c90bde984a2f0d5ff5146` |

## Licences

| component | licence | texts |
|---|---|---|
| libreac | GPL-3.0-or-later | LICENSES/libreac-LICENSE |
| musl libc (static) | MIT | LICENSES/musl-COPYRIGHT |
| LLVM runtimes: compiler-rt builtins; in ASan builds the sanitizer runtime and libunwind | Apache-2.0 WITH LLVM-exception | LICENSES/llvm-compiler-rt-LICENSE.TXT, LICENSES/llvm-libunwind-LICENSE.TXT |
| static-asan patches compiled into the ASan runtime and musl | MIT | LICENSES/static-asan-LICENSE |
| the OSS Verify port's driver (infra/base-builder/driver/: cli.c, adapter.c and the headers they include, and the seals wrap_getenv.c, wrap_mkstemp.c and wrap_getpid.c), linked into every build | MIT OR Apache-2.0 | LICENSES/oss-verify-MIT.txt, LICENSES/oss-verify-LICENSE |

## Rebuild

- the port's projects/libreac/ at 6a4a32ac with tools/ and infra/ of oss-verify's main at 6a4a32ac (the commit 207fe959 port-commit makes of them; oss_verifier.modified: false), tools/check --twice libreac on the builder image: all 36 binaries of the 9 harnesses identical in the second build (port/manifest.yaml, rebuild.result identical), with these SHA-256s
- libreac-bin.tar.zst and the source assets packed by tools/enroll/assets.py from those files; every member of libreac-src.tar.zst is a git blob of an upstream tree its MANIFEST names
