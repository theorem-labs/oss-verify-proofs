# How the binaries of `plugin-hostd/fuzz_command` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `port/` (the OSS Verify port's files for the project and the manifest its `tools/check --twice` wrote) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/FreeMixer/plugin-hostd at `65cd2b02e8306f7e5f98fa0adfd0b3f8c1df6a5c` (0.10.0) |
| OSS-Fuzz project | none |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/fuzz_command.c` from https://github.com/FreeMixer/plugin-hostd `fuzz/fuzz_command.c` at `65cd2b02e830`; unmodified; licence GPL-3.0-or-later |
| Port | `theorem-labs/oss-verify` `projects/plugin-hostd` at `2840abf10963080bf3ef5a52a2af576aef8d1f8f`, with `tools/` and `infra/` of main at `6aab4a04e1c104101e4f5e15bbbf210f05e15f11`; archive `plugin-hostd-port.tar.zst` (sha256 `37e218a4d2192cb48b9ff58eba9fbef9a47f6b23bc3153facc148264d9c08a0c`) |
| Build system | build.sh (clang, ar; plugin-hostd's Makefile is not used) |
| Patches to the library | none |
| Compilers | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Source code | `plugin-hostd-src.tar.zst`, `plugin-hostd-src.MANIFEST.tsv`, `plugin-hostd-port.tar.zst` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `fuzz_command.plain` | 70080 | `a20873dc7f0ef97c37ed3d3ba52f8ec46c65d11791861ddd9496eb460162d163` |
| ubsan | `fuzz_command.ubsan` | 70808 | `941fc716e36e0a944c349592946c49198ea064477c1dae4fbd5a655ca658eab9` |
| asan | `fuzz_command.asan` | 634904 | `c0661b96b5bd458ba489f91a4693b6a8acd6c0f74d5e20798ed78e937f858bb9` |
| asan-ubsan | `fuzz_command.asan-ubsan` | 633720 | `bbe55d24d0965b89b7fe2ae4d7d8f984d83fba09ca3caab96b10d6c1a1ffab16` |

## Licences

| component | licence | texts |
|---|---|---|
| plugin-hostd | GPL-3.0-or-later | LICENSES/plugin-hostd-COPYING |
| mod-host's command protocol headers, as FreeMixer ships them (mod-host with the patches of FreeMixer's mod-host.spec) | GPL-3.0-or-later | LICENSES/mod-host-COPYING |
| musl libc (static) | MIT | LICENSES/musl-COPYRIGHT |
| LLVM runtimes: compiler-rt builtins; in ASan builds the sanitizer runtime and libunwind | Apache-2.0 WITH LLVM-exception | LICENSES/llvm-compiler-rt-LICENSE.TXT, LICENSES/llvm-libunwind-LICENSE.TXT |
| static-asan patches compiled into the ASan runtime and musl | MIT | LICENSES/static-asan-LICENSE |
| the OSS Verify port's driver (infra/base-builder/driver/: cli.c, adapter.c and the headers they include, and the seals wrap_getenv.c, wrap_mkstemp.c and wrap_getpid.c), linked into every build | MIT OR Apache-2.0 | LICENSES/oss-verify-MIT.txt, LICENSES/oss-verify-LICENSE |

## Rebuild

- the port's projects/plugin-hostd/ at 2840abf1 with tools/ and infra/ of oss-verify's main at 6aab4a04 (the commit 89c6050c port-commit makes of them; oss_verifier.modified: false), tools/check --twice plugin-hostd on the builder image: all 8 binaries of the 2 harnesses identical in the second build (port/manifest.yaml, rebuild.result identical), with these SHA-256s
- plugin-hostd-bin.tar.zst and the source assets packed by tools/enroll/assets.py from those files; every member of plugin-hostd-src.tar.zst is a git blob of an upstream tree its MANIFEST names
