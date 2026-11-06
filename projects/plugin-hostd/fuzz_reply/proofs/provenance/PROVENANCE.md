# How the binaries of `plugin-hostd/fuzz_reply` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `port/` (the OSS Verify port's files for the project and the manifest its `tools/check --twice` wrote) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/FreeMixer/plugin-hostd at `65cd2b02e8306f7e5f98fa0adfd0b3f8c1df6a5c` (0.10.0) |
| OSS-Fuzz project | none |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/fuzz_reply.c` from https://github.com/FreeMixer/plugin-hostd `fuzz/fuzz_reply.c` at `65cd2b02e830`; unmodified; licence GPL-3.0-or-later |
| Port | `theorem-labs/oss-verify` `projects/plugin-hostd` at `2840abf10963080bf3ef5a52a2af576aef8d1f8f`, with `tools/` and `infra/` of main at `6aab4a04e1c104101e4f5e15bbbf210f05e15f11`; archive `plugin-hostd-port.tar.zst` (sha256 `37e218a4d2192cb48b9ff58eba9fbef9a47f6b23bc3153facc148264d9c08a0c`) |
| Build system | build.sh (clang, ar; plugin-hostd's Makefile is not used) |
| Patches to the library | none |
| Compilers | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Source code | `plugin-hostd-src.tar.zst`, `plugin-hostd-src.MANIFEST.tsv`, `plugin-hostd-port.tar.zst` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `fuzz_reply.plain` | 58480 | `3f53043e4f872b0ebf394fb67bd1a5dae5131fa08a7208ebfe67e2552ae9f680` |
| ubsan | `fuzz_reply.ubsan` | 60760 | `c5ef8ec8636eaa18f5181ba119a118e211db05b5053cf7cd88581f5d561b3bc5` |
| asan | `fuzz_reply.asan` | 589816 | `42c58610e125e0b47770217f7175ffe2f23ed5ee1399b3e81539eff364611d5a` |
| asan-ubsan | `fuzz_reply.asan-ubsan` | 591224 | `10ffb5f9202ae2bdb01b7a49df9866843a6a6a0e0c50bc67cdba6ce2f6d3cf2c` |

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
