# How the binaries of `reac-pw/fuzz_segconf` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `port/` (the OSS Verify port's files for the project and the manifest its `tools/check --twice` wrote) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/FreeREAC/reac-pw at `f86a30a3d06e84e8a7d6ec647cae77c4cbc9137b` (1.0.42) |
| OSS-Fuzz project | none |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/fuzz_segconf.c` from https://github.com/FreeREAC/reac-pw `fuzz/fuzz_segconf.c` at `f86a30a3d06e`; unmodified; licence GPL-3.0-or-later |
| Port | `theorem-labs/oss-verify` `projects/reac-pw` at `ba46d3675f547098bca08b6353af0f1f8d61549f`, with `tools/` and `infra/` of main at `ba46d3675f547098bca08b6353af0f1f8d61549f`; archive `reac-pw-port.tar.zst` (sha256 `e7802e0c1ee5e46c92827cc0b545c7c4c91636ddec3f71b1da86cc01e0f0d2b6`) |
| Build system | build.sh (clang, ar; reac-pw's meson build and fuzz/build.sh are not used) |
| Patches to the library | none |
| Compilers | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Source code | `reac-pw-src.tar.zst`, `reac-pw-src.MANIFEST.tsv`, `reac-pw-port.tar.zst` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `fuzz_segconf.plain` | 65392 | `3776ca44d75ca77dc7a6946cdae14d87666df7a0a5323a2916b43c94ab5801a3` |
| ubsan | `fuzz_segconf.ubsan` | 67848 | `1696d6c34ffd1e1ec3e6438f21ba9074ab708134bc6fe0e798d4659b5ea6757e` |
| asan | `fuzz_segconf.asan` | 614216 | `48c5355bdacbc5ba2e0a9ff843627969cb5d2913316654369904b549fc904ef8` |
| asan-ubsan | `fuzz_segconf.asan-ubsan` | 616200 | `c3796c0b38f3666f32a3ecff43c9fdb55ead356833af6013a07c404bd0254509` |

## Licences

| component | licence | texts |
|---|---|---|
| reac-pw | GPL-3.0-or-later | LICENSES/reac-pw-LICENSE |
| libreac 1.10.0 | GPL-3.0-or-later | LICENSES/libreac-LICENSE |
| SPA of PipeWire 1.6.10 | MIT | LICENSES/pipewire-COPYING |
| musl libc (static) | MIT | LICENSES/musl-COPYRIGHT |
| LLVM runtimes: compiler-rt builtins; in ASan builds the sanitizer runtime and libunwind | Apache-2.0 WITH LLVM-exception | LICENSES/llvm-compiler-rt-LICENSE.TXT, LICENSES/llvm-libunwind-LICENSE.TXT |
| static-asan patches compiled into the ASan runtime and musl | MIT | LICENSES/static-asan-LICENSE |
| the OSS Verify port's driver (infra/base-builder/driver/: cli.c, adapter.c and the headers they include, and the seals wrap_getenv.c, wrap_mkstemp.c and wrap_getpid.c), linked into every build | MIT OR Apache-2.0 | LICENSES/oss-verify-MIT.txt, LICENSES/oss-verify-LICENSE |

## Rebuild

- the port's projects/reac-pw/ at ba46d367 with tools/ and infra/ of oss-verify's main at ba46d367 (the commit 014aad0c port-commit makes of them; oss_verifier.modified: false), tools/check --twice reac-pw on the builder image: all 28 binaries of the 7 harnesses identical in the second build (port/manifest.yaml, rebuild.result identical), with these SHA-256s
- reac-pw-bin.tar.zst and the source assets packed by tools/enroll/assets.py from those files; every member of reac-pw-src.tar.zst is a git blob of an upstream tree its MANIFEST names
