# How the binaries of `reac-pw/fuzz_rate` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `port/` (the OSS Verify port's files for the project and the manifest its `tools/check --twice` wrote) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/FreeREAC/reac-pw at `f86a30a3d06e84e8a7d6ec647cae77c4cbc9137b` (1.0.42) |
| OSS-Fuzz project | none |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/fuzz_rate.c` from https://github.com/FreeREAC/reac-pw `fuzz/fuzz_rate.c` at `f86a30a3d06e`; unmodified; licence GPL-3.0-or-later |
| Port | `theorem-labs/oss-verify` `projects/reac-pw` at `ba46d3675f547098bca08b6353af0f1f8d61549f`, with `tools/` and `infra/` of main at `ba46d3675f547098bca08b6353af0f1f8d61549f`; archive `reac-pw-port.tar.zst` (sha256 `e7802e0c1ee5e46c92827cc0b545c7c4c91636ddec3f71b1da86cc01e0f0d2b6`) |
| Build system | build.sh (clang, ar; reac-pw's meson build and fuzz/build.sh are not used) |
| Patches to the library | none |
| Compilers | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Source code | `reac-pw-src.tar.zst`, `reac-pw-src.MANIFEST.tsv`, `reac-pw-port.tar.zst` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `fuzz_rate.plain` | 53632 | `2bbd88d40188265153dbe7205abefd9dcdf66369c9cb99e8588999d081a221e6` |
| ubsan | `fuzz_rate.ubsan` | 54736 | `75532555040f82db14128f76fd4d2d19936b993e04ec7c7621cdc5e521e161e8` |
| asan | `fuzz_rate.asan` | 584568 | `22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a` |
| asan-ubsan | `fuzz_rate.asan-ubsan` | 585336 | `c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14` |

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
