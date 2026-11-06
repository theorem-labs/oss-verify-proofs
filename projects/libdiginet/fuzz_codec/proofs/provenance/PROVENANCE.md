# How the binaries of `libdiginet/fuzz_codec` were built

Generated from `PROVENANCE.yaml` beside this file. The build files are in `port/` (the OSS Verify port's files for the project and the manifest its `tools/check --twice` wrote) and the licence texts in `LICENSES/`.

| | |
|---|---|
| Upstream | https://github.com/FreeMixer/libdiginet at `835f336ccb7abac683681c5791a5715041c71e32` (0.1.1) |
| OSS-Fuzz project | none |
| Entry point | `LLVMFuzzerTestOneInput` |
| Harness | `source/fuzz_codec.c` from https://github.com/FreeMixer/libdiginet `fuzz/fuzz_codec.c` at `835f336ccb7a`; unmodified; licence GPL-3.0-or-later |
| Port | `theorem-labs/oss-verify` `projects/libdiginet` at `63e86d975329c21192e679e40fc77bb61203baaf`, with `tools/` and `infra/` of main at `ef32d395512d92ae354ce9b63217e28d42a4b9b9`; archive `libdiginet-port.tar.zst` (sha256 `578f66fcccb01c26b3c78f0b939145e28387b8be9ef5a10cc69af572a15233dd`) |
| Build system | build.sh (clang, ar; libdiginet's Makefile is not used) |
| Patches to the library | none |
| Compilers | clang 20.1.8 |
| Builder image | `ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b` |
| Source code | `libdiginet-src.tar.zst`, `libdiginet-src.MANIFEST.tsv`, `libdiginet-port.tar.zst` |

## Binaries

| build | file | bytes | sha256 |
|---|---|---|---|
| plain | `fuzz_codec.plain` | 56336 | `742003c552f92fe3c5c43c1fe8e485b75f2f454bfb1784c0d4f25058c976622d` |
| ubsan | `fuzz_codec.ubsan` | 57496 | `66f0cba3fa118ae7bc394f5ebcfc2d9e7fef45c76150cfccdcf7fe84cad9fce4` |
| asan | `fuzz_codec.asan` | 590808 | `7d470194ffdbde8b30a9810840f8e81d620ba1c555d510c475daeff37548a422` |
| asan-ubsan | `fuzz_codec.asan-ubsan` | 593144 | `73109e32e77beff294d41ae6f16d607479ad1884485781b322645e6f8afa99c3` |

## Licences

| component | licence | texts |
|---|---|---|
| libdiginet | GPL-3.0-or-later | LICENSES/libdiginet-LICENSE |
| musl libc (static) | MIT | LICENSES/musl-COPYRIGHT |
| LLVM runtimes: compiler-rt builtins; in ASan builds the sanitizer runtime and libunwind | Apache-2.0 WITH LLVM-exception | LICENSES/llvm-compiler-rt-LICENSE.TXT, LICENSES/llvm-libunwind-LICENSE.TXT |
| static-asan patches compiled into the ASan runtime and musl | MIT | LICENSES/static-asan-LICENSE |
| the OSS Verify port's driver (infra/base-builder/driver/: cli.c, adapter.c and the headers they include, and the seals wrap_getenv.c, wrap_mkstemp.c and wrap_getpid.c), linked into every build | MIT OR Apache-2.0 | LICENSES/oss-verify-MIT.txt, LICENSES/oss-verify-LICENSE |

## Rebuild

- the port's projects/libdiginet/ at 63e86d97 with tools/ and infra/ of oss-verify's main at ef32d395 (the commit 12201191 port-commit makes of them; oss_verifier.modified: false), tools/check --twice libdiginet on the builder image: all 16 binaries of the 4 harnesses identical in the second build (port/manifest.yaml, rebuild.result identical), with these SHA-256s
- libdiginet-bin.tar.zst and the source assets packed by tools/enroll/assets.py from those files; every member of libdiginet-src.tar.zst is a git blob of an upstream tree its MANIFEST names
