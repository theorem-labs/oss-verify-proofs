# Licensing

## What we wrote

What this repository wrote is under the MIT licence ([LICENSE](../LICENSE)).
That is the statements, `theories/`, `tools/`, the templates, `docs/`, the
distribution modules, the proofs that we wrote, and the build recipes (the
recipe archives that [release.yaml](../release.yaml) lists under `recipes`),
including the driver linked into every recipe-built binary (their `src/`). Each
recipe archive also carries some upstream files, which keep their own licences;
its `UPSTREAM-CARRIED.tsv` lists them. A port-built binary instead links the
driver in the OSS Verify port's `infra/base-builder/driver/`. Each of its files
says `SPDX-License-Identifier: MIT OR Apache-2.0`, and its source is in that
project's port archive; a Rust port-built binary also links the port's adapter
crate, `infra/base-builder/rust/oft-rust-rt/` (`Apache-2.0`), and a Python
port-built binary the port's interpreter host and `atheris` stand-in,
`infra/base-builder/python/` (`Apache-2.0`). A contribution is
under the MIT licence, apart from files made from the proofs below, which keep
their licence.

## Proofs made from Anthropic's proofs

We made some proofs from proofs that Anthropic wrote and licensed under the
Apache License 2.0 or the MIT licence, at the recipient's option, and adapted
them for this release ([origin.md](origin.md)). These files remain under
Apache-2.0 OR MIT:

- Each such file keeps its licence lines, and a file that we or a contributor
  changed has one more line under them that says so
  ([adding-a-proof.md](adding-a-proof.md), requirement 7). A file that restates
  the instruction words of a program, or holds data computed from one, begins
  with a one-line comment that says so instead of Anthropic's header; the
  program's code in it keeps the program's licences.
- The licence texts are
  [LICENSES/anthropic-proofs-LICENSE](../LICENSES/anthropic-proofs-LICENSE)
  (Apache License 2.0) and
  [LICENSES/anthropic-proofs-LICENSE-MIT](../LICENSES/anthropic-proofs-LICENSE-MIT)
  (MIT), and the notices that came with the proofs are
  [LICENSES/anthropic-proofs-NOTICE](../LICENSES/anthropic-proofs-NOTICE).
  These three files are copies, byte for byte, of the ones that came with the
  proofs.
- The build record of each such proof,
  `proofs/<project>/<harness>/provenance/PROVENANCE.md`, names these three files
  as the licence texts of its Anthropic-licensed files.

## Harness copies and binaries

Files under `projects/*/*/source/` are copies of fuzz targets exactly as they
were built, and keep their upstream licences. Each `harness.yaml` names the
licence under `source.licence`, or gives `NOASSERTION` where it is not recorded
yet. A harness with no `source/` directory has no copy under `projects/` yet;
the files it was built from are in the project's recipe archive
(`targets/<target>/`) or in the project's source archive.

A binary is a combined work under the licences of everything linked into it:
the library and its dependencies, the harness, the C library (musl, MIT), the
compiler's runtime libraries (Apache-2.0 WITH LLVM-exception), the patches of
[static-asan](https://github.com/theorem-labs/static-asan) to the sanitizer
runtime and to musl (MIT), and a driver: a recipe-built binary links this
repository's driver (MIT), a port-built binary the OSS Verify port's driver
(`MIT OR Apache-2.0`). A Rust binary also holds the Rust standard library and
the crates its fuzz target uses. The standard library's own crates are
`MIT OR Apache-2.0`, its `compiler_builtins` crate is
`MIT AND Apache-2.0 WITH LLVM-exception AND (MIT OR Apache-2.0)`, and the
crates it vendors keep their own licences (for example `memchr`,
`Unlicense OR MIT`, and `miniz_oxide`, `MIT OR Zlib OR Apache-2.0`), as each
crate's `Cargo.toml` states; a Rust harness's build record lists each one. A
Python binary holds CPython 3.11.13 (`Python-2.0`) with the third-party code
CPython incorporates (for example its copies of expat, `MIT`, and libmpdec,
`BSD-2-Clause`), the standard-library modules its fuzz target imports, as
bytecode, and the build image's libraries that CPython's built-in modules link
(for example zlib); a Python harness's build record lists each one. Each
project's binary archive, `<project>-bin.tar.zst`, carries the licence files of
every component compiled into its binaries, copied verbatim, as
`LICENSES/<component>/<file>`; `./oft fetch` unpacks them to
`projects/<project>/bin/LICENSES/`. Each proof's build record also lists these
components with their licence texts. No `harness.yaml` records the combined
licence of its binaries yet (`licence: NOASSERTION`).

## Copyleft binaries

A binary under a GPL or LGPL licence is attached to a release only together
with its complete corresponding source: every module linked into it, the
permissive ones included ([reproducing.md](reproducing.md) lists the archives).
A binary counts as GPL or LGPL when one of these is under such a licence: the
binary's own licence, its library's, its harness source's, or a library that it
links from the build image (release.yaml's `image_libraries` records those). A
choice such as `MIT OR GPL-2.0` does not count. The source takes the project's
source archive and manifest, then, for a recipe-built project, the build recipe
its binary archive names, or, for a port-built one, the project's `assets.port`
archive. The port archive contains the port's driver source as well as its
build files. A project whose binaries wait for that source says so on its page,
and their statements are withheld until then. Two parts are not in this
release: the Dockerfile that adds the libraries of the builder image, and the
source of the Alpine packages that the toolchain build installs
([reproducing.md](reproducing.md)).

This project is not affiliated with or endorsed by Google or the OSS-Fuzz
project. See [NOTICE](../NOTICE).

A Go binary is the exception to the list above: it holds no C library, no
compiler runtime and not the port's C driver. It is the library and the Go
modules its fuzz target uses (each under its own licence, pinned by the port's
`go.lock`), the harness, Go 1.27.1's standard library and runtime
(`BSD-3-Clause`), and the port's patches to that runtime and its Go driver,
which Theorem Labs, PBC wrote under the MIT licence (each Go harness's build
record lists them). They come from the port's Go toolchain image, not from the
port archive, so for a Go binary the port archive does not hold the driver's
source; a Go binary under a GPL or LGPL licence waits until a release attaches
that source too.
