# Licensing

## What we wrote

What this repository wrote is under the MIT licence ([LICENSE](../LICENSE)).
That is the statements, `theories/`, `tools/`, the templates, `docs/`, the
distribution modules, the proofs that we wrote, and the build recipe (the
recipe archive that [release.yaml](../release.yaml) names under `recipe`),
including the driver linked into every binary (its `src/`). The recipe archive
also carries some upstream files, which keep their own licences; its
`UPSTREAM-CARRIED.tsv` lists them. A contribution is under the MIT licence,
apart from files made from the proofs below, which keep their licence.

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
the files it was built from are in the release's recipe archive
(`targets/<target>/`) or in the project's source archive.

A binary is a combined work under the licences of everything linked into it:
the library and its dependencies, the harness, the C library (musl, MIT), the
compiler's runtime libraries (Apache-2.0 WITH LLVM-exception), the patches of
[static-asan](https://github.com/theorem-labs/static-asan) to the sanitizer
runtime and to musl (MIT), and this repository's driver (MIT). Each project's
binary archive, `<project>-bin.tar.zst`, carries the licence files of every
component compiled into its binaries, copied verbatim, as
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
choice such as `MIT OR GPL-2.0` does not count. A project whose binaries wait
for that source says so on its page, and their statements are withheld until
then. Two parts are not in this release: the Dockerfile that adds the libraries
of the builder image, and the source of the Alpine packages that the toolchain
build installs ([reproducing.md](reproducing.md)).

This project is not affiliated with or endorsed by Google or the OSS-Fuzz
project. See [NOTICE](../NOTICE).
