# Reproducing the binaries

Each binary is pinned by its SHA-256 in its `harness.yaml`; `./oft fetch` and
`./oft verify-sha` check every file against it.

The build that produced the binaries is described on each project page: the
library's repository and commit (or release archive), its build system, the
compiler version and what each harness build changes. For a binary that a
proof is about, the build record in
`projects/<project>/<harness>/proofs/provenance/` gives all of this in one
place, with the flags and the result of an independent rebuild
([building.md](building.md#where-a-binary-comes-from)).

## What a release attaches

- `<project>-bin.tar.zst`: the project's binaries.
- `<project>-src.tar.zst`, for most projects: the upstream source trees that
  the project's binaries were built from, exactly as upstream publishes them,
  before any patch. Every file in it is an upstream git blob or a file with the
  SHA-256 that its pin declares. `<project>-src.MANIFEST.tsv`, beside it, names
  each tree's repository and commit (or SHA-256) and the directory that the
  build lays it down in. Two projects, coturn and mosquitto, have no source
  archive in this release; their pages name the upstream repository and
  commit.
- The recipe archive, for the projects that a recipe built: the build scripts,
  the pins, the harness copies that were adapted for the build, the patches
  applied before each build of a project that attaches a source archive
  (`patches/series.tsv` gives the order) and the driver linked into those
  binaries (`src/`). mosquitto attaches no source archive, and its one patch is
  in no published archive. An unmodified harness is in the project's source
  archive. The recipe's `README.md` says how the pieces fit together.
  `release.yaml` lists each recipe archive under `recipes`, at most
  one in each GitHub release. A project's `project.yaml` pins the recipe that
  its binary archive was built with (`assets.bin.recipe`), which may be in a
  later release than its source archive; the project page names it, and so does
  the build record of each of its proofs.
- `<project>-port.tar.zst`, for a port-built project that attaches its source:
  `git archive` output, at the commit that `build.oss_verify` names, of the OSS
  Verify port's `infra/`, `tools/` and `projects/<project>/` files: its build
  scripts and the source of the driver linked into the binaries
  (`infra/base-builder/driver/`). No recipe built such a project's binaries, so
  its `project.yaml` pins none.

Two more source archives are release-wide, in the GitHub release that
release.yaml's `sources` names:

- `toolchain-src.tar.zst`: the source of the toolchain that built every binary:
  musl, the LLVM runtimes, and static-asan's patches and Dockerfile. Its
  `build.sh` builds the compiler image from these files, the Alpine 3.22 base
  image (pinned by digest) and Alpine packages, among them clang, lld and llvm
  20.1.8 (pinned by version series).
- `sysroot-src.tar.zst`: the source of every library that a copyleft binary
  links from the build image. release.yaml's `image_libraries` lists each such
  library with its licence. The Dockerfile that adds these libraries to the
  builder image is not in this release.

A GitHub release holds at most 1,000 files, so a release may put the source
assets, their MANIFESTs, the port archives and the recipe in a second GitHub
release, `v<release>-src`, beside `v<release>` with the binaries. A file that
has not changed since an earlier release may stay in the GitHub release that
first held it. Each project page links the release that each file is in, and
`./oft fetch` takes each file from the release that the facts name for it.

## Rebuild a recipe-built binary

1. Unpack the recipe archive. Its `recipe/` directory is the build's `/work`.
2. Lay down each tree of the project's source archive where its MANIFEST says.
   A row of kind `vendor-file` is one file: put it as it is, not unpacked, at
   each place that its row names. For a project with no source archive, use
   the upstream repository at the commit that its page names.
3. Put each row of kind `upstream` in the recipe's `MANIFEST.tsv` at its path.
4. Apply the target's patches in `patches/series.tsv` order. The recipe has
   no row for mosquitto's one patch, which no published archive holds.
5. If the fuzz target's `harness.yaml` says `source.modified: true`, Theorem
   Labs changed its fuzz harness, and the release holds the changed file but
   not a patch. Copy the fuzz target's `source/` file over the file that the
   build compiles. Which file that is depends on where the build takes the
   fuzz harness from:
   - The recipe may keep the fuzz harness itself, as it does for
     `libarchive_fuzzer`. It does when the recipe's `MANIFEST.tsv` has a row
     of kind `upstream` at `targets/<target>/<file>`, where `<file>` is the
     file name of `source.from.path`, and that row's origin (the repository,
     commit and path after `src-asset git` in its last column) is the
     repository, commit and path that `source.from` names. A repository URL
     that ends in `.git` names the same repository as one without it. Step 3
     put that file there. Check that its SHA-256 is the row's, then copy the
     `source/` file over it: for `libarchive_fuzzer`, over
     `targets/libarchive-libarchive_fuzzer/libarchive_fuzzer.cc`.
   - Otherwise, copy the `source/` file over the file that `source.from.path`
     names, in the tree of `source.from.repository` that step 2 laid down.
6. Run `tools/build-body.sh` in the builder image, with the environment that
   `tools/build-env.tsv` gives, and with the network off.

Some builds run a riscv64 program that they have just compiled. For example,
the varnish build runs its `vhp_gen_hufdec` helper, and the thrift build runs
its own code generator. For these builds, the build host needs a riscv64
handler registered with `binfmt_misc` (for example from the
`qemu-user-static` package). Without one, every build of such a target fails.

The project page names the builder image and the recipe archive, and so does
each proof's build record. A binary whose SHA-256 differs after such a rebuild
is a bug: please open an issue.

## Rebuild a port-built binary

Unpack the project's port archive. Its checker is the one of its layout: an
archive with `src/oss_verify/check.py` is run as `PYTHONPATH=src python3 -P -m
oss_verify check`, and an older archive with `tools/check` as `tools/check`.
From the archive's top, run that checker with `--no-shell --lock <harness.yaml>
<project>`, with a harness's `harness.yaml` from a checkout of this repository.
The checker builds the builder image from the archive's
`infra/base-builder/` on the builder image the project page names (`--lock`
takes it from the harness's `project.yaml`), then builds the project's
Dockerfile with the network on, compiles each build with the network off, and
compares every binary with the SHA-256 that `harness.yaml` pins. The Dockerfile
fetches the project's repository (`fetch-commit`) and its other source trees
(`lay-out-sources`) over https, at the commits and SHA-256s the port pins. It
does not read the project's source asset or its MANIFEST: those are attached as
the binaries' corresponding source, not as an input to this build. It needs
Docker, git and PyYAML. A project page whose port archive is not attached says
so.

## Copyleft binaries

A binary under a GPL or LGPL licence is attached only together with its
complete corresponding source: its project's source archive and MANIFEST, the
recipe archive that it was built with for a recipe-built project or the
project's port archive for a port-built one, `toolchain-src.tar.zst` and, if it
links libraries from the build image, `sysroot-src.tar.zst`
([licensing.md](licensing.md)). The project page of such a binary names
`toolchain-src.tar.zst`, and also `sysroot-src.tar.zst` when the binary links a
library from the build image. Until these are attached, such binaries, and the
statements about them, are withheld. Some other builds are not in this release
yet either; their pages say so.

The builder images that release.yaml names (`images.builder`: the image that
the binaries were built in, then the compiler image that it is composed from)
are on ghcr.io.
