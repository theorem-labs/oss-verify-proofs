# Adding a proof

Anyone can add a proof at any time. It enters the repository when its pull
request meets every requirement below; [proving.md](proving.md) says how to
write one.

## Requirements

1. **Binaries.** The proof is about binaries this repository publishes: the
   ones `harness.yaml` pins by SHA-256. New binaries, built in builder images
   that `release.yaml` lists, with a recipe it lists or by the OSS Verify port
   (`build.oss_verify`), enter only through a release pull request. When a
   port-built binary has an attached port archive, `assets.port` contains the
   port source, including the linked `infra/base-builder/driver/`. A rebuild
   from the published recipe and sources gives the same SHA-256 for each
   recipe-built binary.
2. **Statements.** The release's statements, unedited, on the LPS version
   that `release.yaml` names. A proof does not change LPS.
3. **Check.** In the checker image, with the packages tools/oft/requirements.txt
   pins on PYTHONPATH, `./oft check <project>/<harness> --parts statements,proofs` passes:
   every proof compiles on Rocq 9.2.0 and assumes only the axioms in
   [toolchain/allowed-axioms.txt](../toolchain/allowed-axioms.txt)
   ([checking.md](checking.md)).
4. **Programs.** No patch fixes or reveals a bug that is not yet disclosed
   upstream ([SECURITY.md](../SECURITY.md)). Build glue is allowed, and the
   build record labels it.
5. **Text.** Comments and names hold nothing private: no internal names and no
   paths from the machine the proof was written on.
6. **Records.** `projects/<project>/<harness>/proofs/provenance/` holds the
   binaries' build record: `PROVENANCE.yaml`, `PROVENANCE.md`, what built
   them, and the licence of every program in them (`LICENSES/`). What built
   them is `recipe/`, the slice of the recipe that built the target, for a
   recipe-built project; for a port-built project (`build.oss_verify` in its
   `project.yaml`) it is `port/`: `port/manifest.yaml`, the build manifest the
   port's `tools/check --twice` wrote, less every `host` key (its `rebuild`
   block names the machine of the second build, and lint refuses a `host`
   there), and `port/projects/<project>/`, the port's files for the project
   (its `Dockerfile`, `build.sh`, `sources` and the rest) at
   `build.oss_verify.commit`. A build record has one of the two, the one its
   `project.yaml` says, and a port-built project's `PROVENANCE.yaml` cites no
   recipe. GPL and LGPL code has its source archive and manifest in the source
   release, and the recipe or port archive that built it is attached too. The
   maintainer writes and updates the build record, and a release checks each
   record against the facts (`./oft lint --release`, rule `records` in
   [tools/oft/README.md](../tools/oft/README.md#the-rules-oft-lint)).
7. **Licences.** Each file has the licence lines of the first of these cases
   that fits it. A file's licence lines are its first lines that say where it
   comes from and under which licence it is, and each `Modified by` line under
   them. A proof library file (`lib/`) with Anthropic's two lines came from
   Anthropic's proofs and stays under Apache-2.0 OR MIT
   ([licensing.md](licensing.md)); a file with no licence lines was written
   here, under the MIT licence.
   1. A file that restates the instruction words of a program, or holds data
      computed from one, begins with the one-line comment of its kind (as in
      the file it came from, or in another file here of the same kind), then
      the `Modified by` lines of the file it came from. It has no Anthropic
      lines: the program's code in it keeps the program's licences.
   2. A file that holds code from a file with Anthropic's two lines,
      `Copyright 2026 Anthropic PBC` and
      `SPDX-License-Identifier: Apache-2.0 OR MIT`, a whole copy or a part, has
      those lines and the lines that file has under them, unchanged. A file
      made from part of a file with the one-line comment, holding none of its
      instruction words or data, has Anthropic's two lines, then that file's
      `Modified by` lines.
   3. Any other file, written new or with code only from files with no
      licence lines, is under the MIT licence and has no licence lines, or
      only the line `SPDX-License-Identifier: MIT`.

   The licence lines are in a file's first 10 lines, and `oft lint` (its
   `licence` rule) checks them against these cases and the build record. It
   reads each file on its own: no merge check compares one file's text with
   another's, so lint finds no copy and never says which case a file is of.
   Cases 1 to 3 are yours to apply: when a file holds code from a file with
   Anthropic's two lines, give it that file's licence lines, as case 2 says,
   and say in the pull request which file it came from. A fuzz target whose
   licence lines a series of its own applies has a `licence-pending` entry,
   below, which defers that fuzz target's licence refusals.

   A fuzz target whose licence lines are applied in a series of their own has
   a `licence-pending` entry in `tools/oft/lint-exceptions.yaml`: its unit
   (`<project>/<fuzz target>`), the date the series is due, the series' pull
   request (or `pending`) and a reason. Lint then reports that fuzz target's
   licence refusals as pending and does not fail on them. The series removes
   its own entry: an entry fails lint when its fuzz target has Rocq files and
   no licence refusal left; an entry may wait for a fuzz target whose proofs
   have not come yet. After its due date it fails a pull request that touches
   its fuzz target or adds or changes the entry itself, and a lint of the
   whole tree with no change to judge; for any other pull request it is a
   warning, so a series that removes its own entry fails on no other. The list
   only shrinks: a pull request that changes proof files adds no entry, a pull
   request of the tools adds one and its review judges it, and a release
   carries none.

   A file of case 1 or 2 that was changed has one more line under its licence
   lines, true of this file: who changed it, when, and what changed in it,
   from its diff against the file it came from. A change of addresses, numbers
   or module names is a change. The pull request adds no notices, attribution
   or licence file, and changes nothing in `LICENSES/`, `NOTICE` or `LICENSE`.
   It says which files came from which files of the repository; the
   maintainer records that in the build record.
8. **No unused files.** Each `.v` file that the pull request adds is required
   by a proof, directly or through other files.

## Steps

1. On a branch, put the proofs in `projects/<project>/<harness>/proofs/`: one
   directory per statement ([proving.md](proving.md)), and the `.v` files they
   share, if any, in `lib/`, at any depth. A file `lib/A/B.v` is the module
   `OSSVerify.Proofs.<project>.<harness>.lib.A.B`, as in the harness's
   `rocq:` field. In the project and harness names, each character other than
   a letter, a digit or `_` is written as `_` (knot-dns is `knot_dns`), and a
   name that starts with a digit gets `h_` in front (`64bit_fuzzer` is
   `h_64bit_fuzzer`).
2. Remove each file that no proof requires (requirement 8), and give every
   file its licence lines (requirement 7). An agent follows
   [the adding-a-proof skill](../.claude/skills/adding-a-proof/SKILL.md),
   which goes through the files one at a time.
3. Run what CI runs. Commit, with what `oft generate --skip-shared` renders
   (the shared pages and the index are rendered after the merge) and a DCO
   sign-off, before the lint, so that `git diff` lists every changed path:

       ./oft fetch <project>
       ./oft generate --skip-shared
       git add -A && git commit -s
       git diff --name-only origin/main HEAD > changed.txt
       ./oft lint --changed changed.txt --pr-kind contributor
       python3 -m pip install --require-hashes --target "$HOME/oft-pydeps" -r tools/oft/requirements.txt
       docker run --rm --network none --ulimit stack=-1:-1 -u "$(id -u):$(id -g)" -e HOME=/tmp -e PYTHONPATH=/pydeps \
         -v "$HOME/oft-pydeps:/pydeps:ro" -v "$PWD:/work" -w /work <checker image of release.yaml> \
         ./oft check <project>/<harness> --parts statements,proofs

   A harness's counterexamples are checked in the runner image with
   `--parts counterexamples` (tools/oft/ci/check-units.sh, step 4, "Counterexamples").

4. Open a pull request, and say in it which files came from which files of the
   repository. CI runs the same checks
   ([checking.md](checking.md#what-ci-runs)). A maintainer reviews the proof,
   writes or updates its build record, and merges it.
