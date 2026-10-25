# Adding a proof

Anyone can add a proof at any time. It enters the repository when its pull
request meets every requirement below; [proving.md](proving.md) says how to
write one.

## Requirements

1. **Binaries.** The proof is about binaries this repository publishes: the
   ones `harness.yaml` pins by SHA-256. New binaries, built with the release's
   recipe and builder images (`release.yaml`), enter only through a release
   pull request. A rebuild from the published recipe and sources gives the same
   SHA-256 for each.
2. **Statements.** The release's statements, unedited, on the LPS version
   that `release.yaml` names. A proof does not change LPS.
3. **Check.** In the checker image, with PyYAML from tools/oft/requirements.txt
   on PYTHONPATH, `./oft check <project>/<harness> --parts statements,proofs` passes:
   every proof compiles on Rocq 9.2.0 and assumes only the axioms in
   [toolchain/allowed-axioms.txt](../toolchain/allowed-axioms.txt)
   ([checking.md](checking.md)).
4. **Programs.** No patch fixes or reveals a bug that is not yet disclosed
   upstream ([SECURITY.md](../SECURITY.md)). Build glue is allowed, and the
   build record labels it.
5. **Text.** Comments and names hold nothing private: no internal names and no
   paths from the machine the proof was written on.
6. **Records.** `proofs/<project>/<harness>/provenance/` holds the binaries'
   build record (`PROVENANCE.yaml`, `PROVENANCE.md`, `recipe/`) and the licence
   of every program in them (`LICENSES/`). GPL and LGPL code has its source
   archive in the source release. The maintainer writes and updates the build
   record.
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
      licence lines, is under the MIT licence and has no licence lines.

   A file of case 1 or 2 that was changed has one more line under its licence
   lines, true of this file: who changed it, when, and what changed in it,
   from its diff against the file it came from. A change of addresses, numbers
   or module names is a change. The pull request adds no notices, attribution
   or licence file, and changes nothing in `LICENSES/`, `NOTICE` or `LICENSE`.
   It says which files came from which files of the repository; the
   maintainer records that in the build record. CI does not read licence
   lines: a maintainer checks them in review. CI does refuse a contributor's
   change to `LICENSE`, `NOTICE` or `LICENSES/` (the `paths` rule of
   `oft lint`), and pins the bytes of the three `LICENSES/anthropic-proofs-*`
   files.
8. **No unused files.** Each `.v` file that the pull request adds is required
   by a proof, directly or through other files.

## Steps

1. On a branch, put the proofs in `proofs/<project>/<harness>/`: one directory
   per statement ([proving.md](proving.md)), and the `.v` files they share, if
   any, in `lib/`, at any depth. A file `lib/A/B.v` is the module
   `OssFuzzTheorems.Proofs.<project>.<harness>.lib.A.B`, as in the harness's
   `rocq:` field. In the project and harness names, each character other than
   a letter, a digit or `_` is written as `_` (knot-dns is `knot_dns`), and a
   name that starts with a digit gets `h_` in front (`64bit_fuzzer` is
   `h_64bit_fuzzer`).
2. Remove each file that no proof requires (requirement 8), and give every
   file its licence lines (requirement 7). An agent follows
   [the adding-a-proof skill](../.claude/skills/adding-a-proof/SKILL.md),
   which goes through the files one at a time.
3. Run what CI runs. Commit, with what `oft generate` renders and a DCO
   sign-off, before the lint, so that `git diff` lists every changed path:

       ./oft fetch <project>
       ./oft generate
       git add -A && git commit -s
       git diff --name-only origin/main HEAD > changed.txt
       ./oft lint --changed changed.txt --pr-kind contributor
       python3 -m pip install --require-hashes --target "$HOME/oft-pydeps" -r tools/oft/requirements.txt
       docker run --rm --network none -u "$(id -u):$(id -g)" -e HOME=/tmp -e PYTHONPATH=/pydeps \
         -v "$HOME/oft-pydeps:/pydeps:ro" -v "$PWD:/work" -w /work <checker image of release.yaml> \
         ./oft check <project>/<harness> --parts statements,proofs

   A harness's counterexamples are checked in the runner image with
   `--parts counterexamples`.

4. Open a pull request, and say in it which files came from which files of the
   repository. CI runs the same checks
   ([checking.md](checking.md#what-ci-runs)). A maintainer reviews the proof,
   writes or updates its build record, and merges it.
