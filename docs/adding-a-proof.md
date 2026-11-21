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
7. **Licences.** A file's licence lines say where it comes from and under
   which licence it is. They are the copyright line and the licence tag that
   it has, or the one-line comment of case 1, and the lines under them: a
   `Copyright 2026 Theorem Labs` line under Anthropic's two lines, and each
   `Modified by` line. The copyright line and the licence tag, or the
   one-line comment, are in the file's first 10 lines, and the one-line
   comment is its first line. The lines under them follow them, in order,
   with no line limit: the Theorem Labs line, then the `Modified by` lines.
   A new `Modified by` line goes under the last one that is there. A
   `Modified by` line holds no licence tag and no copyright of Anthropic. A
   proof library file (`lib/`) with Anthropic's two lines came from
   Anthropic's proofs and stays under Apache-2.0 OR MIT
   ([licensing.md](licensing.md)). A file of case 4 was written here, under
   the MIT licence. In a project whose `project.yaml` says `release: private`
   and whose folder holds a `NOTICE` file, a file of none of cases 1, 2 and 3
   is under that `NOTICE` instead, and case 4 does not apply there (the
   paragraph before case 4). The rules for files made from other files,
   below the cases, say which code goes in which file. Each file then has the
   licence lines of its case:
   1. A file that restates the instruction words of a program, or holds data
      computed from one, also when you wrote them, begins with the one-line
      comment of its kind (as in the file it came from, or in another file
      here of the same kind), then the `Modified by` lines of the file it
      came from. It has no Anthropic lines: the program's code in it keeps
      the program's licences. As the paragraph after the rules says, a
      changed file of this case also gets one new `Modified by` line of its
      own. A new file made from more than one file also follows the rules
      below.
   2. A file made from a file with Anthropic's two lines,
      `Copyright 2026 Anthropic PBC` and
      `SPDX-License-Identifier: Apache-2.0 OR MIT`, a whole copy or a part,
      has those lines and the lines that file has under them, unchanged. A
      file that was there before the change with Anthropic's two lines, and
      takes code from another such file, is not made from that file: it
      keeps its own licence lines and copies none of the other file's. It
      adds one `Modified by` line under the last of them, which names the
      other file, a commit of theorem-labs/oss-verify-proofs that holds it,
      and the lines taken. A file made from part of a file with the one-line
      comment, holding none of its instruction words or data, has
      Anthropic's two lines, then that file's `Modified by` lines. As the
      paragraph after the rules says, every changed file of this case gets
      one new `Modified by` line of its own: for a file that takes code from
      another such file, that is the one line above. A new file made from
      more than one file also follows the rules below.
   3. A file that comes from another project's proofs and keeps that
      project's licence is a row of `tools/oft/third-party-proofs.yaml`. The
      row gives its path, the SHA-256 of its bytes, its licence, the project's
      repository and commit it came from, and the lines of the upstream
      author's notice. The file keeps that notice unchanged, with the author's
      address in it, and has the line
      `SPDX-License-Identifier: LGPL-2.1-or-later`, the one licence the table
      allows. The project's licence file comes into the tree with the
      project's first files, in `LICENSES/`: for a repository
      `<owner>/<name>` it is `LICENSES/<owner>-<name>-LICENSE`, so for
      coq-community/huffman it is `LICENSES/coq-community-huffman-LICENSE`.
      `oft lint` pins the bytes of that licence file, as it pins the licence
      texts of Anthropic's proofs, and refuses it with any other bytes.
      `oft lint` accepts the file only while its bytes are the ones its row
      pins, so a change to the file changes its row too, and only while its
      project's licence file, one that lint pins, is in `LICENSES/`. A
      maintainer writes the row, and a project whose licence file lint does
      not pin yet needs a change to the tools first. As the paragraph after the
      rules says, a changed file of this case also gets one new
      `Modified by` line of its own.

   In a project whose `project.yaml` says `release: private` and whose
   folder holds a `NOTICE` file, `projects/<project>/NOTICE`, no proof file
   is under the MIT licence, so case 4 does not apply there. A file of such
   a project that is of none of cases 1, 2 and 3 is under that `NOTICE`. It
   has these two lines in its first 10 lines, the copyright line above the
   tag, with the name of its project in place of `<project>`:

       (* Copyright Theorem Labs. All rights reserved: see projects/<project>/NOTICE. *)
       (* SPDX-License-Identifier: LicenseRef-Proprietary *)

   These two lines are one set of lines, and a file of any other project has
   neither of them; a file names no other project's `NOTICE`. In such a
   project, where a rule below puts code in a file of case 4, that code goes
   in a file with these two lines, and a file whose first 10 lines hold no
   licence line but name a licence in words carries that licence's
   `SPDX-License-Identifier` line there too, as in case 4. The `NOTICE` is a
   maintainer's file: a pull request from outside does not add or change it,
   and `oft lint` refuses a `NOTICE` in a project whose `project.yaml` does
   not say `release: private`, since a release would publish it.

   4. Any other file, outside a project of the paragraph above, is under the
      MIT licence. It has one of three forms: no licence lines, only the line
      `SPDX-License-Identifier: MIT`, or a `Copyright 2026 Theorem Labs` line
      over that tag. It has the Theorem Labs line over the tag when it holds
      code copied from a file with that line. A file whose first 10 lines
      hold no licence line but name a licence in words (its name, or the
      opening words of its notice) would read as a file of this case with no
      licence lines, so it must carry that licence's
      `SPDX-License-Identifier` line. A file of case 4 that takes code copied
      from a file with Anthropic's lines keeps its own lines, and the copied
      code goes in a new file, as a rule below says.

   Files made from other files, and code that you write:

   - Copied code, which is code from a file as the last rule below defines
     it, keeps the licence lines of the file it came from, unchanged: its
     copyright line and licence tag, or its one-line comment, and the lines
     under them. Instruction words and data have the one-line comment of
     their kind, also when you wrote them. The rules below win over this one,
     and so does case 2 after its first sentence.
   - Code copied from files with different sets of licence lines goes in
     separate files, one file for each set. A set of lines is the copyright
     line and the licence tag, or the kind of the one-line comment. The
     `Modified by` lines under them make no other set, and a Theorem Labs
     line under Anthropic's two lines makes none either. The three forms of
     case 4 are one set, and a file of case 4 that takes code from a file
     with the Theorem Labs line over the MIT tag has that line over the tag.
     A file made from two files with one-line comments of one kind has the
     comment of one of them. Instruction words or data, also when you wrote
     them, do not share a file with code from a file with Anthropic's lines,
     or with instruction words or data of the other kind. Code that you write
     goes in the file that you add it to, but a lemma whose proof is code
     from a file goes where that code goes (the last rule). When the file
     that you add code to is of case 1, 2 or 3, it is a changed file if it
     was there before the change or is made from another file. A new file
     with your lemmas and code from a file with Anthropic's lines is of
     case 2 (see below). Your code in a file of none of cases 1, 2 and 3 is
     in a file of case 4. A file that you write whole gets no `Modified by`
     line.
   - A new file made from more than one file of case 1 or case 2 with the
     same set of lines has those lines one time. Then it has every line under
     them in each source, each line one time. Then it has one new
     `Modified by` line for its own change, which names each source and a
     commit of theorem-labs/oss-verify-proofs that holds it.
   - A file that is of case 4 before the change and takes code copied from a
     file with Anthropic's lines keeps its own lines. The copied code goes in
     a new file with Anthropic's two lines, the lines that the source has
     under them, then one new `Modified by` line of its own that names the
     source and a commit of theorem-labs/oss-verify-proofs that holds it. A
     new file made from a file with Anthropic's lines and code copied from a
     file of case 4 is two files. A new file made only from files of case 4
     is of case 4, with the Theorem Labs line over the MIT tag when a source
     has that line, and gets no `Modified by` line.
   - A new file that you make from code of a file with Anthropic's lines and
     lemmas that you write yourself is one file of case 2. It has Anthropic's
     two lines, the lines that the source has under them, then one new
     `Modified by` line of its own. Instruction words or data that you write
     are not such lemmas: they do not share a file with that code.
   - Code from a file is text copied from it: a definition, a statement or a
     proof, whole or with other names or arguments. Code that you write is
     not code from a file, also when it calls lemmas of that file or has a
     `Require` of it. A copied proof that names no lemma or definition that
     the source file defines is not code from it. A lemma whose proof is code
     from a file goes, with its statement, where that code goes.

   A changed file of case 1, 2 or 3 has one new `Modified by` line of its own,
   true of this file: who changed it, when, and what changed in it, from its
   diff against the file it came from. A file made from part of a file, or
   from more than one file, is a changed file, and a change of addresses,
   numbers or module names is a change. For code taken into a file that
   already has Anthropic's two lines, this is the one line case 2 names. A
   whole copy of one file that you did not change gets no new line. The new
   line goes under the licence lines that are there, after the last
   `Modified by` line, and the lines that are there stay as they are. A
   change that Theorem Labs made is in the name `Theorem Labs`. A commit
   that a new `Modified by` line names is a commit of
   theorem-labs/oss-verify-proofs. Cases 1, 2 and 4 and the rules are yours
   to apply, and case 3 is a maintainer's. The pull request says which
   files came from which files of the repository, and the maintainer
   records that in the build record. The pull request adds no notices,
   attribution or licence file, and changes nothing in `LICENSES/`,
   `NOTICE`, a project's `NOTICE` or `LICENSE`.

   What the checks do with licence lines:

   - `oft lint`, its `licence` rule, in every kind of run: in each `.v` file
     under a fuzz target's `proofs/` that the run reads, it refuses licence
     lines whose form is wrong. The paragraph on `licence-pending` entries
     below says which files a run reads. The wrong forms are a licence tag,
     a copyright of Anthropic or the copyright line of a project's `NOTICE`,
     in any case, after line 10, a changed copyright line of Anthropic (the
     line is `(* Copyright <year> Anthropic PBC *)`, and in a file that has
     that line a comment may restate its words), the words of the copyright
     line of a project's `NOTICE` in another case than that line's, a second
     tag that names another licence, a licence other than
     `Apache-2.0 OR MIT`, `MIT` and `LicenseRef-Proprietary` (in a file of
     case 3, a licence other than its row's), Anthropic's copyright line
     with no tag or with a tag other than `Apache-2.0 OR MIT`, that tag
     without Anthropic's copyright line, and a licence tag, Anthropic's
     copyright line or the copyright line of a project's `NOTICE` (the
     paragraph before case 4) in a file whose first line begins with one of
     these two texts:
     `(* Machine-generated data computed from the task's compiled program image`
     or
     `(* This file states or restates instruction words of the task's compiled program`.
     The wrong forms are also the tag `LicenseRef-Proprietary` in a project
     whose `project.yaml` does not say `release: private` or whose folder
     holds no `NOTICE`, that tag without the copyright line that names its
     own project's `NOTICE` above it in the first 10 lines, that copyright
     line with another tag or with no tag, a copyright line that names
     another project's `NOTICE`, and, in a project whose `project.yaml` says
     `release: private` and whose folder holds a `NOTICE`, the tag `MIT` and
     no licence line in a file whose first line begins with neither of the
     two texts. It also refuses a file that a row of
     `tools/oft/third-party-proofs.yaml` names whose bytes are not the ones
     the row pins, one whose bytes are the ones the row pins while its
     project's licence file is not in `LICENSES/` or is not one that lint
     pins, a licence text that lint pins whose bytes are not the pinned
     ones, and, as case 4 says, a file whose first 10 lines hold no licence
     line but name a licence in words. The rule knows a file of case 1 only
     by these two texts, and a file of case 3 only by its row. It reads a
     `Modified by` line only for a licence tag, a copyright of Anthropic or
     the copyright line of a project's `NOTICE`. It reads each file on its
     own. No rule of `oft lint` compares one proof file's text with another
     proof file's, so lint finds no copy and never says which case a file is
     of. In a fuzz target with a `licence-pending` entry (below), its
     refusals do not fail lint.
   - `oft lint` with `--pr-kind maintainer` (the default of `./oft lint`) or
     `--pr-kind release`: the `licence` rule also refuses Anthropic's lines
     in a fuzz target whose build record, `provenance/PROVENANCE.yaml`, does
     not list the three licence texts of Anthropic's proofs under
     `proofs.texts`. The maintainer writes that record. With
     `--pr-kind contributor`, the kind of a pull request from outside, the
     `licence` rule does not read the build record. So in a run of that
     kind, a file whose licence lines have the right form passes, also when
     they are not the lines of its case, and Anthropic's lines pass in a fuzz
     target whose build record does not list those texts.
   - One step of the lint job of `pr.yml`, the strip check, compares each
     proof file that the head changes, moves or deletes against the base
     with its file at the head. On a push to `main` that has no base to
     compare with, the base is the pushed commit, so it compares no file.
     A proof file is a `.v` file under a fuzz target's `proofs/`,
     outside `proofs/provenance/`. For a moved file, its file at the head is
     the one that git's rename detection finds. For a deleted file, it is a
     file that the change adds or changes whose text is the same once the
     leading comments, or the licence lines, are taken off. A deleted file
     with no such file is not compared. The check fails when such a file
     holds `Copyright <year> Anthropic PBC` in its first 10 lines at the base
     and not at the head, and its unit at the base has a licence record. A
     unit has a licence record when its
     `proofs/provenance/evidence/licence/made-from.tsv` is in the tree at the
     base or at the head: today `curl/fuzz_bufq`, `curl/fuzz_fnmatch` and
     `libreac/fuzz_scene`. The check does not fail on a file that a
     `left-bare.tsv` declares. That is the
     `proofs/provenance/evidence/licence/left-bare.tsv` of the unit that the
     file's path is in at the head, and its row holds the path relative to
     that unit's `proofs/`, a tab and a reason. So for a file that moves to
     another unit, the unit at the base decides whether the check fails, and
     the unit at the head holds the declaration. A row declares a file only
     when the file at the head is a UTF-8 file, not a symbolic link, whose
     first 10 lines hold no `Copyright <year> Anthropic PBC`, no comment that
     opens `(* Copyright <year> `, `(* SPDX-License-Identifier:` or
     `(* Modified by `, and no line that begins
     `(* Machine-generated data computed` or
     `(* This file states or restates instruction words`. The made-from
     check of a unit (`made_from.py --check`) also reads that unit's
     `left-bare.tsv`, through `dev/licence/made_from.py`; the next bullet
     says which runs run that check. When the file's unit at the base has
     no licence record, the strip check prints a notice and does not fail.
     It fails a file only on the words
     `Copyright <year> Anthropic PBC` in its first 10 lines, wherever they
     are on a line. It reads the other licence lines only to find
     whether a row declares a file and to pair a deleted file with another.
     It runs no code of the change, whatever the kind of the run.
   - The made-from check is the `made_from` job of `pr.yml`. It runs only
     after the lint job passes, and only for a fuzz target whose
     `proofs/provenance/` holds a `made_from.py` or a `made-from.tsv`: for
     such a fuzz target when the change touches its `proofs/provenance/` or
     its `images/dune`, and for every fuzz target whose `proofs/provenance/`
     holds a `made-from.tsv` when the change touches `dev/licence/`,
     `tools/oft/rocq.py`, the job or the list of paths it reads in `pr.yml`,
     a `.gitattributes` or a path that git quotes, or has no base to compare
     with. When the plan's `hold` is `none` (in a merge queue group, on a
     push, and on a pull request that is no draft and has the label
     `check`), it also takes each fuzz target whose `proofs/provenance/`
     holds a `made-from.tsv` and whose `proofs/` the change touches outside
     `proofs/provenance/`. In every kind of run, it first fails each such
     fuzz target whose `made_from.py` or `made-from.tsv` is not in
     `proofs/provenance/evidence/licence/`, beside the other. On a pull
     request of kind `contributor` it then stops, since it runs no code of
     the change. In every other kind of run, it then takes each fuzz target
     that passed. When the tree has `dev/licence/made_from.py`, it first runs
     `dev/licence/made_from.py --unit-file` on the fuzz target's
     `made_from.py`, and a fuzz target that fails it gets no `--check`. Then
     it runs `proofs/provenance/evidence/licence/made_from.py --check`. A
     fuzz target that fails a step fails the job, with two exceptions of
     `--check`. Exit 2, a check that could not decide, is a warning, and
     nothing is failed. Exit 3 comes when the record names no path twice,
     and every row that differs is one a run gives again, for a file that
     the record holds in no row of another kind: it fails the job as exit 1
     does, except for a fuzz target that the `hold` reason above alone
     names, where it is a warning that gives the number of rows that differ
     and the first 20 of them. Exit 5, a defect of the generator's own code,
     fails the job for every fuzz target. The `--check` compares
     files: by a rule of its own, it finds which proof files were made from a
     file with Anthropic's lines, and compares the result with the fuzz
     target's licence record. What a unit's licence record,
     `provenance/evidence/licence/made-from.tsv`, reports and does not report
     is in the module docstring of
     [dev/licence/made_from.py](../dev/licence/made_from.py).
   - The name scan, `ossv-binscan`, holds a fixed list of names, and refuses
     a name of that list in a comment, for example in a `Modified by` line.
     A reviewed row of its exceptions file clears a hit of a name of that
     list. In Theorem Labs' internal repository, where `tools/publish/`
     holds the scan, `pr.yml` runs it in the lint job after the lint step
     passes: on a pull request that is not a draft, on a merge queue group,
     and on a push to `main` that no merge queue group checked first. There
     it reads each file under a fuzz target's `proofs/` that the head adds
     or changes against the base and that the lint job checked out. On a
     push to `main` that has no base to compare with, the base is the pushed
     commit, so it reads no file. A merge queue group and a push to `main`
     check out every file. On a pull request whose lint reads only the
     changed files, the job can leave out each file under `proofs/lib/`,
     other than `proofs/lib/dune` and the files under
     `proofs/lib/Instances/`, that is the same as in the tree that lint
     compares with. When the job leaves those files out and the pull
     request's lint record holds, that tree is the one its last passing lint
     read, so of those files the scan reads only the ones that changed since
     that lint, and it can read none of them. The platform release runs it
     over what it publishes. It does not run on a pull request to
     theorem-labs/oss-verify-proofs, which has no `tools/publish/`.

   A fuzz target whose licence lines are applied in a series of their own has
   a `licence-pending` entry in `tools/oft/lint-exceptions.yaml`: its unit
   (`<project>/<fuzz target>`), the date the series is due, the series' pull
   request (or `pending`) and a reason. Lint then reports that fuzz target's
   licence refusals as pending and does not fail on them. The series removes
   its own entry. An entry whose fuzz target has `.v` files under its
   `proofs/` and no licence refusal left fails a lint whose per-file rules
   (the rules that read each file's text, `licence` among them) read every
   file. It does not fail such a lint while the entry names its series' pull
   request (`#<number>`) and its due date has not passed, or when a sparse
   checkout leaves out a file of its fuzz target. It does not fail a lint
   whose per-file rules read only the changed files. The per-file rules read
   every file in a lint without `--changed-only`, except the files that a
   sparse checkout leaves out. A lint with `--changed-only` names a commit,
   and it also reads every file when a path that differs from that commit
   is a fact (a file that `tools/oft/paths.py` classes as facts,
   other than `CHANGELOG.md`), a finding's `finding.yaml`, a build record's
   `provenance/PROVENANCE.yaml`, a project's `NOTICE`, a `.gitattributes`,
   `tools/oft/lint-exceptions.yaml`, `tools/oft/third-party-proofs.yaml` or
   a licence text that lint pins (`LICENSES/anthropic-proofs-LICENSE`,
   `-LICENSE-MIT` and `-NOTICE`, and `LICENSES/coq-community-huffman-LICENSE`),
   or, when lint runs from the checkout as in step 3, a file under
   `tools/oft/`. In step 3 that commit is the
   merge base with `origin/main`. In CI it can be a commit of the tree that
   the pull request's last passing lint read, and then a path that an
   earlier push changed does not count. An entry may wait for a fuzz target
   whose proofs have not come yet. After its due date it fails a lint with
   no `--changed` list of changed paths, and a lint whose list holds a path
   of its fuzz target. When the list holds
   `tools/oft/lint-exceptions.yaml`, it fails a lint that does not compare
   the entries with the base's, such as the lint of step 3. A lint that
   compares them (`--pending-base`, as CI's lint by the base's rules does)
   fails it for that file only when the change adds or changes the entry.
   For any other change it is a warning. So in that lint of CI, a series
   that removes its own entry does not fail on the due date of another
   entry. It can fail on another entry that has no licence refusal left, as
   above, when its change to `tools/oft/lint-exceptions.yaml` has the
   per-file rules read every file. CI's lint by the base's rules passes
   `--pending-base`, so it refuses an entry that the base does not have in a
   pull request that changes proof files. A pull request of the tools can
   add an entry, and its review judges it. A release carries none.
8. **No unused files.** Each `.v` file that the pull request adds is required
   by a proof, directly or through other files. A file that witnesses the
   premises of a released statement, and each file such a witness requires,
   is exempt: by design no released `Proof.v` requires them, and the release
   cut ships and builds `lib/` anyway.

## Steps

1. On a branch, put the proofs in `projects/<project>/<harness>/proofs/`: one
   directory per statement ([proving.md](proving.md)), and the `.v` files they
   share, if any, in `lib/`, at any depth. A file `lib/A/B.v` is the module
   `OSSVerify.Proofs.<project>.<harness>.lib.A.B`, as in the harness's
   `rocq:` field. In the project and harness names, each character other than
   a letter, a digit or `_` is written as `_` (knot-dns is `knot_dns`), and a
   name that starts with a digit gets `h_` in front (`64bit_fuzzer` is
   `h_64bit_fuzzer`).
2. Remove each file that no proof requires and that requirement 8 does not
   exempt, and give every file its licence lines (requirement 7). An agent
   follows
   [the adding-a-proof skill](../.claude/skills/adding-a-proof/SKILL.md),
   which goes through the files one at a time.
3. Run the lint and the check that CI runs, `oft lint` and `oft check`.
   Commit, with what `oft generate --skip-shared` renders (the shared pages
   and the index are rendered after the merge) and a DCO sign-off, before
   the lint, so that `git diff` lists every changed path:

       ./oft fetch <project>
       ./oft generate --skip-shared
       git add -A && git commit -s
       changed="$(mktemp)"
       git -c core.quotePath=false diff --no-renames --name-only origin/main...HEAD > "$changed"
       ./oft lint --changed "$changed" --changed-only "$(git merge-base origin/main HEAD)" --pr-kind contributor
       python3 -m pip install --require-hashes --target "$HOME/oft-pydeps" -r tools/oft/requirements.txt
       docker run --rm --network none --ulimit stack=-1:-1 -u "$(id -u):$(id -g)" -e HOME=/tmp -e PYTHONPATH=/pydeps \
         -v "$HOME/oft-pydeps:/pydeps:ro" -v "$PWD:/work" -w /work <checker image of release.yaml> \
         ./oft check <project>/<harness> --parts statements,proofs

   The list of changed paths goes to a file outside the checkout, so that
   lint does not read it and no commit holds it. It lists each path that your
   branch changes since its merge base with `origin/main`, as CI's list does.
   When `origin` is your fork, write the remote of
   theorem-labs/oss-verify-proofs (for example `upstream`) in place of
   `origin` in the two commands that name `origin/main`. Give `--pr-kind`
   the kind that CI gives your pull request (`KIND` in
   `.github/workflows/pr.yml`): `contributor`, as in the command, for a pull
   request from outside, `maintainer` for one from an owner, a member or a
   collaborator of the repository or from a branch of it, and `release` for
   such a pull request whose branch name starts with `release/`, in capitals
   or not.

   A harness's counterexamples are checked in the runner image with
   `--parts counterexamples` (tools/oft/ci/check-units.sh, step 4, "Counterexamples").

4. Open a pull request, and say in it which files came from which files of the
   repository. CI runs these checks and more
   ([checking.md](checking.md#what-ci-runs)). A maintainer reviews the proof,
   writes or updates its build record, and merges it.
