---
name: adding-a-proof
description: Use when adding, porting or changing a proof, a proof library (lib/) or a counterexample in this repository, and before opening its pull request; above all when files are copied or adapted from proofs already here.
---

# Adding a proof

A proof enters the repository when its pull request meets every requirement in
[docs/adding-a-proof.md](../../../docs/adding-a-proof.md). Do these steps in order.
The checks see only part of step 3: the `licence` rule of `oft lint` checks the form of each file's licence lines,
but it cannot tell that a file was copied or which case a file is of, and on a pull request from outside no check
does. A review sends back a pull request that skips step 3.

## 1. Put the proof in place

- One directory for each statement, `projects/<project>/<harness>/proofs/<statement>/`, with `Proof.v` (or
  `Refutation.v`), any helper `.v` files, and `proof.yaml` ([docs/proving.md](../../../docs/proving.md)). Files that
  the proofs of a harness share go in `projects/<project>/<harness>/proofs/lib/`. Module names follow step 1 of
  [docs/adding-a-proof.md](../../../docs/adding-a-proof.md).
- Change nothing outside the harness's `proofs/` and `counterexamples/` folders and `docs/`, apart from your fuzz
  target's files that `./oft generate --skip-shared` renders. The shared pages and the index (`tools/oft/paths.py`
  `SHARED`) are rendered after the merge, and lint refuses a pull request that carries one.
- A counterexample that shows a memory-safety bug in a library goes to that library first
  ([SECURITY.md](../../../SECURITY.md)).

## 2. Remove the files that the proof does not use

Follow the `Require` lines from each `Proof.v` or `Refutation.v`, and delete each `.v` file that you added and nothing
requires. `From A Require B` also finds a file `A/x/B.v`, so `oft check` (step 4) is the test: it fails if you deleted
a file that a proof needs. A file that witnesses the premises of a released statement, and each file it requires,
stays (requirement 8).

## 3. Give every file its licence lines

Requirement 7 of [docs/adding-a-proof.md](../../../docs/adding-a-proof.md) gives the forms of the licence lines, the
three cases, the rules for files made from other files, and what each check does with them. Read it whole first. Then:

1. Go through your `.v` files one at a time.
2. Split the copied code first: code copied from files with different sets of licence lines goes in separate files,
   one for each set. Instruction words or data never share a file with code from a file with Anthropic's lines.
3. Give each file the lines of its case: 1, it restates a program's instruction words or holds data computed from one;
   2, it is made from a file with Anthropic's lines, or from a part of a file of case 1 that holds none of its
   instruction words or data; 3, any other file, under the MIT licence. In a project whose `project.yaml` says
   `release: private` and whose folder holds a `NOTICE`, no file is of case 3: any other file is under that `NOTICE`,
   with its two lines `(* Copyright Theorem Labs. All rights reserved: see projects/<project>/NOTICE. *)` and
   `(* SPDX-License-Identifier: LicenseRef-Proprietary *)`, its own project in place of `<project>`.
4. A changed file of case 1 or 2 gets one new line of its own, true of this file, under the lines that are there, which
   stay as they are: `(* Modified by <name>, <year>-<month>: <what changed in this file>. *)`, for example
   `(* Modified by Theorem Labs, 2026-10: hex addresses, numbers and module names for the binaries of
   zlib/checksum_fuzzer. *)`. A change of addresses, numbers or module names is a change; a whole copy that you did
   not change gets no line. `<name>` is `Theorem Labs` for a change Theorem Labs made, never one of its people (the
   name scan of the platform release and of Theorem Labs' internal repository refuses one), and your own name for a
   change you make as an outside contributor. A commit the line names is a commit of theorem-labs/oss-verify-proofs.

## 4. Check, then open the pull request

Run step 3 of [docs/adding-a-proof.md](../../../docs/adding-a-proof.md) as it is written: it commits what
`./oft generate --skip-shared` renders with `git commit -s`, lints the change from its merge base with the kind that
CI gives the pull request, and runs `oft check`. A proof's check counts only on the checker image that release.yaml
pins (images.checker), and its counterexamples only on the runner image that release.yaml pins (images.runner). A
check on any other image, or on an image named by a digest from somewhere else, does not count. Sign every commit
off: `git commit -s`.

## Mistakes that a review sends back

| Mistake | Instead |
|---|---|
| One note pasted onto files of case 1 or 2 that changed in different ways | A line on each such file, true of that file |
| A new file made from part of the code of a library file that has Anthropic's lines, given no licence lines | Anthropic's two lines, that file's lines under them, then one new `Modified by` line of its own |
| A file of case 3 that was there before your change and copied a lemma from a file with Anthropic's lines, given Anthropic's lines over all its code | The copied lemma in a new file with Anthropic's two lines, the source's lines under them, then one new `Modified by` line that names the source and a commit of theorem-labs/oss-verify-proofs that holds it. The old file keeps its own lines |
| A new `Modified by` line that names a commit theorem-labs/oss-verify-proofs does not have | The same line with a commit of theorem-labs/oss-verify-proofs that holds the source |
| Anthropic's two lines on a file that restates a program's instruction words | The lines of case 1: the one-line comment of its kind, the `Modified by` lines of the file it came from, then its own new line when it changed |
| A file of a `release: private` project with a `NOTICE` given no licence lines, or `SPDX-License-Identifier: MIT` | The two lines of that project's `NOTICE`, unless the file is of case 1 or 2 (requirement 7, the paragraph before case 3) |
| A notices file, or a statement that the repository's `LICENSE` covers the copied files | No such file and no such statement. Say in the pull request where the files came from |
| A build record that you wrote | Leave the build record (requirement 6) to the maintainer |
