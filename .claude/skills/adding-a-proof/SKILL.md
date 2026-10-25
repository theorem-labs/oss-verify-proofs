---
name: adding-a-proof
description: Use when adding, porting or changing a proof, a proof library (lib/) or a counterexample in this repository, and before opening its pull request; above all when files are copied or adapted from proofs already here.
---

# Adding a proof

A proof enters the repository when its pull request meets every requirement in
[docs/adding-a-proof.md](../../../docs/adding-a-proof.md). Do these steps in order. Nothing checks step 3 for you:
`oft check` and `oft lint` pass without it (CI only refuses a change to `LICENSE`, `NOTICE` or `LICENSES/`), and a
review sends back a pull request that skips it.

## 1. Put the proof in place

- One directory for each statement, `proofs/<project>/<harness>/<statement>/`, with `Proof.v` (or `Refutation.v`),
  any helper `.v` files, and `proof.yaml` ([docs/proving.md](../../../docs/proving.md)). Files that the proofs of a
  harness share go in `proofs/<project>/<harness>/lib/`. Module names follow step 1 of
  [docs/adding-a-proof.md](../../../docs/adding-a-proof.md).
- Change nothing outside `proofs/`, `counterexamples/` and `docs/`, apart from the files that `./oft generate`
  renders.
- A counterexample that shows a memory-safety bug in a library goes to that library first
  ([SECURITY.md](../../../SECURITY.md)).

## 2. Remove the files that the proof does not use

Each `.v` file that you add is required by a `Proof.v` or `Refutation.v`, directly or through other files. Follow the
`Require` lines from each proof, and delete each file that you added and nothing requires. `From A Require B` also
finds a file `A/x/B.v`, so `oft check` (step 4) is the test: it fails if you deleted a file that a proof needs.

## 3. Give every file its licence lines

A file's licence lines are its first lines that say where it comes from and under which licence it is, and each
`Modified by` line under them. In this repository they are one of these:

- Anthropic's two lines, sometimes with a third line under them that says whose its proofs and statements are:

      (* Copyright 2026 Anthropic PBC *)
      (* SPDX-License-Identifier: Apache-2.0 OR MIT *)

  A proof library file (`lib/`) with these lines came from Anthropic's proofs. It stays under Apache-2.0 OR MIT:
  Anthropic's licence covers it, not the repository's `LICENSE`.
- A one-line comment, in a file that restates the instruction words of a program or holds data computed from one,
  beginning `(* This file states or restates instruction words` or `(* Machine-generated data computed from`. The
  program's code in such a file keeps the program's licences, and the file has no Anthropic lines.
- None, in a file written here, under the MIT licence: the `Proof.v` of each statement's directory, and the library
  files with no licence lines.

Go through your `.v` files one at a time, and take the first case that fits:

1. **It restates the instruction words of a program, or holds data computed from one**, whoever wrote it: its first
   line is the one-line comment of its kind, copied from the file it came from or from a file of this repository of
   the same kind, then the `Modified by` lines of the file it came from.
2. **It holds code from a file with Anthropic's lines** (a whole copy, or a part of one): those lines and the lines
   that file has under them (a third line, its `Modified by` lines), unchanged. A file made from part of a file with
   the one-line comment, holding none of its instruction words or data, gets Anthropic's two lines, then that file's
   `Modified by` lines.
3. **Any other file**: you wrote it, or it holds code only from files with no licence lines, such as a statement's
   `Proof.v`. It is under the MIT licence, and has no licence lines.

In cases 1 and 2, if you changed anything, add one line under the licence lines, true of this file, from its diff
against the file that it came from: `(* Modified by <name>, <year>-<month>: <what changed in this file>. *)`, for
example `(* Modified by Alex Doe, 2026-10: hex addresses, numbers and module names for the binaries of
zlib/checksum_fuzzer. *)`. The name is that of the person who signs the commits off. A change of addresses, numbers
or module names is a change. A copy that you did not change gets no line.

Then, for the whole pull request:

- Add no notices, attribution or licence file, and change nothing in `LICENSES/`, `NOTICE` or `LICENSE`.
- In the pull request, say which of your files came from which files of the repository. The maintainer writes or
  updates the harness's build record (`provenance/`) from that.

## 4. Check, then open the pull request

Run step 3 of [docs/adding-a-proof.md](../../../docs/adding-a-proof.md) as it is written: it commits what
`./oft generate` renders with `git commit -s`, lints the change, and runs `oft check` in the checker image
(counterexamples with `--parts counterexamples`, in the runner image). Sign every commit off: `git commit -s`.

## Mistakes that a review sends back

| Mistake | Instead |
|---|---|
| A changed copy with no `Modified by` line, because only addresses or names changed | A line on each changed file |
| One note pasted onto files that changed in different ways | A line on each file, true of that file |
| A `Modified by` line in someone else's name, or a line that was there edited | Your own line, under the lines that are there |
| A file made from part of a library file, with no licence lines | Anthropic's two lines, its `Modified by` lines, and yours |
| Anthropic's two lines on a file that restates a program's instruction words | The one-line comment of its kind |
| A notices file, or a statement that the repository's `LICENSE` covers the copied files | No such file; say in the pull request where the files came from |
| A build record that you wrote | Leave `provenance/` to the maintainer |
| Files that you added and no proof requires | Delete them |
