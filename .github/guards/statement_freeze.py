#!/usr/bin/env python3
# Copyright 2026 Theorem Labs, PBC
# SPDX-License-Identifier: Apache-2.0
"""Name every change this pull request makes to what this repository ASSERTS, and refuse it unless
a code owner has approved that head.

    statement_freeze.py --base SHA --head SHA [--approvals FILE] [--owners FILE]
    statement_freeze.py --self-test

WHAT IT WATCHES, and what it deliberately does not.

    watched   **/Statements.v                 the text of the theorem statements themselves
    watched   index/statements.tsv            the kind, builds, reading, exits and status of a row
    NOT       any proof body, anywhere        the kernel is the reviewer for a proof

That last line is a ruling, not a preference: "It is correct that the proof body needs no Human
Reviewer" -- the owner of this work, 2026-11-07, answering the question directly. (The reference
for it is an internal one, and this repository's own lint refuses an internal tracker link in a
published file, so it is not written here; the maintainers have it.) If this check ever fires on
a proof file, that is a defect in this file, not caution. The self-test holds it to that with
fixtures that change a proof and must pass.

WHAT THIS ADDS OVER CODEOWNERS, stated without inflation. CODEOWNERS already requires a code
owner's approval on these paths, and the ruleset already enforces it. **This check is not a second
lock on that door.** What it adds is that the change is NAMED: `index/statements.tsv` has twenty
thousand rows and a diff of it is unreadable, so an approver cannot see from the diff that one row
went from `open` to `proved`, or that a statement's `reading` moved from `budget` to `may-fail`.
This prints one line per changed assertion, old value and new value, by statement id, in a log
that is part of the merge record -- so the change is visible, named and kept, rather than only
blocked. It also leaves that record on a merge a CODEOWNERS gate never sees: a ruleset bypass is
per ruleset, so the Apps in `bypass_actors` merge without a code owner, and this job still runs
and still writes down what moved.

EXITS

    0   nothing watched changed, or a code owner approved this head
    1   something watched changed and no code owner has approved this head
    2   the check could not finish (a git call failed, a table it cannot parse, a bad argument)
"""

import argparse
import json
import os
import re
import subprocess
import sys

# A statement FILE: `Statements.v` that is not inside a proof or counterexample tree. A
# cross-model audit put a changed proof body in `projects/p/h/proofs/Statements.v` and this
# check fired on it, which is the one thing it must never do.
STATEMENTS_V = re.compile(r"(?:^|/)Statements\.v$")
NOT_A_STATEMENT_FILE = re.compile(r"(?:^|/)(proofs|counterexamples)/")
# A proof script inside a watched file. A `Statements.v` of this repository holds none -- its
# own header says "this file changes only when a statement does" -- but if one ever does, the
# proof in it is still a proof body and still needs no human.
PROOF_OPEN = re.compile(r"^\s*(Proof|Next Obligation)\b")
PROOF_CLOSE = re.compile(r"^\s*(Qed|Defined|Admitted|Abort)\s*\.")
INDEX = "index/statements.tsv"
# The columns of a statements row that say what is ASSERTED. `detail`, `revision`, `fingerprint`
# and `proof` are bookkeeping: they record how a claim was checked, not what the claim is.
ASSERTED = ("kind", "builds", "reading", "exits", "status")


class Stop(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status, self.message = status, message


def die(message):
    raise Stop(2, message)


def git(*args):
    done = subprocess.run(("git",) + args, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if done.returncode != 0:
        die("git %s failed (%d): %s" % (" ".join(args), done.returncode,
                                        done.stderr.decode("utf-8", "replace").strip()))
    return done.stdout


def blob(rev, path):
    at = subprocess.run(("git", "cat-file", "-e", "%s:%s" % (rev, path)),
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if at.returncode != 0:
        return None
    return git("cat-file", "blob", "%s:%s" % (rev, path)).decode("utf-8", "replace")


def rows_of(text, where):
    """`id` -> {column: value} for a statements table. A table this cannot parse stops the check:
    reading twenty thousand rows as none is the quiet failure this whole check exists against."""
    if text is None:
        return {}
    lines = [ln for ln in text.split("\n") if ln != ""]
    if not lines:
        die("%s is empty" % where)
    header = lines[0].split("\t")
    # A repeated column name, or a repeated id, makes the table ambiguous, and `dict(zip(...))`
    # and `out[id] = row` would resolve the ambiguity SILENTLY, in favour of the last one. An
    # audit used both: a second `status` column with `proved` in the first and `open` in the
    # second, and a changed row followed by an unchanged duplicate of its id. Each hid a real
    # change and this check said nothing. Neither is a table anyone writes by accident, so both
    # stop the check rather than being resolved one way or the other.
    if len(set(header)) != len(header):
        repeated = sorted({c for c in header if header.count(c) > 1})
        die("%s repeats the column name(s) %s, so a row has no one value for them"
            % (where, ", ".join(repeated)))
    for column in ("id",) + ASSERTED:
        if column not in header:
            die("%s has no `%s` column; its header is %r" % (where, column, header))
    out = {}
    for number, line in enumerate(lines[1:], 2):
        cells = line.split("\t")
        if len(cells) != len(header):
            die("%s line %d has %d columns, not %d" % (where, number, len(cells), len(header)))
        row = dict(zip(header, cells))
        if row["id"] in out:
            die("%s line %d repeats the statement id %s" % (where, number, row["id"]))
        out[row["id"]] = row
    return out


def meaningful(text):
    """A file's lines with blank ones dropped, for comparing text. Whitespace at the end of a line
    is dropped too; nothing else is normalised. A comment IS part of a statement -- it is what says
    what the theorem means -- so comments are compared like any other line."""
    out, in_proof = [], False
    for line in (text or "").split("\n"):
        if not line.strip():
            continue
        if in_proof:
            in_proof = PROOF_CLOSE.match(line) is None
            continue
        if PROOF_OPEN.match(line):
            in_proof = PROOF_CLOSE.search(line) is None
            continue
        out.append(line.rstrip())
    return out


def watched_changes(base, head, read=blob, changed=None):
    """(statement changes, Statements.v changes). Each is a list of printable lines."""
    if changed is None:
        names = git("diff", "--name-only", "-z", "--no-renames", base, head).split(b"\0")
        changed = [n.decode("utf-8", "replace") for n in names if n]

    statements = []
    if INDEX in changed:
        old = rows_of(read(base, INDEX), "%s at the base" % INDEX)
        new = rows_of(read(head, INDEX), "%s at this head" % INDEX)
        for ident in sorted(set(old) - set(new)):
            statements.append("%s: REMOVED (it was %s)" % (ident, old[ident]["status"]))
        # A row with no counterpart at the base is a claim this repository did not make before.
        # Nothing of it was "changed", so an earlier version of this check said nothing about it
        # -- which meant a whole new statement, in any state, arrived unnamed.
        for ident in sorted(set(new) - set(old)):
            statements.append("%s: NEW (%s, %s, reading %s, status %s)"
                              % (ident, new[ident]["kind"], new[ident]["builds"],
                                 new[ident]["reading"], new[ident]["status"]))
        for ident in sorted(set(old) & set(new)):
            for column in ASSERTED:
                before, after = old[ident][column], new[ident][column]
                if before != after:
                    statements.append("%s: %s %s -> %s" % (ident, column, before, after))

    texts = []
    for path in sorted(changed):
        if not STATEMENTS_V.search(path) or NOT_A_STATEMENT_FILE.search(path):
            continue
        before, after = meaningful(read(base, path)), meaningful(read(head, path))
        if before == after:
            continue
        added = len([ln for ln in after if ln not in set(before)])
        removed = len([ln for ln in before if ln not in set(after)])
        texts.append("%s: %s (%d line(s) added, %d removed)"
                     % (path, "new file" if read(base, path) is None else "text changed",
                        added, removed))
    return statements, texts


def owners_of(codeowners):
    """Every owner named anywhere in CODEOWNERS, lower-cased, without the `@`.

    Deliberately not per-pattern: this check does not re-implement CODEOWNERS matching, which
    GitHub already does and already enforces. It asks the weaker, honest question -- did one of
    the people this repository calls owners approve this head -- and says so in those words."""
    out = set()
    for line in (codeowners or "").split("\n"):
        line = line.split("#", 1)[0]
        for token in line.split()[1:]:
            out.add(token.lstrip("@").lower())
    return out


# The review states that replace an owner's previous verdict. COMMENTED and PENDING do not:
# a comment on an approved pull request withdraws nothing. Anything else this check has not seen
# is treated as replacing the verdict, so an unknown state can only ever LOSE an approval.
DECIDING = ("APPROVED", "CHANGES_REQUESTED", "DISMISSED")


def approved_by(approvals, head, owners):
    """The owners whose EFFECTIVE review of exactly this head is APPROVED.

    Effective, not "any review ever": an audit submitted APPROVED and then CHANGES_REQUESTED from
    the same owner and this check still said "approved at this head". A gate that honours a
    withdrawn approval is a gate that can be walked through. GitHub returns reviews oldest first,
    so the last deciding one per login wins.

    `commit_id` must be the head as well: the ruleset dismisses an approval on a push
    (`dismiss_stale_reviews_on_push`), and an approval of an earlier head was an approval of
    different statements."""
    verdict = {}
    for review in approvals or []:
        login = ((review.get("user") or {}).get("login") or "").lower()
        if login not in owners or review.get("commit_id") != head:
            continue
        state = review.get("state")
        if state in ("COMMENTED", "PENDING"):
            continue
        verdict[login] = state
    return sorted(login for login, state in verdict.items() if state == "APPROVED")


# ------------------------------------------------------------------------------------------------
# The self-test: fixtures whose verdict is known, including one that MUST pass.

HEADER = "id\tkind\tbuilds\treading\texits\tstatus\tdetail\trevision\tfingerprint\tproof"
ROW = "p/h/asan_agrees\tagreement\tplain,asan\tmay-fail\t-\t%s\t-\t1\t%s\t-"
FIXTURES = (
    # name, base tree, head tree, must the verdict be "watched changed"?
    ("a status flipped from open to proved",
     {INDEX: HEADER + "\n" + ROW % ("open", "aa")},
     {INDEX: HEADER + "\n" + ROW % ("proved", "aa")}, True),
    ("a reading changed from may-fail to budget",
     {INDEX: HEADER + "\n" + ROW % ("open", "aa")},
     {INDEX: HEADER + "\n" + ROW.replace("may-fail", "budget") % ("open", "aa")}, True),
    ("a statement row removed",
     {INDEX: HEADER + "\n" + ROW % ("open", "aa")}, {INDEX: HEADER}, True),
    ("the text of a Statements.v changed",
     {"projects/p/h/Statements.v": "Theorem t : 1 = 1.\n"},
     {"projects/p/h/Statements.v": "Theorem t : 1 = 2.\n"}, True),
    ("a comment in a Statements.v changed, which is part of what it asserts",
     {"projects/p/h/Statements.v": "(* holds for the plain build *)\nTheorem t : 1 = 1.\n"},
     {"projects/p/h/Statements.v": "(* holds for every build *)\nTheorem t : 1 = 1.\n"}, True),
    # The ones that MUST NOT fire. A check that fires on a proof body re-imposes a human gate the
    # owner of this repository ruled unnecessary, so each of these is as load-bearing as the five
    # above.
    ("a proof body changed", {"projects/p/h/proofs/lib/A/Pf.v": "Proof. lia. Qed.\n"},
     {"projects/p/h/proofs/lib/A/Pf.v": "Proof. now lia. Qed.\n"}, False),
    ("a Statements.v inside a proofs/ tree changed, which is a proof file",
     {"projects/p/h/proofs/Statements.v": "Proof. lia. Qed.\n"},
     {"projects/p/h/proofs/Statements.v": "Proof. now lia. Qed.\n"}, False),
    ("a proof block inside a watched Statements.v changed",
     {"projects/p/h/Statements.v": "Theorem t : True.\nProof. exact I. Qed.\n"},
     {"projects/p/h/Statements.v": "Theorem t : True.\nProof. now exact I. Qed.\n"}, False),
    ("a proof file named Statements_proof.v changed",
     {"projects/p/h/proofs/Statements_proof.v": "Proof. lia. Qed.\n"},
     {"projects/p/h/proofs/Statements_proof.v": "Proof. now lia. Qed.\n"}, False),
    ("a fingerprint was recomputed, which records how a claim was checked",
     {INDEX: HEADER + "\n" + ROW % ("open", "aa")},
     {INDEX: HEADER + "\n" + ROW % ("open", "bb")}, False),
    ("a Statements.v gained blank lines and trailing spaces only",
     {"projects/p/h/Statements.v": "Theorem t : 1 = 1.\n"},
     {"projects/p/h/Statements.v": "\nTheorem t : 1 = 1.   \n\n"}, False),
    ("a statement row was added, which is a claim this repository did not make before",
     {INDEX: HEADER}, {INDEX: HEADER + "\n" + ROW % ("proved", "aa")}, True),
    ("a file outside the watched set changed",
     {"README.md": "a\n"}, {"README.md": "b\n"}, False),
)


def self_test():
    failures, fired = [], 0
    for name, base_tree, head_tree, must_fire in FIXTURES:
        trees = {"BASE": base_tree, "HEAD": head_tree}
        read = lambda rev, path: trees[rev].get(path)                      # noqa: E731
        changed = sorted(set(base_tree) | set(head_tree))
        try:
            statements, texts = watched_changes("BASE", "HEAD", read=read, changed=changed)
        except Stop as stop:
            failures.append("%s: the check stopped (%s)" % (name, stop.message))
            continue
        did = bool(statements or texts)
        fired += int(did)
        if did != must_fire:
            failures.append("%s: fired=%s, must be %s" % (name, did, must_fire))
    print("STATEMENT FREEZE: self-test: %d of %d fixtures gave their known verdict; %d of them "
          "must fire and did, %d must not fire and did not"
          % (len(FIXTURES) - len(failures), len(FIXTURES),
             len([f for f in FIXTURES if f[3]]), len([f for f in FIXTURES if not f[3]])))
    if failures:
        raise Stop(2, "SELF-TEST FAILED, so this check's verdict on a real change means nothing:"
                      "\n  " + "\n  ".join(failures))
    return fired


def main(argv):
    parser = argparse.ArgumentParser(add_help=True)
    parser.add_argument("--base")
    parser.add_argument("--head")
    parser.add_argument("--approvals", help="JSON from GitHub's list-reviews endpoint")
    parser.add_argument("--owners", help="a CODEOWNERS file", default=".github/CODEOWNERS")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--report-only", action="store_true",
                        help="name what changed and exit 0 whatever it is (a merge group, where "
                             "the approval already happened on the pull request)")
    args = parser.parse_args(argv)

    self_test()
    if args.self_test:
        print("STATEMENT FREEZE: nothing was read (--self-test).")
        return 0
    if not args.base or not args.head:
        die("--base and --head are required")

    statements, texts = watched_changes(args.base, args.head)
    if not statements and not texts:
        print("STATEMENT FREEZE: this change alters no theorem statement and no asserted column "
              "of %s. Proof bodies, fingerprints and everything else are not read." % INDEX)
        return 0

    print("::group::what this change asserts differently")
    for line in texts:
        print("  statement text  %s" % line)
    for line in statements:
        print("  statement row   %s" % line)
    print("::endgroup::")
    rows = len({line.split(":", 1)[0] for line in statements})
    print("STATEMENT FREEZE: %d statement(s) and %d statement file(s) changed, in %d named line(s)."
          % (rows, len(texts), len(statements) + len(texts)))

    if args.report_only:
        print("STATEMENT FREEZE: reporting only; the approval was given on the pull request.")
        return 0

    owners = owners_of(read_file(args.owners))
    if not owners:
        die("%s names no owner, so this check cannot tell whether an owner approved. A repository "
            "that asserts theorems without a CODEOWNERS file is the thing this check is for."
            % args.owners)
    approvals = json.loads(read_file(args.approvals)) if args.approvals else []
    who = approved_by(approvals, args.head, owners)
    if who:
        print("STATEMENT FREEZE: approved at this head by %s, who is a code owner." % ", ".join(who))
        return 0
    raise Stop(1, "this change alters what this repository asserts, and no code owner has an "
                  "APPROVED review of this exact head (%s). Owners named in %s: %s. An approval of "
                  "an earlier head does not count: the ruleset dismisses it on a push, and it was "
                  "an approval of different statements."
                  % (args.head[:12], args.owners, ", ".join(sorted(owners))))


def read_file(path):
    if not path:
        return ""
    try:
        with open(path, encoding="utf-8") as handle:
            return handle.read()
    except OSError as exc:
        die("cannot read %s (%s)" % (path, exc))


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except Stop as stop:
        sys.stderr.write("::error::STATEMENT FREEZE: %s\n" % stop.message)
        sys.exit(stop.status)
