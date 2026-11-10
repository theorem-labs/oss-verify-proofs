#!/usr/bin/env python3
# Copyright 2026 Theorem Labs, PBC
# SPDX-License-Identifier: Apache-2.0
"""A moved binary pin must move the statements that are about that binary.

    pin_coherence.py --base SHA --head SHA
    pin_coherence.py --self-test

THE RULE, IN ONE SENTENCE. When a pull request changes the `sha256` of a build of a unit -- in
`projects/<p>/<h>/harness.yaml` under `builds:`, or in the `index/binaries.tsv` row for that build
-- every row of `index/statements.tsv` whose id starts `<p>/<h>/` and whose `builds` column names
that build must come out with a DIFFERENT `fingerprint`, and must be `open` unless a proof of that
unit changed in the same pull request; because a statement is about a binary, and a different
binary is a different claim.

WHY THAT RULE IS EXACT HERE AND NOT A HEURISTIC. `tools/oft/facts.py`'s `fingerprint()` puts the
line `build <name> <sha256>` into the hash, for each build the statement names, reading the sha256
from `harness.yaml`'s `builds`. So a moved build sha256 **must** move that statement's
fingerprint. A fingerprint that did not move is therefore not "probably stale": it was carried
over rather than recomputed, and this check can say so from the tree alone, with no build.

WHY IT EXISTS. A swapped binary makes a true statement false without touching one character of the
statement. Nobody reviewing the diff sees it: the statement file is unchanged, the statement row's
text is unchanged, and the only thing that moved is a hex digest in a build record. The statement
freeze (#28) watches the statement; this watches the thing the statement is ABOUT.

WHAT IT CANNOT DO, said at the top because it is the honest half. It cannot tell whether a
statement is TRUE of the new binary. That needs a build and a check, and no tree read substitutes
for one. It decides the part that IS decidable from the tree: that the statements about a moved
binary were revisited rather than carried over.

EXITS

    0   coherent (or no pin moved)
    1   a pin moved and the statements about it did not
    2   the check could not finish: a record it cannot parse, a git call that failed
"""

import argparse
import os
import re
import subprocess
import sys

STATEMENTS = "index/statements.tsv"
BINARIES = "index/binaries.tsv"
HARNESS = re.compile(r"^projects/([^/]+)/([^/]+)/harness\.yaml$")
PROJECT = re.compile(r"^projects/([^/]+)/project\.yaml$")
# A proof of a unit, in either layout this repository uses (tools/oft/layout.py): the per-project
# one and the older top-level one.
PROOF_NEW = re.compile(r"^projects/([^/]+)/([^/]+)/proofs/")
PROOF_OLD = re.compile(r"^proofs/([^/]+)/([^/]+)/")
# A status that still claims something about the binary. `open` claims nothing yet.
CLAIMING = ("proved", "false", "suspected_false")


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


# ------------------------------------------------------------------------------------------------
# The records.  Both readers STOP on anything they do not recognise: a record read as empty is a
# pin that moved with nothing to compare it to, which is the failure this check is against.


def scalar(value):
    value = value.strip()
    if len(value) >= 2 and value[0] == value[-1] and value[0] in "'\"":
        return value[1:-1]
    return value


def block_under(text, where, top, depth=2):
    """The scalar `key: value` pairs of each entry of a two-level block mapping under the
    column-zero key `top`:  top: / <entry>: / <key>: <value>.  Lines deeper than the key level are
    skipped (a build's `segments:` list, its `archives:` entries); a line that is neither is an
    error, so a shape this reader does not know stops the check rather than reading as nothing."""
    out, entry, inside = {}, None, False
    for number, line in enumerate((text or "").split("\n"), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        indent = len(line) - len(line.lstrip(" "))
        if indent == 0:
            if not line.startswith(" ") and line.rstrip().endswith(":") and line.rstrip()[:-1] == top:
                inside, entry = True, None
                continue
            if inside:
                break                       # the next column-zero key ends the block
            continue
        if not inside:
            continue
        if indent == depth:
            name = line.strip()
            if not name.endswith(":"):
                die("%s line %d: expected an entry of `%s:`, found %r" % (where, number, top, line))
            entry, out[name[:-1]] = name[:-1], {}
            continue
        if indent == depth + 2 and entry is not None:
            body = line.strip()
            if body.startswith("- "):
                continue                    # a list item at the key level: not a scalar field
            if ":" not in body:
                die("%s line %d: expected `key: value`, found %r" % (where, number, line))
            key, _, value = body.partition(":")
            if value.strip():
                out[entry][key.strip()] = scalar(value)
            continue
        # deeper than the key level: part of a value this check does not read
    if not inside:
        return None
    return out


def harness_builds(text, where):
    """build -> {file, bytes, sha256} from a harness record."""
    builds = block_under(text, where, "builds")
    if builds is None:
        die("%s has no `builds:` block" % where)
    for name, body in builds.items():
        if "sha256" not in body:
            die("%s: build %s has no sha256" % (where, name))
    return builds


def project_bin(text, where):
    """The `assets.bin` pin of a project record, or None."""
    assets = block_under(text, where, "assets")
    if assets is None:
        return None
    return assets.get("bin")


def table(text, where, key_columns, need):
    """Rows of a TSV, keyed by the tuple of key_columns -- or by the bare value when there is one.
    """
    if text is None:
        return {}
    lines = [ln for ln in text.split("\n") if ln != ""]
    if not lines:
        die("%s is empty" % where)
    header = lines[0].split("\t")
    for column in tuple(key_columns) + tuple(need):
        if column not in header:
            die("%s has no `%s` column; its header is %r" % (where, column, header))
    out = {}
    for number, line in enumerate(lines[1:], 2):
        cells = line.split("\t")
        if len(cells) != len(header):
            die("%s line %d has %d columns, not %d" % (where, number, len(cells), len(header)))
        row = dict(zip(header, cells))
        key = tuple(row[c] for c in key_columns)
        out[key[0] if len(key) == 1 else key] = row
    return out


# ------------------------------------------------------------------------------------------------
# The rule


def check(base, head, read=blob, changed=None):
    """(findings, notes). A finding fails the check; a note is printed and fails nothing."""
    if changed is None:
        names = git("diff", "--name-only", "-z", "--no-renames", base, head).split(b"\0")
        changed = [n.decode("utf-8", "replace") for n in names if n]
    findings, notes = [], []

    proved_again = set()
    for path in changed:
        for pattern in (PROOF_NEW, PROOF_OLD):
            found = pattern.match(path)
            if found:
                proved_again.add((found.group(1), found.group(2)))

    # Where a build's sha256 moved, from both places a pin lives.
    moved, touched = {}, set()
    for path in changed:
        found = HARNESS.match(path)
        if not found:
            continue
        unit = (found.group(1), found.group(2))
        touched.add(unit)
        old_text, new_text = read(base, path), read(head, path)
        old = harness_builds(old_text, "%s at the base" % path) if old_text is not None else {}
        new = harness_builds(new_text, "%s at this head" % path) if new_text is not None else {}
        for build, body in new.items():
            was = (old.get(build) or {}).get("sha256")
            if was is not None and was != body["sha256"]:
                moved[unit + (build,)] = (was, body["sha256"], path)

    old_bin = table(read(base, BINARIES), "%s at the base" % BINARIES,
                    ("project", "harness", "build"), ("sha256", "bytes", "file"))
    new_bin = table(read(head, BINARIES), "%s at this head" % BINARIES,
                    ("project", "harness", "build"), ("sha256", "bytes", "file"))
    if BINARIES in changed:
        for key, row in new_bin.items():
            was = old_bin.get(key)
            if was is not None and was["sha256"] != row["sha256"]:
                touched.add(key[:2])
                moved.setdefault(key, (was["sha256"], row["sha256"], BINARIES))

    # The project's binary archive. Moving it alone is coherent -- a repack can hold the very same
    # binaries -- because what a statement's fingerprint binds is the BINARY's sha256, not the
    # archive's. Said out loud so nobody reads its silence as a check.
    for path in changed:
        found = PROJECT.match(path)
        if not found:
            continue
        old_text, new_text = read(base, path), read(head, path)
        was = project_bin(old_text, "%s at the base" % path) if old_text is not None else None
        now = project_bin(new_text, "%s at this head" % path) if new_text is not None else None
        if was and now and was.get("sha256") != now.get("sha256"):
            under = [k for k in moved if k[0] == found.group(1)]
            notes.append("%s: the project's binary archive assets.bin moved (%s -> %s); %d build "
                         "pin(s) of this project moved with it. The archive alone changes no "
                         "statement: a fingerprint binds each binary's own sha256."
                         % (path, (was.get("sha256") or "?")[:12], (now.get("sha256") or "?")[:12],
                            len(under)))

    if not moved:
        return findings, notes

    old_st = table(read(base, STATEMENTS), "%s at the base" % STATEMENTS,
                   ("id",), ("builds", "status", "fingerprint"))
    new_st = table(read(head, STATEMENTS), "%s at this head" % STATEMENTS,
                   ("id",), ("builds", "status", "fingerprint"))

    for (project, harness, build), (was, now, where) in sorted(moved.items()):
        prefix = "%s/%s/" % (project, harness)
        about = [i for i in sorted(new_st)
                 if i.startswith(prefix) and build in new_st[i]["builds"].split(",")]
        if not about:
            notes.append("%s: the %s pin of %s%s moved (%s -> %s) and no published statement names "
                         "that build." % (where, build, project, "/" + harness, was[:12], now[:12]))
            continue
        for ident in about:
            old_row = old_st.get(ident)
            new_row = new_st[ident]
            if old_row is None:
                continue                    # a new statement: nothing was carried over
            if old_row["fingerprint"] == new_row["fingerprint"]:
                findings.append(
                    "%s: the %s binary moved (%s -> %s, in %s) and the fingerprint of this "
                    "statement did not: %s is still %s. tools/oft/facts.py puts `build %s "
                    "<sha256>` into that hash, so it CANNOT be current -- it was carried over, not "
                    "recomputed." % (ident, build, was[:12], now[:12], where, ident,
                                     new_row["fingerprint"][:12], build))
            if new_row["status"] in CLAIMING and (project, harness) not in proved_again:
                findings.append(
                    "%s: the %s binary moved (%s -> %s) and this statement still says `%s`, with "
                    "no proof of %s%s changed in this pull request. A claim about the old binary "
                    "is not a claim about the new one: set it to `open`, or re-prove it here."
                    % (ident, build, was[:12], now[:12], new_row["status"], project,
                       "/" + harness))

    # The two places a pin lives must agree at the head, for every unit this change touched.
    for project, harness in sorted(touched):
        text = read(head, "projects/%s/%s/harness.yaml" % (project, harness))
        if text is None:
            continue
        builds = harness_builds(text, "projects/%s/%s/harness.yaml at this head" % (project, harness))
        for build, body in sorted(builds.items()):
            row = new_bin.get((project, harness, build))
            if row is None:
                findings.append("projects/%s/%s/harness.yaml names the build %s and %s has no row "
                                "for it." % (project, harness, build, BINARIES))
                continue
            for column in ("sha256", "bytes", "file"):
                if column in body and body[column] != row[column]:
                    findings.append(
                        "projects/%s/%s/harness.yaml and %s disagree about %s of %s: %r against "
                        "%r. One of the two pins moved and the other did not."
                        % (project, harness, BINARIES, column, build, body[column], row[column]))
    return findings, notes


# ------------------------------------------------------------------------------------------------
# The self-test

H = """schema: oss-fuzz-theorems/harness/1
builds:
  plain:
    file: f.plain
    bytes: 10
    sha256: %s
    segments:
    - 1
    archives:
    - name: libc.a
      kind: libc
      sha256: cc
  asan:
    file: f.asan
    bytes: 20
    sha256: %s
licence: NOASSERTION
"""
ST = ("id\tkind\tbuilds\treading\texits\tstatus\tdetail\trevision\tfingerprint\tproof\n"
      "p/h/asan_agrees\tagreement\tplain,asan\tmay-fail\t-\t%s\t-\t1\t%s\t-\n"
      "p/h/plain_halts\thalts\tplain\tbudget\t0,2\t%s\t-\t1\t%s\t-\n")
BIN = ("project\tharness\tbuild\tfile\tstatus\twithheld_reason\tbytes\tsha256\tlicence\n"
       "p\th\tplain\tf.plain\tpublished\t-\t10\t%s\tNOASSERTION\n"
       "p\th\tasan\tf.asan\tpublished\t-\t20\t%s\tNOASSERTION\n")


def tree(plain, asan, status, fp, extra=None):
    out = {"projects/p/h/harness.yaml": H % (plain, asan),
           STATEMENTS: ST % (status, fp, status, fp),
           BINARIES: BIN % (plain, asan)}
    out.update(extra or {})
    return out


FIXTURES = (
    # name, base, head, how many findings are required
    ("the ASan binary moved and no statement was recomputed -- this week's defect",
     tree("aa", "bb", "open", "ff"), tree("aa", "cc", "open", "ff"), 1),
    ("the ASan binary moved and a proved statement stayed proved",
     tree("aa", "bb", "proved", "ff"), tree("aa", "cc", "proved", "ff"), 2),
    ("the plain binary moved, so BOTH statements that name it must move",
     tree("aa", "bb", "open", "ff"), tree("dd", "bb", "open", "ff"), 2),
    ("harness.yaml moved and index/binaries.tsv did not",
     tree("aa", "bb", "open", "ff"),
     {"projects/p/h/harness.yaml": H % ("aa", "cc"), STATEMENTS: ST % ("open", "gg", "open", "gg"),
      BINARIES: BIN % ("aa", "bb")}, 1),
    # the ones that must NOT fire
    ("the ASan binary moved and every statement about it was recomputed",
     tree("aa", "bb", "open", "ff"), tree("aa", "cc", "open", "gg"), 0),
    ("the ASan binary moved, the statements were recomputed, and a proof of the unit was rewritten",
     tree("aa", "bb", "proved", "ff"),
     tree("aa", "cc", "proved", "gg", {"projects/p/h/proofs/lib/A.v": "Proof. lia. Qed.\n"}), 0),
    ("nothing moved at all", tree("aa", "bb", "proved", "ff"), tree("aa", "bb", "proved", "ff"), 0),
    ("a proof changed and no pin did",
     tree("aa", "bb", "proved", "ff"),
     tree("aa", "bb", "proved", "ff", {"proofs/p/h/lib/A.v": "Proof. now lia. Qed.\n"}), 0),
)


def self_test():
    failures = []
    for name, base_tree, head_tree, want in FIXTURES:
        trees = {"BASE": base_tree, "HEAD": head_tree}
        read = lambda rev, path: trees[rev].get(path)                      # noqa: E731
        changed = sorted({p for p in set(base_tree) | set(head_tree)
                          if base_tree.get(p) != head_tree.get(p)})
        try:
            findings, _notes = check("BASE", "HEAD", read=read, changed=changed)
        except Stop as stop:
            failures.append("%s: the check stopped (%s)" % (name, stop.message))
            continue
        if len(findings) != want:
            failures.append("%s: %d finding(s), expected %d: %s" % (name, len(findings), want, findings))
    print("PIN COHERENCE: self-test: %d of %d fixtures gave their known verdict; %d must find an "
          "incoherence and did, %d must find none and did not"
          % (len(FIXTURES) - len(failures), len(FIXTURES),
             len([f for f in FIXTURES if f[3]]), len([f for f in FIXTURES if not f[3]])))
    if failures:
        raise Stop(2, "SELF-TEST FAILED, so this check's verdict on a real change means nothing:"
                      "\n  " + "\n  ".join(failures))


def main(argv):
    parser = argparse.ArgumentParser(add_help=True)
    parser.add_argument("--base")
    parser.add_argument("--head")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)

    self_test()
    if args.self_test:
        print("PIN COHERENCE: nothing was read (--self-test).")
        return 0
    if not args.base or not args.head:
        die("--base and --head are required")

    findings, notes = check(args.base, args.head)
    for note in notes:
        print("  note  %s" % note)
    if not findings:
        print("PIN COHERENCE: every binary pin this change moves is matched by the statements "
              "about that binary. (This reads the tree; it does not build anything, so it says "
              "nothing about whether those statements are TRUE of the new binaries.)")
        return 0
    print("::group::pins that moved without their statements")
    for finding in findings:
        print("  %s" % finding)
    print("::endgroup::")
    raise Stop(1, "%d incoherence(s) between a moved binary pin and the statements about that "
                  "binary. A statement is about a binary: a different binary is a different claim."
                  % len(findings))


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except Stop as stop:
        sys.stderr.write("::error::PIN COHERENCE: %s\n" % stop.message)
        sys.exit(stop.status)
