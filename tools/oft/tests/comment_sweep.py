"""The comment sweep: before a fuzz target's approval, every whole comment line of its new Rocq files that is neither
released text nor generated text is deleted, and a check proves that the sweep deleted nothing else.

    PYTHONPATH=<tools> python3 -m oft.tests.comment_sweep plan  --repo GIT --unit P/H --head REV [--main REV]
        [--base REV] [--keep FILE] [--tsv OUT] [--citations OUT]
    PYTHONPATH=<tools> python3 -m oft.tests.comment_sweep apply --worktree DIR (and the plan's arguments)
    PYTHONPATH=<tools> python3 -m oft.tests.comment_sweep check --swept REV (and the plan's arguments)

The rule is item 19 of OSSV-134's comment-pass rulings (2026-11-01) with its conditions 20-25: deleting a comment makes
no claim, so the sweep needs a check that only those comment lines went, not a reader.  This file is under
tools/oft/tests/, beside stale_base.py and parallel.py, for their reason: keys.NOT_THE_CHECKER names tests/, so this
file and a change to it re-key no fuzz target.

plan prints, per file, each line it deletes and each comment line it keeps, with the reason, and the citations it
re-resolves or leaves (--tsv writes the rows to a file; --citations writes the citation rows alone, with a column the
fuzz target's owner fills); apply writes the swept files into DIR, a checkout of HEAD; check compares HEAD with the
commit of the swept files (--swept) and exits 1 naming each change the rule does not allow.  None of them commits,
pushes or runs a build.  Exit 2: bad arguments or a KEEP row that names no line to keep.

REV values.  HEAD is the fuzz target's head before the sweep; MAIN (default origin/main) is the released line; BASE
(default: the merge base of MAIN and HEAD) is the commit that decides which files are new, as the (7A) scope of the
merge gate reads it.

Definitions, each with the evidence it rests on:

New files.  The files of the fuzz target's proofs folder, in either layout (layout.proofs_dir), that `git diff
--no-renames --diff-filter=A BASE HEAD` adds, less each one that `git diff -M -l0 BASE HEAD` pairs with a file deleted
from BASE: item 13 of the rulings counts a rename pair as released text, which the (7A) reader reads against its old
file, and the (7A) scope uses these two diffs.  Only the .v files among them are swept, since the comments here are
Rocq's; the other new files (scripts, tables, logs and notes of provenance/) are counted and left as they are, and
the fuzz target's approval states that scope and that count (the CI/CD lead's ruling on pull request 639).

Comment lines.  Lexed by rocq.tokens, the lexer of the repository's tools (nested comments; string literals, in which
a `*)` closes nothing, inside comments too).  A whole comment line is a line whose every non-blank character is inside
a comment, its `(*` and `*)` included, or a blank line inside a comment.  A comment block is a run of lines that
comments join (a comment that spans the line feed between two lines joins them).  The sweep touches a block only when
every line of it is a whole comment line: a comment that starts or ends on a line that holds code -- a trailing
comment, or one in the middle of a line -- keeps every line (condition 20).  A file is refused (listed and left as it
is) when a comment opens directly after a non-blank character other than the end of another comment (Rocq 9.2's `.(`
and `` `( `` take the `(` of a following `(*`, so rocq.tokens would read code as a comment: rocq.py, the docstring of
rocq.code), when it holds `:{{` (the body of an `ident:{{ ... }}` quotation is raw text, not comments), or when a
comment or string literal is still open at its end.  These are the stated limits L1 and L2 of the registered
comment-diff (c7c70fff23c1) and rocq-chunks (d6b19c9cdcaf) tools, which ask a caller to refuse those shapes.

Kept lines.  Each whole comment line of a block the sweep touches gets the first reason that applies:
  header       lines 1-10 as they read (lint.HEADER_LINES, the lines where lint.scan_licence reads a file's licence
               lines; condition 21, which the CI/CD lead's ruling on pull request 639 keeps literal);
  modified-by  a line that holds `(* Modified by`, and every line of a comment that starts so (condition 21);
  timeout-ok   a line that lint.TIMEOUT_JUSTIFIED matches (condition 20; lint requires that comment on the line of the
               command it excuses, a code line, which the sweep never touches anyway);
  released     a line with a non-blank character that is byte-equal, without its line feed, to a line of a .v file
               of the same fuzz target at MAIN, in either layout (its statement folder and old-layout proofs folder).
               A new file has no released version of its own, or it would not be new (item 13), so the sweep reads
               "a released line on main" as text this fuzz target has released.  A line equal only to another fuzz
               target's line was copied from a donor, whose text was written for another program and read for none
               (the inherited lines of a donor were found wrong and fixed on reac-repacer/fuzz_wire in this series):
               it is deleted (the CI/CD lead's ruling on pull request 639 keeps this reading).  Measured on
               reac-repacer/fuzz_wire at 194eada797d0 against main 1791c44240f6: past line 10, 151 non-blank lines
               (and 46 blank lines inside comments, which are never released text here) of 8,157 are equal to the
               fuzz target's own released lines, and 3,522 to a line of any .v file of main;
  keep-list    a line that the KEEP file names (generated text, below);
  cited        a line that a kept line cites (citations, below).
Every other line of the block is deleted, but the sweep never deletes a run of lines that starts and ends in two
different lexer states (comment depth, inside a string literal or not): the rest of the file then lexes as before.
Within a run of lines to delete it deletes as many lines as that allows (a dynamic program over the run's line
boundaries) and keeps the rest with the reason `structural`; on reac-repacer/fuzz_wire 153 of its 155 such lines
close a comment that starts in the header and runs past line 10, and the other 2 open and close the comment that
holds a cited line (lib/B/YD3d.v:80).

Generated text.  No mechanical marker says which comment lines a measurement script wrote and which table they cite.
Measured on reac-repacer/fuzz_wire at 194eada797d0: generated files say so once, for the whole file, in their first
lines ("Generated by port_core.py: ...", "(* GENERATED by tools/startup/colrun.py ...", "Machine-generated data
computed from the task's compiled program image", "(* Modified by Theorem Labs, 2026-10: generated for ... by
atable.py (sha256 ...)"), and their outputs are kept in provenance/ records whose form differs from tool to tool.  So
the sweep keeps generated text only where the fuzz target's owner lists it in the KEEP file, and never guesses; plan
lists the new files whose first ten lines say "generated", as a hint, and keeps nothing for it.

KEEP file.  One row per kept span, tab-separated: the path from the repository root, a selector, and why (the script
and the output table the text comes from; required).  Selector: N or N-M (line numbers at HEAD), `*` (every comment
line of the file), or sha256:<hex> (each line whose UTF-8 bytes, without the line feed, have that SHA-256).  Blank rows
and rows that start with # are skipped.  A row whose path is not a new .v file of the fuzz target, whose lines are not
all whole comment lines the sweep would touch, or whose hash names no such line, stops the run (exit 2): a stale or
mistyped row keeps nothing silently.

Notice (condition 21).  A swept file (one line or more deleted) that came from a donor -- it starts with Anthropic's
licence lines (the copyright line, the SPDX line in either form, and the optional attribution line, as
the notice tool reads them) or it holds a `(* Modified by` line -- gains NOTICE, one line, under the last licence
line of its first ten lines (LICENCE_LINE, lint's test of a licence line; Anthropic's header lines are licence lines,
and so is a later line such as a doc comment that restates Anthropic's copyright), else at the top; then after the
notices there (the comments that start with `(* Modified by`, one after the other), and never inside a comment.  So
no licence line moves, and lint.scan_licence still finds each one in the first ten lines.  A file whose last licence
line is line 10 cannot take the notice in its header: the rule refuses it (listed, and left as it is), as the CI/CD
lead ruled on pull request 639 (its review counted, of the 236,615 .v files at its head, 25 with a licence line on
line 10 and 15 on line 9).  A file whose only change is a re-resolved citation number gains no notice: the notice
records the sweep's deletions (on reac-repacer/fuzz_wire at 194eada797d0 no file is changed by a citation alone).

Citations (condition 24).  A citation is `<path>.v:N` or `<path>.v:N-M`, with any `, :N[-M]` that follows it (the same
file), inside a comment of a line the sweep keeps, in a .v file of the fuzz target (new or released; its statement
folder and both proofs folders).  Its target: a path from projects/ or proofs/ names that file; another path with a /
names the fuzz target's one .v file whose path ends with it; a bare name names the file of that name in the citing
file's folder, else the fuzz target's one .v file of that name.  When the target is a new file, every line of the
cited line or range that the rule would delete stays, with the reason `cited`: the citing line is one the sweep keeps
for another reason (a header, notice, released or listed line, or a code line), so condition 24's "deleted" branch
cannot apply to it, and the citation keeps naming the text it named.  The plan is computed again until no new line
is cited, and then each number becomes the new number of the line it named.  The sweep maps numbers and judges no
citation: on reac-repacer/fuzz_wire at 194eada797d0, 3 of the 52 citations of swept files name, at that head, the
definition their text gives (lib/A/AD1q.v:172 twice, lib/B/YE2k.v:28); the others were written against another
version of their file.  Left as they are, and listed: a citation with no single target among the files the sweep
changes; one after a possessive whose owner is another fuzz target's project or harness name, with or without its
fuzz_ prefix (`cgif's YG0n.v:17`; `the core's lib/A/AD1q.v:172` is this fuzz target's file); one inside round
brackets that name a commit (`at [rN] <hex>` or `commit <hex>`: its numbers are that commit's); one in an outside
contributor's notice (item 17: no byte of it changes but its donor path); one past the end of its target; one in a
file the rule refuses for its licence line, which keeps all its lines (they still keep the lines they cite).
Citations in files other than .v (provenance records, tables, logs) are not changed: they record the files as they
were when measured, and MANIFEST.md files pin their bytes; plan counts the ones that name a swept file.  The edit and
citation-left rows (plan --citations) go with the fuzz target's approval, each marked `checked` or `deleted` by its
owner (the CI/CD lead's ruling on pull request 639): the sweep moves numbers, and the owner says each one is true.

The check.  check reads HEAD and the swept commit and does not run the plan: every path the diff changes is a .v file
of the fuzz target; each changed file lexes as a whole (no comment or string literal open at its end, the shapes the
rule refuses at HEAD) and has the same code as before (rocq.code, which takes each comment as one space); with the
notice line taken out (when the file came from a donor, exactly where the rule puts it, and nowhere else), the swept
file is the HEAD file less some lines, aligned by a dynamic program, each removed line being a whole comment line
past line 10 of a new file, in a block of whole comment lines, that no reason keeps; a kept line differs only in the
numbers of its citations, and each number is the one its target's own alignment gives; no citation of a kept line
names a removed line; a file the rule refuses for its licence line lost no line; and no new file still holds a run of
lines the rule deletes that could go (a run that starts and ends in one lexer state; a line that a citation at HEAD
names need not go).  Where equal lines next to each other leave the alignment a choice, it takes the one that removes
the fewest lines a citation at HEAD names, so a cited line and its equal neighbour are told apart as the plan tells
them.  Its comment analysis, alignment, notice placement and completeness test are its own code; it shares with plan
the git reading, the KEEP and citation parsers, rocq.py, and the definitions of the classes of kept lines and of donor
files (anthropic_header, from_donor, MODIFIED_BY, LICENCE_LINE, released_lines, string_closed), so a defect in one
of those is in both.

What the sweep does not do, which its report names: it changes git object ids, so each swept fuzz target re-keys
(keys.py: a path's id is a digest of its entries' object ids) and takes a new check of record on the build farm, one
Job per fuzz target (condition 22); the released-proof index (.github/proof-index.py, rebuilt by proof-index.yml on
the push to main), the stream's lemma and cold-heads indexes and its search corpora store path:line and
harvest addresses from comments, so they are rebuilt after the merge (condition 23); a fuzz target with a
licence-pending entry in lint-exceptions.yaml is swept after or beside its licence series (condition 25).
"""
import argparse
import bisect
import collections
import hashlib
import os
import re
import subprocess
import sys

import yaml

from oft import layout, lint, rocq

NOTICE = "(* Modified by Theorem Labs, 2026-11: comments removed *)"
# Anthropic's licence lines, as the stream's notice tool reads them: the copyright line, line 2 in either form, and
# the optional attribution line of a Proof.v.
ANTHROPIC_LINE1 = "(* Copyright 2026 Anthropic PBC *)"
ANTHROPIC_LINE2 = ("(* SPDX-License-Identifier: Apache-2.0 *)", "(* SPDX-License-Identifier: Apache-2.0 OR MIT *)")
ANTHROPIC_ATTRIBUTION = "(* The proofs in this file are Anthropic's; "
MODIFIED_BY = re.compile(r"\(\*\s*Modified by\b")
OUR_NOTICE = re.compile(r"\(\*\s*Modified by Theorem Labs\b")
LICENCE_LINE = re.compile(r"SPDX-License-Identifier:|(?i:Copyright\b[^\n]*?\bAnthropic\b)")
GENERATED_HINT = re.compile(r"(?i)\bgenerated\b")
BLANKS = " \t\r\n"
CITATION = re.compile(r"(?<![\w./-])((?:[\w.-]+/)*[\w-]+\.v):(\d+)(?:-(\d+))?")
CONTINUATION = re.compile(r"\s*,\s*:(\d+)(?:-(\d+))?")
POSSESSOR = re.compile(r"([\w.+-]+)'s\s+$")
PINNED = re.compile(r"\b(?:at|commit)\s+(?:r\d+\s+)?[0-9a-f]{7,40}\b")
REASONS = ("header", "modified-by", "timeout-ok", "released", "keep-list", "cited", "structural")
CHUNK = 200     # files per git cat-file when the plan counts the citations of the fuzz target's other files
# why the rule refuses a donor file whose last licence line is the header's last line (the module docstring)
LICENCE_REFUSAL = ("a licence line is on line %d, the header's last: the notice under it would be line %d, outside the "
                   "header" % (lint.HEADER_LINES, lint.HEADER_LINES + 1))


class SweepError(Exception):
    """Bad input: the run stops with exit 2 and changes nothing."""


# ------------------------------------------------------------------------------------------------------------- git


def git(repo, *args, stdin=None):
    done = subprocess.run(["git", "-C", repo, *args], input=stdin, capture_output=True)
    if done.returncode != 0:
        raise SweepError("git %s: %s" % (" ".join(args), done.stderr.decode("utf-8", "replace").strip()))
    return done.stdout


def rev(repo, name):
    return git(repo, "rev-parse", "--verify", name + "^{commit}").decode().strip()


def ls_files(repo, commit, dirs):
    """The files under dirs at commit."""
    out = git(repo, "ls-tree", "-r", "-z", "--name-only", commit, "--", *dirs)
    return sorted(p for p in out.decode("utf-8", "surrogateescape").split("\0") if p)


def read_blobs(repo, commit, paths):
    """{path: bytes} of paths at commit, in one git cat-file; a path absent there is left out.  cat-file reads one
    object name per line, so a path with a line feed stops the run rather than shift every answer after it."""
    paths = list(paths)
    if not paths:
        return {}
    odd = [p for p in paths if "\n" in p]
    if odd:
        raise SweepError("a path with a line feed cannot be read: %r" % odd[0])
    data = git(repo, "cat-file", "--batch",
               stdin="".join("%s:%s\n" % (commit, p) for p in paths).encode("utf-8", "surrogateescape"))
    out, at = {}, 0
    for p in paths:
        nl = data.index(b"\n", at)
        head = data[at:nl].split()
        if head[-1] == b"missing":
            at = nl + 1
            continue
        size = int(head[2])
        out[p] = data[nl + 1:nl + 1 + size]
        at = nl + 1 + size + 1
    return out


class Unit:
    """One fuzz target `<project>/<harness>` and the three commits a sweep reads."""

    def __init__(self, repo, unit, head, main="origin/main", base=None):
        if unit.count("/") != 1 or not all(unit.split("/")):
            raise SweepError("--unit is <project>/<harness>, not %r" % unit)
        self.repo, self.name = repo, unit
        p, h = unit.split("/")
        self.proofs_dirs = [layout.proofs_dir(p, h, layout.NEW), layout.proofs_dir(p, h, layout.OLD)]
        # the fuzz target's own files: its statement folder (which holds the new layout's proofs folder) and the old
        # layout's proofs folder
        self.own_dirs = [layout.statement_dir(p, h), layout.proofs_dir(p, h, layout.OLD)]
        self.head, self.main = rev(repo, head), rev(repo, main)
        self.base = rev(repo, base) if base else git(repo, "merge-base", self.main, self.head).decode().strip()

    def own(self, path):
        return any(path.startswith(d + "/") for d in self.own_dirs)


def new_files(u):
    """(the new files of the fuzz target's proofs folders, {new path: old path} of the rename pairs left out)."""
    out = git(u.repo, "diff", "--no-renames", "--diff-filter=A", "--name-only", "-z", u.base, u.head, "--",
              *u.proofs_dirs)
    added = {p for p in out.decode("utf-8", "surrogateescape").split("\0") if p}
    fields = git(u.repo, "diff", "-M", "-l0", "--diff-filter=R", "--name-status", "-z", u.base, u.head, "--",
                 *u.proofs_dirs).decode("utf-8", "surrogateescape").split("\0")
    pairs = {}
    for i in range(0, len(fields) - 2, 3):
        if fields[i].startswith("R"):
            pairs[fields[i + 2]] = fields[i + 1]
    return sorted(added - set(pairs)), pairs


def released_lines(u):
    """The lines of the fuzz target's .v files at MAIN, in either layout."""
    files = [p for p in ls_files(u.repo, u.main, u.own_dirs) if p.endswith(".v")]
    out = set()
    for data in read_blobs(u.repo, u.main, files).values():
        out.update(data.decode("utf-8", "surrogateescape").split("\n"))
    return out


def licence_pending(u, commit):
    """The licence-pending entry of the fuzz target in tools/oft/lint-exceptions.yaml at commit, or None."""
    name = "tools/oft/lint-exceptions.yaml"
    data = read_blobs(u.repo, commit, [name]).get(name)
    if data is None:
        return None
    for e in (yaml.safe_load(data) or {}).get("exceptions") or []:
        if isinstance(e, dict) and e.get("rule") == lint.PENDING and e.get("unit") == u.name:
            return e
    return None


def pending_note(u):
    """Condition 25's line of the report: the fuzz target's licence-pending entry at MAIN and at HEAD."""
    out = []
    for what, commit in (("main", u.main), ("head", u.head)):
        e = licence_pending(u, commit)
        out.append("at %s, %s" % (what, "a licence-pending entry (due %s, series %s)" % (e.get("due"), e.get("series"))
                                  if e else "no licence-pending entry"))
    return "; ".join(out)


def anthropic_header(lines):
    """The number of Anthropic's licence lines at the top (as the stream's notice tool counts them), 0 when none."""
    if not (len(lines) > 1 and lines[0] == ANTHROPIC_LINE1 and lines[1] in ANTHROPIC_LINE2):
        return 0
    return 3 if len(lines) > 2 and lines[2].startswith(ANTHROPIC_ATTRIBUTION) else 2


def from_donor(lines):
    """Whether a file came from a donor: Anthropic's licence lines at its top, or a `(* Modified by` line."""
    return anthropic_header(lines) > 0 or any(MODIFIED_BY.search(line) for line in lines)


def line_count(lines):
    """The number of lines of a text split at its line feeds (the empty piece after a last line feed is no line)."""
    return len(lines) - (1 if lines and lines[-1] == "" else 0)


def string_closed(piece):
    """Whether a string literal of rocq.tokens ends with its closing quote: inside a string literal `""` is one quote,
    so a closed piece ends in an odd run of quotes after its opening one, and an open one in an even run."""
    rest = piece[1:]
    return (len(rest) - len(rest.rstrip('"'))) % 2 == 1


ROWS_HEADER = "path\tline\taction\treason\ttext"


def _tsv(row):
    return "\t".join(str(x).replace("\t", "\\t") for x in row)


def _numbers(numbers):
    """A citation's numbers as a row shows them: 12, or 12,14 for a range or a continuation."""
    return ",".join(map(str, numbers))


# ------------------------------------------------------------------------------------------------------ KEEP file


def read_keep(path):
    """[(row number, path, selector, why)] of a KEEP file (the module docstring); a malformed row stops the run."""
    rows = []
    if path is None:
        return rows
    with open(path, encoding="utf-8") as f:
        for n, line in enumerate(f, 1):
            line = line.rstrip("\n")
            if not line.strip() or line.startswith("#"):
                continue
            cols = line.split("\t")
            if len(cols) != 3 or not cols[2].strip():
                raise SweepError("%s:%d: a KEEP row is <path><TAB><selector><TAB><why>, why not empty" % (path, n))
            sel = cols[1]
            if not (sel == "*" or re.fullmatch(r"\d+(?:-\d+)?", sel) or re.fullmatch(r"sha256:[0-9a-f]{64}", sel)):
                raise SweepError("%s:%d: the selector %r is not N, N-M, * or sha256:<64 hex>" % (path, n, sel))
            rows.append((n, cols[0], sel, cols[2]))
    return rows


def keep_lines(rows, path, lines, sweepable):
    """{line index} the KEEP rows name in one file; a row that names a line outside sweepable stops the run."""
    out = set()
    for n, p, sel, _why in rows:
        if p != path:
            continue
        if sel == "*":
            out |= sweepable
            continue
        if sel.startswith("sha256:"):
            want = sel[len("sha256:"):]
            hit = {i for i in sweepable
                   if hashlib.sha256(lines[i].encode("utf-8", "surrogateescape")).hexdigest() == want}
            if not hit:
                raise SweepError("KEEP row %d: no whole comment line of %s has the hash %s" % (n, p, want))
            out |= hit
            continue
        a, _, b = sel.partition("-")
        span = set(range(int(a) - 1, int(b or a)))
        bad = sorted(i + 1 for i in span - sweepable)
        if bad or not span:
            raise SweepError("KEEP row %d: %s line(s) %s are not whole comment lines the sweep touches"
                             % (n, p, ", ".join(map(str, bad[:5])) or sel))
        out |= span
    return out


def keep_paths(rows, new_v, unit):
    """KEEP may name the fuzz target's new .v files only."""
    stray = sorted({p for _n, p, _s, _w in rows} - set(new_v))
    if stray:
        raise SweepError("KEEP names files that are not new .v files of %s: %s" % (unit, ", ".join(stray[:5])))


# ----------------------------------------------------------------------------------------------------- citations


Citation = collections.namedtuple("Citation", "ref start numbers")   # numbers: [(start, end, value)] in the line


def find_citations(line, in_comment):
    """The citations of a line whose characters at the columns in_comment(k) holds are inside a comment."""
    out = []
    for m in CITATION.finditer(line):
        if not in_comment(m.start()):
            continue
        nums = [(m.start(2), m.end(2), int(m.group(2)))]
        if m.group(3):
            nums.append((m.start(3), m.end(3), int(m.group(3))))
        at = m.end()
        while True:
            c = CONTINUATION.match(line, at)
            if not c:
                break
            nums.append((c.start(1), c.end(1), int(c.group(1))))
            if c.group(2):
                nums.append((c.start(2), c.end(2), int(c.group(2))))
            at = c.end()
        out.append(Citation(m.group(1), m.start(), nums))
    return out


def citation_groups(line, cit):
    """[(index of the first number, index of the last)] of a citation: one per N, N-M and continuation."""
    groups, i, nums = [], 0, cit.numbers
    while i < len(nums):
        if i + 1 < len(nums) and line[nums[i][1]:nums[i + 1][0]] == "-":
            groups.append((i, i + 1))
            i += 2
        else:
            groups.append((i, i))
            i += 1
    return groups


class Targets:
    """Where a citation's path points: the fuzz target's .v files at HEAD (the module docstring)."""

    def __init__(self, files):
        self.files = set(files)
        self.suffix = collections.defaultdict(set)
        for f in files:
            parts = f.split("/")
            for k in range(1, len(parts)):
                self.suffix["/".join(parts[k:])].add(f)

    def candidates(self, ref, citing):
        if ref.startswith(("projects/", "proofs/")):
            return {ref} & self.files
        if "/" not in ref:
            beside = os.path.join(os.path.dirname(citing), ref)
            if beside in self.files:
                return {beside}
        return set(self.suffix.get(ref, ()))

    def resolve(self, ref, citing):
        hits = self.candidates(ref, citing)
        return next(iter(hits)) if len(hits) == 1 else None


def other_names(u):
    """The names that point a possessive at another fuzz target: every project and harness on MAIN, and each harness
    without its fuzz_ prefix, but the fuzz target's own (its project's name too)."""
    out = git(u.repo, "ls-tree", "-r", "-z", "--name-only", u.main, "--", "projects", "proofs")
    own_p, own_h = u.name.split("/")
    names = set()
    for f in out.decode("utf-8", "surrogateescape").split("\0"):
        parts = f.split("/")
        if len(parts) < 4 or (parts[0] == "projects" and parts[3] != "harness.yaml") \
                or (parts[0] == "proofs" and parts[1] in ("lib", "lib-lean")):
            continue
        p, h = parts[1], parts[2]
        names |= {p, h, h[len("fuzz_"):] if h.startswith("fuzz_") else h}
    return names - {own_p, own_h, own_h[len("fuzz_"):] if own_h.startswith("fuzz_") else own_h}


def _group(comment, at):
    """The innermost round-bracket group of a comment's text (its own `(*` and `*)` aside) that holds offset at, or
    None."""
    depth, i = 0, at - 1
    while i >= 2:
        ch = comment[i]
        if ch == ")" and comment[i - 1] != "*":
            depth += 1
        elif ch == "(" and comment[i + 1:i + 2] != "*":
            if depth == 0:
                break
            depth -= 1
        i -= 1
    else:
        return None
    depth = 0
    for j in range(at, len(comment) - 2):
        ch = comment[j]
        if ch == "(" and comment[j + 1:j + 2] != "*":
            depth += 1
        elif ch == ")" and comment[j - 1] != "*":
            if depth == 0:
                return comment[i:j + 1]
            depth -= 1
    return None


def exclusion(line, cit, comment, others):
    """Why a citation is left as it is whatever its target (the module docstring), or None.  comment: (the text of
    the comment that holds it, the citation's offset in that text), or None; others: other_names."""
    owner = POSSESSOR.search(line[:cit.start])
    if owner and owner.group(1) in others:
        return "another fuzz target's file (%s's)" % owner.group(1)
    if comment is not None:
        text, at = comment
        group = _group(text, at)
        if group is not None and PINNED.search(group):
            return "pinned to a commit in its brackets"
        if MODIFIED_BY.match(text) and not OUR_NOTICE.match(text):
            return "outside contributor's notice"
    return None


def cited_ranges(line, cit, size):
    """[(first line index, last line index)] a citation names, or None when a number is past the end (size lines)."""
    out = []
    for g0, g1 in citation_groups(line, cit):
        lo, hi = cit.numbers[g0][2] - 1, cit.numbers[g1][2] - 1
        if not 0 <= lo <= hi < size:
            return None
        out.append((lo, hi))
    return out


# --------------------------------------------------------------------------------------------- the plan's lexing


class Lexed:
    """A Rocq file as the plan reads it: lines, comment spans, line-start lexer states, whole comment lines."""

    def __init__(self, text):
        self.text = text
        self.lines = text.split("\n")
        self.starts = [0]
        for line in self.lines[:-1]:
            self.starts.append(self.starts[-1] + len(line) + 1)
        n = len(text)
        self.mask = bytearray(n)
        self.spans = []                  # (first line, last line, start offset, end offset) of each outermost comment
        self.refused = []
        nl_state = {}
        depth, pos, start = 0, 0, None
        open_string = False
        for kind, piece, inside in rocq.tokens(text):
            size = len(piece)
            if kind == "open":
                if depth == 0:
                    start = pos
                    if pos > 0 and text[pos - 1] not in BLANKS and text[max(0, pos - 2):pos] != "*)":
                        self.refused.append("line %d: a comment opens directly after a non-blank character (Rocq "
                                            "may read it as code: `.(`, `` `( ``)" % (self.line_of(pos) + 1))
                depth += 1
                self.mask[pos:pos + size] = b"\x01" * size
            elif kind == "close" and inside:
                self.mask[pos:pos + size] = b"\x01" * size
                depth -= 1
                if depth == 0:
                    self.spans.append((self.line_of(start), self.line_of(pos + size - 1), start, pos + size))
            else:
                if depth > 0:
                    self.mask[pos:pos + size] = b"\x01" * size
                j = piece.find("\n")
                while j >= 0:
                    nl_state[pos + j] = (depth, kind == "string")
                    j = piece.find("\n", j + 1)
                if kind == "string":
                    open_string = pos + size == n and not string_closed(piece)
            pos += size
        if depth > 0:
            self.refused.append("a comment opened at line %d is still open at the end" % (self.line_of(start) + 1))
            self.spans.append((self.line_of(start), len(self.lines) - 1, start, n))
        if open_string:
            self.refused.append("a string literal is still open at the end")
        if ":{{" in text:
            self.refused.append("line %d: `:{{`, a quotation whose body is raw text"
                                % (self.line_of(text.index(":{{")) + 1))
        self.span_starts = [s for _a, _b, s, _e in self.spans]
        # the lexer state at the start of each line, and at the end of the text
        self.state = [(0, False)] + [nl_state[s - 1] for s in self.starts[1:]] + [(depth, open_string)]
        self.whole = []
        for i, line in enumerate(self.lines):
            s = self.starts[i]
            marks = [self.mask[s + k] for k, ch in enumerate(line) if ch not in BLANKS]
            self.whole.append(all(marks) if marks else self.state[i][0] > 0)
        blocks = []
        for a, b, _s, _e in self.spans:
            if blocks and a <= blocks[-1][1]:
                blocks[-1][1] = max(blocks[-1][1], b)
            else:
                blocks.append([a, b])
        # the lines of the blocks every line of which is a whole comment line: the lines the sweep touches
        self.sweepable = set()
        for a, b in blocks:
            if all(self.whole[a:b + 1]):
                self.sweepable.update(range(a, b + 1))
        self.notice_spans = {s: b for a, b, s, _e in self.spans if MODIFIED_BY.match(text, s)}
        self.modified_by = {i for a, b, s, _e in self.spans if s in self.notice_spans for i in range(a, b + 1)}
        self.modified_by.update(i for i, line in enumerate(self.lines) if MODIFIED_BY.search(line))

    def line_of(self, offset):
        return bisect.bisect_right(self.starts, offset) - 1

    def comment_at(self, offset):
        """(the text of the outermost comment holding offset, offset's place in it), or None."""
        k = bisect.bisect_right(self.span_starts, offset) - 1
        if k >= 0 and offset < self.spans[k][3]:
            return self.text[self.spans[k][2]:self.spans[k][3]], offset - self.spans[k][2]
        return None


def _licence_last(lines):
    """The index of the last licence line (LICENCE_LINE) of the first ten lines, or -1."""
    last = -1
    for i, line in enumerate(lines[:lint.HEADER_LINES]):
        if LICENCE_LINE.search(line):
            last = i
    return last


class FilePlan:
    """The sweep of one .v file: a reason for each line it touches, the lines it deletes, the notice, the edits.  A
    released file (sweep=False) is only read: it changes by its citations' numbers alone."""

    def __init__(self, path, text, released=None, keep_rows=(), sweep=True, lex=None):
        self.path, self.lex = path, lex or Lexed(text)
        self.lines = self.lex.lines
        self.refused = list(self.lex.refused) if sweep else []
        self.keep = set()
        self.cited = {}                  # line -> the first citing location, for the reason `cited`
        self.edits = {}                  # line -> its text with its citations re-resolved
        self.reasons, self.deleted, self.notice_at = {}, set(), None
        self.released = released
        self.licence_last = _licence_last(self.lines)
        if sweep and not self.refused:
            self.keep = keep_lines(keep_rows, path, self.lines, self.lex.sweepable)
            self.decide()

    def decide(self):
        lex, lines = self.lex, self.lines
        self.reasons, self.deleted, self.notice_at, self.refused = {}, set(), None, list(self.lex.refused)
        todo = []
        for i in sorted(lex.sweepable):
            line = lines[i]
            if i < lint.HEADER_LINES:
                r = "header"
            elif i in lex.modified_by:
                r = "modified-by"
            elif lint.TIMEOUT_JUSTIFIED.search(line):
                r = "timeout-ok"
            elif line.strip(BLANKS) and line in self.released:
                r = "released"
            elif i in self.keep:
                r = "keep-list"
            elif i in self.cited:
                r = "cited"
            else:
                r = None
                todo.append(i)
            self.reasons[i] = r
        runs = []
        for i in todo:
            if runs and runs[-1][-1] == i - 1:
                runs[-1].append(i)
            else:
                runs.append([i])
        for run in runs:
            self._delete_most(run)
        for i in todo:
            self.reasons[i] = "deleted" if i in self.deleted else "structural"
        if self.deleted and from_donor(lines) and NOTICE not in lines:
            if self.licence_last == lint.HEADER_LINES - 1:
                self.refused.append(LICENCE_REFUSAL)
                self.reasons, self.deleted = {}, set()
                return
            self.notice_at = self._notice_place()

    def _delete_most(self, run):
        """Delete as many lines of run (consecutive lines) as can go in runs that start and end in one lexer state."""
        state, a, m = self.lex.state, run[0], len(run)
        best, back = [0] * (m + 1), [None] * (m + 1)
        seen = {state[a]: (0, 0)}           # state -> (best[u] - u, u), the best boundary u with that state so far
        for t in range(1, m + 1):
            best[t] = best[t - 1]
            s = state[a + t]
            if s in seen and seen[s][0] + t > best[t]:
                best[t], back[t] = seen[s][0] + t, seen[s][1]
            if s not in seen or best[t] - t > seen[s][0]:
                seen[s] = (best[t] - t, t)
        t = m
        while t > 0:
            if back[t] is None:
                t -= 1
            else:
                self.deleted.update(range(a + back[t], a + t))
                t = back[t]

    def _notice_place(self):
        """Under the last licence line of the header (Anthropic's lines are licence lines), else at the top; after
        the `(* Modified by` comments there, and never inside a comment."""
        lines, lex = self.lines, self.lex
        k = max(anthropic_header(lines), self.licence_last + 1)
        while True:
            while 0 < k < len(lines) and lex.state[k][0] > 0:     # line k starts inside a comment
                k += 1
            if k >= len(lines):
                return k
            first = lex.starts[k] + len(lines[k]) - len(lines[k].lstrip(" \t"))
            if first not in lex.notice_spans:
                return k
            k = lex.notice_spans[first] + 1

    def line_map(self):
        """[new line index or None] for each old line index, after the sweep."""
        out, new = [], 0
        for i in range(len(self.lines)):
            if i == self.notice_at:
                new += 1
            if i in self.deleted:
                out.append(None)
            else:
                out.append(new)
                new += 1
        return out

    def swept_text(self):
        out = []
        for i, line in enumerate(self.lines):
            if i == self.notice_at:
                out.append(NOTICE)
            if i not in self.deleted:
                out.append(self.edits.get(i, line))
        return "\n".join(out)

    def changed(self):
        return bool(self.deleted or self.edits)


class Plan:
    """The sweep of one fuzz target (the module docstring)."""

    def __init__(self, u, keep_rows=(), count_other=True):
        self.u = u
        self.new, self.pairs = new_files(u)
        self.new_v = [p for p in self.new if p.endswith(".v")]
        keep_paths(keep_rows, self.new_v, u.name)
        self.released = released_lines(u)
        self.citing = [p for p in ls_files(u.repo, u.head, u.own_dirs) if p.endswith(".v")]
        blobs = read_blobs(u.repo, u.head, set(self.citing) | set(self.new_v))
        for p in self.new_v:
            try:
                blobs[p].decode("utf-8")
            except UnicodeDecodeError:
                raise SweepError("%s is not UTF-8" % p)
        self.texts = {p: d.decode("utf-8", "surrogateescape") for p, d in blobs.items()}
        self.files = {p: FilePlan(p, self.texts[p], self.released, keep_rows) for p in self.new_v}
        self.targets, self.others = Targets(self.citing), other_names(u)
        self.resolutions, self.left = [], []
        self._citations()
        self.other_citations = self._count_other() if count_other else None

    def _citations(self):
        """Keep every line a kept line cites, until no new line is cited; then re-resolve the citations' numbers.  A
        file the rule refuses for its licence line keeps all its lines, so its citations keep the lines they name, but
        its numbers are not changed: each one that would change is listed."""
        lexes = {p: (self.files[p].lex if p in self.files else Lexed(self.texts[p])) for p in self.citing}
        while True:
            fresh = False
            for path, cit, i, line, lex in self._kept_citations(lexes):
                target = self.targets.resolve(cit.ref, path)
                fp = self.files.get(target)
                if fp is None or fp.refused or exclusion(line, cit, lex.comment_at(lex.starts[i] + cit.start),
                                                         self.others):
                    continue
                for lo, hi in cited_ranges(line, cit, line_count(fp.lines)) or ():
                    for k in range(lo, hi + 1):
                        if k in fp.lex.sweepable and k not in fp.cited:
                            fp.cited[k] = "%s:%d" % (path, i + 1)
                            if fp.reasons.get(k) in ("deleted", "structural"):
                                fresh = True
            if not fresh:
                break
            for fp in self.files.values():
                if fp.cited and not fp.lex.refused:
                    fp.decide()
        maps = {p: fp.line_map() for p, fp in self.files.items() if fp.deleted or fp.notice_at is not None}
        edits = collections.defaultdict(dict)
        for path, cit, i, line, lex in self._kept_citations(lexes):
            hits = self.targets.candidates(cit.ref, path)
            if len(hits) != 1:
                if hits & set(maps):
                    self.left.append((path, i, cit.ref, "no single target", line))
                continue
            target = next(iter(hits))
            if target not in maps:
                continue
            why = exclusion(line, cit, lex.comment_at(lex.starts[i] + cit.start), self.others)
            ranges = cited_ranges(line, cit, line_count(self.files[target].lines))
            if why or ranges is None:
                self.left.append((path, i, cit.ref, why or "past the end of its target", line))
                continue
            m, new = maps[target], {}
            for (g0, g1), (lo, hi) in zip(citation_groups(line, cit), ranges):
                new[g0], new[g1] = m[lo] + 1, m[hi] + 1
            old = [n[2] for n in cit.numbers]
            got = [new.get(k, v) for k, v in enumerate(old)]
            if got == old:
                continue
            if path in self.files and self.files[path].refused:
                self.left.append((path, i, cit.ref, "in a file the rule refuses, so %s stays (the sweep gives %s)"
                                  % (_numbers(old), _numbers(got)), line))
                continue
            text = edits[path].get(i, line)
            for k in reversed(range(len(cit.numbers))):
                s, e, _v = cit.numbers[k]
                text = text[:s] + str(got[k]) + text[e:]
            edits[path][i] = text
            self.resolutions.append((path, i, cit.ref, old, got))
        for path, es in edits.items():
            if path not in self.files:
                self.files[path] = FilePlan(path, self.texts[path], sweep=False, lex=lexes[path])
            self.files[path].edits = es

    def _kept_citations(self, lexes):
        """(path, citation, line index, line, Lexed) of each citation in a comment of a kept line, numbers last first
        within a line, so that edits by offset stay valid."""
        for path in self.citing:
            lex = lexes[path]
            fp = self.files.get(path)
            if lex.refused:
                continue
            for i, line in enumerate(lex.lines):
                if ".v:" not in line or (fp is not None and i in fp.deleted):
                    continue
                s0 = lex.starts[i]
                for cit in reversed(find_citations(line, lambda k, s0=s0: lex.mask[s0 + k] == 1)):
                    yield path, cit, i, line, lex

    def _count_other(self):
        """The citations, in the fuzz target's files other than .v, whose path names a file the sweep changes."""
        swept = {p for p, fp in self.files.items() if fp.changed() and p in self.new_v}
        others = [p for p in ls_files(self.u.repo, self.u.head, self.u.proofs_dirs) if not p.endswith(".v")]
        n = 0
        for k in range(0, len(others), CHUNK):
            for p, data in read_blobs(self.u.repo, self.u.head, others[k:k + CHUNK]).items():
                text = data.decode("utf-8", "surrogateescape")
                if ".v:" not in text:
                    continue
                for m in CITATION.finditer(text):
                    if self.targets.resolve(m.group(1), p) in swept:
                        n += 1
        return n

    # --------------------------------------------------------------------------------------------- the report

    def rows(self):
        """Rows: path, line, action, reason, text."""
        resolved = collections.defaultdict(list)
        for path, i, ref, old, new in self.resolutions:
            resolved[(path, i)].append("%s:%s -> %s" % (ref, _numbers(old), _numbers(new)))
        out = []
        for p in sorted(self.files):
            fp = self.files[p]
            if fp.refused:
                out.append((p, 0, "refused", "; ".join(fp.refused), ""))
                continue
            for i in sorted(fp.reasons):
                r = fp.reasons[i]
                if r == "deleted":
                    out.append((p, i + 1, "delete", "no reason keeps it", fp.lines[i]))
                else:
                    out.append((p, i + 1, "keep", "cited by " + fp.cited[i] if r == "cited" else r, fp.lines[i]))
            if fp.notice_at is not None:
                out.append((p, fp.notice_at + 1, "insert", "the notice goes above this line", NOTICE))
            for i in sorted(fp.edits):
                out.append((p, i + 1, "edit", "citation re-resolved: " + "; ".join(resolved[(p, i)]), fp.edits[i]))
        for path, i, ref, why, line in self.left:
            out.append((path, i + 1, "citation-left", "%s: %s" % (ref, why), line))
        return out

    def citation_rows(self):
        """The edit and citation-left rows: the ones the fuzz target's approval carries, each marked by its owner."""
        return [row for row in self.rows() if row[2] in ("edit", "citation-left")]

    def summary(self):
        u, c = self.u, collections.Counter()
        touched = notices = header_licence = 0
        hints = []
        for p in self.new_v:
            fp = self.files[p]
            if fp.refused:
                continue
            for i, r in fp.reasons.items():
                c[r] += 1
                if r == "header" and (LICENCE_LINE.search(fp.lines[i]) or MODIFIED_BY.search(fp.lines[i])
                                      or fp.lines[i].startswith(lint.PROGRAM_LINES)):
                    header_licence += 1
            touched += bool(fp.deleted)
            notices += fp.notice_at is not None
            if any(GENERATED_HINT.search(line) for line in fp.lines[:lint.HEADER_LINES]):
                hints.append((p, len(fp.deleted)))
        refused = [(p, self.files[p].refused) for p in self.new_v if self.files[p].refused]
        out = [
            "comment sweep of %s" % u.name,
            "  head %s, main %s, base %s" % (u.head, u.main, u.base),
            "  scope: .v files only (the CI/CD lead's ruling on pull request 639): %d new files, %d .v files swept, "
            "%d other new files not swept; rename pairs, released: %d"
            % (len(self.new), len(self.new_v), len(self.new) - len(self.new_v), len(self.pairs)),
            "  whole comment lines in the blocks the sweep touches: %d" % sum(c.values()),
            "    deleted: %d, in %d files" % (c["deleted"], touched),
        ]
        for r in REASONS:
            out.append("    kept, %s: %d%s" % (r, c[r], " (%d of them licence or notice lines)" % header_licence
                                               if r == "header" else ""))
        out += [
            "  notices added: %d" % notices,
            "  citations re-resolved: %d, in %d lines of %d files; left as they are: %d"
            % (len(self.resolutions), len({(p, i) for p, i, *_ in self.resolutions}),
               len({p for p, *_ in self.resolutions}), len(self.left)),
            "  citations in the fuzz target's other files that name a swept file (records, not changed): %s"
            % ("not counted" if self.other_citations is None else self.other_citations),
            "  citation rows for the approval (edit and citation-left; the owner marks each checked or deleted): %d"
            % len(self.citation_rows()),
            "  refused files (left as they are): %d" % len(refused),
        ]
        out += ["    %s: %s" % (p, "; ".join(r)) for p, r in refused]
        out.append("  new .v files whose first %d lines say 'generated' (a hint for the KEEP file; nothing is kept for "
                   "it): %d, %d of them with lines deleted (%d lines)"
                   % (lint.HEADER_LINES, len(hints), sum(1 for _p, n in hints if n), sum(n for _p, n in hints)))
        out += ["    %s: %d deleted" % h for h in hints if h[1]]
        out += [
            "  after the sweep (the sweep does none of these):",
            "    - the swept fuzz target re-keys (its files' object ids change) and takes a new check of record on the "
            "build farm, one Job per fuzz target (condition 22);",
            "    - after the merge, the released-proof index (.github/proof-index.py, which proof-index.yml runs on "
            "the push to main), the stream's lemma and cold-heads indexes and its search corpora are rebuilt "
            "(condition 23);",
            "    - licence (condition 25): %s; a fuzz target with an entry is swept after or beside its licence "
            "series." % pending_note(u),
        ]
        return "\n".join(out)


# --------------------------------------------------------------------------------------------------------- apply


def apply(plan, worktree):
    """Write each changed file of plan into worktree, a checkout of HEAD whose copies of them are HEAD's."""
    got = git(worktree, "rev-parse", "HEAD").decode().strip()
    if got != plan.u.head:
        raise SweepError("%s is at %s, not at head %s" % (worktree, got, plan.u.head))
    changed = sorted(p for p, fp in plan.files.items() if fp.changed())
    if changed:
        dirty = git(worktree, "status", "--porcelain", "-z", "--", *changed).decode("utf-8", "surrogateescape")
        if dirty.strip("\0"):
            raise SweepError("%s has changes in files the sweep writes: %s" % (worktree, dirty.split("\0")[0]))
    for p in changed:
        with open(os.path.join(worktree, p), "w", encoding="utf-8", newline="") as f:
            f.write(plan.files[p].swept_text())
    return changed


# --------------------------------------------------------------------------------------------------------- check


class Seen:
    """A Rocq file as the check reads it, by its own walk over rocq.tokens: which characters are inside a comment,
    which line feeds a comment spans, the lexer state after each line feed, and the outermost comments."""

    def __init__(self, text):
        self.text, self.lines = text, text.split("\n")
        n = len(self.lines)
        self.offsets = [0] * n
        for i in range(1, n):
            self.offsets[i] = self.offsets[i - 1] + len(self.lines[i - 1]) + 1
        self.inside = bytearray(len(text))
        self.joined = [False] * n            # line i's line feed lies inside a comment
        self.state_after = [None] * n        # the lexer state after line i's line feed
        self.comments = []                   # (start offset, end offset) of each outermost comment
        self.bad = []
        depth, pos, opened, open_string = 0, 0, 0, False
        for kind, piece, inside in rocq.tokens(text):
            if kind == "open":
                if depth == 0:
                    opened = pos
                    if pos and text[pos - 1] not in BLANKS and text[max(0, pos - 2):pos] != "*)":
                        self.bad.append("a comment opens after a non-blank character at offset %d" % pos)
                depth += 1
            if depth > 0:
                self.inside[pos:pos + len(piece)] = b"\x01" * len(piece)
            if kind == "close" and inside:
                depth -= 1
                if depth == 0:
                    self.comments.append((opened, pos + len(piece)))
            if kind == "string":
                open_string = pos + len(piece) == len(text) and not string_closed(piece)
            k = piece.find("\n")
            while k >= 0:
                line = bisect.bisect_right(self.offsets, pos + k) - 1
                self.joined[line] = depth > 0
                self.state_after[line] = (depth, kind == "string")
                k = piece.find("\n", k + 1)
            pos += len(piece)
        # no line feed follows the last line: the state after it is the state at the end of the text
        self.state_after[-1] = (depth, open_string)
        if depth:
            self.bad.append("a comment still open at the end")
        if open_string:
            self.bad.append("a string literal still open at the end")
        if ":{{" in text:
            self.bad.append("a `:{{` quotation")
        self.whole = []
        for i, line in enumerate(self.lines):
            o = self.offsets[i]
            cols = [k for k, ch in enumerate(line) if ch not in BLANKS]
            self.whole.append(all(self.inside[o + k] for k in cols) if cols else bool(i and self.joined[i - 1]))
        # blocks: lines joined through a comment's line feed; a line is clean when every line of its block is whole
        clean_block, block = {}, [0] * n
        for i in range(n):
            block[i] = block[i - 1] if i and self.joined[i - 1] else i
            clean_block[block[i]] = clean_block.get(block[i], True) and self.whole[i]
        self.clean = [self.whole[i] and clean_block[block[i]] for i in range(n)]
        self.notice = set()                  # the lines of the comments that start with `(* Modified by`
        for s, e in self.comments:
            if MODIFIED_BY.match(text, s):
                a = bisect.bisect_right(self.offsets, s) - 1
                b = bisect.bisect_right(self.offsets, e - 1) - 1
                self.notice.update(range(a, b + 1))

    def comment_mask(self, i):
        o = self.offsets[i]
        return lambda k: self.inside[o + k] == 1

    def comment_text(self, i, col):
        """(the text of the outermost comment that holds line i's column col, the column's place in it), or None."""
        at = self.offsets[i] + col
        for s, e in self.comments:
            if s <= at < e:
                return self.text[s:e], at - s
        return None


def _notice_anchor(lines, seen):
    """(where the check expects NOTICE, _licence_last), worked out from HEAD's lines (the module docstring)."""
    last = _licence_last(lines)
    k = max(anthropic_header(lines), last + 1)
    while True:
        while 0 < k < len(lines) and seen.joined[k - 1]:
            k += 1
        if k >= len(lines) or not MODIFIED_BY.match(lines[k].lstrip(" \t")):
            return k, last
        k += 1


def _norm(line):
    return CITATION.sub(lambda m: m.group(1) + ":#", CONTINUATION.sub(", :#", line))


def _align(old, new, deletable, avoid=()):
    """[new index or None] for each old line when new is old less some lines deletable(i) allows, every other line
    equal to its old one or equal but for citation numbers; None when there is no such alignment.  Of the alignments,
    it takes one that removes the fewest lines of avoid (the lines a citation names), and at each line keeping before
    removing: two equal lines next to each other are one text, and which of them went is the rule's to say."""
    k = len(old) - len(new)
    if k < 0:
        return None
    cost, back = {0: 0}, []                    # d (old lines removed so far) -> the fewest avoid lines removed
    norm_old, norm_new = {}, {}

    def same(i, j):
        if old[i] == new[j]:
            return True
        if ".v:" not in old[i]:
            return False
        if i not in norm_old:
            norm_old[i] = _norm(old[i])
        if j not in norm_new:
            norm_new[j] = _norm(new[j])
        return norm_old[i] == norm_new[j]

    for i in range(len(old)):
        nxt = {}
        for d, c in cost.items():
            if i - d < len(new) and same(i, i - d):
                nxt[d] = (c, d, True)
        if deletable(i):
            w = 1 if i in avoid else 0
            for d, c in cost.items():
                if d < k and (d + 1 not in nxt or c + w < nxt[d + 1][0]):
                    nxt[d + 1] = (c + w, d, False)
        if not nxt:
            return None
        back.append(nxt)
        cost = {d: v[0] for d, v in nxt.items()}
    if k not in cost:
        return None
    out, d = [None] * len(old), k
    for i in reversed(range(len(old))):
        _c, prev, kept = back[i][d]
        if kept:
            out[i] = i - d
        d = prev
    return out


def _cited_lines(citing, olds, seen_of, new_set, targets, others):
    """{new file: the lines that a citation in a comment of a .v file of the fuzz target at HEAD names}, whether or not
    the citing line stays: the alignment's tie-break and the lines the completeness test does not require to go."""
    out = collections.defaultdict(set)
    for p in citing:
        if ".v:" not in olds[p]:
            continue
        so = seen_of(p)
        if so.bad:
            continue
        for i, line in enumerate(so.lines):
            if ".v:" not in line:
                continue
            for cit in find_citations(line, so.comment_mask(i)):
                t = targets.resolve(cit.ref, p)
                if t in new_set and not exclusion(line, cit, so.comment_text(i, cit.start), others):
                    for lo, hi in cited_ranges(line, cit, line_count(seen_of(t).lines)) or ():
                        out[t].update(range(lo, hi + 1))
    return out


def _deletable_runs(m, after, removable):
    """[[HEAD line index, ...]] of each run of consecutive lines of the swept file (after, a Seen; m maps HEAD's lines
    to its lines) that removable holds for and that the rule could still delete: some part of it starts and ends in
    one lexer state."""
    runs, run = [], []
    for i, j in enumerate(m):
        if j is None:
            continue
        if removable(i) and (not run or run[-1][0] == j - 1):
            run.append((j, i))
            continue
        runs.append(run)
        run = [(j, i)] if removable(i) else []
    runs.append(run)
    out = []
    for run in runs:
        if run:
            j0 = run[0][0]
            states = [after.state_after[j0 - 1] if j0 else (0, False)] + [after.state_after[j] for j, _i in run]
            if len(set(states)) < len(states):
                out.append([i for _j, i in run])
    return out


def check(u, swept, keep_rows=()):
    """(violations, report lines) of the swept commit against HEAD (the module docstring)."""
    swept = rev(u.repo, swept)
    bad = []
    raw = git(u.repo, "diff", "--no-renames", "--name-status", "-z", u.head, swept).decode("utf-8", "surrogateescape")
    parts = [x for x in raw.split("\0") if x]
    changed = []
    for i in range(0, len(parts), 2):
        status, path = parts[i], parts[i + 1]
        if status != "M":
            bad.append("%s: %s by the sweep, which only edits files"
                       % (path, {"A": "added", "D": "deleted"}.get(status, "changed (%s)" % status)))
        elif not (path.endswith(".v") and u.own(path)):
            bad.append("%s: changed, and it is not a .v file of %s" % (path, u.name))
        else:
            changed.append(path)
    # the new files, found another way than the plan finds them: the proofs folders' files at HEAD that BASE lacks,
    # less the new side of each rename or copy pair git finds
    at_base = set(ls_files(u.repo, u.base, u.proofs_dirs))
    fields = git(u.repo, "diff", "-M", "-l0", "--name-status", "-z", u.base, u.head, "--",
                 *u.proofs_dirs).decode("utf-8", "surrogateescape").split("\0")
    paired, i = set(), 0
    while i < len(fields) - 1:
        if fields[i][:1] in ("R", "C"):
            paired.add(fields[i + 2])
            i += 3
        else:
            i += 2
    new_v = sorted(p for p in set(ls_files(u.repo, u.head, u.proofs_dirs)) - at_base - paired if p.endswith(".v"))
    new_set = set(new_v)
    stray = sorted({p for _n, p, _s, _w in keep_rows} - new_set)
    if stray:
        bad.append("KEEP names files that are not new .v files: %s" % ", ".join(stray[:5]))
    released = released_lines(u)
    citing = [p for p in ls_files(u.repo, u.head, u.own_dirs) if p.endswith(".v")]
    olds = {p: d.decode("utf-8", "surrogateescape")
            for p, d in read_blobs(u.repo, u.head, set(citing) | new_set | set(changed)).items()}
    news = {p: d.decode("utf-8", "surrogateescape") for p, d in read_blobs(u.repo, swept, set(changed)).items()}
    targets, others = Targets(citing), other_names(u)
    seen = {p: Seen(olds[p]) for p in sorted(set(changed) | new_set)}

    def seen_of(p):
        """HEAD's file p as the check reads it, read once for _cited_lines and the citation pass both."""
        if p not in seen:
            seen[p] = Seen(olds[p])
        return seen[p]

    avoid = _cited_lines(citing, olds, seen_of, new_set, targets, others)
    afters, maps, keep_by, refuses_licence, counts = {}, {}, {}, {}, collections.Counter()

    def unkept(p, i):
        """Whether the rule deletes line i of new file p, but for the citations that name it."""
        so, line = seen[p], seen[p].lines[i]
        return (i >= lint.HEADER_LINES and so.clean[i] and i not in so.notice and not MODIFIED_BY.search(line)
                and not lint.TIMEOUT_JUSTIFIED.search(line) and not (line.strip(BLANKS) and line in released)
                and i not in keep_by[p])

    def removable(p):
        """The lines of new file p that may not stay: unkept, and named by no citation at HEAD."""
        return lambda i: unkept(p, i) and i not in avoid[p]

    for p in sorted(set(changed) | new_set):
        so = seen[p]
        old_lines = so.lines
        if p in new_set:
            try:
                keep_by[p] = keep_lines(keep_rows, p, old_lines, {i for i, c in enumerate(so.clean) if c})
            except SweepError as e:
                bad.append(str(e))
                keep_by[p] = set()
        anchor, licence_last = _notice_anchor(old_lines, so)
        # a donor file the rule refuses once it would delete a line: no notice fits under its last licence line
        refuses_licence[p] = (from_donor(old_lines) and NOTICE not in old_lines
                              and licence_last == lint.HEADER_LINES - 1)
        if p not in news:
            maps[p] = list(range(len(old_lines)))
            counts["refused"] += bool(so.bad and p in new_set)
            continue
        s = news[p]
        if so.bad:
            bad.append("%s: changed, but the rule refuses it (%s)" % (p, "; ".join(so.bad)))
            continue
        after = afters[p] = Seen(s)
        if after.bad:
            bad.append("%s: the swept file does not lex as HEAD's does (%s)" % (p, "; ".join(after.bad)))
            continue
        if rocq.code(olds[p]) != rocq.code(s):
            bad.append("%s: its code changed (rocq.code differs): the sweep may change comments only" % p)
            continue
        new_lines = after.lines
        has_notice = NOTICE not in old_lines and anchor < len(new_lines) and new_lines[anchor] == NOTICE
        body = new_lines[:anchor] + new_lines[anchor + 1:] if has_notice else new_lines
        if NOTICE in body and NOTICE not in old_lines:
            bad.append("%s: the notice is not at line %d, where the rule puts it" % (p, anchor + 1))
            continue
        m = _align(old_lines, body, (lambda i, p=p: unkept(p, i)) if p in new_set else (lambda i: False),
                   avoid[p])
        if m is None:
            bad.append("%s: not HEAD's file less whole comment lines the rule deletes (with the notice and "
                       "re-resolved citations)" % p)
            continue
        deleted = sum(1 for x in m if x is None)
        if deleted and refuses_licence[p]:
            bad.append("%s: lines deleted, but the rule refuses the file: %s" % (p, LICENCE_REFUSAL))
            continue
        if deleted and from_donor(old_lines) and NOTICE not in old_lines and not has_notice:
            bad.append("%s: lines deleted from a file that came from a donor, and no notice at line %d"
                       % (p, anchor + 1))
        if has_notice and not (deleted and from_donor(old_lines)):
            bad.append("%s: a notice where the rule adds none" % p)
        maps[p] = [x if x is None or not has_notice or x < anchor else x + 1 for x in m]
        counts["deleted"] += deleted
        counts["files"] += bool(deleted)
        counts["notices"] += has_notice
    failed = set(changed) - set(maps)
    # the new files the rule refuses for their licence line: left as they are, though it would delete some line.  A
    # line counts here whatever cites it at HEAD, as the plan counts it: a line named only by a citation on a line the
    # sweep deletes goes, so the plan refuses the file (ThermoDeep639-2).  Being here only skips the number checks of
    # a file the sweep left byte-identical.
    refused_licence = {p for p in new_v if refuses_licence[p] and p not in news and not seen[p].bad
                       and _deletable_runs(maps[p], seen[p], lambda i, p=p: unkept(p, i))}
    counts["refused"] += len(refused_licence)

    # citations, in every kept line of every .v file of the fuzz target at HEAD; a changed file that failed above is
    # not read again, nor are the citations of its lines; a refused file keeps its numbers
    for p in citing:
        if p in failed or ".v:" not in olds[p]:
            continue
        so = seen_of(p)
        if so.bad:
            continue
        m, after = maps.get(p), afters.get(p)
        for i, line in enumerate(so.lines):
            if ".v:" not in line or (m is not None and m[i] is None):
                continue
            cits = find_citations(line, so.comment_mask(i))
            after_cits = find_citations(after.lines[m[i]], after.comment_mask(m[i])) if after is not None else cits
            if [c.ref for c in after_cits] != [c.ref for c in cits]:
                bad.append("%s:%d: its citations differ from HEAD's in more than their numbers" % (p, i + 1))
                continue
            for cit, now in zip(cits, after_cits):
                want = [x[2] for x in cit.numbers]
                got = [x[2] for x in now.numbers]
                target = targets.resolve(cit.ref, p)
                if target in failed:
                    continue
                gone = False
                if target in new_set and not exclusion(line, cit, so.comment_text(i, cit.start), others):
                    ranges = cited_ranges(line, cit, line_count(seen[target].lines))
                    if ranges is not None:
                        tm, want = maps[target], list(want)
                        for (g0, g1), (lo, hi) in zip(citation_groups(line, cit), ranges):
                            if any(tm[k] is None for k in range(lo, hi + 1)):
                                bad.append("%s:%d: cites %s line(s) %d-%d, and the sweep deleted one of them"
                                           % (p, i + 1, target, lo + 1, hi + 1))
                                gone = True
                            else:
                                want[g0], want[g1] = tm[lo] + 1, tm[hi] + 1
                if gone or p in refused_licence:
                    continue
                if got != want:
                    bad.append("%s:%d: citation %s reads %s after the sweep; the rule gives %s"
                               % (p, i + 1, cit.ref, got, want))
                elif got != [x[2] for x in cit.numbers]:
                    counts["citations"] += 1

    # completeness: no new file keeps a run of lines the rule deletes that could go
    for p in new_v:
        if seen[p].bad or p not in maps or p in refused_licence:
            continue
        for run in _deletable_runs(maps[p], afters.get(p, seen[p]), removable(p)):
            bad.append("%s: line(s) %s are still there, and the rule deletes them"
                       % (p, ", ".join(str(i + 1) for i in run[:5])))
    notes = [
        "checked %s against head %s (main %s, base %s): %d new .v files, %d changed files"
        % (swept, u.head, u.main, u.base, len(new_v), len(changed)),
        "  lines deleted: %d in %d files; notices: %d; citations re-resolved: %d; new files the rule refuses, "
        "unchanged: %d" % (counts["deleted"], counts["files"], counts["notices"], counts["citations"],
                           counts["refused"]),
    ]
    return bad, notes


# ------------------------------------------------------------------------------------------------------------ cli


def main(argv=None):
    ap = argparse.ArgumentParser(prog="python3 -m oft.tests.comment_sweep", description=__doc__.split("\n\n")[0])
    ap.add_argument("mode", choices=("plan", "apply", "check"))
    ap.add_argument("--repo", required=True, help="a git repository that holds HEAD, MAIN and BASE")
    ap.add_argument("--unit", required=True, help="the fuzz target, <project>/<harness>")
    ap.add_argument("--head", required=True, help="the fuzz target's head before the sweep")
    ap.add_argument("--main", default="origin/main", help="the released line (default origin/main)")
    ap.add_argument("--base", help="the commit that decides which files are new (default: merge base of main, head)")
    ap.add_argument("--keep", help="the KEEP file: the generated lines the owner keeps")
    ap.add_argument("--tsv", help="plan, apply: write the plan's rows to this file (default: print them)")
    ap.add_argument("--citations", help="plan, apply: write the edit and citation-left rows to this file, with an "
                                        "owner column for checked or deleted (the fuzz target's approval carries it)")
    ap.add_argument("--worktree", help="apply: a checkout of head to write the swept files into")
    ap.add_argument("--swept", help="check: the commit that holds the swept files")
    a = ap.parse_args(argv)
    try:
        u = Unit(a.repo, a.unit, a.head, a.main, a.base)
        keep_rows = read_keep(a.keep)
        if a.mode == "check":
            if not a.swept:
                raise SweepError("check needs --swept")
            bad, notes = check(u, a.swept, keep_rows)
            for line in notes:
                print(line)
            for b in bad:
                print("FAIL %s" % b)
            print("check: %s" % ("FAIL, %d violation(s)" % len(bad) if bad else "PASS"))
            return 1 if bad else 0
        if a.mode == "apply" and not a.worktree:
            raise SweepError("apply needs --worktree")
        plan = Plan(u, keep_rows)
        rows = [ROWS_HEADER] + [_tsv(row) for row in plan.rows()]
        if a.tsv:
            with open(a.tsv, "w", encoding="utf-8") as f:
                f.write("\n".join(rows) + "\n")
        elif a.mode == "plan":
            print("\n".join(rows))
        if a.citations:
            with open(a.citations, "w", encoding="utf-8") as f:
                f.write("\n".join([ROWS_HEADER + "\towner"] + [_tsv(row) + "\t" for row in plan.citation_rows()])
                        + "\n")
        print(plan.summary())
        if a.mode == "apply":
            changed = apply(plan, a.worktree)
            print("apply: wrote %d files into %s" % (len(changed), a.worktree))
        return 0
    except SweepError as e:
        print("comment_sweep: %s" % e, file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
