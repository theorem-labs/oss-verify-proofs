#!/usr/bin/env python3
"""notice_claims.py - measure each donor notice of the unit against the file it cites, and print one row per notice.

A donor notice is a `(* Modified by ... *)` comment whose text says the file was "copied from", "made from" or has
lines that "match lines of" another file (the donor). For each one this script reads the donor, measures how the
unit's file differs from it, and says whether the notice's claim agrees with the measurement.

WHAT A NOTICE CLAIMS

 - categories   The kinds of change the notice declares: "module paths" (also "module path"), "addresses" (also
                "addresses moved to ...") and "numbers", and "module names" in a "match lines of" notice.
 - counts       A "made from" notice may give "N of its M lines of code are new or changed and K lines of the
                source are left out". A "match lines of" notice gives "N of its M lines of code ... match lines of".
 - words        Any other change the notice names in words (a rename, a renumbered label, a lemma added or
                removed, "for libreac/fuzz_identity's program walk: ...", and so on). A program cannot check words.
A notice is PLAIN when it is one of the forms
   copied from <donor>[ (donor image sha256 <h>)][ for libreac/fuzz_identity's program walk],
       with its <categories> changed[ and its addresses moved to libreac/fuzz_identity's <build>].
   made from <donor>[ (donor image sha256 <h>)][, with its <categories> changed]; N of its M lines ... K lines
       of the source ... left out.
   written for ...; N of its M lines of code, ..., match lines of <donor> up to <categories>, and the rest is new.
   no single donor found by measurement; N of its M lines of code match lines of <donor> up to <categories>.
and WORDED otherwise.

THE MEASURE

Lines of code are the lines of a file that keep some text when Rocq comments (nested, with their strings) are
removed, each with its leading and trailing blanks removed. Before two files are compared, each line is masked
by the declared categories:
 - module paths: every OssFuzzTheorems[.Proofs].<project>.<target>[.lib|.images][.<dir>...] path, and the image
   module names Plain, Ubsan, Asan and AsanUbsan, become one placeholder; and on a line made only of Require
   sentences, side-by-side sentences of the same kind from masked paths are joined into one, its modules sorted
   (a list of modules from one directory, split because the modules now live in two, is a change of module paths);
 - addresses:    every 0x hex numeral becomes one placeholder;
 - numbers:      every 0x hex numeral and every decimal numeral becomes one placeholder;
 - module names: the module list of a Require line becomes one placeholder.
The masked lines of the file and of the donor, with all whitespace inside each line removed, are aligned by
Python's difflib.SequenceMatcher (autojunk off).
matched is the number of aligned lines; new_or_changed = M - matched, where M is the file's lines of code;
left_out = D - matched, where D is the donor's lines of code. This is the measure that gives exactly the counts
of the "made from" notices whose files did not change after the notices were written (lib/Reusable/YH01.v
9 of 19 and 37, YL0t.v 2 of 183 and 2, YL0v.v 9 of 714 and 9).

THE VERDICT

The verdicts are tried in this order, and the first that holds is the row's.
 agrees                 made from or match lines of, with counts: N, M (and K) equal the measurement (N =
                        matched for match lines of); any other notice: new_or_changed = left_out = 0.
 counts differ          a notice with counts whose numbers are not the measured ones.
 agrees up to Require layout
                        a notice without counts, where the file equals the donor under the declared categories once
                        each Require sentence that runs over several lines is joined onto one line (a list of
                        imports laid out again when its paths changed). The line counts still show the layout change.
 worded                 a worded notice without counts that the checks above do not decide: the counts are
                        measured, the words are not checked.
 donor holds under half a plain copied notice, where the donor holds fewer than half of the file's lines of code.
 numerals only          a plain copied notice that declares addresses, where the file equals the donor (Require sentences joined) when
                        every numeral, hex and decimal, is masked too. A program cannot tell an address written
                        in decimal from a count, so this row is not decided.
 omits changes          any other plain copied notice: the file differs from the donor in lines that the declared
                        categories and the Require layout do not cover.
 donor not found        the cited path is not in the tree at --rev, nor (for a path pinned to a commit with
                        "a working branch <commit>") at that commit, nor (a path that begins with lib/) in the unit.

DONORS

A path that begins with projects/ is read at --rev (default HEAD) of the repository, so a sparse checkout works.
A path pinned with "a working branch <commit>" is read at that commit when the repository has it. A path that
begins with lib/ is read from the unit's own proofs/ directory. A notice that names two donors is measured
against the first; the second is in its words.

THE TABLE

One row per notice, sorted by file and line, tab-separated, with a header row:
 file             the unit file, under proofs/
 line             the line where the notice starts
 form             copied, made or match; and plain or worded
 donor            the first donor path, as the notice writes it
 read_at          where the donor was read: "rev" (at --rev), the pinned commit, "unit", or "-"
 categories       the declared categories
 claimed_counts   N/M/K for made from, N/M for match lines of, "-" otherwise
 loc              M, the file's lines of code
 donor_loc        D, the donor's lines of code
 matched          aligned lines
 new_or_changed   M - matched
 left_out         D - matched
 verdict          as above
 changed_since_base  with --base: "no" when the file's notice of the same rank at --base, its donor paths moved
                  to the projects/<p>/<t>/proofs/ layout, equals the notice here; "yes" when it differs; "new"
                  when the file had no such notice at --base. "-" without --base.
 verdict_at_base  with --base: the verdict of that notice of --base, measured on the file as it was at --base,
                  its donor read as above (an old-layout path that resolves nowhere is read in the projects/
                  layout at --rev). "-" without --base or for a new notice.
The last lines "# rows <n> <verdict>=<count> ..." and "# rows_at_base ..." give the totals.

USAGE

  python3 notice_claims.py --repo <repository root> --unit projects/libreac/fuzz_identity \\
      [--rev HEAD] [--base <commit>] > notice-claims.tsv
"""
import argparse
import collections
import difflib
import os
import re
import subprocess
import sys

NOTICE_START = "(* Modified by "
DONOR = re.compile(
    r"(?:copied from|made from(?: part of)?(?: the TFIB_T definition of)?|match lines of)\s+(\S+)")
PIN = re.compile(r"working branch ([0-9a-f]{7,40})")
CAT = r"(?:module paths|addresses|numbers)"
CATS = CAT + r"(?:(?:, | and |, and )" + CAT + r")*"
HEAD = r"^\(\* Modified by [^,]+, [0-9-]+: "
PLAIN = [
    re.compile(HEAD + r"copied from (?P<d>\S+?),? with its (?P<c>" + CATS + r") changed\. \*\)$"),
    re.compile(HEAD + r"copied from (?P<d>\S+)(?: \(donor image sha256 [0-9a-f]+\))?"
               r"(?: for libreac/fuzz_identity's program walk)?, with its (?P<c>module paths) changed"
               r"(?P<mv> and its addresses moved to libreac/fuzz_identity's [^.]*?)?\. \*\)$"),
    re.compile(HEAD + r"made from (?P<d>[^\s,;]+)(?: \(donor image sha256 [0-9a-f]+\))?(?:, with its (?P<c>" + CATS
               + r") changed)?; (?P<n>\d+) of its "
               r"(?P<m>\d+) lines? of code (?:are|is) new or changed and (?P<k>\d+) lines? of the source (?:are|is) "
               r"left out\. \*\)$"),
    re.compile(HEAD + r"(?:written for [^;]*|no single donor found by measurement); (?P<n>\d+) of its (?P<m>\d+) "
               r"lines of code(?:, among them its imports,)? match lines of (?P<d>\S+) up to "
               r"(?P<c>(?:module paths|module names|addresses|numbers)"
               r"(?: and (?:module paths|module names|addresses|numbers))*)(?:, and the rest is new)?\. \*\)$"),
]
COUNTS_MADE = re.compile(r"(\d+) of its (\d+) lines? of code (?:are|is) new or changed and (\d+) lines? of the "
                         r"source (?:are|is) left out")
COUNTS_MATCH = re.compile(r"(\d+) of its (\d+) lines of code[^;]*?match lines of")
MODPATH = re.compile(r"OssFuzzTheorems(?:\.Proofs)?\.[A-Za-z0-9_\-]+\.[A-Za-z0-9_\-]+"
                     r"(?:\.(?:lib|images)(?:\.[A-Za-z0-9_]+)*)?")
IMGMOD = re.compile(r"\b(?:Plain|Ubsan|Asan|AsanUbsan)\b")
HEX = re.compile(r"0x[0-9a-fA-F]+")
DEC = re.compile(r"(?<![A-Za-z_0-9'])\d+(?![A-Za-z_0-9'])")
REQ = re.compile(r"(Require(?: Import| Export)?)\s.*$")
REQ_SENTENCE = re.compile(r"From <MOD> Require( Import| Export)? ([^.]+)\.(?: +|$)")
OLD_LAYOUT = re.compile(r"\bproofs/([A-Za-z0-9_.\-]+)/([A-Za-z0-9_.\-]+)/lib/")


def strip_comments(text):
    """The text with every Rocq comment (nested, strings inside it included) blanked; newlines are kept."""
    out, i, n, depth = [], 0, len(text), 0
    in_str = False
    while i < n:
        c = text[i]
        if depth == 0:
            if in_str:
                out.append(c)
                if c == '"':
                    if i + 1 < n and text[i + 1] == '"':
                        out.append('"')
                        i += 2
                        continue
                    in_str = False
                i += 1
                continue
            if c == '"':
                in_str = True
                out.append(c)
                i += 1
                continue
            if text.startswith("(*", i):
                depth = 1
                out.append("  ")
                i += 2
                continue
            out.append(c)
            i += 1
            continue
        if text.startswith("(*", i):
            depth += 1
            out.append("  ")
            i += 2
            continue
        if text.startswith("*)", i):
            depth -= 1
            out.append("  ")
            i += 2
            continue
        if c == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2
                        continue
                    break
                j += 1
            out.append(re.sub(r"[^\n]", " ", text[i:j + 1]))
            i = j + 1
            continue
        out.append("\n" if c == "\n" else " ")
        i += 1
    return "".join(out)


def code_lines(text):
    return [line.strip() for line in strip_comments(text).split("\n") if line.strip()]


def join_requires(line):
    """On a line made only of `From <MOD> Require ...` sentences, join side-by-side sentences of one kind and sort
    the modules, since a list split by directory also changes order (for example `YG00 YG0d YB1v YFen` becoming
    `YG00 YG0d YFen. From ... Require Import YB1v`)."""
    pos, parts = 0, []
    while pos < len(line):
        m = REQ_SENTENCE.match(line, pos)
        if not m:
            return line
        if parts and parts[-1][0] == m.group(1):
            parts[-1][1].extend(m.group(2).split())
        else:
            parts.append((m.group(1), m.group(2).split()))
        pos = m.end()
    return " ".join(f"From <MOD> Require{kind or ''} {' '.join(sorted(names))}." for kind, names in parts)


def mask(line, cats):
    if "module paths" in cats:
        line = join_requires(IMGMOD.sub("<IMG>", MODPATH.sub("<MOD>", line)))
    if "addresses" in cats or "numbers" in cats:
        line = HEX.sub("<HEX>", line)
    if "numbers" in cats:
        line = DEC.sub("<NUM>", line)
    if "module names" in cats:
        line = REQ.sub(r"\1 <NAMES>", line)
    return line


def join_open_requires(lines):
    """Lines with each Require sentence that runs over several lines joined onto its first line."""
    out, i = [], 0
    while i < len(lines):
        line = lines[i]
        k = line.rfind("Require")
        while k >= 0 and not re.search(r"\.(?:\s|$)", line[k:]) and i + 1 < len(lines):
            i += 1
            line += " " + lines[i]
        out.append(line)
        i += 1
    return out


def measure(ours, theirs, cats, sentences=False):
    a, b = code_lines(ours), code_lines(theirs)
    if sentences:
        a, b = join_open_requires(a), join_open_requires(b)
    a = ["".join(mask(x, cats).split()) for x in a]
    b = ["".join(mask(x, cats).split()) for x in b]
    sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
    matched = sum(block.size for block in sm.get_matching_blocks())
    return len(a), len(b), matched


def same_sentences(ours, theirs, cats):
    """True when the two files are equal under cats once each Require sentence is on one line."""
    loc, dloc, matched = measure(ours, theirs, cats, sentences=True)
    return loc == dloc == matched


def notices(text):
    """(first line, notice text joined on one line) for each Modified-by comment of the file."""
    lines = text.split("\n")
    out, i = [], 0
    while i < len(lines):
        k = lines[i].find(NOTICE_START)
        if k < 0:
            i += 1
            continue
        buf, j = lines[i][k:], i
        while "*)" not in buf and j + 1 < len(lines):
            j += 1
            buf += " " + lines[j].strip()
        out.append((i + 1, re.sub(r"\s+", " ", buf[:buf.index("*)") + 2] if "*)" in buf else buf)))
        i = j + 1
    return out


def categories(text):
    cats = []
    if re.search(r"module paths?\b", text):
        cats.append("module paths")
    if "module names" in text:
        cats.append("module names")
    if re.search(r"\baddresses\b", text):
        cats.append("addresses")
    if re.search(r"\bnumbers\b", text):
        cats.append("numbers")
    return cats


class Repo:
    def __init__(self, root):
        self.root = root
        self.cache = {}

    def show(self, rev, path):
        key = (rev, path)
        if key not in self.cache:
            r = subprocess.run(["git", "cat-file", "blob", f"{rev}:{path}"], cwd=self.root, capture_output=True)
            self.cache[key] = r.stdout.decode("utf-8", "replace") if r.returncode == 0 else None
        return self.cache[key]

    def commit(self, rev):
        r = subprocess.run(["git", "rev-parse", "--verify", "--quiet", f"{rev}^{{commit}}"], cwd=self.root,
                           capture_output=True, text=True)
        return r.stdout.strip() if r.returncode == 0 else None


def resolve(repo, rev_id, unit_proofs, donor, text, moved=False):
    """(donor text, where it was read) or (None, '-'). With moved, an old-layout path that resolves nowhere is
    also tried in the projects/ layout at rev_id."""
    if donor.startswith("projects/"):
        t = repo.show(rev_id, donor)
        return (t, "rev") if t is not None else (None, "-")
    if donor.startswith("proofs/"):
        tail = text[text.find(donor) + len(donor):]
        m = PIN.search(tail)
        if m:
            sha = repo.commit(m.group(1))
            if sha:
                t = repo.show(sha, donor)
                if t is not None:
                    return t, sha[:12]
        if moved:
            return resolve(repo, rev_id, unit_proofs, to_new_layout(donor), text)
        return None, "-"
    if donor.startswith("lib/"):
        p = os.path.join(unit_proofs, donor)
        if os.path.isfile(p):
            with open(p, encoding="utf-8", errors="replace") as f:
                return f.read(), "unit"
    return None, "-"


def to_new_layout(text):
    return OLD_LAYOUT.sub(lambda m: f"projects/{m.group(1)}/{m.group(2)}/proofs/lib/", text)


def assess(repo, rev_id, unit_proofs, ours, text, moved=False):
    """The row fields of one notice (text) of a file (ours), or None when the notice names no donor."""
    dm = DONOR.search(text)
    if not dm:
        return None
    donor = dm.group(1).rstrip(".,;:)")
    kind, plain = judge(text)
    cats = categories(text[dm.start():])
    theirs, read_at = resolve(repo, rev_id, unit_proofs, donor, text, moved)
    cm = COUNTS_MADE.search(text) if kind == "made" else (COUNTS_MATCH.search(text) if kind == "match" else None)
    row = {"form": f"{kind} {'plain' if plain else 'worded'}", "donor": donor, "read_at": read_at,
           "categories": ", ".join(cats) or "-", "claimed_counts": "/".join(cm.groups()) if cm else "-"}
    if theirs is None:
        row.update(loc=len(code_lines(ours)), donor_loc="-", matched="-", new_or_changed="-", left_out="-",
                   verdict="donor not found")
        return row
    loc, dloc, matched = measure(ours, theirs, cats)
    new, left = loc - matched, dloc - matched
    if kind == "made" and cm:
        n, m, k = (int(x) for x in cm.groups())
        verdict = "agrees" if (n, m, k) == (new, loc, left) else "counts differ"
    elif kind == "match" and cm:
        n, m = (int(x) for x in cm.groups())
        verdict = "agrees" if (n, m) == (matched, loc) else "counts differ"
    elif new == 0 and left == 0:
        verdict = "agrees"
    elif same_sentences(ours, theirs, cats):
        verdict = "agrees up to Require layout"
    elif not plain:
        verdict = "worded"
    elif matched * 2 < loc:
        verdict = "donor holds under half"
    elif "addresses" in cats and same_sentences(ours, theirs, cats + ["addresses", "numbers"]):
        verdict = "numerals only"
    else:
        verdict = "omits changes"
    row.update(loc=loc, donor_loc=dloc, matched=matched, new_or_changed=new, left_out=left, verdict=verdict)
    return row


def judge(text):
    for i, p in enumerate(PLAIN):
        if p.match(text):
            return ["copied", "copied", "made", "match"][i], True
    return ("made" if "made from" in text else ("match" if "match lines of" in text else "copied")), False


COLUMNS = ["file", "line", "form", "donor", "read_at", "categories", "claimed_counts", "loc", "donor_loc",
           "matched", "new_or_changed", "left_out", "verdict", "changed_since_base", "verdict_at_base"]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--repo", required=True, help="repository root (the directory that holds projects/)")
    ap.add_argument("--unit", required=True, help="unit directory under the repository, e.g. projects/libreac/fuzz_identity")
    ap.add_argument("--rev", default="HEAD", help="commit at which projects/ donors are read (default HEAD)")
    ap.add_argument("--base", help="commit whose notices and files are also measured (the last two columns)")
    args = ap.parse_args()

    repo = Repo(args.repo)
    rev_id = repo.commit(args.rev)
    if not rev_id:
        sys.exit(f"notice_claims: {args.rev} is not a commit of {args.repo}")
    base_id = repo.commit(args.base) if args.base else None
    if args.base and not base_id:
        sys.exit(f"notice_claims: {args.base} is not a commit of {args.repo}")
    unit_proofs = os.path.join(args.repo, args.unit, "proofs")
    paths = []
    for d, _, fs in os.walk(os.path.join(unit_proofs, "lib")):
        paths += [os.path.relpath(os.path.join(d, f), unit_proofs) for f in fs if f.endswith(".v")]
    paths.sort()

    print("\t".join(COLUMNS))
    totals, base_totals = collections.Counter(), collections.Counter()
    for rel in paths:
        with open(os.path.join(unit_proofs, rel), encoding="utf-8", errors="replace") as f:
            ours = f.read()
        rows = [(line, text, assess(repo, rev_id, unit_proofs, ours, text)) for line, text in notices(ours)]
        rows = [(line, text, row) for line, text, row in rows if row]
        if not rows:
            continue
        base_text, base_notices = None, []
        if base_id:
            base_text = repo.show(base_id, os.path.join(args.unit, "proofs", rel))
            if base_text is not None:
                base_notices = [text for _, text in notices(base_text) if DONOR.search(text)]
        for i, (line, text, row) in enumerate(rows):
            row.update(file=rel, line=line, changed_since_base="-", verdict_at_base="-")
            if base_id:
                old = base_notices[i] if i < len(base_notices) else None
                if old is None:
                    row["changed_since_base"] = "new"
                else:
                    row["changed_since_base"] = "no" if to_new_layout(old) == text else "yes"
                    at_base = assess(repo, rev_id, unit_proofs, base_text, old, moved=True)
                    row["verdict_at_base"] = at_base["verdict"]
                    base_totals[at_base["verdict"]] += 1
            totals[row["verdict"]] += 1
            print("\t".join(str(row[c]) for c in COLUMNS))
    for name, t in (("rows", totals), ("rows_at_base", base_totals)):
        if t:
            print(f"# {name} {sum(t.values())} " + " ".join(f"{k.replace(' ', '_')}={v}" for k, v in sorted(t.items())))


if __name__ == "__main__":
    main()
