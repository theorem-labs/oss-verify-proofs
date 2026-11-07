#!/usr/bin/env python3
# Copyright 2026 Theorem Labs, PBC
# SPDX-License-Identifier: Apache-2.0
"""Refuse held content in what a pull request would add to this PUBLIC repository.

    held_content_scan.py --commits BASE HEAD     the content BASE..HEAD introduces
    held_content_scan.py --files FILE...         those files, read as text
    held_content_scan.py --self-test             the detectors alone, nothing scanned

This is a port of the public leak check that guards every push and every `gh` write from Theorem's
machines (theorem-labs/agent-infra, tag leak-check-v13, `public_leak_check.py`): its rule table, its
credential detectors, its fresh-canary self-test, its must-pass negative controls and its four
exits.  What is ported is the DISCIPLINE, not the file: that check's own patterns name what they
look for, so it cannot live in a public repository -- running it over itself refuses it.  Here the
patterns a public file may carry are in `detectors.tsv` beside this script, and the rest come from
the Actions secret HELD_CONTENT_RULES in the same format, pinned by row count and sha256 in
`private-detectors.sha256`.

EXITS, in one place so a reader can see them together:

    0   nothing matched
    2   the check could not finish: a detector that will not compile, a canary its own detector did
        not find, a must-pass line that matched, a private table that is missing or does not match
        its pin, a git call that failed, more text than MAX_BYTES.  EXIT 2 IS NEVER A PASS.
    3   held content was found.

THE SELF-TEST IS THE POINT.  A scanner that finds nothing and a scanner that cannot find anything
print the same thing.  So before any real text is read, every detector draws a fresh canary from
/dev/urandom through its own template and must find it, attributed to ITSELF and not merely to some
other row of the same category; and every line of `must-pass-lines.txt` -- real text already
published in this repository -- must match NO detector.  Either failure is exit 2 with the detector
named.  The numbers go to the job log on every run, pass or fail.

WHAT A PUBLIC LOG MAY SAY.  A refusal names the path, the line number and the detector, and NOT the
text that matched: this log is public, and copying held content into it to complain about held
content is the same leak.  `HELD_CONTENT_SHOW_MATCHES=1` prints the matching text, masked for
credentials, for a run on your own machine.  The workflow never sets it.
"""

import hashlib
import os
import re
import subprocess
import sys

SELF = os.path.realpath(__file__)
HERE = os.path.dirname(SELF)

# The most text one run reads.  Above it the run stops (exit 2) rather than scanning a part of a
# change and calling the whole of it clean.
MAX_BYTES = 64 * 1024 * 1024
# A blob with a NUL byte in this much of its head is read as bytes, not as lines: its printable
# ASCII runs of at least RUN_MIN characters are scanned, as the ported check reads a raw file.
NUL_WINDOW = 64 * 1024
RUN_MIN = 5

ALNUM = (b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789")
# NUL is left out as well as the whitespace the detectors' own classes exclude: a canary written
# to a file would otherwise make that file one this check reads as binary, and the canary would be
# cut into printable runs instead of staying one line.
_NONSPACE = bytes(c for c in range(1, 256) if c not in b" \t\n\v\f\r")


def _without(excluded):
    return bytes(c for c in _NONSPACE if c not in excluded)


# The alphabets a canary template may draw from.  Each is the smallest set its detector's field
# accepts, so a canary exercises the field rather than a friendly corner of it.
ALPHABETS = {
    "alnum": ALNUM,
    "token": ALNUM + b"_-",
    "pat": ALNUM + b"_",
    "hex": b"0123456789abcdef",
    "aws": b"ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789",
    "b64": ALNUM + b"+/",
    "b64p": ALNUM + b"+/=",
    "bearer": ALNUM + b"._~+/-",
    "basic": ALNUM + b"._~+/=-",
    "slash": ALNUM + b"/_-",
    "sig": ALNUM + b"%+/=_-",
    "sentry": ALNUM + b"_=+/-",
    "slackdash": ALNUM + b"-",
    "lowerdash": b"abcdefghijklmnopqrstuvwxyz0123456789-",
    "nonspace": _NONSPACE,
    "nsurl1": _without(b"/:@"),
    "nsurl2": _without(b"/@$<>{}*[]"),
    "nsurl3": _without(b"/"),
    "nsq": _without(b"\"'$<>{}*"),
    "nse": _without(b"\"'$<>{}*`"),
    "nssemi": _without(b";\"'$<>{}*"),
}

PLACEHOLDER = re.compile(r"\{(\d+):([a-z0-9]+)\}")


class Stop(Exception):
    """Raised with the exit status this run must end with."""

    def __init__(self, status, message):
        super().__init__(message)
        self.status = status
        self.message = message


def die(message):
    raise Stop(2, message)


# ------------------------------------------------------------------------------------------------
# The rule table


class Detector:
    __slots__ = ("name", "category", "pattern", "flags", "canary", "source", "rx")

    def __init__(self, name, category, flags, pattern, canary, source):
        self.name, self.category, self.canary, self.source = name, category, canary, source
        self.pattern = pattern
        self.flags = re.MULTILINE | (re.IGNORECASE if flags == "i" else 0)
        try:
            self.rx = re.compile(pattern.encode(), self.flags)
        except re.error as exc:
            die("detector %r from %s does not compile (%s)" % (name, source, exc))


def parse_table(text, source):
    """Rows of `name<TAB>category<TAB>flags<TAB>pattern<TAB>canary`.  A row this parser does not
    understand stops the check: a table read as four rows when it has five is a scan with a hole."""
    out, names = [], set()
    for number, line in enumerate(text.split("\n"), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) != 5:
            die("%s line %d has %d tab-separated fields, not 5" % (source, number, len(parts)))
        name, category, flags, pattern, canary = parts
        if not name or not category or flags not in ("-", "i") or not pattern or not canary:
            die("%s line %d has an empty field or an unknown flags value %r" % (source, number, flags))
        if name in names:
            die("%s line %d repeats the detector name %r" % (source, number, name))
        names.add(name)
        out.append(Detector(name, category, flags, pattern, canary, source))
    if not out:
        die("%s holds no detector" % source)
    return out


def load_detectors():
    """The public table beside this script, then the private table from HELD_CONTENT_RULES, which
    must match the row count and sha256 pinned in private-detectors.sha256.

    The pin is why an absent secret cannot quietly halve the scan.  The job that runs this check is
    the same job for a fork's pull request and for ours, and a secret that did not arrive would
    otherwise turn the check into one that reads for credentials alone and says `clean`."""
    public = parse_table(read_text(os.path.join(HERE, "detectors.tsv")), "detectors.tsv")
    pin = read_text(os.path.join(HERE, "private-detectors.sha256"))
    rows = [ln.split() for ln in pin.split("\n") if ln.strip() and not ln.lstrip().startswith("#")]
    if len(rows) != 1 or len(rows[0]) != 2 or not rows[0][1].isdigit():
        die("private-detectors.sha256 must hold one line `<sha256-hex> <row count>`")
    want_digest, want_rows = rows[0][0], int(rows[0][1])
    raw = os.environ.get("HELD_CONTENT_RULES")
    if not raw:
        die("HELD_CONTENT_RULES is not set, so %d of this check's detectors are missing. The "
            "private table is an Actions secret of this repository; a job without it scans less "
            "than this check claims to scan, so it stops here instead of reporting clean."
            % want_rows)
    # Normalised before hashing, so that a trailing newline GitHub's secret store keeps or drops
    # cannot turn a correct table into a pin mismatch: CRLF to LF, and exactly one final newline.
    raw = raw.replace("\r\n", "\n").rstrip("\n") + "\n"
    got = hashlib.sha256(raw.encode()).hexdigest()
    if got != want_digest:
        die("HELD_CONTENT_RULES does not match its pin in private-detectors.sha256 (sha256 %s, "
            "pinned %s). Change the secret and the pin in the same pull request." % (got, want_digest))
    private = parse_table(raw, "HELD_CONTENT_RULES")
    if len(private) != want_rows:
        die("HELD_CONTENT_RULES holds %d detectors; private-detectors.sha256 pins %d"
            % (len(private), want_rows))
    clash = {d.name for d in public} & {d.name for d in private}
    if clash:
        die("a detector name is in both tables: %s" % ", ".join(sorted(clash)))
    return public, private


def read_text(path):
    try:
        with open(path, "rb") as handle:
            return handle.read().decode("utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        die("cannot read %s (%s)" % (path, exc))


# ------------------------------------------------------------------------------------------------
# The self-test


def draw_canary(template, draw):
    out, at = [], 0
    for match in PLACEHOLDER.finditer(template):
        out.append(template[at:match.start()].encode())
        alphabet = ALPHABETS.get(match.group(2))
        if alphabet is None:
            die("canary template names the unknown alphabet %r" % match.group(2))
        out.append(draw(int(match.group(1)), alphabet))
        at = match.end()
    out.append(template[at:].encode())
    return b"".join(out)


def self_test(detectors):
    """Every detector finds its own fresh canary, and no detector matches a must-pass line.

    Returns (found, total).  Anything short of all of them is exit 2: a clean verdict from a
    detector that did not fire on a line built to fire it says nothing about the text it read."""
    try:
        source = open("/dev/urandom", "rb")
    except OSError as exc:
        die("no fresh canaries could be drawn (%s)" % exc)
    with source:
        def draw(n, alphabet):
            raw = source.read(n)
            if len(raw) != n:
                die("short read from /dev/urandom")
            return bytes(alphabet[c % len(alphabet)] for c in raw)

        canaries = [(d, draw_canary(d.canary, draw)) for d in detectors]

    missed = []
    for detector, text in canaries:
        if not detector.rx.search(text):
            missed.append("detector %r (%s) did not find its own canary" % (detector.name, detector.source))
    controls = read_text(os.path.join(HERE, "must-pass-lines.txt"))
    for number, line in enumerate(controls.split("\n"), 1):
        if not line or line.startswith("#"):
            continue
        raw = line.encode()
        for detector in detectors:
            if detector.rx.search(raw):
                missed.append("detector %r matches must-pass-lines.txt line %d, which is text this "
                              "repository already publishes" % (detector.name, number))
    if missed:
        raise Stop(2, "SELF-TEST FAILED, so a clean result would mean nothing:\n  "
                      + "\n  ".join(missed))
    return len(canaries), len(canaries)


# ------------------------------------------------------------------------------------------------
# What is scanned


def git(*args):
    done = subprocess.run(("git",) + args, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if done.returncode != 0:
        die("git %s failed (%d): %s" % (" ".join(args), done.returncode,
                                        done.stderr.decode("utf-8", "replace").strip()))
    return done.stdout


def printable_runs(blob):
    """Printable ASCII runs of at least RUN_MIN characters, one per line, for a blob git would call
    binary.  A key or a name pasted into a binary file is still a key or a name."""
    out, run = [], bytearray()
    for byte in blob:
        if 32 <= byte < 127 or byte == 9:
            run.append(byte)
        else:
            if len(run) >= RUN_MIN:
                out.append(bytes(run))
            run = bytearray()
    if len(run) >= RUN_MIN:
        out.append(bytes(run))
    return out


def lines_of(blob):
    if b"\0" in blob[:NUL_WINDOW]:
        return printable_runs(blob), True
    return blob.split(b"\n"), False


def records_for_commits(base, head):
    """(label, line number, bytes) for everything BASE..HEAD introduces.

    Three sources, each of which has published held content before: the commit messages, the
    PATHNAMES (a file named after a thing we hold back names it whether or not it is opened), and,
    per path, the lines of the new blob that are NOT already lines of the old blob at that same
    path.  The subtraction is the ported check's: re-stating a line this repository already
    publishes at that path publishes nothing new, and without it every rename and every generated
    table would be refused on content that is already out."""
    records, total = [], 0

    messages = git("log", "--no-show-signature", "--format=%H%x00%B%x00", "%s..%s" % (base, head))
    parts = messages.split(b"\0")
    for i in range(0, len(parts) - 1, 2):
        commit = parts[i].strip().decode("ascii", "replace")[:12]
        if not commit:
            continue
        for number, line in enumerate(parts[i + 1].split(b"\n"), 1):
            records.append(("commit %s (message)" % commit, number, line))
            total += len(line)

    # One `git diff` for every text path, rather than two `cat-file` calls per path: on this
    # repository the per-path form took 24 s on a 706-line change, almost all of it process
    # start-up and lazy blob fetches of files whose lines did not move.
    binary = set()
    stat = git("diff", "--numstat", "-z", "--no-renames", "--diff-filter=ACMT", base, head)
    fields = stat.split(b"\0")
    i = 0
    while i < len(fields) and fields[i]:
        row = fields[i].split(b"\t")
        if len(row) == 3:
            added, removed, path = row
            records.append(("path %s" % path.decode("utf-8", "replace"), 0, path))
            total += len(path)
            if added == b"-" and removed == b"-":
                binary.add(path.decode("utf-8", "replace"))
        i += 1

    diff = git("diff", "--unified=0", "--no-renames", "--no-color", "--no-ext-diff",
               "--diff-filter=ACMT", "--no-prefix", base, head)
    path, number = None, 0
    for line in diff.split(b"\n"):
        if line.startswith(b"+++ "):
            path = line[4:].decode("utf-8", "replace")
            if path == "/dev/null":
                path = None
            number = 0
        elif line.startswith(b"@@"):
            head_marks = line.split(b"+", 1)
            number = 0
            if len(head_marks) == 2:
                start = head_marks[1].split(b" ", 1)[0].split(b",")[0]
                number = int(start) - 1 if start.isdigit() else 0
        elif path and line.startswith(b"+"):
            number += 1
            records.append((path, number, line[1:]))
            total += len(line)
            if total > MAX_BYTES:
                die("this change introduces more than %d bytes of text; nothing was judged"
                    % MAX_BYTES)

    # A blob git calls binary gets no `+` lines from diff, so it is read whole and its printable
    # ASCII runs are scanned: a key or a held name pasted into a binary file is still one.
    for shown in sorted(binary):
        blob = git("cat-file", "blob", "%s:%s" % (head, shown)) if _exists(head, shown) else b""
        old = git("cat-file", "blob", "%s:%s" % (base, shown)) if _exists(base, shown) else b""
        already = set(printable_runs(old))
        for number, run in enumerate(printable_runs(blob), 1):
            if run in already:
                continue
            records.append(("%s (binary)" % shown, number, run))
            total += len(run)
        if total > MAX_BYTES:
            die("this change introduces more than %d bytes of text; nothing was judged" % MAX_BYTES)
    return records


def not_already_published(base, hits):
    """Drop a hit whose exact line is already a line of the same path at BASE.

    `git diff` shows a line that MOVED as added, and a generated table that is sorted again shows
    thousands of them.  Re-stating a line this repository already publishes at that path publishes
    nothing new, so the ported check's subtraction is applied here -- once, to the few paths that
    matched, rather than to every path of the change."""
    kept, cache = [], {}
    for label, number, detector, token, line in hits:
        if label.startswith("commit ") or label.startswith("path ") or label.endswith(" (binary)"):
            kept.append((label, number, detector, token))
            continue
        if label not in cache:
            blob = git("cat-file", "blob", "%s:%s" % (base, label)) if _exists(base, label) else b""
            cache[label] = set(blob.split(b"\n"))
        if line in cache[label]:
            continue
        kept.append((label, number, detector, token))
    return kept


def _exists(rev, path):
    done = subprocess.run(("git", "cat-file", "-e", "%s:%s" % (rev, path)),
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return done.returncode == 0


def records_for_files(paths):
    records, total = [], 0
    for path in paths:
        try:
            with open(path, "rb") as handle:
                blob = handle.read()
        except OSError as exc:
            die("cannot read %s (%s)" % (path, exc))
        records.append(("path %s" % path, 0, path.encode()))
        for number, line in enumerate(lines_of(blob)[0], 1):
            records.append((path, number, line))
            total += len(line)
        if total > MAX_BYTES:
            die("more than %d bytes of text; nothing was judged" % MAX_BYTES)
    return records


# ------------------------------------------------------------------------------------------------
# The scan and what it says


def shown(detector, token):
    if not os.environ.get("HELD_CONTENT_SHOW_MATCHES"):
        return "<withheld: this log is public>"
    text = token.decode("utf-8", "replace")
    if detector.category == "secret":
        return text[:10] + "[redacted]"
    return text if len(text) <= 60 else text[:57] + "..."


def scan(records, detectors):
    """One hit per (record, detector) pair: (label, line number, detector, matched bytes, line)."""
    hits = []
    for label, number, line in records:
        for detector in detectors:
            found = detector.rx.search(line)
            if found:
                hits.append((label, number, detector, found.group(0), line))
    return hits


def main(argv):
    public, private = load_detectors()
    detectors = public + private
    found, total = self_test(detectors)
    print("HELD CONTENT: self-test: %d of %d fresh canaries found; %d detectors "
          "(%d public in detectors.tsv, %d from the pinned private table); "
          "%d must-pass control lines matched none of them"
          % (found, total, len(detectors), len(public), len(private),
             len([ln for ln in read_text(os.path.join(HERE, "must-pass-lines.txt")).split("\n")
                  if ln and not ln.startswith("#")])))

    if not argv or argv[0] == "--self-test":
        print("HELD CONTENT: nothing was scanned (--self-test).")
        return 0
    if argv[0] == "--commits":
        if len(argv) != 3:
            die("--commits takes exactly BASE and HEAD")
        records = records_for_commits(argv[1], argv[2])
        what = "%s..%s" % (argv[1][:12], argv[2][:12])
    elif argv[0] == "--files":
        records = records_for_files(argv[1:])
        what = "%d file(s)" % (len(argv) - 1)
    else:
        die("unknown mode %r" % argv[0])

    hits = scan(records, detectors)
    if argv[0] == "--commits":
        hits = not_already_published(argv[1], hits)
    else:
        hits = [(label, number, detector, token) for label, number, detector, token, _l in hits]
    if not hits:
        print("HELD CONTENT: clean: %d line(s) and pathname(s) of %s matched no detector."
              % (len(records), what))
        return 0
    paths = sorted({label for label, _n, _d, _t in hits})
    print("::error::HELD CONTENT: %d match(es) in %d place(s) of %s. This repository is public; "
          "the matching text is not copied into this log." % (len(hits), len(paths), what))
    for label, number, detector, token in hits[:200]:
        where = "%s:%d" % (label, number) if number else label
        print("  %s  detector %s (%s)  %s" % (where, detector.name, detector.category,
                                              shown(detector, token)))
    if len(hits) > 200:
        print("  ... and %d more" % (len(hits) - 200))
    print("Run this check on your own machine with HELD_CONTENT_SHOW_MATCHES=1 to see the text, or "
          "ask a maintainer. Nothing here may be merged while it matches.")
    return 3


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except Stop as stop:
        sys.stderr.write("::error::HELD CONTENT: %s\n" % stop.message)
        sys.stderr.write("The check could not finish, so nothing is passed (exit %d). %s\n"
                         % (stop.status, SELF))
        sys.exit(stop.status)
