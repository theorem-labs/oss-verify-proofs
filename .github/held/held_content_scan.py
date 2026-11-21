#!/usr/bin/env python3
# Copyright 2026 Theorem Labs, PBC
# SPDX-License-Identifier: Apache-2.0
"""Refuse held content in what a pull request would add to this PUBLIC repository.

    held_content_scan.py [--public-only] --commits BASE HEAD   the content BASE..HEAD introduces
    held_content_scan.py [--public-only] --files FILE...       those files, read as text
    held_content_scan.py [--public-only] --self-test           the detectors alone, nothing scanned
    held_content_scan.py [--public-only] --pull-request REPO HEAD NUMBER... --verdict FILE
                                                               the pull requests of REPO whose head
                                                               is HEAD, read through the GitHub API

This is a port of the leak check that guards every push and every `gh` write from Theorem's own
machines, at the tag `leak-check-v13` of the internal tool that holds it: its rule table, its
credential detectors, its fresh-canary self-test, its must-pass negative controls and its four
exits.  What is ported is the DISCIPLINE, not the file: that check's own patterns name what they
look for, so it cannot live in a public repository -- running it over itself refuses it.  Here the
patterns a public file may carry are in `detectors.tsv` beside this script, and the rest come from
the Actions secret HELD_CONTENT_RULES in the same format, pinned by row count and sha256 in
`private-detectors.sha256`.

WHICH DETECTORS A RUN READS.  Without `--public-only`, a run reads both tables, and a private table
that is missing or does not match its pin stops it with exit 2.  With `--public-only`, a run reads
`detectors.tsv` alone and never reads HELD_CONTENT_RULES, and its first line of output says so.
`.github/workflows/held-content.yml` runs on `pull_request`, where the change of a fork gets no
secret, so it gives `--public-only`.  `.github/workflows/held-content-private.yml` runs with the
secret.  This script never changes to `--public-only` by itself.  The flag can stand anywhere among
the arguments, so give a file with that name as `./--public-only`.

TO CHANGE THE PRIVATE TABLE, change the pin on main of the internal repository first.  Set the new
secret right after the release that publishes that pin.  Until then the secret and the pin differ,
and every run that reads the secret stops with exit 2.

EXITS, in one place so a reader can see them together:

    0   nothing matched.  With --pull-request, 0 means that the verdict was written, whatever its
        state is.
    2   the check could not finish: a detector that will not compile, a canary its own detector did
        not find, a must-pass line that matched, a private table that is missing or does not match
        its pin (without --public-only), a git call that failed, more text than MAX_BYTES.
        EXIT 2 IS NEVER A PASS.
    3   held content was found.

THE SELF-TEST IS THE POINT.  A scanner that finds nothing and a scanner that cannot find anything
print the same thing.  So before any real text is read, every detector draws a fresh canary from
/dev/urandom through its own template and must find it, attributed to ITSELF and not merely to some
other row of the same category; and every line of `must-pass-lines.txt` -- real text already
published in this repository -- must match NO detector.  Either failure is exit 2 with the detector
named: a row of `detectors.tsv` by its name, and a private row as `private row N`, N being its line
in the text of the secret.  The numbers go to the job log on every run, pass or fail.

WHAT A PUBLIC LOG MAY SAY.  A refusal names its place by number and NOT the text that matched: this
log is public, and copying held content into it to complain about held content is the same leak.
A path name or a commit message can be the held content, so a refusal names no path and no commit
either.  `commit K` is the K-th commit of `git log --reverse BASE..HEAD`, `path K` is the K-th
record of `git diff --raw --no-renames BASE HEAD` (a deleted path and a submodule are records too),
and `path K line N` is line N of the new text of that path.  The log names HEAD and no other
commit.  A row of `detectors.tsv` is named with its category.  A private row is named by its number
alone, with no name and no category.  With `--files`, the refusal names the files, and
`HELD_CONTENT_SHOW_MATCHES=1` prints the matching text, masked for credentials, for a run on your
own machine.  No workflow sets it, and the other modes never print the text.

THE API MODE.  `--pull-request REPO HEAD NUMBER...` scans each pull request NUMBER of REPO whose
head is the commit HEAD.  `.github/workflows/held-content-private.yml` runs it from main, with the
secret.  It checks out nothing of a pull request and runs none of its files.  Every read is one
GET of the GitHub API at GITHUB_API_URL, which the scan sends itself with Python's HTTP client:

    repos/REPO/pulls/NUMBER                             the base branch, the head, the labels
    repos/REPO/compare/<base branch>...HEAD             the merge base and the count of commits
    repos/REPO/compare/<merge base>...HEAD, each page   the commits, with both ends fixed
    repos/REPO/git/trees/<id>, never recursive          one folder
    repos/REPO/git/blobs/<id>, as raw bytes             one file, read once
    rate_limit                                          the requests left

A pull request whose head is no longer HEAD is not scanned.  The commits are numbered as
`git log --reverse <merge base>..HEAD` numbers them, by a walk from HEAD over their parents and
committer times, and never by the order of the answer.  The two trees are read together, one
folder at a time, and a folder is read only when its id differs.  The entries are compared as git
compares them, so the paths come out in the order of `git diff --raw --no-renames`.  The records
are the three that `--commits` reads: each commit message, each path, and the new lines of each
path.  A change of mode alone is a path with no text, and no blob is read for it.

WHY THE API MODE DOES NOT READ THROUGH gh.  gh changes each C0 and C1 control character of a JSON
answer to its caret pair, except tab, newline, vertical tab and carriage return: ESC becomes `^[`.
gh does this to each answer whose content type matches `[/+]json($|;)`, and no option of gh stops
it.  The code of go-gh that gh 2.98.0 runs shows this: `newSanitizerRoundTripper` in
`pkg/api/http_client.go`, and `pkg/asciisanitizer`.  So through gh, a name or a commit message is
not the text that git reads, and the two names `n<ESC>` and `n^[` become one name.  Python's HTTP
client gives each answer byte for byte.  So the scan reads each name and each message in UTF-8 as
git reads it.  git takes any byte but NUL and `/` in the name of a folder entry, but a JSON answer
is Unicode text.  So a name or a message that is not UTF-8 cannot come in an answer as the bytes
that git holds.  For such a name or message, the scan judges the text that GitHub gives.  The
order of the paths, the numbers `path K` and the text that a row is matched against can then
differ from those of git.  This script calls `git` and the GitHub API, and no other program or
service.

The label `prove-it-can-fail` on a pull request makes its scan a demonstration.  After every read
succeeded, the scan adds one fresh canary of every detector to the records, as `planted sample K`.
Its verdict is then `failure` when every detector found its own sample, and `error` when one did
not.  It is never `success`.

THE VERDICT of the API mode is the JSON object in FILE: `state` (`success`, `failure` or `error`),
`description` (at most 140 characters) and `pull_requests` (the numbers that the verdict is
about).  Several pull requests on one head get one verdict: `failure` when one of them failed,
else `error` when one of them could not be judged, else `success`.  The mode posts nothing: the
next step of the workflow posts the verdict.  A `failure` lists its places by number.  Each cause
of `error` has one fixed description, with no count and no time in it.  So two runs with the same
cause write the same text, and the workflow posts it once.  The log of the mode names the pull
request numbers and HEAD, and no other commit, no path and no matching text.

THE REQUESTS of the API mode.  They are made one at a time, at least REQUEST_GAP seconds apart.
Before the first read and after every 100 reads, the scan reads `rate_limit`, and it stops with
`error` when the requests left are under `min(3000, limit // 5)`.  Every GITHUB_TOKEN of the
repository draws on the same count, so the scan leaves that part to the other workflows.  A 403
or 429 answer that names a rate limit stops the scan with the same `error`.  Before it reads a
blob, the scan stops with `error` when a blob is over 100 MB, or when the requests left cannot
pay for the blob reads above the floor.  As in `--commits`, the scan stops with `error` when the
text that the change introduces is over MAX_BYTES, and the size of its blobs does not count.  The
hourly run of the workflow scans a head with an `error` again.

THE CLOCK of the API mode.  TIME_LIMIT seconds after it started, the scan stops with `error`: it
starts no request after that time, and it stops before the next read of the body of an answer.
Each read of the socket waits for a part of the answer for the time that was left at the start
of the request, but CALL_MOST seconds at most and CALL_LEAST seconds at least.  A read that waits
that long stops the scan, with `error` "the scan ran past its time" when the time is out and else
"a GitHub read failed".  So once the time is out, a read of the body stops the scan CALL_MOST
seconds later at most.  That is well inside the 60 minutes of the job, and the next step of the
workflow can still post the verdict.

The clock does not bound the status line and the headers of an answer.  It also does not bound
the chunk-size lines and the trailer of a chunked answer.  http.client reads each of these lines
with the timeout of the socket alone, and it reads no clock.  So a server that sends them one byte
at a time can hold a request past the time of the scan.  GitHub does not answer that way.  The
`timeout-minutes` of the job ends such a run, and the hourly run then scans the head again.

THE TOKEN of the API mode is the value of GH_TOKEN.  When GH_TOKEN is not set, the scan stops with
`error` before its first read.  The scan sends the token in the Authorization header, and only to
the scheme, host and port of GITHUB_API_URL.  GitHub's runner sets GITHUB_API_URL, and the scan
uses https://api.github.com when it is not set.  The scan uses no proxy, also when `http_proxy` or
`https_proxy` is set.  The scan follows no redirect: a 3xx answer stops the scan with `error`, as
each other answer that is not 2xx does.  No message of the scan holds the token, a header or an
answer.
"""

import collections
import datetime
import hashlib
import heapq
import http.client
import io
import json
import os
import re
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

SELF = os.path.realpath(__file__)
HERE = os.path.dirname(SELF)

# The most text that one run judges.  For a change, that is the text it introduces (records_of),
# not the size of its blobs.  Above it the run stops (exit 2) rather than scanning a part of a
# change and calling the whole of it clean.
MAX_BYTES = 64 * 1024 * 1024
# A blob with a NUL byte in this much of its head is read as bytes, not as lines: its printable
# ASCII runs of at least RUN_MIN characters are scanned, as the ported check reads a raw file.
NUL_WINDOW = 64 * 1024
RUN_MIN = 5

# The API mode (--pull-request).  The largest blob that the git blobs of the API give.
MAX_BLOB = 100 * 1024 * 1024
# The label that makes the scan of a pull request a demonstration.
LABEL = "prove-it-can-fail"
# The commits on one page of a comparison, the most that GitHub gives.
PER_PAGE = 100
# The seconds between two requests, at least, so one job makes at most 300 requests a minute.
# Then the seconds after which a scan stops, under the 60 minutes that the workflow gives its job.
# The tests give other values in HELD_CONTENT_REQUEST_GAP and HELD_CONTENT_TIME_LIMIT.  No workflow
# sets them.
REQUEST_GAP = 0.2
TIME_LIMIT = 50 * 60
# The least time that one read of the socket waits for a part of the answer, in seconds, also when
# less of TIME_LIMIT was left at the start of the request.
CALL_LEAST = 5
# The most time that one read of the socket waits for a part of the answer, in seconds.  THE CLOCK,
# in the docstring of this file, says what a read that waits that long does.
CALL_MOST = 60
# The scan stops when the requests left this hour are under min(FLOOR_MOST, limit // 5).  The
# limit is 15,000 an hour for all the GITHUB_TOKENs of a repository together, and 3,000 leaves a
# fifth of it to the other workflows.  The scan reads the count again after FLOOR_EVERY reads.
FLOOR_MOST = 3000
FLOOR_EVERY = 100
# The most characters that GitHub keeps of the description of a status.
DESCRIPTION_MOST = 140
# The description of each cause of an `error` verdict.  Each is fixed text with no count, no time
# and no run in it, so two runs with the same cause write the same bytes.  The workflow writes one
# more, for a step that failed before the scan finished.
SECRET = "the secret HELD_CONTENT_RULES is missing or differs from its pin"
SELF_TEST = "the self-test of the patterns failed"
LISTING = "a folder listing came back cut short"
FLOOR = "the request floor was reached, or GitHub answered with a rate limit"
TOO_LARGE = "a file is over %d MB or the text is over %d MiB" % (MAX_BLOB >> 20, MAX_BYTES >> 20)
INCOMPLETE = "the comparison was incomplete"
READ = "a GitHub read failed"
TIME = "the scan ran past its time"
PLANTED = "a planted sample was not found"

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
    """Raised with the exit status this run must end with.  `cause` is the description of the
    `error` verdict that the API mode writes for this stop, when the place of the stop knows it."""

    def __init__(self, status, message, cause=None):
        super().__init__(message)
        self.status = status
        self.message = message
        self.cause = cause


def die(message, cause=None):
    raise Stop(2, message, cause)


# ------------------------------------------------------------------------------------------------
# The rule table


class Detector:
    """One row of a table.  `row` is the line of a private row in the text of the secret, and None
    for a row of detectors.tsv.  `label` is how the messages of the table and of the self-test name
    the row: a public row by its name, a private row as `private row N` alone, because its name and
    its fields say what it looks for.  `hit` is how a hit line of report() names the row: a public
    row by its name and category, and a private row by its label."""
    __slots__ = ("name", "category", "pattern", "flags", "canary", "source", "row", "label", "hit",
                 "rx")

    def __init__(self, name, category, flags, pattern, canary, source, row=None):
        self.name, self.category, self.canary, self.source = name, category, canary, source
        self.pattern, self.row = pattern, row
        self.label = ("private row %d" % row if row is not None
                      else "detector %r (%s)" % (name, source))
        self.hit = (self.label if row is not None
                    else "detector %s (%s)" % (name, category))
        self.flags = re.MULTILINE | (re.IGNORECASE if flags == "i" else 0)
        for found in PLACEHOLDER.finditer(canary):
            if found.group(2) not in ALPHABETS:
                die("%s: its canary template names an unknown alphabet%s"
                    % (self.label, "" if row is not None else " %r" % found.group(2)))
        try:
            self.rx = re.compile(pattern.encode(), self.flags)
        except re.error as exc:
            if row is not None:
                die("%s does not compile (at position %s)" % (self.label, exc.pos))
            die("%s does not compile (%s)" % (self.label, exc))


def parse_table(text, source, private=False):
    """Rows of `name<TAB>category<TAB>flags<TAB>pattern<TAB>canary`.  A row this parser does not
    understand stops the check: a table read as four rows when it has five is a scan with a hole.
    A message about a row of the private table names it `private row N`, N being its line in text,
    and prints no field of it."""
    out, names = [], {}
    for number, line in enumerate(text.split("\n"), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        where = "private row %d" % number if private else "%s line %d" % (source, number)
        parts = line.split("\t")
        if len(parts) != 5:
            die("%s has %d tab-separated fields, not 5" % (where, len(parts)))
        name, category, flags, pattern, canary = parts
        if not name or not category or flags not in ("-", "i") or not pattern or not canary:
            die("%s has an empty field or an unknown flags value%s"
                % (where, "" if private else " %r" % flags))
        if name in names:
            die("%s repeats the name of private row %d" % (where, names[name]) if private
                else "%s repeats the detector name %r" % (where, name))
        names[name] = number
        out.append(Detector(name, category, flags, pattern, canary, source,
                            number if private else None))
    if not out:
        die("%s holds no detector" % source)
    return out


def load_detectors(public_only=False):
    """(public, private): the public table beside this script, then, unless public_only, the private
    table from HELD_CONTENT_RULES, which must match the row count and sha256 pinned in
    private-detectors.sha256.  With public_only, private is empty and nothing of the secret is read.

    The pin is why an absent secret cannot quietly halve the scan.  A secret that did not arrive
    would otherwise turn the check into one that reads for credentials alone and says `clean`, so
    without public_only it stops the run.  A `pull_request` run of a fork's change gets no secret:
    held-content.yml gives `--public-only` and says so, and held-content-private.yml reads the
    secret."""
    public = parse_table(read_text(os.path.join(HERE, "detectors.tsv")), "detectors.tsv")
    if public_only:
        return public, []
    pin = read_text(os.path.join(HERE, "private-detectors.sha256"))
    rows = [ln.split() for ln in pin.split("\n") if ln.strip() and not ln.lstrip().startswith("#")]
    if len(rows) != 1 or len(rows[0]) != 2 or not rows[0][1].isdigit():
        die("private-detectors.sha256 must hold one line `<sha256-hex> <row count>`",
            cause=SECRET)
    want_digest, want_rows = rows[0][0], int(rows[0][1])
    raw = os.environ.get("HELD_CONTENT_RULES")
    if not raw:
        die("HELD_CONTENT_RULES is not set, so %d of this check's detectors are missing. The "
            "private table is an Actions secret of this repository; a job without it scans less "
            "than this check claims to scan, so it stops here instead of reporting clean."
            % want_rows, cause=SECRET)
    # Normalised before hashing, so that a trailing newline GitHub's secret store keeps or drops
    # cannot turn a correct table into a pin mismatch: CRLF to LF, and exactly one final newline.
    raw = raw.replace("\r\n", "\n").rstrip("\n") + "\n"
    got = hashlib.sha256(raw.encode()).hexdigest()
    if got != want_digest:
        die("HELD_CONTENT_RULES does not match its pin in private-detectors.sha256 (sha256 %s, "
            "pinned %s). To change the private table, change the pin on main of the internal "
            "repository first, and set the new secret right after the release that publishes "
            "that pin." % (got, want_digest), cause=SECRET)
    private = parse_table(raw, "HELD_CONTENT_RULES", private=True)
    if len(private) != want_rows:
        die("HELD_CONTENT_RULES holds %d detectors; private-detectors.sha256 pins %d"
            % (len(private), want_rows), cause=SECRET)
    names = {d.name for d in public}
    clash = [d.label for d in private if d.name in names]
    if clash:
        die("a row of detectors.tsv has the name of %s" % ", ".join(clash))
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
        # Detector checks each alphabet that a canary template names when its table loads.
        out.append(draw(int(match.group(1)), ALPHABETS[match.group(2)]))
        at = match.end()
    out.append(template[at:].encode())
    return b"".join(out)


def fresh_canaries(detectors):
    """[(detector, bytes)]: one fresh canary of each detector, drawn from /dev/urandom through its
    own template.  The self-test draws them, and so does the API mode for the label LABEL."""
    try:
        source = open("/dev/urandom", "rb")
    except OSError as exc:
        die("no fresh canaries could be drawn (%s)" % exc, cause=SELF_TEST)
    with source:
        def draw(n, alphabet):
            raw = source.read(n)
            if len(raw) != n:
                die("short read from /dev/urandom", cause=SELF_TEST)
            return bytes(alphabet[c % len(alphabet)] for c in raw)

        return [(d, draw_canary(d.canary, draw)) for d in detectors]


def self_test(detectors):
    """Every detector finds its own fresh canary, and no detector matches a must-pass line.

    Returns (found, total).  Anything short of all of them is exit 2: a clean verdict from a
    detector that did not fire on a line built to fire it says nothing about the text it read."""
    canaries = fresh_canaries(detectors)

    missed = []
    for detector, text in canaries:
        if not detector.rx.search(text):
            missed.append("%s did not find its own canary" % detector.label)
    controls = read_text(os.path.join(HERE, "must-pass-lines.txt"))
    for number, line in enumerate(controls.split("\n"), 1):
        if not line or line.startswith("#"):
            continue
        raw = line.encode()
        for detector in detectors:
            if detector.rx.search(raw):
                missed.append("%s matches must-pass-lines.txt line %d, which is text this "
                              "repository already publishes" % (detector.label, number))
    if missed:
        raise Stop(2, "SELF-TEST FAILED, so a clean result would mean nothing:\n  "
                      + "\n  ".join(missed))
    return len(canaries), len(canaries)


# ------------------------------------------------------------------------------------------------
# What is scanned


def git(*args, stdin=None, env=None):
    # Neither git's own message nor its arguments go to the log: either can name a path or a
    # commit, and this log is public.  Run the same git command on your own machine to read it.
    done = subprocess.run(("git",) + args, input=stdin, env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE)
    if done.returncode != 0:
        # the git command, after the `-c NAME=VALUE` that can come before it
        command = args[2] if args[0] == "-c" else args[0]
        die("git %s failed (exit %d). Its message is not printed, because it can name a path or a "
            "commit." % (command, done.returncode))
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


RAW = re.compile(rb"^:(\d{6}) (\d{6}) ([0-9a-f]+) ([0-9a-f]+) ([A-Z])\d*$")
ZERO = re.compile(rb"^0+$")
# The mode of a submodule entry: its id names a commit of another repository, not a blob here.
SUBMODULE = b"160000"


class Blobs:
    """One `git cat-file --batch` for the whole run, read by OBJECT ID.

    By id, never by `<rev>:<path>`: a pathname has to be decoded to go into a command line, and a
    path holding a byte that is not UTF-8 came back as a different path, whose lookup failed --
    and a failed lookup read as `the file is not there`, which reads as clean.  Here a read that
    fails STOPS the check (exit 2), which also covers the case this repository actually has: the
    job checks out with `filter=blob:none`, so a blob arrives by a fetch that can fail."""

    def __init__(self):
        self.proc = subprocess.Popen(["git", "cat-file", "--batch"],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def read(self, oid, place):
        """The blob oid, which is the old or the new text of `place`, the name messages give it."""
        if oid is None:
            return b""
        self.proc.stdin.write(oid + b"\n")
        self.proc.stdin.flush()
        header = self.proc.stdout.readline()
        if not header:
            die("git cat-file --batch stopped while reading a blob of %s" % place)
        parts = header.split()
        if len(parts) != 3 or parts[1] != b"blob":
            die("git cat-file --batch could not give a blob of %s" % place)
        want, out = int(parts[2]), bytearray()
        while len(out) < want:
            chunk = self.proc.stdout.read(want - len(out))
            if not chunk:
                die("git cat-file --batch gave %d of %d bytes of a blob of %s"
                    % (len(out), want, place))
            out += chunk
        self.proc.stdout.read(1)
        return bytes(out)

    def close(self):
        try:
            self.proc.stdin.close()
            self.proc.stdout.close()
        finally:
            self.proc.wait()


def changed_blobs(base, head):
    """[(path bytes, old oid or None, new oid or None)] for BASE..HEAD, from `git diff --raw -z`, in
    its order, which numbers the paths.

    A raw record gives the BLOB IDS, so nothing downstream turns a pathname back into a lookup,
    and `-z` gives each path as its own NUL-terminated field, so a tab or a line break in a name
    is part of the name rather than a field separator.  The reader this replaces parsed `git
    diff`'s patch text, where a content line beginning `++ ` is indistinguishable from a `+++ `
    file header: an audit built a change that hid a credential behind exactly that, and another
    that hid a binary file behind a tab in its name.  Neither is expressible here.  A record this
    does not understand stops the check.  A side that is a submodule (mode 160000) is None, as an
    absent side is: its id is a commit of another repository, so the path is a record with no
    text."""
    fields = git("diff", "--raw", "-z", "--no-renames", "--abbrev=64", base, head).split(b"\0")
    out, i = [], 0
    while i + 1 < len(fields):
        info, path = fields[i], fields[i + 1]
        i += 2
        if not info:
            continue
        found = RAW.match(info)
        if found is None:
            die("git diff --raw gave a record this check does not understand: %r" % info[:200])
        old, new = found.group(3), found.group(4)
        out.append((path, None if ZERO.match(old) or found.group(1) == SUBMODULE else old,
                    None if ZERO.match(new) or found.group(2) == SUBMODULE else new))
    return out


def records_of(messages, changes, read):
    """[(place, bytes)] for everything a change introduces, each place by number: `commit K` for a
    line of the K-th of messages, `path K` for the name of the K-th of changes, and `path K line N`
    for its line N.  messages holds the message of each commit, in the order of `git log
    --reverse`.  changes holds (path, old blob id or None, new blob id or None) for each path, in
    the order of `git diff --raw --no-renames`.  read(id, place) gives the bytes of a blob, and no
    byte for None.  It reads the ids of blob_reads(changes), in their order.  `--commits` and the
    API mode both build their records here, so both read the same three things.

    Three sources, each of which has published held content before: the commit messages, the
    PATHNAMES (a file named after a thing we hold back names it whether or not it is opened), and,
    per path, the lines of the new blob that are NOT already lines of the OLD BLOB OF THAT SAME
    PATH.  That subtraction is the ported check's -- re-stating a line this repository already
    publishes at that path publishes nothing new, and without it every regenerated table would be
    refused on content that is already out -- and it is done here, against the old blob of the
    same path, so no line can be excused by a line of some other file."""
    records, total = [], 0
    for number, message in enumerate(messages, 1):
        for line in message.split(b"\n"):
            records.append(("commit %d" % number, line))
            total += len(line)
    for number, (path, old, new) in enumerate(changes, 1):
        place = "path %d" % number
        records.append((place, path))
        total += len(path)
        if new is None:
            continue                            # deleted, or a submodule: no new text
        already = set(lines_of(read(old, place))[0])
        for line_number, line in enumerate(lines_of(read(new, place))[0], 1):
            if line in already:
                continue
            records.append(("%s line %d" % (place, line_number), line))
            total += len(line)
        if total > MAX_BYTES:
            die("this change introduces more than %d bytes of text; nothing was judged"
                % MAX_BYTES, cause=TOO_LARGE)
    return records


def blob_reads(changes):
    """The ids that records_of gives to read for changes, in its order, with no None: for each path
    with a new blob, its old blob when it has one, and then its new blob.  fetch_blobs and the API
    mode take the reads of records_of from here, and a test holds records_of to them."""
    return [oid for _path, old, new in changes if new is not None
            for oid in (old, new) if oid is not None]


def promisor_remote():
    """The remote that a partial clone fetches a missing object from: the remote that
    `extensions.partialClone` names, else `origin` when `remote.origin.promisor` is true, as
    `actions/checkout` with a `filter` sets it.  None in a full clone."""
    name = git("config", "--default", "", "--get", "extensions.partialClone").strip()
    if name:
        return name
    promisor = git("config", "--type=bool", "--default", "false", "--get", "remote.origin.promisor")
    return b"origin" if promisor.strip() == b"true" else None


def fetch_blobs(changes):
    """In a partial clone, fetch in ONE `git fetch` each blob of blob_reads(changes) that the clone
    does not have.

    The job checks out with `filter=blob:none`, so most blobs of the change are not in the clone.
    Without this fetch, `git cat-file --batch` fetches each missing blob with a `git fetch` of its
    own: two for each changed path, so a large pull request can run past the 10 minutes of the
    job.  This is the command that git runs for one missing object, with every id on its stdin.
    It asks for the missing blobs alone: a blob that only this clone has, as the planted commit of
    a demonstration has, is not on the remote, and the remote refuses the whole request for it.  A
    full clone makes no fetch.  A fetch that fails stops the check (exit 2)."""
    wanted = list(dict.fromkeys(blob_reads(changes)))
    remote = promisor_remote() if wanted else None
    if remote is None:
        return
    # With GIT_NO_LAZY_FETCH, this look-up of what the clone has fetches nothing itself.
    here = git("cat-file", "--batch-check", stdin=b"".join(oid + b"\n" for oid in wanted),
               env=dict(os.environ, GIT_NO_LAZY_FETCH="1"))
    missing = [line.split()[0] for line in here.splitlines() if line.endswith(b" missing")]
    if missing:
        git("-c", "fetch.negotiationAlgorithm=noop", "fetch", "--no-tags", "--no-write-fetch-head",
            "--recurse-submodules=no", "--filter=blob:none", "--stdin", remote,
            stdin=b"".join(oid + b"\n" for oid in missing))


def records_for_commits(base, head):
    """records_of for BASE..HEAD, read with git: `commit K` is the K-th commit of `git log
    --reverse BASE..HEAD`, and `path K` is the K-th path of `git diff --raw --no-renames BASE
    HEAD`."""
    parts = git("log", "--reverse", "--no-show-signature", "--format=%H%x00%B%x00",
                "%s..%s" % (base, head)).split(b"\0")
    messages = [parts[i + 1] for i in range(0, len(parts) - 1, 2) if parts[i].strip()]
    changes = changed_blobs(base, head)
    fetch_blobs(changes)
    blobs = Blobs()
    try:
        return records_of(messages, changes, blobs.read)
    finally:
        blobs.close()


def records_for_files(paths):
    """[(place, bytes)] for the files, each place by its name: `path FILE` and `FILE:N`."""
    records, total = [], 0
    for path in paths:
        try:
            with open(path, "rb") as handle:
                blob = handle.read()
        except OSError as exc:
            die("cannot read %s (%s)" % (path, exc))
        records.append(("path %s" % path, path.encode()))
        for number, line in enumerate(lines_of(blob)[0], 1):
            records.append(("%s:%d" % (path, number), line))
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
    """One hit per (record, detector) pair: (place, detector, matched bytes).

    A record is ONE LINE, so a detector only ever matches within a line: nothing here joins two.
    Every pattern in both tables is written to fit in one, and the canaries are single lines for
    the same reason -- a pattern that could straddle a line break would be a detector the
    self-test cannot vouch for."""
    hits = []
    for place, line in records:
        for detector in detectors:
            found = detector.rx.search(line)
            if found:
                hits.append((place, detector, found.group(0)))
    return hits


def report(hits, records, what, files):
    """Print the verdict on the records of `what`, and return the exit: 0 when nothing matched, 3
    when something did.  A hit names its place, and then its detector by Detector.hit.  The text
    that matched is printed only with `--files` (`files`), and there only when
    HELD_CONTENT_SHOW_MATCHES is set."""
    if not hits:
        print("HELD CONTENT: clean: %d line(s) and pathname(s) of %s matched no detector."
              % (len(records), what))
        return 0
    places = {place for place, _d, _t in hits}
    print("::error::HELD CONTENT: %d match(es) in %d place(s) of %s. This repository is public; "
          "the matching text is not copied into this log." % (len(hits), len(places), what))
    for place, detector, token in hits[:200]:
        print("  %s  %s%s" % (place, detector.hit, "  " + shown(detector, token) if files else ""))
    if len(hits) > 200:
        print("  ... and %d more" % (len(hits) - 200))
    if files:
        print("Run this check on your own machine with HELD_CONTENT_SHOW_MATCHES=1 to see the "
              "text, or ask a maintainer. Nothing here may be merged while it matches.")
    else:
        print("Find each place on your own machine. Commit K is the K-th commit of `git log "
              "--reverse BASE..HEAD`, and path K is the K-th line of `git diff --raw --no-renames "
              "BASE HEAD`, BASE being the merge base. Then --files with "
              "HELD_CONTENT_SHOW_MATCHES=1 shows the text, or ask a maintainer. Nothing here may "
              "be merged while it matches.")
    return 3


def checked_detectors(public_only):
    """The detectors of this run, after their self-test, whose numbers this prints."""
    public, private = load_detectors(public_only)
    detectors = public + private
    found, total = self_test(detectors)
    print("HELD CONTENT: self-test: %d of %d fresh canaries found; %d detectors "
          "(%d public in detectors.tsv, %s); "
          "%d must-pass control lines matched none of them"
          % (found, total, len(detectors), len(public),
             "the private table not read" if public_only
             else "%d from the pinned private table" % len(private),
             len([ln for ln in read_text(os.path.join(HERE, "must-pass-lines.txt")).split("\n")
                  if ln and not ln.startswith("#")])))
    return detectors


# ------------------------------------------------------------------------------------------------
# The API mode: the pull requests of one head, read from the GitHub API

OID = re.compile(r"[0-9a-f]{40}(?:[0-9a-f]{24})?")
REPOSITORY = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+")
NUMBER = re.compile(r"[1-9][0-9]*")
# Where the requests go when GITHUB_API_URL is not set, and the headers of each request but the
# token.  A raw blob read asks for the bytes of the blob, and each other read asks for JSON.
API_URL = "https://api.github.com"
API_VERSION = "2022-11-28"
JSON_TYPE = "application/vnd.github+json"
RAW_TYPE = "application/vnd.github.raw"
USER_AGENT = "held-content-scan"
# The most bytes that one read of the socket takes from an answer.
CHUNK = 1 << 20
# The messages of a read that stops the scan before its answer ends.  %s names the read.  LATE is
# for GitHub.stop_when_late.  STALLED is for READ, when a read of the socket got no byte in its
# time and stop_when_late did not stop the scan: %g is that time in seconds.
LATE = "a read of %s did not end in the time that the scan gave it"
STALLED = "a read of %s got no byte for %g seconds"
# An entry of a folder listing: `kind` is `blob` for a file and a symbolic link, `tree` for a folder
# and `commit` for a submodule, and `size` is 0 for an entry that is no blob.
Entry = collections.namedtuple("Entry", "mode kind id size")
# A commit of a comparison: its committer time in seconds, the ids of its parents, its message as
# bytes, and the id of its tree.
Commit = collections.namedtuple("Commit", "time parents message tree")


def part(answer, *keys, kind=str):
    """answer[key] for each of keys in turn, which must be a `kind`.  An answer of another shape
    stops the scan: a read that this check does not understand is a read that failed.  A message
    names the key, which is text of this file, and nothing of the answer."""
    for key in keys:
        if type(answer) is not dict or key not in answer:
            die("an answer of GitHub has no %r where this check reads it" % key, cause=READ)
        answer = answer[key]
    if type(answer) is not kind:
        die("an answer of GitHub has another kind of value than this check reads%s"
            % (" at %r" % keys[-1] if keys else ""), cause=READ)
    return answer


def object_id(answer, *keys):
    """part(), for the id of a commit, a tree or a blob.  The id goes into the next request."""
    found = part(answer, *keys)
    if not OID.fullmatch(found):
        die("an answer of GitHub has no object id at %r" % keys[-1], cause=READ)
    return found


def is_http_url(url):
    """Whether url is an http or https url with a host, and with a port of 0 to 65535 when it names
    a port.  The scan reads GitHub only at a GITHUB_API_URL of this kind."""
    try:
        parts = urllib.parse.urlsplit(url)
        parts.port      # a ValueError for a port that is not a number of 0 to 65535
    except ValueError:
        return False
    return parts.scheme in ("https", "http") and bool(parts.hostname)


class NoRedirect(urllib.request.HTTPRedirectHandler):
    """Follow no redirect.  urllib's own HTTPRedirectHandler follows a redirect to any host, and it
    sends the headers of the request there.  With this handler, a 3xx answer is an HTTPError, as
    each other answer that is not 2xx is."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


class GitHub:
    """The reads of one repository, each of them one GET of the GitHub API at GITHUB_API_URL, with
    the token of GH_TOKEN.  Python's HTTP client sends it, and not gh: gh changes each control
    character of a JSON answer to its caret pair (go-gh `pkg/api/http_client.go`,
    `newSanitizerRoundTripper`, and `pkg/asciisanitizer`, gh 2.98.0), and this client changes no
    byte.

    One at a time, and at least `gap` seconds after the one before.  `rate_limit` is read before
    the first read and after every FLOOR_EVERY reads, and the scan stops when the requests left
    are under the floor.  The clock of the scan ends at `end`, and THE CLOCK, in the docstring of
    this file, says how long a read waits.  A request that fails stops the scan.  Neither an answer
    nor a header goes to the log: an answer can name a path or a commit, a header holds the token,
    and this log is public."""

    def __init__(self, repo, clock=time.monotonic, sleep=time.sleep):
        self.repo, self.clock, self.sleep = repo, clock, sleep
        self.gap = float(os.environ.get("HELD_CONTENT_REQUEST_GAP", REQUEST_GAP))
        self.end = clock() + float(os.environ.get("HELD_CONTENT_TIME_LIMIT", TIME_LIMIT))
        self.last, self.reads = None, 0
        self.base = os.environ.get("GITHUB_API_URL", API_URL).rstrip("/")
        self.base_is_http = is_http_url(self.base)
        self.token = os.environ.get("GH_TOKEN", "")
        # No proxy: urllib's own ProxyHandler reads http_proxy and https_proxy, and it sends the
        # request through that proxy.
        self.opener = urllib.request.build_opener(NoRedirect, urllib.request.ProxyHandler({}))

    def stop_when_late(self, message, now=None):
        """Stop the scan with TIME and `message` when the clock is at or past `end`.  `now` is a
        time that the caller read from the clock.  When it is None, this method reads the clock.
        THE CLOCK, in the docstring of this file, says when the scan makes this check.  No other
        place of this class gives the cause TIME.  So a stop with TIME means that the clock is out,
        and each later read stops at once.  scan_pull_requests gives the verdict of such a stop to
        the pull requests that are left too."""
        if (self.clock() if now is None else now) >= self.end:
            die(message, cause=TIME)

    def call(self, what, endpoint, raw=False):
        """The bytes that GitHub answers to a GET of endpoint.  `what` names the read in a message.
        With raw, the answer is the bytes of a blob and not JSON."""
        now = self.clock()
        self.stop_when_late("the scan ran past its time before a read of %s" % what, now)
        if not self.token:
            die("GH_TOKEN is not set, so the scan cannot read %s" % what, cause=READ)
        if not self.base_is_http:
            die("GITHUB_API_URL is not an http or https url, so the scan cannot read %s" % what,
                cause=READ)
        url = "%s/%s" % (self.base, endpoint)
        request = urllib.request.Request(url, headers={
            "Accept": RAW_TYPE if raw else JSON_TYPE, "X-GitHub-Api-Version": API_VERSION,
            "User-Agent": USER_AGENT})
        # urllib copies no unredirected header to the request of a redirect, and NoRedirect makes
        # no such request.
        request.add_unredirected_header("Authorization", "Bearer " + self.token)
        if self.last is not None and now - self.last < self.gap:
            self.sleep(self.gap - (now - self.last))
        self.last = self.clock()
        self.stop_when_late("the scan ran past its time before a read of %s" % what, self.last)
        timeout = max(CALL_LEAST, min(CALL_MOST, self.end - self.last))
        try:
            with self.opener.open(request, timeout=timeout) as answer:
                return self.body(what, answer)
        except urllib.error.HTTPError as refusal:
            try:
                self.refused(what, refusal)
            finally:
                refusal.close()
        except http.client.IncompleteRead:
            die("the answer to a read of %s was cut short" % what, cause=READ)
        except TimeoutError:
            self.stalled(what, timeout)
        except urllib.error.URLError as failure:
            if isinstance(failure.reason, TimeoutError):
                self.stalled(what, timeout)
            die("a read of %s did not reach GitHub" % what, cause=READ)
        except (http.client.HTTPException, OSError, ValueError):
            # ValueError: http.client refuses a header or a URL that it cannot send
            die("a read of %s failed before its whole answer came" % what, cause=READ)

    def body(self, what, answer):
        """The bytes of answer.  Each read of the socket takes at most CHUNK bytes, and it waits as
        long as `call` lets it.  The scan stops when the clock passes `end` before the answer ends.
        An answer whose length is not its Content-Length stops the scan: an answer with fewer bytes,
        or a chunked answer with more bytes.  http.client reads a chunked answer without regard to
        its Content-Length."""
        pieces = io.BytesIO()
        while True:
            self.stop_when_late(LATE % what)
            piece = answer.read1(CHUNK)
            if not piece:
                break
            pieces.write(piece)
        data = pieces.getvalue()
        length = answer.headers.get("Content-Length")
        if length is not None and length.strip() != str(len(data)):
            die("the answer to a read of %s was cut short" % what, cause=READ)
        return data

    def stalled(self, what, timeout):
        """Stop the scan on a read of the socket that got no byte for `timeout` seconds.  When
        stop_when_late does not stop it, the cause is READ: a later read can still succeed."""
        self.stop_when_late(LATE % what)
        die(STALLED % (what, timeout), cause=READ)

    def refused(self, what, refusal):
        """Stop the scan on an answer that is not 2xx.  A 403 or 429 answer names a rate limit with
        the header `x-ratelimit-remaining: 0`, with a `retry-after` header, or with the words "rate
        limit" in its body, and it stops the scan at the floor.  The message names the HTTP status
        and nothing of the answer."""
        status, headers = refusal.code, refusal.headers
        if status in (403, 429):
            limited = headers.get("x-ratelimit-remaining") == "0" or "retry-after" in headers
            if not limited:
                try:
                    limited = b"rate limit" in self.body(what, refusal).lower()
                except TimeoutError:
                    # If stop_when_late does not stop the scan, this body names no rate limit.
                    self.stop_when_late(LATE % what)
                except (http.client.HTTPException, OSError):
                    pass        # a body that does not come names no rate limit
            if limited:
                die("GitHub answered a read of %s with HTTP %d and named a rate limit"
                    % (what, status), cause=FLOOR)
        die("a read of %s failed (HTTP %d). The answer is not printed, because it can name a path "
            "or a commit." % (what, status), cause=READ)

    def floor(self, cost=0):
        """Stop when the requests left this hour cannot pay for `cost` more reads above the floor.
        A read of `rate_limit` takes nothing from the count."""
        what = "the rate limit"
        core = part(self.json_of(what, self.call(what, "rate_limit")), "resources", "core",
                    kind=dict)
        left, limit = part(core, "remaining", kind=int), part(core, "limit", kind=int)
        if left - cost < min(FLOOR_MOST, limit // 5):
            die("the requests left this hour %s the floor that this scan leaves to the other "
                "workflows of the repository"
                % ("cannot pay for the reads of the files above" if cost else "are under"),
                cause=FLOOR)

    def read(self, what, endpoint, raw=False):
        if self.reads % FLOOR_EVERY == 0:
            self.floor()
        self.reads += 1
        return self.call(what, endpoint, raw)

    def json(self, what, endpoint):
        return self.json_of(what, self.read(what, endpoint))

    @staticmethod
    def json_of(what, answer):
        try:
            return json.loads(answer)
        except ValueError:
            die("the answer to a read of %s is not JSON" % what, cause=READ)


def committer_time(date):
    """A date of the API in seconds, which is how git compares the committer times of commits."""
    try:
        when = datetime.datetime.fromisoformat(date.replace("Z", "+00:00"))
    except ValueError:
        when = None
    if when is None or when.tzinfo is None:
        die("an answer of GitHub gives a commit a date that this check cannot read", cause=READ)
    return int(when.timestamp())


def commits_of(api, base_ref, head):
    """(the tree of the merge base, the tree of `head`, the message of each commit of `git log
    --reverse <merge base>..<head>` in its order) for a pull request into the branch base_ref.

    The first comparison, of the branch and `head`, gives the merge base and the count of commits.
    The branch can move during a scan, so every page of commits is then read from the comparison
    of the merge base and `head`, whose two ends are fixed.  A page that names another merge base
    or another count, and a number of commits that is not the count, stop the scan: a part of the
    commits is not the commits.

    GitHub documents the order of the commits in the answer as chronological, and no more.  So
    the order is computed here as git computes it.  Start at `head`.  Take next, each time, the
    commit with the newest committer time among those reached, and the one reached first when
    times are equal.  Then reach each of its parents that is a commit of the comparison, in the
    order of the parents, the first time it is seen.  `git log --reverse` lists the commits in
    the reverse of that order."""
    what = "the comparison"
    compare = "repos/%s/compare/%%s...%s?per_page=%d" % (api.repo, head, PER_PAGE)
    first = api.json(what, compare % urllib.parse.quote(base_ref, safe="/"))
    base = object_id(first, "merge_base_commit", "sha")
    total = part(first, "total_commits", kind=int)
    old_tree = object_id(first, "merge_base_commit", "commit", "tree", "sha")
    commits = {}
    for page in range(1, (total + PER_PAGE - 1) // PER_PAGE + 1):
        answer = api.json(what, compare % base + "&page=%d" % page)
        if (object_id(answer, "merge_base_commit", "sha"),
                part(answer, "total_commits", kind=int)) != (base, total):
            die("two reads of the comparison name another merge base or another count of commits",
                cause=INCOMPLETE)
        for commit in part(answer, "commits", kind=list):
            message = part(commit, "commit", "message")
            commits[object_id(commit, "sha")] = Commit(
                committer_time(part(commit, "commit", "committer", "date")),
                [object_id(parent, "sha") for parent in part(commit, "parents", kind=list)],
                message.encode("utf-8", "surrogatepass"),
                object_id(commit, "commit", "tree", "sha"))
    if len(commits) != total or (head in commits) != (total > 0) or (total == 0 and base != head):
        die("the comparison did not give the commits that its count names, up to the head",
            cause=INCOMPLETE)
    if not commits:
        return old_tree, old_tree, []
    order, reached, seen = [], [(-commits[head].time, 0, head)], {head}
    while reached:
        commit = heapq.heappop(reached)[2]
        order.append(commit)
        for parent in commits[commit].parents:
            if parent in commits and parent not in seen:
                seen.add(parent)
                heapq.heappush(reached, (-commits[parent].time, len(seen), parent))
    if len(order) != total:
        die("a commit of the comparison is not reached from the head", cause=INCOMPLETE)
    return old_tree, commits[head].tree, [commits[commit].message for commit in reversed(order)]


def tree_changes(api, old, new):
    """[(path, old entry or None, new entry or None)] for each path that differs between the trees
    old and new, in the order of `git diff --raw --no-renames`.  An entry is an Entry.  A folder
    listing that names one entry twice stops the scan: a git tree holds each name once, so such a
    listing is a broken answer, and the scan would not read one of the two entries.

    One folder is one read, never a recursive one: GitHub cuts a recursive listing short at
    100,000 entries or 7 MB, and it cuts the tree of this repository short.  A listing of one
    folder that GitHub cut short stops the scan.  The two sides of a folder are read only when
    its id differs, so the cost follows the size of the change and not the size of the tree.  A
    folder on one side alone is read too: each path that it adds or deletes is a record.

    The order is git's: the names of one folder compare as bytes, and a folder compares as its
    name with `/` after it.  So a file and a folder of one name are two entries.  A file that
    becomes a folder is its deletion, and then the additions under the folder."""
    listings = {None: {}}

    def folder(prefix, *sides):
        for tree in sides:
            if tree in listings:
                continue
            answer = api.json("a folder listing", "repos/%s/git/trees/%s" % (api.repo, tree))
            if part(answer, "truncated", kind=bool):
                die("GitHub cut a folder listing short", cause=LISTING)
            listings[tree] = entries = {}
            for entry in part(answer, "tree", kind=list):
                kind, name = part(entry, "type"), part(entry, "path")
                key = name.encode("utf-8", "surrogatepass") + (b"/" if kind == "tree" else b"")
                if key in entries:
                    die("a folder listing names one entry twice, so the scan would not read one "
                        "of the two", cause=READ)
                entries[key] = Entry(part(entry, "mode"), kind, object_id(entry, "sha"),
                                     part(entry, "size", kind=int) if kind == "blob" else 0)
        before, after = (listings[tree] for tree in sides)
        return prefix, before, after, iter(sorted(set(before) | set(after)))

    out, folders = [], [folder(b"", old, new)]
    while folders:
        prefix, before, after, names = folders[-1]
        for name in names:
            a, b = before.get(name), after.get(name)
            if a == b:
                continue
            if name.endswith(b"/"):
                folders.append(folder(prefix + name, a and a.id, b and b.id))
                break
            out.append((prefix + name, a, b))
        else:
            folders.pop()
    return out


def pull_request_records(api, base_ref, head):
    """(records, the count of commits, the count of paths) for a pull request into the branch
    base_ref whose head is `head`: records_of, over what commits_of and tree_changes read.

    Before the first blob is read, the scan stops when it cannot read them all: a blob over
    MAX_BLOB, or too few requests left for the blob reads.  The sizes are those of the folder
    listings, and a blob that comes back with another size stops the scan.  MAX_BYTES counts the
    text that the change introduces, in records_of, as in `--commits`.

    Each blob is read once.  It stays in memory only until the last read of its id, so the scan
    holds about the blobs of one path and not all the blobs of the change."""
    old_tree, new_tree, messages = commits_of(api, base_ref, head)
    changes, sizes = [], {}
    for path, *sides in tree_changes(api, old_tree, new_tree):
        # The entry of each side that is a blob.  None for no entry and for a submodule, whose id
        # names a commit of another repository, as in changed_blobs.
        old, new = (side if side and side.kind == "blob" else None for side in sides)
        sizes.update((side.id, side.size) for side in (old, new) if side)
        if new is None or (old is not None and old.id == new.id):
            # no new text: a deleted path, a submodule, or a change of mode alone
            changes.append((path, None, None))
        else:
            changes.append((path, old and old.id, new.id))
    left = collections.Counter(blob_reads(changes))     # the reads of each id that are to come
    if any(sizes[blob] > MAX_BLOB for blob in left):
        die("a file is over %d bytes, and the API gives no blob of that size" % MAX_BLOB,
            cause=TOO_LARGE)
    api.floor(len(left))
    kept = {}

    def read(blob, place):
        if blob is None:
            return b""
        data = kept.pop(blob, None)
        if data is None:
            data = api.read("a file", "repos/%s/git/blobs/%s" % (api.repo, blob), raw=True)
            if len(data) != sizes[blob]:
                die("a blob of %s did not come back with the size of its listing" % place,
                    cause=READ)
        left[blob] -= 1
        if left[blob]:
            kept[blob] = data           # a later path reads this id again
        return data

    return records_of(messages, changes, read), len(messages), len(changes)


def scan_pull_request(api, head, number, detectors):
    """(state, text for the description) for pull request `number`, or None when its head is no
    longer `head`.  The state is `success` or `failure`.  A stop is the caller's `error`."""
    pull = api.json("pull request %d" % number, "repos/%s/pulls/%d" % (api.repo, number))
    if object_id(pull, "head", "sha") != head:
        print("HELD CONTENT: pull request %d no longer has the head %s. It is not scanned."
              % (number, head))
        return None
    labels = [part(label, "name") for label in part(pull, "labels", kind=list)]
    records, commits, paths = pull_request_records(api, part(pull, "base", "ref"), head)
    # Only now, after every read succeeded: a demonstration that could not read the pull request
    # shows nothing about the reads.
    planted = fresh_canaries(detectors) if LABEL in labels else []
    records += [("planted sample %d" % k, text) for k, (_d, text) in enumerate(planted, 1)]
    hits = scan(records, detectors)
    report(hits, records, "pull request %d at head %s" % (number, head), files=False)
    if planted:
        found = {(place, detector) for place, detector, _token in hits}
        if any(("planted sample %d" % k, detector) not in found
               for k, (detector, _text) in enumerate(planted, 1)):
            die("pull request %d has the label %s, and a detector did not find its own planted "
                "sample" % (number, LABEL), cause=PLANTED)
        print("HELD CONTENT: pull request %d has the label %s. Each of the %d detectors found its "
              "own planted sample, so this verdict is a failure on purpose."
              % (number, LABEL, len(planted)))
    if hits:
        places = dict.fromkeys(place for place, _detector, _token in hits)
        return "failure", "pull request %d: %s" % (number, ", ".join(places))
    return "success", "pull request %d: %d commit(s), %d path(s)" % (number, commits, paths)


def scan_pull_requests(repo, head, numbers, verdict, public_only):
    """Scan each pull request of numbers whose head is `head`, and write the one verdict on that
    head to the file `verdict`: `failure` when a pull request failed, else `error` when one could
    not be judged, else `success`.  Return 0, the exit of a run that wrote its verdict."""
    api = GitHub(repo)                      # the clock of the scan starts here
    try:
        detectors = checked_detectors(public_only)
    except Stop as stop:
        sys.stderr.write("::error::HELD CONTENT: %s\n" % stop.message)
        return write_verdict(verdict, head, "error", stop.cause or SELF_TEST, numbers)
    results, about, left = [], [], list(numbers)
    while left:
        number = left.pop(0)
        try:
            result = scan_pull_request(api, head, number, detectors)
        except Stop as stop:
            sys.stderr.write("::error::HELD CONTENT: pull request %d could not be judged: %s\n"
                             % (number, stop.message))
            result = ("error", stop.cause or READ)
            if stop.cause in (FLOOR, TIME):
                # After FLOOR the scan sends no more requests, and after TIME each later read
                # stops at once, because the clock is out.  So this verdict is about the other
                # numbers too.
                about, left = about + left, []
        if result is not None:
            results.append(result)
            about.append(number)
    failed = [text for state, text in results if state == "failure"]
    errors = [text for state, text in results if state == "error"]
    if failed:
        return write_verdict(verdict, head, "failure", "held content: " + "; ".join(failed), about)
    if errors:
        return write_verdict(verdict, head, "error", errors[0], about)
    if results:
        return write_verdict(verdict, head, "success", "no pattern matched: "
                             + "; ".join(text for _state, text in results), about)
    # `pull_requests` is empty, so the workflow posts nothing for this verdict
    return write_verdict(verdict, head, "success",
                         "no pull request has this head now, so nothing was scanned", about)


def write_verdict(path, head, state, description, numbers):
    if len(description) > DESCRIPTION_MOST:
        description = description[:DESCRIPTION_MOST - 3] + "..."
    with open(path, "w") as handle:
        json.dump({"state": state, "description": description, "pull_requests": numbers}, handle)
    print("HELD CONTENT: the verdict on head %s is %s: %s" % (head, state, description))
    return 0


def main(argv):
    # `--public-only` can stand anywhere among the arguments. The first other argument is the mode.
    public_only = "--public-only" in argv
    argv = [arg for arg in argv if arg != "--public-only"]
    if not argv:
        die("no mode given. Use --commits BASE HEAD, --files FILE..., --self-test, or "
            "--pull-request REPO HEAD NUMBER... --verdict FILE, each with or without --public-only")
    mode, args = argv[0], argv[1:]
    if mode not in ("--self-test", "--commits", "--files", "--pull-request"):
        die("unknown mode %r" % mode)
    if mode == "--self-test" and args:
        die("--self-test takes no other argument; it scans nothing")
    if mode == "--commits" and len(args) != 2:
        die("--commits takes exactly BASE and HEAD")
    if mode == "--files" and not args:
        die("--files takes at least one file")
    if mode == "--pull-request" and not (
            len(args) >= 5 and args[-2] == "--verdict" and REPOSITORY.fullmatch(args[0])
            and OID.fullmatch(args[1]) and all(NUMBER.fullmatch(n) for n in args[2:-2])):
        die("--pull-request takes REPO (owner/name), HEAD (a whole commit id), one NUMBER or "
            "more, and then --verdict FILE")
    if public_only:
        print("HELD CONTENT: this run covers the patterns of detectors.tsv only (--public-only). "
              "The private table runs in .github/workflows/held-content-private.yml.")

    if mode == "--pull-request":
        numbers = list(dict.fromkeys(int(n) for n in args[2:-2]))
        return scan_pull_requests(args[0], args[1], numbers, args[-1], public_only)
    detectors = checked_detectors(public_only)

    if mode == "--self-test":
        print("HELD CONTENT: nothing was scanned (--self-test).")
        return 0
    if mode == "--commits":
        records = records_for_commits(args[0], args[1])
        head = git("rev-parse", "--verify", args[1] + "^{commit}").decode("ascii").strip()
        what = "the commits up to head %s" % head
    else:
        records = records_for_files(args)
        what = "%d file(s)" % len(args)
    return report(scan(records, detectors), records, what, files=mode == "--files")


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except Stop as stop:
        sys.stderr.write("::error::HELD CONTENT: %s\n" % stop.message)
        sys.stderr.write("The check could not finish, so nothing is passed (exit %d). %s\n"
                         % (stop.status, SELF))
        sys.exit(stop.status)
    except Exception as exc:                                              # noqa: BLE001
        # Exit 2 means "could not finish", and it has to mean that for EVERY way of not
        # finishing. Without this, a missing `git` binary left Python's own exit 1 behind, which
        # is the status a content refusal would use in a sibling check -- a reader cannot tell
        # "it refused" from "it fell over" on a status alone.
        # The frames of the traceback go to the log, and the message of the exception does not: a
        # message can hold a path of the change, and this log is public.
        import traceback
        traceback.print_tb(exc.__traceback__)
        sys.stderr.write("::error::HELD CONTENT: the check hit an error it does not handle (%s). "
                         "Its message is not printed, because it can hold a path. Nothing was "
                         "passed (exit 2). %s\n" % (type(exc).__name__, SELF))
        sys.exit(2)
