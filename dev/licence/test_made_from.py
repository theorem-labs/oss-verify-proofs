#!/usr/bin/env python3
"""Tests of dev/licence/made_from.py, the one generator of every unit's made-from record.

Run: python3 -B -m unittest discover -s dev/licence -t dev/licence -v   (from the top of the checkout)

Every case builds a scratch checkout under tempfile.mkdtemp(), with the repository's layout: dev/licence/made_from.py
copied from the file beside this one (so an edit of it is what runs), tools/oft/rocq.py copied from the repository,
one unit with a unit file of the shape the generator accepts, images/dune, first-added.tsv and the .v files the case
needs.  The Fixture cases start from one file with Anthropic's lines, one copied from it with none (`made from`),
one with Anthropic's tag alone (its tag becomes MIT) and two written here, and a record made as each real record
was, by one run with --apply.  No case reads a real unit's record or proofs (the made-from job of pr.yml runs each
unit's --check); one case checks each unit file the checkout holds with --unit-file, and one reads the strip step of
.github/workflows/pr.yml, when the checkout holds it.  Each case that runs the command line holds its exit code to 0,
1, 2, 3, 4 or 5, the codes of the generator's docstring.  Only --check exits 3 (drift): when the record names no path
twice, every row that differs is one a run gives again, and no such row names a path that the record holds in a row a
run does not give again (the cases of Drift and CheckC2).  5 (DEFECT) is a defect of the generator's own code.
"""
import ast
import contextlib
import glob
import importlib.util
import io
import os
import random
import re
import runpy
import shutil
import signal
import subprocess
import sys
import sysconfig
import tempfile
import textwrap
import threading
import time
import unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))   # the checkout this file is in: it lives in dev/licence
SCRIPT = os.path.join(HERE, "made_from.py")
_spec = importlib.util.spec_from_file_location("licence_made_from", SCRIPT)
mf = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(mf)
mf.load_lexer(REPO)   # for the cases that call licence_comments, own_lines and unclosed directly

EXITS = {0, 1, 2, 3, 4, 5}   # the exit codes of the generator's docstring; only --check exits 3 (drift), 5 a defect
# the line --check prints after the rows that differ when the difference is drift (exit 3), and only then
DRIFT_SAYS = ("made_from.py --check: every row that differs is one a run gives again, for a file that the record "
              "holds in no row of another kind: `made_from.py --record` brings the record up to date")
# seconds a command of a forged generator may take, the two runs of its --check among them (Tree.cli): a run on a test
# tree ends in under 1 s, and the walk that the fault case forges would, without its guard, never end, growing a list
# by some 37 MiB/s a run, so that 10 s holds the two runs of a forged --check to about 750 MiB
FORGED = 10
ANTHROPIC = ["(* Copyright 2026 Anthropic PBC *)", "(* SPDX-License-Identifier: Apache-2.0 OR MIT *)"]
UNIT = ("demo", "fuzz_demo")
HISTORY = "history-named.tsv"
# A `Modified by` comment of several lines, as 86 of Anthropic's sources in curl/fuzz_fnmatch carry
MULTI = ["(* Modified by Theorem Labs, 2026-10: new file, written for this test; it goes on over three lines,",
         "   as such comments do in this repository,",
         "   so the comment ends only here. *)"]
OWN = "(* Modified by Theorem Labs, 2026-10: a line of the file's own, closed on its line. *)"


def code(word, n):
    """n distinctive lines of code, each its own after made_from.py's masks (no digits in them)."""
    return ["Lemma %s_%s : forall x y : nat, x + y = y + x." % (word, chr(97 + i // 26) + chr(97 + i % 26))
            for i in range(n)]


def docstring(unit):
    return ('"""made_from.py of %s/%s: this unit\'s data for the rule of dev/licence/made_from.py, which decides '
            "which\nof the unit's proof files were made from a file that carries Anthropic's licence lines and the "
            'lines each takes."""\n' % unit)


def unit_file_text(unit=UNIT, donors=(), history=HISTORY):
    """A unit file of the shape the generator accepts."""
    return ("#!/usr/bin/env python3\n" + docstring(unit) + "# the fuzz targets this unit's history copied from\n"
            + "DONORS = %r\n" % (tuple(donors),) + "HISTORY = %r\n\n" % history + mf.FIXED_BLOCK)


def first_lines_only(text):
    """The licence lines as fuzz_bufq's earlier copy took them, one line at a time, whatever a line's comment does:
    what left twenty files of curl/fuzz_bufq with an unclosed comment."""
    lines, j = text.split("\n"), 0
    while j < min(len(lines), mf.HEADER_LINES) and mf.LICENCE.match(lines[j]):
        j += 1
    return lines[:j], "\n".join(lines[j:])


@contextlib.contextmanager
def sigterm_interrupts():
    """While the block runs, a SIGTERM of this process raises KeyboardInterrupt in it, so that the clauses around it
    run (Tree.cli's kill of its command's group) and unittest then stops (a SystemExit it would record as an error,
    and go on); when the block ends, however it ends, the handler before it is back.  Only the main thread can set a
    handler (signal.signal raises in another), so in another thread the block runs with none."""
    if threading.current_thread() is not threading.main_thread():
        yield
        return

    def interrupt(_signum, _frame):
        raise KeyboardInterrupt("SIGTERM")

    before = signal.signal(signal.SIGTERM, interrupt)
    try:
        yield
    finally:
        signal.signal(signal.SIGTERM, before)


class Tree(unittest.TestCase):
    """A scratch checkout: dev/licence/made_from.py (the file under test), tools/oft/rocq.py, and one unit."""
    unit, donors, history = UNIT, (), HISTORY

    def setUp(self):
        self.top = tempfile.mkdtemp(prefix="made_from-test-")
        self.addCleanup(shutil.rmtree, self.top)
        for rel, src in (("dev/licence/made_from.py", SCRIPT),) + tuple((r, os.path.join(REPO, r)) for r in mf.READS):
            os.makedirs(os.path.join(self.top, os.path.dirname(rel)), exist_ok=True)
            shutil.copy(src, os.path.join(self.top, rel))
        self.root = "projects/%s/%s/proofs" % self.unit
        self.licence = self.root + "/provenance/evidence/licence"
        self.unit_file = os.path.join(self.top, self.licence, "made_from.py")
        self.layout = mf.Layout(self.unit_file, self.donors, self.history)
        self.put(self.layout.images_dune, "(rule (targets Img.v) (action (run true)))\n")
        self.put_unit_file(unit_file_text(self.unit, self.donors, self.history))
        if self.history:
            self.put(self.layout.history, "path\tsource\n")
        self.record = os.path.join(self.top, self.layout.record)

    def put(self, rel, text):
        path = os.path.join(self.top, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8", newline="") as f:
            f.write(text)

    def put_unit_file(self, text):
        self.put(os.path.relpath(self.unit_file, self.top), text)

    def write(self, rel, lines):
        self.put(os.path.join(self.root, rel), "\n".join(lines) + "\n")

    def read(self, rel):
        with open(os.path.join(self.top, self.root, rel), encoding="utf-8", newline="") as f:
            return f.read()

    def born(self, **times):
        """first-added.tsv: lib/<stem>.v first came at each time."""
        self.put(self.layout.first_added, "path\tfirst_added_commit_time\n" + "".join(
            "lib/%s.v\t%d\n" % (n, t) for n, t in sorted(times.items())))

    def history_args(self):
        return ["--history", os.path.join(self.top, self.layout.history)] if self.history else []

    def cli(self, *args, script=None, cwd=None, env=None, timeout=None):
        """(exit code, stdout + stderr) of the unit file (or script) run with args; the code is one the docstring
        names.  Untimed (timeout None), the command stays in this process's group, so an outer `timeout`, which
        signals its own group, stops it with this process.  Timed, it runs in a session of its own, so that its whole
        process group, the two runs a --check starts among them, can be killed: past timeout seconds (the case fails),
        and when another stop comes while it waits (test_random_units' alarm, or a SIGTERM of this process, which that
        group does not get and which sigterm_interrupts makes a KeyboardInterrupt).  An untimed command that an
        exception stops is killed alone."""
        cmd = [sys.executable, script or self.unit_file] + list(args)
        timed = timeout is not None
        p = subprocess.Popen(cmd, cwd=cwd or self.top, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             text=True, start_new_session=timed)
        try:
            with sigterm_interrupts() if timed else contextlib.nullcontext():
                stdout, stderr = p.communicate(timeout=timeout)
        except BaseException as e:   # the timeout, or another stop (the alarm, a SIGTERM): leave no process running
            if timed:
                # the command's whole group: it is its own session's, so no signal to this process's group reached it
                with contextlib.suppress(ProcessLookupError):
                    os.killpg(p.pid, signal.SIGKILL)
            else:
                # the command alone: its group is this process's own, which a kill of the group would kill as well
                p.kill()
            p.communicate()
            if isinstance(e, subprocess.TimeoutExpired):
                self.fail("%s did not end within %s s: its process group was killed" % (" ".join(cmd), timeout))
            raise
        self.assertIn(p.returncode, EXITS, stdout + stderr)
        return p.returncode, stdout + stderr

    def run_plain(self, *extra, out="out.tsv", env=None, timeout=None):
        """A plain run on the tree, OUT at the top of the scratch checkout."""
        return self.cli("--top", self.top, os.path.join(self.top, out), *(self.history_args() + list(extra)),
                        env=env, timeout=timeout)

    def refresh(self, *extra):
        return self.cli(self.layout.record, "--record", *(self.history_args() + list(extra)))

    def check(self, *extra, timeout=None):
        """(exit code, stdout + stderr) of `made_from.py --check` run from outside the tree, with no --top."""
        return self.cli("--check", *extra, cwd=tempfile.gettempdir(), timeout=timeout)

    def assert_check(self, rc, signed):
        """--check exits rc and prints, for the rows that differ, exactly the `-` and `+` lines of signed, in order;
        with rc 3 it then prints the line of drift, and with no other code that line.  Returns its output."""
        got, out = self.check()
        self.assertEqual(got, rc, out)
        lines = out.split("\n")
        at = [i for i, x in enumerate(lines) if x.startswith(("- ", "+ "))]
        self.assertEqual([lines[i] for i in at], signed, out)
        if signed:
            self.assertIn("is not what this generator gives on this tree; the rows that differ", out)
        if rc == 3:
            self.assertEqual(lines[at[-1] + 1], DRIFT_SAYS, out)   # the rows as for exit 1, then the line of drift
        else:
            self.assertNotIn(DRIFT_SAYS, out)
        return out

    def call(self, *args):
        """main() of the generator under test, in this process (so a case may patch it): (exit code, output)."""
        out = io.StringIO()
        with mock.patch.object(sys, "argv", [self.unit_file] + list(args)), contextlib.redirect_stdout(out), \
                contextlib.redirect_stderr(out):
            try:
                mf.main(self.unit_file)
                status = 0
            except SystemExit as e:
                status = e.code
        rc = 0 if status is None else status if isinstance(status, int) else 1
        self.assertIn(rc, EXITS, out.getvalue())
        return rc, out.getvalue() + (status if isinstance(status, str) else "")

    def apply(self, *extra, out="out.tsv"):
        """A run with --apply in this process: (exit code, output)."""
        return self.call("--top", self.top, os.path.join(self.top, out), "--apply", *(self.history_args()
                                                                                       + list(extra)))

    def rows(self, path=None):
        return [r.split("\t") for r in mf.rows_of(path or self.record)[1:]]

    def decisions(self, path=None):
        return {r[0]: r[6] for r in self.rows(path)}

    def snapshot(self):
        """Every file of the scratch checkout, as bytes, but Python's bytecode cache (__pycache__), which the fixed
        block's import of the generator may write before the generator reads anything."""
        out = {}
        for d, dirs, names in os.walk(self.top):
            dirs[:] = [x for x in dirs if x != "__pycache__"]
            for n in names:
                with open(os.path.join(d, n), "rb") as f:
                    out[os.path.join(d, n)] = f.read()
        return out

    def assert_a_second_apply_changes_nothing(self):
        """A second --apply, OUT again.tsv, writes no file but again.tsv, and that holds the header alone."""
        before = self.snapshot()
        rc, out = self.apply(out="again.tsv")
        self.assertEqual(rc, 0, out)
        after = self.snapshot()
        self.assertEqual(after.pop(os.path.join(self.top, "again.tsv")), mf.HEADER.encode() + b"\n")
        self.assertEqual(before, after)


class Fixture(Tree):
    def setUp(self):
        super().setUp()
        self.write("lib/Src.v", ANTHROPIC + code("src", 40))
        self.write("lib/Copy.v", code("src", 40))                     # made from lib/Src.v
        self.write("lib/Tag.v", ANTHROPIC[1:] + code("tag", 10))      # written here: its tag becomes MIT
        self.write("lib/Own.v", code("own", 10))                      # written here
        self.write("lib/Mine.v", code("mine", 10))                    # written here
        self.born(Copy=2, Mine=2, Own=2, Src=1, Tag=2)
        rc, out = self.cli(self.layout.record, "--apply", *self.history_args())
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.decisions(), {"lib/Copy.v": "made from (block)",
                                            "lib/Tag.v": "written here (Apache-2.0 OR MIT tag becomes MIT)",
                                            "lib/Own.v": "written here", "lib/Mine.v": "written here"})

    def edit_record(self, change):
        rows = mf.rows_of(self.record)
        with open(self.record, "w", encoding="utf-8") as f:
            f.write("".join(r + "\n" for r in change(rows)))

    def row(self, path):
        return next(r for r in mf.rows_of(self.record) if r.startswith(path + "\t"))

    def record_with(self, row):
        """The record with row among its rows, in path order, where --record would put it."""
        self.edit_record(lambda rows: rows[:1] + sorted(rows[1:] + [row], key=lambda r: r.split("\t")[0]))

    def record_bytes(self):
        with open(self.record, "rb") as f:
            return f.read()


# OuterTimeout's command: it writes its pid to the file argv[1] names (whole, by a rename), then sleeps
SLEEPER = """import os, sys, time
with open(sys.argv[1] + ".new", "w") as f:
    f.write(str(os.getpid()))
os.rename(sys.argv[1] + ".new", sys.argv[1])
time.sleep(60)
"""
# OuterTimeout's command of two processes, as a --check is three: it starts a child that sleeps, in its own process
# group and with pipes of its own, as generate() starts a --check's runs, writes its pid and the child's, then sleeps
SLEEPER_AND_CHILD = """import os, subprocess, sys, time
child = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"], stdout=subprocess.DEVNULL,
                         stderr=subprocess.DEVNULL)
with open(sys.argv[1] + ".new", "w") as f:
    f.write("%d %d" % (os.getpid(), child.pid))
os.rename(sys.argv[1] + ".new", sys.argv[1])
time.sleep(60)
"""
# OuterTimeout's test run: one Tree case whose cli runs that command (argv: the directory of this file, the pid file,
# the command, and cli's timeout, "" for none)
SLEEPS = """import sys, unittest
sys.path.insert(0, sys.argv[1])
import test_made_from as t


class Sleeps(t.Tree):
    def test_sleeps(self):
        self.cli(sys.argv[2], script=sys.argv[3], timeout=float(sys.argv[4]) if sys.argv[4] else None)


unittest.main(argv=["sleeps"])
"""


def running(pid):
    """Whether the process pid is there and has not ended: a zombie (a process that ended, which its parent, or init,
    has not reaped yet) has ended."""
    try:
        os.kill(pid, 0)
        with open("/proc/%d/stat" % pid) as f:
            return f.read().rpartition(")")[2].split()[0] != "Z"
    except (ProcessLookupError, FileNotFoundError):
        return False


@unittest.skipUnless(os.path.isfile("/proc/self/stat"), "it reads the state of a process in /proc")
class OuterTimeout(unittest.TestCase):
    """A command that Tree.cli starts does not outlive a SIGTERM of the test run's process group, which is how GNU
    timeout stops what it runs (the tests step of pr.yml's made-from job: timeout 900 python3 -B -m unittest ...):
    a test run in a group of its own, as timeout runs it, whose Tree case runs a command that sleeps, untimed and with
    a timeout of 50 s."""

    def test_a_command_does_not_outlive_a_sigterm_of_the_test_runs_group(self):
        for timeout in (None, 50):
            # sigterm_interrupts: a SIGTERM of this test, too, leaves nothing of it running
            with self.subTest(timeout=timeout), sigterm_interrupts():
                self.sigterm_of_the_group(timeout)

    def test_a_command_s_children_do_not_outlive_a_sigterm_of_the_test_runs_group(self):
        # a --check's two runs are children of its process: a kill of the command alone would leave them running
        for timeout in (None, 50):
            with self.subTest(timeout=timeout), sigterm_interrupts():
                self.sigterm_of_the_group(timeout, SLEEPER_AND_CHILD)

    def sigterm_of_the_group(self, timeout, command=SLEEPER):
        scratch = tempfile.mkdtemp(prefix="made_from-sigterm-")
        self.addCleanup(shutil.rmtree, scratch)
        pid_file, sleeper, said = (os.path.join(scratch, n) for n in ("pid", "sleeper.py", "said.txt"))
        with open(sleeper, "w") as f:
            f.write(command)
        # in a session of its own, as GNU timeout runs what it runs in a group of its own; its TMPDIR is scratch, where
        # the checkout of its Tree stays when the SIGTERM stops it before its cleanup
        with open(said, "w") as out:
            child = subprocess.Popen([sys.executable, "-B", "-c", SLEEPS, HERE, pid_file, sleeper,
                                      "" if timeout is None else str(timeout)],
                                     stdout=out, stderr=subprocess.STDOUT, start_new_session=True,
                                     env=dict(os.environ, TMPDIR=scratch))

        def output():
            with open(said, encoding="utf-8", errors="replace") as f:
                return f.read()

        pids, gone = [], False
        try:
            end = time.monotonic() + 10
            while not os.path.exists(pid_file):
                if child.poll() is not None or time.monotonic() > end:
                    self.fail("the test run started no command within 10 s:\n" + output())
                time.sleep(0.02)
            with open(pid_file) as f:
                pids = [int(x) for x in f.read().split()]
            os.killpg(child.pid, signal.SIGTERM)   # what GNU timeout does at its limit
            try:
                child.wait(10)
            except subprocess.TimeoutExpired:
                self.fail("the test run did not end within 10 s of the SIGTERM:\n" + output())
            end = time.monotonic() + 3
            while any(map(running, pids)) and time.monotonic() < end:
                time.sleep(0.02)
            left = [pid for pid in pids if running(pid)]
            if left:
                self.fail("of its command's processes %s, %s outlive a SIGTERM of the test run's group by 3 s; the "
                          "test run said:\n%s" % (pids, left, output()))
            gone = True
        finally:
            if not gone:   # leave nothing running: the test run's group while it runs, and the command by its pid
                if child.poll() is None:
                    with contextlib.suppress(ProcessLookupError):
                        os.killpg(child.pid, signal.SIGKILL)
                    child.wait()
                for pid in pids:
                    if running(pid):
                        os.kill(pid, signal.SIGKILL)


class Mask(unittest.TestCase):
    def test_mask_reads_ossverify_module_paths(self):
        # since the namespace rename, a module path is spelled OSSVerify. as well as OssFuzzTheorems.
        for old, new in (("From OssFuzzTheorems.Proofs.curl.fuzz_bufq.lib.U Require Import Agree.",
                          "From OSSVerify.Proofs.curl.fuzz_bufq.lib.U Require Import Agree."),
                         ("Require Import OssFuzzTheorems.curl.fuzz_bufq.images.Plain.",
                          "Require Import OSSVerify.curl.fuzz_bufq.images.Plain.")):
            with self.subTest(new=new):
                self.assertEqual(mf.masked(new, set()), mf.masked(old, set()))
                self.assertNotIn("OSSVerify", mf.masked(new, set()))

    def test_mask_is_no_wider(self):
        # a module path of two parts (OSSVerify.curl.fuzz_bufq) is not masked: that wider mask is not measured
        self.assertEqual(mf.MODULE.pattern,
                         r"(?:OssFuzzTheorems|OSSVerify)\.(?:Proofs\.\w+\.\w+\.lib(?:\.\w+)*|\w+\.\w+\.images)")
        self.assertIn("OSSVerify.curl.fuzz_bufq Require", mf.masked("From OSSVerify.curl.fuzz_bufq Require X.", set()))


class LicenceLines(unittest.TestCase):
    def test_licence_lines_stops_at_a_comment_that_does_not_close(self):
        text = "\n".join([OWN] + MULTI + code("x", 2))
        lic, rest = mf.licence_lines(text)
        self.assertEqual(lic, [OWN])
        self.assertTrue(rest.startswith(MULTI[0]))

    def test_tagged_with_the_bundle_tag(self):
        self.assertTrue(mf.tagged("\n".join([mf.BUNDLE_TAG] + code("x", 2))))
        self.assertTrue(mf.tagged("\n".join([mf.APACHE_TAG, OWN] + code("x", 2))))
        self.assertFalse(mf.tagged("\n".join(ANTHROPIC + code("x", 2))))
        self.assertFalse(mf.tagged("\n".join([mf.MIT_TAG] + code("x", 2))))

    def test_modified_only(self):
        self.assertTrue(mf.modified_only("\n".join([OWN, OWN] + code("x", 2))))
        self.assertFalse(mf.modified_only("\n".join(code("x", 2))))
        self.assertFalse(mf.modified_only("\n".join([mf.APACHE_TAG, OWN] + code("x", 2))))
        self.assertFalse(mf.modified_only("\n".join([ANTHROPIC[0], OWN] + code("x", 2))))

    def test_own_lines_are_whole_comments(self):
        # a RelimCut.v-shaped file: one closed `Modified by` line, then one over three lines
        text = "\n".join([OWN] + MULTI + code("x", 2))
        self.assertTrue(mf.modified_only(text))
        self.assertEqual(mf.own_lines(text), [OWN, "\n".join(MULTI)])
        self.assertEqual(mf.own_lines("\n".join([mf.APACHE_TAG] + MULTI + code("x", 2))), ["\n".join(MULTI)])
        self.assertEqual(mf.own_lines("\n".join(code("x", 2))), [])

    def test_lint_lexer_reads_strings_and_nesting(self):
        # the comment rule is oft lint's: a string literal inside a comment is read as one, so its `*)` closes
        # nothing, and comments nest
        head = '(* Modified by X: a string "*)" and a (* nested *) comment\n   go on to here. *)\nLemma a : True.'
        lic, rest = mf.licence_comments(head)
        self.assertEqual(lic, [head.split("\nLemma")[0]])
        self.assertEqual(rest, "Lemma a : True.")
        self.assertIsNone(mf.unclosed(head))
        self.assertEqual(mf.unclosed('(* a "*)" *'), "comment")
        self.assertEqual(mf.unclosed('(* a (* b *)'), "comment")
        self.assertIsNone(mf.unclosed('Definition s := "a ""quoted"" word".'))
        two = ("(* Copyright 2026 Anthropic PBC *) (* SPDX-License-Identifier: Apache-2.0 OR MIT *)\n"
               "(* Modified by X *)\nA.")
        self.assertEqual(mf.licence_comments(two), (two.split("\n")[:2], "A."))
        self.assertEqual(mf.unclosed('Definition s := "open "".'), "string literal")


class Writes(Tree):
    """What a run writes: whole comments, in R4's order, the code of no file changed, every refusal before a write."""

    def setUp(self):
        super().setUp()
        self.files = {"Src": ANTHROPIC + code("src", 40), "Copy": code("src", 40)}

    def tree(self):
        for stem, lines in self.files.items():
            self.write("lib/%s.v" % stem, lines)
        self.born(**{stem: 1 if stem == "Src" else 2 for stem in self.files})

    def assert_refused_before_any_write(self, rc, out, says):
        self.assertEqual(rc, 1, out)
        self.assertIn(says, out)
        self.assertFalse(os.path.exists(os.path.join(self.top, "out.tsv")), "OUT written before the refusal")
        for stem, lines in self.files.items():
            self.assertEqual(self.read("lib/%s.v" % stem), "\n".join(lines) + "\n", stem)

    def test_apply_copies_a_multi_line_source_comment_whole(self):
        self.files["Src"] = ANTHROPIC + MULTI + code("src", 40)
        self.tree()
        rc, out = self.apply()
        self.assertEqual(rc, 0, out)
        copy = self.read("lib/Copy.v").split("\n")
        src = ANTHROPIC + MULTI
        self.assertEqual(copy[:len(src)], src)
        self.assertRegex(copy[len(src)], r"^\(\* Modified by Theorem Labs, 2026-11: (made|copied) from "
                                         r"proofs/demo/fuzz_demo/lib/Src\.v\b.* \*\)$")
        self.assertEqual(copy[len(src) + 1:], code("src", 40) + [""])
        self.assertIsNone(mf.unclosed("\n".join(copy)))

    def test_own_comments_written_whole_in_r4_order(self):
        # a RelimCut.v-shaped file: one closed `Modified by` line, then one over three lines.  Written: the source's
        # whole leading licence comments, then the file's own `Modified by` lines, then one new line, then its code
        self.files["Src"] = ANTHROPIC + MULTI + code("src", 40)
        mine = ["(* Modified by Theorem Labs, 2026-10: the file's own change, in other words than the source's;",
                "   it goes on over three lines too,",
                "   and closes only on this one. *)"]
        self.files["Copy"] = [OWN] + mine + code("src", 40)
        self.tree()
        rc, out = self.apply()
        self.assertEqual(rc, 0, out)
        copy = self.read("lib/Copy.v").split("\n")
        head = ANTHROPIC + MULTI + [OWN] + mine
        self.assertEqual(copy[:len(head)], head)
        self.assertTrue(copy[len(head)].startswith("(* Modified by Theorem Labs, 2026-11: "), copy[len(head)])
        self.assertEqual(copy[len(head) + 1:], code("src", 40) + [""])
        self.assertEqual(self.decisions(os.path.join(self.top, "out.tsv"))["lib/Copy.v"], "made from (block)")

    def test_modified_only_file_is_decided_and_keeps_its_lines(self):
        self.files["Copy"] = [OWN] + code("src", 40)
        self.tree()
        rc, out = self.apply()
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.decisions(os.path.join(self.top, "out.tsv")), {"lib/Copy.v": "made from (block)"})
        copy = self.read("lib/Copy.v").split("\n")
        self.assertEqual(copy[:3], ANTHROPIC + [OWN])
        self.assertTrue(copy[3].startswith("(* Modified by Theorem Labs, 2026-11: "))

    def test_tagged_file_with_the_bundle_tag_is_decided(self):
        self.files["Tag"] = [mf.BUNDLE_TAG, OWN] + code("tag", 10)
        self.tree()
        rc, out = self.apply()
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.decisions(os.path.join(self.top, "out.tsv"))["lib/Tag.v"],
                         "written here (Apache-2.0 OR MIT tag becomes MIT)")
        self.assertEqual(self.read("lib/Tag.v"), "\n".join([mf.MIT_TAG, OWN] + code("tag", 10)) + "\n")

    def test_tag_pass_rewrites_the_bundle_tag(self):
        self.files["Old"] = [ANTHROPIC[0], mf.BUNDLE_TAG] + code("old", 10)
        self.tree()
        rc, out = self.apply()
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.read("lib/Old.v"), "\n".join(ANTHROPIC + code("old", 10)) + "\n")
        # a plain run's order: the decided files in path order, then the rows of the tag pass
        self.assertEqual([(r[0], r[6]) for r in self.rows(os.path.join(self.top, "out.tsv"))],
                         [("lib/Copy.v", "made from (block)"),
                          ("lib/Old.v", "Anthropic-licensed: tag Apache-2.0 becomes Apache-2.0 OR MIT")])

    def test_code_check_on_an_mit_tag_write(self):
        # a write of the MIT tag is checked too: one that changed the file's code is refused, and nothing written
        self.files["Tag"] = [mf.APACHE_TAG] + code("tag", 10)
        self.tree()
        with mock.patch.object(mf, "MIT_TAG", mf.MIT_TAG + " Definition leak := tt."):
            rc, out = self.apply()
        self.assert_refused_before_any_write(rc, out, "the licence lines would change the code of")
        self.assertIn("lib/Tag.v", out)

    def test_code_check_on_a_tag_pass_write(self):
        self.files["Old"] = [ANTHROPIC[0], mf.BUNDLE_TAG] + code("old", 10)
        self.tree()
        with mock.patch.object(mf, "APACHE_TAG", mf.APACHE_TAG + " Definition leak := tt."):
            rc, out = self.apply()
        self.assert_refused_before_any_write(rc, out, "the licence lines would change the code of")
        self.assertIn("lib/Old.v", out)

    def test_ten_line_rule_lets_modified_by_lines_go_below_line_10(self):
        # the copyright and the tag within the first 10 lines; the `Modified by` lines may go on below them
        many = ["(* Modified by Theorem Labs, 2026-10: change %s. *)" % chr(97 + i) for i in range(8)]
        self.files["Src"] = ANTHROPIC + many + code("src", 40)
        self.tree()
        rc, out = self.apply()
        self.assertEqual(rc, 0, out)
        copy = self.read("lib/Copy.v").split("\n")
        self.assertEqual(copy[:10], ANTHROPIC + many)
        self.assertTrue(copy[10].startswith("(* Modified by Theorem Labs, 2026-11: "))

    def test_copyright_or_tag_below_line_10_is_refused_before_any_write(self):
        # the 10 lines are counted in the lines of the file as written (lines_of): a copyright or a tag that would
        # start below line 10 is refused
        self.tree()
        with mock.patch.object(mf, "lines_of", lambda items: [n + mf.HEADER_LINES for n in range(len(items))]):
            rc, out = self.apply()
        self.assert_refused_before_any_write(rc, out, "not fit in the first 10 lines of, or hold no Anthropic "
                                                      "copyright line for: lib/Copy.v")

    def test_source_licence_passes_over_a_note_above_anthropic_lines(self):
        # a source whose copyright and tag stand below a note of the branch it was carried from, under a Modified by
        # line of its own (lib/R/Reusable/YP0iR.v of curl/fuzz_bufq): the copy takes every licence comment of the
        # source's opening comments, in order, and not the note; so it carries Anthropic's lines, and a second run
        # no longer decides it
        note = ["(* CARRIED from commit 0123abc, proofs/other/fuzz_other/lib/Src.v.", "   DO NOT EDIT in this tree. *)"]
        self.files["Src"] = [OWN] + note + ANTHROPIC + MULTI + code("src", 40)
        self.tree()
        rc, out = self.apply()
        self.assertEqual(rc, 0, out)
        copy = self.read("lib/Copy.v").split("\n")
        head = [OWN] + ANTHROPIC + MULTI
        self.assertEqual(copy[:len(head)], head)
        self.assertTrue(copy[len(head)].startswith("(* Modified by Theorem Labs, 2026-11: "), copy[len(head)])
        self.assertEqual(copy[len(head) + 1:], code("src", 40) + [""])
        rc, out = self.run_plain(out="again.tsv")
        self.assertEqual(rc, 0, out)
        self.assertNotIn("lib/Copy.v", self.decisions(os.path.join(self.top, "again.tsv")))

    def test_apply_copies_the_source_s_modified_by_lines_below_its_line_10(self):
        # a source whose `Modified by` lines go on below its line 10, as lib/KindBGlue.v of curl/fuzz_bufq does (its
        # lines 11 and 12) and as this generator's own writes leave a file (the 10-line rule needs only the copyright
        # and the tag there): the copy takes every one of the source's leading licence comments, unchanged, then its
        # own line (R4: the source's whole leading licence comments; .claude/skills/adding-a-proof/SKILL.md step 3,
        # case 2: Anthropic's lines and the Modified by lines under them, unchanged)
        mods = ["(* Modified by Theorem Labs, 2026-10: change %d of the source, closed on its line. *)" % n
                for n in range(1, 11)]
        self.files["Src"] = ANTHROPIC + mods + code("src", 40)
        self.tree()
        rc, out = self.apply()
        self.assertEqual(rc, 0, out)
        copy = self.read("lib/Copy.v").split("\n")
        src = ANTHROPIC + mods
        self.assertEqual(copy[:len(src)], src, "the copy lacks licence lines of its source")
        self.assertRegex(copy[len(src)], r"^\(\* Modified by Theorem Labs, 2026-11: (made|copied) from "
                                         r"proofs/demo/fuzz_demo/lib/Src\.v\b.* \*\)$")
        self.assertEqual(copy[len(src) + 1:], code("src", 40) + [""])

    def test_a_source_written_in_this_run_gives_its_own_lines_below_a_note(self):
        # a file licensed in this run that keeps a `Modified by` line of its own in its body, below a note
        # (lib/R/Reusable/YG0dH.v of curl/fuzz_bufq): a file made from it later in the run takes that line too, as it
        # would take it from a source this run does not write (the licence comments among the opening comments of the
        # source as written), and the source's body stays as it was.  The run licenses one file at a time: lib/Copy.v
        # and lib/Mid.v hold lib/Src.v's 40 lines alike, so the first path, lib/Copy.v, joins first, and is then the
        # source of lib/Mid.v (on a tie, path order), which is then the source of lib/Leaf.v
        note = ["(* CARRIED from commit 0123abc, proofs/other/fuzz_other/lib/Mid.v.", "   DO NOT EDIT in this tree. *)"]
        below = "(* Modified by Theorem Labs, 2026-10: a second line of the file's own, below the note. *)"
        self.files["Mid"] = [OWN] + note + [below] + code("src", 40) + code("mid", 40)
        self.files["Leaf"] = code("mid", 40)   # shares nothing with lib/Src.v or lib/Copy.v: made from lib/Mid.v
        self.tree()
        self.born(Copy=2, Leaf=3, Mid=2, Src=1)
        rc, out = self.apply()
        self.assertEqual(rc, 0, out)
        rows = {r[0]: r for r in self.rows(os.path.join(self.top, "out.tsv"))}
        self.assertEqual({p: (r[5], r[6]) for p, r in rows.items()},
                         {"lib/Copy.v": ("lib/Src.v", "made from (block)"),
                          "lib/Mid.v": ("lib/Copy.v", "made from (block)"),
                          "lib/Leaf.v": ("lib/Mid.v", "made from (block)")})
        copied = ("(* Modified by Theorem Labs, 2026-11: copied from proofs/demo/fuzz_demo/lib/Src.v, with only its "
                  "comments or blank lines changed. *)")
        made = ("(* Modified by Theorem Labs, 2026-11: made from proofs/demo/fuzz_demo/lib/Copy.v; 40 of its 80 lines "
                "of code are new or changed. *)")
        self.assertEqual(self.read("lib/Copy.v"), "\n".join(ANTHROPIC + [copied] + code("src", 40)) + "\n")
        self.assertEqual(self.read("lib/Mid.v"), "\n".join(ANTHROPIC + [copied, OWN, made] + note + [below]
                                                           + code("src", 40) + code("mid", 40)) + "\n",
                         "Mid's body changed")
        leaf = ("(* Modified by Theorem Labs, 2026-11: made from proofs/demo/fuzz_demo/lib/Mid.v; 40 lines of the "
                "source are left out. *)")
        self.assertEqual(self.read("lib/Leaf.v"), "\n".join(ANTHROPIC + [copied, OWN, made, below, leaf]
                                                            + code("mid", 40)) + "\n",
                         "the copy lacks the line its source keeps below a note")

    def test_an_own_line_equal_to_a_source_line_is_written_once(self):
        # a file that carries, as its own, a `Modified by` line its source gives too (a copy that came with the
        # source's line): that line is not written again, so it stands once, as the source's, then the file's other
        # own line, then the new line
        same = "(* Modified by Theorem Labs, 2026-10: a change of the source, closed on its line. *)"
        self.files["Src"] = ANTHROPIC + [same] + code("src", 40)
        self.files["Copy"] = [same, OWN] + code("src", 40)
        self.tree()
        rc, out = self.apply()
        self.assertEqual(rc, 0, out)
        copy = self.read("lib/Copy.v").split("\n")
        head = ANTHROPIC + [same, OWN]
        self.assertEqual(copy[:len(head)], head, "a line is written twice at the top")
        self.assertRegex(copy[len(head)], r"^\(\* Modified by Theorem Labs, 2026-11: (made|copied) from "
                                          r"proofs/demo/fuzz_demo/lib/Src\.v\b.* \*\)$")
        self.assertEqual(copy[len(head) + 1:], code("src", 40) + [""])

    def test_licence_lines_with_no_anthropic_copyright_line_are_refused_before_any_write(self):
        # Anthropic's copyright stands only inside a note, which is no licence line: the copy would carry no
        # copyright, and be a file this generator still decides
        self.files["Src"] = ["(* A note that restates Copyright 2026 Anthropic PBC in its words. *)"] + code("src", 40)
        self.tree()
        rc, out = self.apply()
        self.assert_refused_before_any_write(rc, out, "hold no Anthropic copyright line for: lib/Copy.v")

    def test_unclosed_comment_is_refused_before_any_write(self):
        # copying the licence lines one line at a time, as before, gives a copy whose comment never closes: refused,
        # and nothing written
        self.files["Src"] = ANTHROPIC + MULTI + code("src", 40)
        self.tree()
        with mock.patch.object(mf, "source_licence", lambda text: first_lines_only(text)[0]):
            rc, out = self.apply()
        self.assert_refused_before_any_write(rc, out, "refusing to write a file with an unclosed comment")
        self.assertIn("lib/Copy.v", out)

    def test_unclosed_string_is_refused_before_any_write(self):
        # a file the run writes (its tag becomes MIT) whose text leaves a string literal open
        self.files["Tag"] = ANTHROPIC[1:] + code("tag", 10) + ['Definition s := "never closed.']
        self.tree()
        rc, out = self.apply()
        self.assert_refused_before_any_write(rc, out, "refusing to write a file with an unclosed string literal")
        self.assertIn("lib/Tag.v", out)

    def test_missing_lexer(self):
        # oft lint's lexer is an input of every run: a run on a checkout without it is refused before it reads the
        # tree, naming it, and writes nothing
        self.tree()
        os.remove(os.path.join(self.top, mf.LEXER))
        before = self.snapshot()
        rc, out = self.run_plain()
        self.assertEqual(rc, 4, out)
        self.assertIn("made_from.py: refusing the run: %s is missing" % mf.LEXER, out)
        self.assertEqual(self.snapshot(), before)

    def test_run_on_its_own_output_changes_nothing(self):
        self.files["Copy"] = [OWN] + MULTI + code("src", 40)
        self.tree()
        self.assertEqual(self.apply()[0], 0)
        self.assert_a_second_apply_changes_nothing()


class HistoryNamed(Tree):
    """A history row whose source carries no licence lines yet: no KeyError; the named file waits until its source is
    licensed in the run and is then made from it, and when the source never is, the wait fails at the end and the rule
    decides the file."""

    def setUp(self):
        super().setUp()
        self.write("lib/Src.v", ANTHROPIC + code("src", 40))
        self.write("lib/Mid.v", code("src", 40))      # made from lib/Src.v by the rule
        self.write("lib/Early.v", code("early", 12))  # shares nothing: the rule finds it written here
        self.write("lib/Own.v", code("own", 10))      # written here, and never takes lines
        self.born(Early=2, Mid=2, Own=2, Src=1)

    def name(self, path, source):
        self.put(self.layout.history, "path\tsource\n%s\t%s\n" % (path, source))

    def test_source_that_never_takes_lines(self):
        self.name("lib/Early.v", "lib/Own.v")
        rc, out = self.run_plain()
        self.assertEqual(rc, 0, out)
        self.assertNotIn("KeyError", out)
        self.assertEqual(self.decisions(os.path.join(self.top, "out.tsv"))["lib/Early.v"], "written here")

    def test_source_licensed_later_in_the_run(self):
        # lib/Early.v comes before lib/Mid.v in path order; its history row waits until lib/Mid.v is licensed, by the
        # rule, and then decides it, whatever the rule finds for it
        self.name("lib/Early.v", "lib/Mid.v")
        rc, out = self.apply()
        self.assertEqual(rc, 0, out)
        rows = {r[0]: r for r in self.rows(os.path.join(self.top, "out.tsv"))}
        self.assertEqual(rows["lib/Mid.v"][5:7], ["lib/Src.v", "made from (block)"])
        copied = ("(* Modified by Theorem Labs, 2026-11: copied from proofs/demo/fuzz_demo/lib/Src.v, with only its "
                  "comments or blank lines changed. *)")
        made = ("(* Modified by Theorem Labs, 2026-11: made from proofs/demo/fuzz_demo/lib/Mid.v; 12 of its 12 lines "
                "of code are new or changed and 40 lines of the source are left out. *)")
        self.assertEqual(rows["lib/Early.v"], ["lib/Early.v", "0", "0", "12", "0.000", "lib/Mid.v",
                                               "made from (history)", made])
        self.assertEqual(self.read("lib/Mid.v"), "\n".join(ANTHROPIC + [copied] + code("src", 40)) + "\n")
        self.assertEqual(self.read("lib/Early.v"), "\n".join(ANTHROPIC + [copied, made] + code("early", 12)) + "\n")


def derived(path):
    """derive_y.py's note of its first form, in a `Modified by` line, as curl/fuzz_fnmatch's copies carry it."""
    return ("(* Modified by Theorem Labs, 2026-11: derived from %s of this library by derive_y.py: module names "
            "A.Axyz -> AU.Yxyz. *)" % path)


def relocated(path):
    """A relocation's comment, as curl/fuzz_fnmatch's lib/A/Prog/ files open with it."""
    return "(* Relocated from %s (the plain image) to the ASan image (fuzz_demo.asan): module paths changed. *)" % path


class Origins(unittest.TestCase):
    """What names a file's origin, read from its text alone (origins_named)."""

    def named(self, *lines):
        return mf.origins_named("\n".join(list(lines) + code("x", 2)), UNIT)

    def test_derive_y_first_form_far_down_and_split_over_lines(self):
        # read however far down the opening comments go (lib/AU/YFk0g.v of curl/fuzz_fnmatch has its derive_y line at
        # line 90), below a comment that is no licence line, and the words may be split by any blanks
        notes = ["(* A note of the copy step, number %d. *)" % n for n in range(12)]
        self.assertEqual(self.named(OWN, *notes, "(* Modified by Theorem Labs, 2026-11: derived from",
                                    "   lib/A/X.v of this", "   library by derive_y.py: module names. *)"),
                         ["lib/A/X.v"])
        self.assertEqual(self.named(derived("lib/A/X.v")), ["lib/A/X.v"])
        self.assertEqual(self.named("(* derived from lib/A/X.v of this library, by derive_y.py *)"), [])

    def test_derive_y_second_form(self):
        self.assertEqual(self.named("(* Modified by X: copied from proofs/demo/fuzz_demo/lib/A/X.v; then by "
                                    "derive_y.py *)"), ["lib/A/X.v"])
        self.assertEqual(self.named("(* copied from proofs/demo/fuzz_demo/lib/A/X.v by hand *)"), [])
        self.assertEqual(self.named("(* by derive_y.py, copied from proofs/demo/fuzz_demo/lib/A/X.v *)"), [])
        self.assertEqual(self.named("(* copied from lib/A/X.v by derive_y.py *)"), [])

    def test_relocated_from_at_the_start_of_a_comment(self):
        self.assertEqual(self.named(relocated("lib/A/X.v")), ["lib/A/X.v"])
        self.assertEqual(self.named("(*", "   Relocated from lib/A/X.v. *)"), ["lib/A/X.v"])
        # in the middle of a comment, or in small letters, it names nothing
        self.assertEqual(self.named("(* A note.", "   Relocated from lib/A/X.v at the plain image. *)"), [])
        self.assertEqual(self.named("(* Modified by Theorem Labs, 2026-10: relocated from lib/A/X.v by hand. *)"), [])

    def test_each_comment_of_a_line_on_its_own(self):
        self.assertEqual(self.named(ANTHROPIC[0] + " " + relocated("lib/A/X.v")), ["lib/A/X.v"])

    def test_a_line_inside_another_comment_names_nothing(self):
        self.assertEqual(self.named("(* A note (* " + derived("lib/A/X.v")[3:] + " *)"), [])
        self.assertEqual(self.named("(* A note. " + relocated("lib/A/X.v") + " *)"), [])
        # the words around a comment inside it stay apart
        self.assertEqual(self.named("(* Relocated from lib/A/X.v(* a note *)by hand *)"), ["lib/A/X.v"])

    def test_only_the_opening_comments(self):
        self.assertEqual(mf.origins_named("\n".join(code("x", 1) + [relocated("lib/A/X.v")]), UNIT), [])
        self.assertEqual(self.named("(* never closed", relocated("lib/A/X.v")), [])

    def test_paths_that_name_no_file_of_the_unit(self):
        self.assertEqual(self.named("(* Relocated from lib/A/X.v at 3b7a474b88e by wlreloc.py *)"), [])
        self.assertEqual(self.named("(* Relocated from lib/A/X.v at abcdef by hand *)"), ["lib/A/X.v"])   # 6 digits
        self.assertEqual(self.named(relocated("proofs/other/fuzz_other/lib/A/X.v")), [])
        self.assertEqual(self.named(relocated("proofs/lib/A/X.v")), [])
        self.assertEqual(self.named(relocated("proofs/demo/fuzz_demo/lib/A/X.v")), ["lib/A/X.v"])
        self.assertEqual(self.named(relocated("projects/demo/fuzz_demo/proofs/lib/A/X.v;")), ["lib/A/X.v"])
        self.assertEqual(self.named(relocated("projects/other/fuzz_other/proofs/lib/A/X.v")), [])

    def test_a_path_that_the_comment_s_close_ends(self):
        # R4: a `Relocated from` line names its origin when its path is a file of the unit.  When the comment closes
        # right after the path, its `*)` is the comment's close, not part of the path
        self.assertEqual(self.named("(* Relocated from lib/A/X.v*)"), ["lib/A/X.v"])
        self.assertEqual(self.named("(* Relocated from lib/A/X.v.*)"), ["lib/A/X.v"])

    def test_a_path_at_a_commit_in_parentheses(self):
        # R4: ` (at <commit>)` after the path, as ` at <commit>` after it, is the path at another commit and names
        # no origin: its digits in either case, the comment's close right after it, and in derive_y's second form
        self.assertEqual(self.named("(* Relocated from lib/A/X.v (at 904d53323840) by wlreloc.py *)"), [])
        self.assertEqual(self.named("(* Relocated from lib/A/X.v (at 904D533)*)"), [])
        self.assertEqual(self.named("(* Relocated from lib/A/X.v at 3b7a474b88e*)"), [])
        self.assertEqual(self.named("(* Modified by X: copied from proofs/demo/fuzz_demo/lib/A/X.v (at 904d53323840) "
                                    "by derive_y.py *)"), [])
        self.assertEqual(self.named("(* Relocated from lib/A/X.v (at abcdef) by hand *)"), ["lib/A/X.v"])   # 6 digits


class Cases(Tree):
    """The rule's cases, each written by a method under a prefix k of its file names and its code's words, so that one
    tree can hold several (case 14).  Each gives its first-added times, history rows and left-bare rows."""

    def setUp(self):
        super().setUp()
        self.times, self.named, self.declared = {}, [], []

    def files(self, k, times, **files):
        for stem, lines in files.items():
            self.write("lib/%s%s.v" % (k, stem), lines)
            self.times[k + stem] = times[stem]

    def finish(self):
        self.born(**self.times)
        self.put(self.layout.history, "path\tsource\n" + "".join("%s\t%s\n" % r for r in self.named))
        self.put(self.layout.left_bare_tsv, "path\treason\n" + "".join("%s\t%s\n" % r for r in self.declared))

    def out(self, apply=False):
        """{path: row} of a run on the tree (with --apply in this process when apply), and its output."""
        self.finish()
        rc, out = self.apply() if apply else self.run_plain()
        self.assertEqual(rc, 0, out)
        return {r[0]: r for r in self.rows(os.path.join(self.top, "out.tsv"))}, out

    def apply_then_check(self):
        """A run with --apply whose OUT is the unit's record, then --check, each with exit 0: ({path: row} of the record
        that run writes, its output).  --check writes nothing, so the record and files stay as --apply wrote them."""
        self.finish()
        rc, out = self.cli(self.layout.record, "--apply", *self.history_args())
        self.assertEqual(rc, 0, out)
        rows = {r[0]: r for r in self.rows()}
        rc, checked = self.check()
        self.assertEqual(rc, 0, checked)
        return rows, out

    def outs_under_two_hash_seeds(self, timeout=None):
        """The command line run twice on the tree, with PYTHONHASHSEED 1 and 2, each run exiting 0 (within timeout
        seconds, as cli), and its two OUT files equal byte for byte: that OUT, as bytes."""
        outs = []
        for seed in ("1", "2"):
            out = "seed%s.tsv" % seed
            rc, said = self.run_plain(out=out, env=dict(os.environ, PYTHONHASHSEED=seed), timeout=timeout)
            self.assertEqual(rc, 0, said)
            with open(os.path.join(self.top, out), "rb") as f:
                outs.append(f.read())
        self.assertEqual(outs[0], outs[1], "two hash seeds give two OUT files")
        return outs[0]

    def forge(self, old, new):
        """The unit's record, by a run of the generator as it is; then the scratch checkout's generator, the one its
        unit file runs, forged: its one text old made new."""
        rc, out = self.cli(self.layout.record, *self.history_args())
        self.assertEqual(rc, 0, out)
        path = os.path.join(self.top, "dev/licence/made_from.py")
        with open(path, encoding="utf-8") as f:
            text = f.read()
        self.assertEqual(text.count(old), 1)
        with open(path, "w", encoding="utf-8") as f:
            f.write(text.replace(old, new))

    def direct(self, order, shortcut):
        """licensed_in_order on the tree, after the tag pass, of the files a run decides (to_decide, as decide() takes
        them), in path order, reversed, or shuffled with the seed order."""
        u = mf.Unit(self.top, self.layout)
        files = mf.to_decide(u)[1]
        if order == "reversed":
            files.reverse()
        elif order != "path":
            random.Random(order).shuffle(files)
        return mf.licensed_in_order(u, files, self.layout, mf.left_bare(self.top, u.files, self.layout),
                                    mf.history_of(os.path.join(self.top, self.layout.history)),
                                    mf.first_added_of(os.path.join(self.top, self.layout.first_added)), shortcut)

    def text(self, *parts):
        return "\n".join(x for part in parts for x in part) + "\n"

    def case1(self, k=""):
        # a derive_y copy whose origin is younger than it by first-added.tsv, and a second Anthropic copy that holds
        # all of it, where the origin holds a third
        self.files(k, dict(Orig=3, Near=1, Copy=2),
                   Orig=ANTHROPIC + code(k + "a", 20), Near=ANTHROPIC + code(k + "a", 20) + code(k + "c", 40),
                   Copy=[derived("lib/%sOrig.v" % k)] + code(k + "a", 20) + code(k + "c", 40))

    def case6(self, k=""):
        # origins the run does not license: written here, borderline, left bare (twice); and a tagged file
        a = code(k + "a", 40)
        self.files(k, dict(Orig=1, W=2, B=2, L=2, L2=2, P1=2, P2=2, P3=2, P4=2, T=2),
                   Orig=ANTHROPIC + a, W=code(k + "w", 10), B=a[:5] + code(k + "b", 10), L=code(k + "l", 10),
                   L2=a[10:], P1=[relocated("lib/%sW.v" % k)] + a[:5] + code(k + "p", 10),
                   P2=[relocated("lib/%sB.v" % k)] + code(k + "q", 10),
                   P3=[relocated("lib/%sL.v" % k)] + code(k + "s", 10),
                   P4=[relocated("lib/%sL2.v" % k)] + code(k + "u", 10),
                   T=[mf.APACHE_TAG, relocated("lib/%sW.v" % k)] + code(k + "t", 10))
        self.declared += [("lib/%sL.v" % k, "ours: written for this test, not copied"),
                          ("lib/%sL2.v" % k, "ours: not copied from lib/%sOrig.v" % k)]

    def case8(self, k=""):
        # a history row and a named origin, both licensed; and a history row whose source is never licensed
        self.files(k, dict(Orig=1, H=1, P=2, W=2, Q=2),
                   Orig=ANTHROPIC + code(k + "a", 40), H=ANTHROPIC + code(k + "h", 40),
                   P=[derived("lib/%sOrig.v" % k)] + code(k + "a", 40) + code(k + "h", 10), W=code(k + "w", 10),
                   Q=[relocated("lib/%sOrig.v" % k)] + code(k + "q", 10))
        self.named += [("lib/%sP.v" % k, "lib/%sH.v" % k), ("lib/%sQ.v" % k, "lib/%sW.v" % k)]

    def case10(self, k=""):
        # the origin is made from a file with Anthropic's lines in the same run
        self.files(k, dict(Src=1, Mid=2, P=2),
                   Src=ANTHROPIC + code(k + "a", 40), Mid=code(k + "a", 40) + code(k + "m", 10),
                   P=[relocated("lib/%sMid.v" % k)] + code(k + "m", 10) + code(k + "p", 5))

    def case12(self, k=""):
        # Q holds 31 distinctive lines of R and a block of its own; P holds Q's own block and a run of 6 lines of R
        self.files(k, dict(R=1, Q=2, P=3),
                   R=ANTHROPIC + code(k + "r", 40), Q=code(k + "r", 31) + code(k + "q", 40),
                   P=code(k + "q", 40) + code(k + "r", 6))

    def case13(self, k="", equal=False):
        # P and Q share a block R lacks, and each holds a block of R: Q's the longer, or the two of equal length
        r = code(k + "r", 80)
        self.files(k, dict(R=1, Q=2, P=2),
                   R=ANTHROPIC + r, Q=r[:40] + code(k + "s", 40), P=r[40:80 if equal else 72] + code(k + "s", 40))

    def case_bare_origin(self, k=""):
        # a file with Anthropic's tag alone whose origin is left bare, overruling the source the rule finds for it
        a = code(k + "a", 40)
        self.files(k, dict(X=1, O=2, P=2), X=ANTHROPIC + a, O=a,
                   P=[mf.APACHE_TAG, relocated("lib/%sO.v" % k)] + code(k + "p", 10))
        self.declared.append(("lib/%sO.v" % k, "ours: not copied from lib/%sX.v" % k))

    def case_tagged_origin(self, k=""):
        # a file that names an origin with Anthropic's tag alone, which the run finds written here, and that holds a
        # block of 40 distinctive lines of a file with Anthropic's lines that the origin lacks
        self.files(k, dict(X=1, O=2, P=2), X=ANTHROPIC + code(k + "x", 40), O=[mf.APACHE_TAG] + code(k + "o", 10),
                   P=[relocated("lib/%sO.v" % k)] + code(k + "x", 40) + code(k + "p", 10))

    def case_tagged_origin_licensed(self, k=""):
        # a file that names an origin with Anthropic's tag alone, which the rule finds made from a file with
        # Anthropic's lines: lib/O.v holds 40 lines of lib/X.v, and lib/P.v the other 60, so the rule would find lib/P.v
        # the stronger
        x, y = code(k + "x", 40), code(k + "y", 60)
        self.files(k, dict(X=1, O=2, P=2), X=ANTHROPIC + x + y, O=[mf.APACHE_TAG] + x,
                   P=[relocated("lib/%sO.v" % k)] + y)

    def case_failed_history(self, k="", name="P"):
        # two files that name lib/R.v as their origin, each with a history row that fails at the same stall: lib/S.v's
        # names lib/W.v, which the run finds written here, and lib/P.v's (lib/<name>.v's) names lib/S.v.  lib/S.v
        # holds 20 lines of lib/R.v and 10 of its own; lib/P.v 10 other lines of lib/R.v, lib/S.v's 10 and 5 of its own.
        # And lib/B.v, left bare, which names lib/R.v as well, holds 30 other lines of it and 10 of its own, and whose
        # history row names lib/W.v: a file left bare never stalls, so that wait stands to the end of the run
        r, s = code(k + "r", 40), code(k + "s", 10)
        self.files(k, {"R": 1, "S": 2, "W": 2, "B": 2, name: 2}, R=ANTHROPIC + r,
                   S=[relocated("lib/%sR.v" % k)] + r[:20] + s, W=code(k + "w", 10),
                   B=[relocated("lib/%sR.v" % k)] + r[10:] + code(k + "b", 10),
                   **{name: [relocated("lib/%sR.v" % k)] + r[20:30] + s + code(k + "p", 5)})
        self.named += [("lib/%sS.v" % k, "lib/%sW.v" % k), ("lib/%s%s.v" % (k, name), "lib/%sS.v" % k),
                       ("lib/%sB.v" % k, "lib/%sW.v" % k)]
        self.declared.append(("lib/%sB.v" % k, "ours: not copied from lib/%sR.v" % k))

    def case_late_history(self, k=""):
        # two files that name no origin, whose history rows fail at the first stall: lib/P.v holds 40 lines of lib/X.v
        # and 40 of its own, and its row names lib/W.v, which the run finds written here; lib/H.v holds lib/P.v's own
        # 40, so the rule licenses it from lib/P.v after the stall; lib/Q.v holds 10 of its own, and its row names
        # lib/H.v
        self.files(k, dict(X=1, P=2, W=2, H=2, Q=2), X=ANTHROPIC + code(k + "x", 40),
                   P=code(k + "x", 40) + code(k + "p", 40), W=code(k + "w", 10), H=code(k + "p", 40),
                   Q=code(k + "q", 10))
        self.named += [("lib/%sP.v" % k, "lib/%sW.v" % k), ("lib/%sQ.v" % k, "lib/%sH.v" % k)]

    def case_cycle(self, k=""):
        # a cycle of two named origins, of which the rule licenses one file: lib/A.v holds 40 lines of lib/X.v, and
        # lib/B.v 10 of its own
        self.files(k, dict(X=1, A=2, B=2), X=ANTHROPIC + code(k + "x", 40),
                   A=[relocated("lib/%sB.v" % k)] + code(k + "x", 40),
                   B=[relocated("lib/%sA.v" % k)] + code(k + "b", 10))

    def case_broken_cycle(self, k=""):
        # a cycle of three named origins, lib/A.v -> lib/B.v -> lib/C.v -> lib/A.v, of which the rule licenses lib/C.v
        # (40 lines of lib/X.v), and lib/B.v is left bare; lib/A.v and lib/B.v hold 10 lines of their own each
        self.files(k, dict(X=1, A=2, B=2, C=2), X=ANTHROPIC + code(k + "x", 40),
                   A=[relocated("lib/%sB.v" % k)] + code(k + "a", 10),
                   B=[relocated("lib/%sC.v" % k)] + code(k + "b", 10),
                   C=[relocated("lib/%sA.v" % k)] + code(k + "x", 40))
        self.declared.append(("lib/%sB.v" % k, "ours: written for this test"))

    def case_history_and_tagged_origin(self, k=""):
        # a file left bare whose history row names lib/X.v, which carries Anthropic's lines, and whose named origin is
        # lib/T.v, which carries Anthropic's tag alone and which the run finds written here
        self.files(k, dict(X=1, T=2, B=2), X=ANTHROPIC + code(k + "x", 40), T=[mf.APACHE_TAG] + code(k + "t", 10),
                   B=[relocated("lib/%sT.v" % k)] + code(k + "b", 10))
        self.named.append(("lib/%sB.v" % k, "lib/%sX.v" % k))
        self.declared.append(("lib/%sB.v" % k, "ours: written for this test"))

    def case_tagged_cycle(self, k=""):
        # a cycle of three named origins, lib/A.v -> lib/T.v -> lib/C.v -> lib/A.v, of which lib/T.v carries Anthropic's
        # tag alone: lib/A.v and lib/T.v hold 10 lines of their own each, and lib/C.v 15 lines of lib/X.v, each one
        # followed by two lines of its own
        x, c = code(k + "x", 40), code(k + "c", 30)
        self.files(k, dict(X=1, A=2, T=2, C=2), X=ANTHROPIC + x,
                   A=[relocated("lib/%sT.v" % k)] + code(k + "a", 10),
                   T=[mf.APACHE_TAG, relocated("lib/%sC.v" % k)] + code(k + "t", 10),
                   C=[relocated("lib/%sA.v" % k)] + [y for i in range(15) for y in (x[i], c[2 * i], c[2 * i + 1])])

    def case_history_and_origin(self, k="", bare=False):
        # two files that name lib/O.v as their origin, lib/H.v and lib/P.v, with 10 lines of their own each; lib/P.v's
        # history row names lib/H.v, and lib/P.v is left bare when bare.  lib/O.v holds the 40 lines of lib/X.v, and its
        # history row names lib/Nope.v, which holds 10 other lines, so the rule licenses lib/O.v after the stall, and
        # lib/H.v then takes it: lib/P.v's history source and its named origin are then both licensed
        self.files(k, dict(X=1, O=2, Nope=2, H=2, P=2), X=ANTHROPIC + code(k + "x", 40), O=code(k + "x", 40),
                   Nope=code(k + "n", 10), H=[relocated("lib/%sO.v" % k)] + code(k + "h", 10),
                   P=[relocated("lib/%sO.v" % k)] + code(k + "p", 10))
        self.named += [("lib/%sO.v" % k, "lib/%sNope.v" % k), ("lib/%sP.v" % k, "lib/%sH.v" % k)]
        if bare:
            self.declared.append(("lib/%sP.v" % k, "ours: written for this test"))


class NamedOrigin(Cases):
    """A file that names its origin takes it, with no score and no age test (cases 1 to 11), and what a tagged file or
    a tagged origin takes, which --apply gives the MIT tag."""

    def test_case_1_derive_y_names_its_origin_over_a_better_copy(self):
        # the Kit/Ext_memcpy.v kind: lib/Near.v holds all of lib/Copy.v and lib/Orig.v a third, and lib/Orig.v is
        # younger than lib/Copy.v; the derive_y line names lib/Orig.v, so that is its source
        self.case1()
        rows, _ = self.out(apply=True)
        self.assertEqual(rows["lib/Copy.v"], ["lib/Copy.v", "20", "20", "60", "0.333", "lib/Orig.v",
                                              "made from (named origin)", "-"])
        self.assertEqual(self.read("lib/Copy.v"), self.text(ANTHROPIC, [derived("lib/Orig.v")], code("a", 20),
                                                            code("c", 40)))
        # without the derive_y line the rule takes the copy that scores higher
        self.write("lib/Copy.v", code("a", 20) + code("c", 40))
        rows, _ = self.out()
        self.assertEqual(rows["lib/Copy.v"][1:7], ["60", "60", "60", "1.000", "lib/Near.v", "made from (block)"])

    def test_case_2_derive_y_second_form_of_the_layout_before_projects(self):
        self.case1()
        self.write("lib/Copy.v", ["(* Modified by Theorem Labs, 2026-11: copied from proofs/demo/fuzz_demo/lib/Orig.v, "
                                  "its module names and addresses changed by derive_y.py. *)"]
                   + code("a", 20) + code("c", 40))
        rows, _ = self.out()
        self.assertEqual(rows["lib/Copy.v"][1:], ["20", "20", "60", "0.333", "lib/Orig.v", "made from (named origin)",
                                                  "-"])
        # the generator reads the layout before projects/ as tools/oft/layout.py canonical does, without loading it
        spec = importlib.util.spec_from_file_location("oft_layout", os.path.join(REPO, "tools", "oft", "layout.py"))
        layout = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(layout)
        for path in ("proofs/demo/fuzz_demo/lib/Orig.v", "proofs/other/fuzz_other/lib/A/X.v", "proofs/lib/A/X.v",
                     "proofs/lib-lean/X.v", "proofs/demo/fuzz_demo", "proofs/demo/X.v",
                     "projects/demo/fuzz_demo/proofs/lib/Orig.v", "lib/Orig.v"):
            with self.subTest(path=path):
                self.assertEqual(mf.new_layout(path), layout.canonical(path))
        self.assertEqual(mf.origin_path("proofs/demo/fuzz_demo/lib/Orig.v", UNIT), "lib/Orig.v")
        self.assertIsNone(mf.origin_path("proofs/other/fuzz_other/lib/Orig.v", UNIT))

    def test_case_3_relocated_from_at_the_start_of_a_comment(self):
        a = code("a", 40)
        self.files("", dict(Orig=1, Rel=2, Mid=2, Low=2), Orig=ANTHROPIC + a,
                   Rel=["(* Relocated from lib/Orig.v (the plain image) to the ASan image (fuzz_demo.asan): module",
                        "   paths changed, and every address moved by symbol. *)"] + a[:10] + code("r", 10),
                   Mid=["(* A note of the copy step.", "   Relocated from lib/Orig.v by wlreloc.py. *)"]
                   + a[10:20] + code("m", 10),
                   Low=["(* Modified by Theorem Labs, 2026-10: relocated from lib/Orig.v by hand. *)"]
                   + a[20:30] + code("l", 10))
        rows, _ = self.out()
        self.assertEqual(rows["lib/Rel.v"][1:], ["10", "10", "20", "0.500", "lib/Orig.v", "made from (named origin)",
                                                 "-"])
        for p in ("lib/Mid.v", "lib/Low.v"):   # by the rule
            self.assertEqual(rows[p][1:7], ["10", "10", "20", "0.500", "lib/Orig.v", "made from (share)"], p)

    def test_case_4_lines_that_name_no_origin(self):
        # each such file is decided by the rule: lib/Orig.v holds all of it, so `made from (block)` with a line
        self.files("", dict(Orig=1, Two=1, Neg=2), Orig=ANTHROPIC + code("a", 40), Two=ANTHROPIC + code("z", 5),
                   Neg=code("a", 40))
        self.write("provenance/Old.v", code("a", 40))
        for name, lines in (
                ("at a commit", ["(* Relocated from lib/Orig.v at 3b7a474b88e by wlreloc.py (by symbol). *)"]),
                ("a commit before it", ["(* Relocated from (origin/cold/port-fm-rtscan f8664b31b9c, "
                                        "proofs/demo/fuzz_demo/lib/Orig.v) to the ASan image. *)"]),
                ("another unit", [relocated("proofs/other/fuzz_other/lib/Orig.v")]),
                ("no file", [relocated("lib/Missing.v")]),
                ("a file under provenance/", [relocated("provenance/Old.v")]),
                ("its own path", [relocated("lib/Neg.v")]),
                ("two origins", [derived("lib/Orig.v"), relocated("lib/Two.v")]),
                ("inside another comment", [OWN, "(* A note of the copy step. %s *)" % derived("lib/Orig.v")])):
            with self.subTest(name=name):
                self.write("lib/Neg.v", lines + code("a", 40))
                rows, out = self.out()
                self.assertEqual(rows["lib/Neg.v"][1:7], ["40", "40", "40", "1.000", "lib/Orig.v", "made from (block)"])
                self.assertTrue(rows["lib/Neg.v"][7].startswith("(* Modified by Theorem Labs, 2026-11: copied from "))
                if name == "two origins":
                    self.assertIn("made_from.py: lib/Neg.v names 2 origins, lib/Orig.v and lib/Two.v: it names none",
                                  out)

    def test_case_5_a_cycle_of_named_origins(self):
        # lib/X.v and lib/Y.v name each other: the cycle keeps their origins, and at the stall each stops waiting for
        # its origin; the rule licenses lib/X.v (each holds all of lib/Orig.v: the first path), and lib/Y.v, still
        # undecided, then takes its origin.  lib/Z.v names lib/X.v and keeps it
        a = code("a", 40)
        self.files("", dict(Orig=1, X=2, Y=2, Z=2), Orig=ANTHROPIC + a, X=[relocated("lib/Y.v")] + a,
                   Y=[relocated("lib/X.v")] + a, Z=[relocated("lib/X.v")] + code("z", 10))
        rows, out = self.out(apply=True)
        self.assertIn("made_from.py: a cycle of named origins, lib/X.v and lib/Y.v: each of them may stop waiting for "
                      "its origin when the run stalls", out)
        self.assertEqual(rows["lib/X.v"][1:7], ["40", "40", "40", "1.000", "lib/Orig.v", "made from (block)"])
        self.assertEqual(rows["lib/Y.v"][1:], ["40", "40", "40", "1.000", "lib/X.v", "made from (named origin)", "-"])
        self.assertEqual(rows["lib/Z.v"][1:], ["0", "0", "10", "0.000", "lib/X.v", "made from (named origin)", "-"])
        x = self.read("lib/X.v").split("\n")
        self.assertEqual(self.read("lib/Z.v"), self.text(x[:3], [relocated("lib/X.v")], code("z", 10)))
        self.assertEqual(self.read("lib/Y.v"), self.text(x[:3], [relocated("lib/X.v")], a))

    def test_case_6_an_origin_the_run_does_not_license(self):
        # the file takes its origin's decision, with its own counts and best source; a left-bare origin's reason
        self.case6()
        rows, _ = self.out(apply=True)
        reason, reason2 = "ours: written for this test, not copied", "ours: not copied from lib/Orig.v"
        self.assertEqual(rows["lib/W.v"][1:], ["0", "0", "10", "0.000", "-", "written here", ""])
        self.assertEqual(rows["lib/B.v"][1:], ["5", "5", "15", "0.333", "lib/Orig.v", "borderline: written here", ""])
        self.assertEqual(rows["lib/L.v"][1:], ["0", "0", "10", "0.000", "-", "left bare", reason])
        self.assertEqual(rows["lib/L2.v"][1:], ["30", "30", "30", "1.000", "lib/Orig.v",
                                                "left bare (overrules made from (block))", reason2])
        self.assertEqual(rows["lib/P1.v"][1:], ["5", "5", "15", "0.333", "lib/Orig.v", "written here", ""])
        self.assertEqual(rows["lib/P2.v"][1:], ["0", "0", "10", "0.000", "-", "borderline: written here", ""])
        self.assertEqual(rows["lib/P3.v"][1:], ["0", "0", "10", "0.000", "-", "left bare", reason])
        self.assertEqual(rows["lib/P4.v"][1:], ["0", "0", "10", "0.000", "-", "left bare (overrules made from (block))",
                                                reason2])
        self.assertEqual(rows["lib/T.v"][1:], ["0", "0", "10", "0.000", "-",
                                               "written here (Apache-2.0 OR MIT tag becomes MIT)", ""])
        self.assertEqual(self.read("lib/T.v"), self.text([mf.MIT_TAG, relocated("lib/W.v")], code("t", 10)))
        for p in ("P1", "P2", "P3", "P4"):   # nothing written
            self.assertFalse(mf.ANTHROPIC.search(self.read("lib/%s.v" % p)), p)

    def test_case_7_an_origin_with_the_mit_tag_names_none(self):
        a = code("a", 40)
        self.files("", dict(Orig=1, M=2, P=2), Orig=ANTHROPIC + a, M=[mf.MIT_TAG] + a, P=[relocated("lib/M.v")] + a)
        rows, _ = self.out()
        self.assertNotIn("lib/M.v", rows)   # a file the run does not decide
        self.assertEqual(rows["lib/P.v"][1:7], ["40", "40", "40", "1.000", "lib/Orig.v", "made from (block)"])

    def test_case_8_history_wins(self):
        self.case8()
        rows, _ = self.out(apply=True)
        made = ("(* Modified by Theorem Labs, 2026-11: made from proofs/demo/fuzz_demo/lib/H.v; 40 of its 50 lines of "
                "code are new or changed and 30 lines of the source are left out. *)")
        self.assertEqual(rows["lib/P.v"][1:], ["10", "10", "50", "0.200", "lib/H.v",
                                               "made from (history; it names lib/Orig.v)", made])
        self.assertEqual(self.read("lib/P.v"), self.text(ANTHROPIC, [derived("lib/Orig.v"), made], code("a", 40),
                                                         code("h", 10)))
        # a history source never licensed: the wait fails, and the file takes its named origin
        self.assertEqual(rows["lib/W.v"][6], "written here")
        self.assertEqual(rows["lib/Q.v"][1:], ["0", "0", "10", "0.000", "lib/Orig.v", "made from (named origin)", "-"])
        self.assertEqual(self.read("lib/Q.v"), self.text(ANTHROPIC, [relocated("lib/Orig.v")], code("q", 10)))

    def test_a_failed_history_row_and_a_named_origin_are_decided_together_against_one_a(self):
        # both history rows fail at one stall, and each file names lib/R.v: a failed history row and a named origin
        # are decided together, every such file against the same licensed files, which hold lib/R.v and not lib/S.v,
        # so lib/S.v and lib/P.v take their origin whether lib/P.v sorts before lib/S.v or, named lib/T.v, after it.
        # Deciding them one at a time gave lib/P.v lib/R.v (named origin) and lib/T.v lib/S.v (history; it names
        # lib/R.v), by the order of the files.  lib/B.v, left bare, waits to the end, where its history source is not
        # licensed and its origin is: it takes its origin
        got = []
        for name in ("P", "T"):
            self.times, self.named, self.declared = {}, [], []
            self.case_failed_history(name=name)
            rows, _ = self.out()
            got.append((rows["lib/%s.v" % name][5:7], rows["lib/S.v"][5:7]))
            self.assertEqual(rows["lib/B.v"][1:], ["30", "30", "40", "0.750", "lib/R.v",
                                                   "left bare (overrules made from (named origin))",
                                                   "ours: not copied from lib/R.v"])
            os.remove(os.path.join(self.top, self.root, "lib/%s.v" % name))
        self.assertEqual(got[0], got[1])
        self.assertEqual(got[0], (["lib/R.v", mf.NAMED], ["lib/R.v", mf.NAMED]))

    def test_a_failed_history_row_decides_its_file_when_its_source_joins_later(self):
        # lib/Q.v's history row fails at the first stall, and after it the rule licenses lib/P.v (its own row failed
        # too), then lib/H.v from it: lib/Q.v names no origin, so its history row is its one claim, and decides it
        # then.  After --apply lib/P.v, lib/H.v and lib/Q.v all carry Anthropic's lines, so a run on that output
        # decides none of them, and --check passes because it compares no row of theirs.  When a failed history row
        # decided nothing, lib/Q.v was written here, and --check after --apply found it made from (history)
        self.case_late_history()
        rows, _ = self.apply_then_check()
        self.assertEqual(rows["lib/P.v"][5:7], ["lib/X.v", "made from (block)"])
        self.assertEqual(rows["lib/H.v"][5:7], ["lib/P.v", "made from (block)"])
        self.assertEqual(rows["lib/Q.v"][5:7], ["lib/H.v", "made from (history)"])

    def test_a_cycle_of_which_the_rule_licenses_one_file(self):
        # lib/A.v and lib/B.v name each other: the cycle keeps their origins, and at the stall each stops waiting for
        # its origin; the rule licenses lib/A.v (40 lines of lib/X.v), and lib/B.v, still undecided, takes its
        # origin.  After --apply lib/A.v and lib/B.v both carry Anthropic's lines, so a run on that output decides
        # neither, and --check passes because it compares no row of either.  When a cycle named no origin, lib/B.v was
        # written here, and --check after --apply found it made from (named origin)
        self.case_cycle()
        rows, out = self.apply_then_check()
        self.assertEqual(rows["lib/A.v"][1:7], ["40", "40", "40", "1.000", "lib/X.v", "made from (block)"])
        self.assertEqual(rows["lib/B.v"][1:], ["0", "0", "10", "0.000", "lib/A.v", mf.NAMED, "-"])
        self.assertIn("made_from.py: a cycle of named origins, lib/A.v and lib/B.v: each of them may stop waiting for "
                      "its origin when the run stalls", out)
        a = self.read("lib/A.v").split("\n")
        self.assertEqual(self.read("lib/B.v"), self.text(a[:3], [relocated("lib/A.v")], code("b", 10)))

    def test_a_chain_of_named_origins_that_returns_to_its_file_is_a_fault(self):
        # a fault no input reaches, so the scratch checkout's generator, the one its unit file runs, is forged to
        # forget its cycles: lib/A.v and lib/B.v of case_cycle then wait for each other to the end of the run, where
        # the walk of named origins returns to lib/A.v and, without its guard, would grow for ever (FORGED bounds each
        # command).  The guard stops the run with a Fault: a plain run exits DEFECT (5), naming the chain, with no
        # traceback, and --check exits DEFECT, a defect of the generator, which the made-from job of pr.yml fails on (it
        # only warns on 2, a check that cannot decide, and on 3, drift, for a unit that only a change to its proofs
        # names, and its text for 1 says the record differs)
        self.case_cycle()
        self.finish()
        self.forge("origins, cycle = named_origins(u, files, layout.unit)",
                   "origins, cycle = named_origins(u, files, layout.unit)[0], {}")
        chain = "lib/A.v -> lib/B.v returns to lib/A.v"
        rc, out = self.run_plain(timeout=FORGED)
        self.assertEqual(rc, mf.DEFECT, out)
        self.assertIn(mf.FAULT + "at the end of the run, the chain of named origins " + chain, out)
        self.assertNotIn("Traceback", out)
        rc, out = self.check(timeout=FORGED)
        self.assertEqual(rc, mf.DEFECT, out)
        self.assertIn("made_from.py --check: a run stopped on a defect of this generator", out)
        self.assertIn(mf.FAULT + "at the end of the run, the chain of named origins " + chain, out)

    def test_an_uncaught_exception_of_a_run_is_a_defect(self):
        # the scratch checkout's generator forged so that licensed_in_order raises a KeyError, an exception that is no
        # Fault: a plain run exits DEFECT with its traceback, and --check exits DEFECT, printing the run's traceback
        self.case_cycle()
        self.finish()
        self.forge("chain, x = [], p", "chain, x = [], {}[p]")
        rc, out = self.run_plain(timeout=FORGED)
        self.assertEqual(rc, mf.DEFECT, out)
        for says in ("Traceback (most recent call last):", ", in licensed_in_order\n", "KeyError: 'lib/A.v'"):
            self.assertIn(says, out)
        self.assertNotIn(mf.FAULT, out)
        rc, out = self.check(timeout=FORGED)
        self.assertEqual(rc, mf.DEFECT, out)
        for says in ("made_from.py --check: a run stopped on a defect of this generator",
                     "Traceback (most recent call last):", ", in licensed_in_order\n", "KeyError: 'lib/A.v'"):
            self.assertIn(says, out)

    def test_a_cycle_that_the_rule_breaks_and_a_file_left_bare_holds_back(self):
        # lib/A.v -> lib/B.v -> lib/C.v -> lib/A.v: at the stall each file stops waiting for its origin; the rule
        # licenses lib/C.v, and then lib/A.v waits again: lib/B.v, left bare, takes lib/C.v as its origin and is never
        # licensed, so lib/A.v takes lib/B.v's decision.  A run on the output of --apply, where lib/C.v carries
        # Anthropic's lines and the cycle is gone, decides them so, and --check passes.  When lib/A.v did not wait
        # again, the rule decided it, written here
        self.case_broken_cycle()
        rows, _ = self.apply_then_check()
        reason = "ours: written for this test"
        self.assertEqual(rows["lib/C.v"][1:7], ["40", "40", "40", "1.000", "lib/X.v", "made from (block)"])
        self.assertEqual(rows["lib/B.v"][1:], ["0", "0", "10", "0.000", "lib/C.v",
                                               "left bare (overrules made from (named origin))", reason])
        self.assertEqual(rows["lib/A.v"][1:], ["0", "0", "10", "0.000", "-",
                                               "left bare (overrules made from (named origin))", reason])

    def test_a_cycle_with_a_tagged_file_waits_while_the_file_is_tagged(self):
        # lib/A.v -> lib/T.v -> lib/C.v -> lib/A.v, where lib/T.v carries Anthropic's tag alone: at the stall lib/A.v
        # stops waiting for lib/T.v, a tagged origin, and the rule finds it written here; lib/T.v and lib/C.v keep
        # waiting, since a file of their cycle is tagged, so lib/C.v takes lib/A.v's decision, and lib/T.v takes
        # lib/C.v's.  --apply gives lib/T.v the MIT tag, after which lib/A.v names no origin and the cycle is gone; a
        # run on that output decides lib/A.v and lib/C.v the same way, and no longer decides lib/T.v, whose row
        # --check does not compare, so --check passes.  When lib/T.v and lib/C.v stopped waiting too, the rule found
        # lib/C.v borderline, and --check after --apply found it written here
        self.case_tagged_cycle()
        rows, _ = self.apply_then_check()
        self.assertEqual(rows["lib/A.v"][1:], ["0", "0", "10", "0.000", "-", "written here", ""])
        self.assertEqual(rows["lib/T.v"][1:], ["0", "0", "10", "0.000", "-",
                                               "written here (Apache-2.0 OR MIT tag becomes MIT)", ""])
        self.assertEqual(rows["lib/C.v"][1:], ["15", "15", "45", "0.333", "lib/X.v", "written here", ""])

    def test_a_history_row_names_no_tagged_origin_that_the_run_does_not_license(self):
        # lib/B.v, left bare, takes lib/X.v by its history row; its named origin lib/T.v is a tagged file the run finds
        # written here, which --apply gives the MIT tag, after which lib/B.v names no origin: its decision names none
        # either, as the run on the output of --apply decides it, and --check passes
        self.case_history_and_tagged_origin()
        rows, _ = self.apply_then_check()
        self.assertEqual(rows["lib/B.v"][1:], ["0", "0", "10", "0.000", "lib/X.v",
                                               "left bare (overrules made from (history))",
                                               "ours: written for this test"])
        self.assertEqual(rows["lib/T.v"][6], "written here (Apache-2.0 OR MIT tag becomes MIT)")

    def test_a_history_row_comes_before_a_named_origin_when_both_are_licensed(self):
        # lib/P.v's history row names lib/H.v and its named origin is lib/O.v.  Its row fails at the stall, with
        # lib/O.v's; the rule then licenses lib/O.v, and lib/H.v takes it, so A holds both when lib/P.v, deferred, is
        # decided (either): its history row wins (R4), as it does while it waits.  --check compares no `made from` row,
        # so only the row shows the order: with the named origin first, lib/P.v was made from (named origin) lib/O.v
        self.case_history_and_origin()
        rows, _ = self.apply_then_check()
        made = ("(* Modified by Theorem Labs, 2026-11: made from proofs/demo/fuzz_demo/lib/H.v; 10 of its 10 lines of "
                "code are new or changed and 10 lines of the source are left out. *)")
        self.assertEqual(rows["lib/P.v"][1:], ["0", "0", "10", "0.000", "lib/H.v",
                                               "made from (history; it names lib/O.v)", made])

    def test_a_file_left_bare_takes_its_history_row_before_its_named_origin(self):
        # the same tree with lib/P.v left bare: a file left bare never stalls, so its history row waits to the end of
        # the run, where A holds lib/H.v and lib/O.v and either gives it its history source, which its row overrules.
        # With the named origin first, its row overruled made from (named origin) lib/O.v
        self.case_history_and_origin(bare=True)
        rows, _ = self.apply_then_check()
        self.assertEqual(rows["lib/P.v"][1:], ["0", "0", "10", "0.000", "lib/H.v",
                                               "left bare (overrules made from (history; it names lib/O.v))",
                                               "ours: written for this test"])

    def test_case_9_apply_writes_the_origin_s_lines_and_no_made_from_line(self):
        # the origin's licence lines unchanged (a comment over several lines whole), then each of the file's own
        # `Modified by` lines that they do not hold, then its body; for a file with no licence lines, one with
        # `Modified by` lines only (its derive_y line split over lines), and one with Anthropic's tag alone
        same = "(* Modified by Theorem Labs, 2026-10: a change of the source, closed on its line. *)"
        split = ["(* Modified by Theorem Labs, 2026-11: derived from", "   lib/Orig.v of this library by",
                 "   derive_y.py: module names A.Axyz -> AU.Yxyz. *)"]
        a = code("a", 40)
        self.files("", dict(Orig=1, Bare=2, Mod=2, Tag=2), Orig=ANTHROPIC + MULTI + [same] + a,
                   Bare=[relocated("lib/Orig.v")] + a[:10], Mod=[same] + split + [OWN] + a[10:20],
                   Tag=[mf.APACHE_TAG, OWN, relocated("lib/Orig.v")] + a[20:30])
        rows, _ = self.out(apply=True)
        for p in ("lib/Bare.v", "lib/Mod.v", "lib/Tag.v"):
            self.assertEqual(rows[p][1:], ["10", "10", "10", "1.000", "lib/Orig.v", "made from (named origin)", "-"], p)
        head = ANTHROPIC + MULTI + [same]
        self.assertEqual(self.read("lib/Bare.v"), self.text(head, [relocated("lib/Orig.v")], a[:10]))
        self.assertEqual(self.read("lib/Mod.v"), self.text(head, split, [OWN], a[10:20]))
        self.assertEqual(self.read("lib/Tag.v"), self.text(head, [OWN, relocated("lib/Orig.v")], a[20:30]))
        self.assert_a_second_apply_changes_nothing()

    def test_case_10_an_origin_licensed_in_the_same_run(self):
        self.case10()
        rows, _ = self.out(apply=True)
        self.assertEqual(rows["lib/Mid.v"][5:7], ["lib/Src.v", "made from (block)"])
        self.assertEqual(rows["lib/P.v"][1:], ["10", "10", "15", "0.667", "lib/Mid.v", "made from (named origin)", "-"])
        mid = self.read("lib/Mid.v").split("\n")
        self.assertEqual(mid[:2], ANTHROPIC)
        self.assertEqual(self.read("lib/P.v"), self.text(mid[:3], [relocated("lib/Mid.v")], code("m", 10),
                                                         code("p", 5)))

    def test_case_11_an_origin_of_fewer_than_5_distinctive_lines(self):
        # Unit.best gives no source below MIN_D distinctive lines; the row's counts are those of lcs_len
        short = code("a", 3) + ["Proof.", "  lia.", "Qed."]
        self.files("", dict(Orig=1, P=2), Orig=ANTHROPIC + short, P=[derived("lib/Orig.v")] + short)
        rows, _ = self.out()
        self.assertEqual(rows["lib/P.v"][1:], ["6", "3", "6", "1.000", "lib/Orig.v", "made from (named origin)", "-"])

    def test_a_tagged_file_whose_origin_is_left_bare_over_a_source(self):
        # lib/P.v takes lib/O.v's decision, plain `left bare` since its own tag becomes MIT: no run decides it after
        # --apply, so its row is one --check does not compare.  `left bare (overrules made from (block))`, lib/O.v's
        # own decision, is one --check compares, which no run gives again after --apply
        self.case_bare_origin()
        rows, _ = self.apply_then_check()
        reason = "ours: not copied from lib/X.v"
        self.assertEqual(rows["lib/O.v"][1:], ["40", "40", "40", "1.000", "lib/X.v",
                                               "left bare (overrules made from (block))", reason])
        self.assertEqual(rows["lib/P.v"][1:], ["0", "0", "10", "0.000", "-",
                                               "left bare (Apache-2.0 OR MIT tag becomes MIT)", reason])
        self.assertEqual(self.read("lib/P.v"), self.text([mf.MIT_TAG, relocated("lib/O.v")], code("p", 10)))
        self.assertEqual(self.read("lib/O.v"), self.text(code("a", 40)))

    def test_an_origin_that_apply_gives_the_mit_tag(self):
        # lib/O.v carries Anthropic's tag alone and the run finds it written here, so --apply gives it the MIT tag,
        # after which it names no origin: the rule decides lib/P.v, made from lib/X.v, and --apply gives lib/P.v
        # Anthropic's lines, so no run decides it after --apply
        self.case_tagged_origin()
        rows, _ = self.out()
        made = ("(* Modified by Theorem Labs, 2026-11: made from proofs/demo/fuzz_demo/lib/X.v; 10 of its 50 lines of "
                "code are new or changed. *)")
        self.assertEqual(rows["lib/P.v"][1:], ["40", "40", "50", "0.800", "lib/X.v", "made from (block)", made])
        self.assertEqual(rows["lib/O.v"][1:], ["0", "0", "10", "0.000", "-",
                                               "written here (Apache-2.0 OR MIT tag becomes MIT)", ""])
        applied, _ = self.apply_then_check()
        self.assertEqual(applied, rows)
        self.assertEqual(self.read("lib/P.v"), self.text(ANTHROPIC, [made, relocated("lib/O.v")], code("x", 40),
                                                         code("p", 10)))
        self.assertEqual(self.read("lib/O.v"), self.text([mf.MIT_TAG], code("o", 10)))
        self.assert_a_second_apply_changes_nothing()

    def test_a_file_waits_for_a_tagged_origin_that_the_run_licenses(self):
        # lib/P.v names lib/O.v, which carries Anthropic's tag alone: it waits for lib/O.v until the run stalls, and the
        # rule licenses lib/O.v first (40 lines of lib/X.v), so lib/P.v takes it as its named origin, and --apply gives
        # it lib/O.v's lines as written.  After --apply lib/O.v and lib/P.v both carry Anthropic's copyright line, so a
        # run on that output decides neither, and --check passes because it compares no row of either.  When a file
        # stopped waiting for a tagged origin before a stall, lib/P.v was open to the rule from the start, and the rule
        # licensed it first, the stronger (60 lines of lib/X.v): made from (block) lib/X.v
        self.case_tagged_origin_licensed()
        rows, _ = self.apply_then_check()
        made = ("(* Modified by Theorem Labs, 2026-11: made from proofs/demo/fuzz_demo/lib/X.v; 60 lines of the source "
                "are left out. *)")
        self.assertEqual(rows["lib/O.v"][1:], ["40", "40", "40", "1.000", "lib/X.v", "made from (block)", made])
        self.assertEqual(rows["lib/P.v"][1:], ["0", "0", "60", "0.000", "lib/O.v", mf.NAMED, "-"])
        o = self.read("lib/O.v").split("\n")
        self.assertEqual(o[:3], ANTHROPIC + [made])
        self.assertEqual(self.read("lib/P.v"), self.text(o[:3], [relocated("lib/O.v")], code("y", 60)))


class NamedOriginRecord(Cases):
    """The decisions of named origins against --check's exit 3 and --record's refusals.  A `made from ...` row of a
    named origin, or of a history row of a file that names one, and the row of a tagged file whose origin is left bare,
    are decisions --apply carries out: after --apply no run decides the file, so no run gives the row again.  --record
    without --apply refuses to write such a row, and --check reads no difference in such a row, or in a row for its
    path, as drift."""

    def short_origin(self):
        """test_case_11's tree: lib/P.v names lib/Orig.v, whose code is under 5 distinctive lines.  The text of lib/P.v,
        as written."""
        short = code("a", 3) + ["Proof.", "  lia.", "Qed."]
        self.files("", dict(Orig=1, P=2), Orig=ANTHROPIC + short, P=[derived("lib/Orig.v")] + short)
        return self.read("lib/P.v")

    def test_made_from_rows_of_a_named_origin_are_not_given_again(self):
        # case 8's run gives lib/Q.v `made from (named origin)` and lib/P.v `made from (history; it names
        # lib/Orig.v)`.  --apply gives each file licence lines, after which no run decides it: neither row is one a
        # run gives again, and --check does not compare it
        self.case8()
        rows, _ = self.out()
        self.assertEqual(rows["lib/Q.v"][6], mf.NAMED)
        self.assertEqual(rows["lib/P.v"][6], "made from (history; it names lib/Orig.v)")
        for p in ("lib/Q.v", "lib/P.v"):
            row = "\t".join(rows[p])
            self.assertFalse(mf.given_again(row), row)
            self.assertFalse(mf.regenerable(row), row)

    def test_record_refusal_unwritten_named_origin(self):
        # the record holds its header alone, so it keeps no row for lib/P.v, which the run finds made from its named
        # origin.  --record without --apply would write that row for a file with no licence lines, and --check would
        # report it on every run: it refuses, and writes nothing
        self.short_origin()
        self.finish()
        self.put(self.layout.record, mf.HEADER + "\n")
        before = self.snapshot()
        rc, out = self.refresh()
        self.assertEqual(rc, 1, out)
        self.assertIn("for a file the record keeps no row for: lib/P.v, decided `made from (named origin)`.", out)
        self.assertEqual(self.snapshot(), before)

    def test_a_named_origin_s_file_that_loses_its_licence_lines(self):
        # after --apply the record keeps lib/P.v's `made from (named origin)` row.  Its licence lines then come off, its
        # text back to what it was before --apply, and a run decides it again, giving that row.  --check exits 1, not
        # drift: the row is one no run gives again.  --record refuses (back), and writes nothing: the run's row in the
        # record would hide that the file lost what --apply wrote
        before = self.short_origin()
        rows, _ = self.apply_then_check()
        self.assertEqual(rows["lib/P.v"][6], mf.NAMED)
        self.assertTrue(mf.ANTHROPIC.search(self.read("lib/P.v")))
        self.put(os.path.join(self.root, "lib/P.v"), before)
        self.assert_check(1, ["+ " + "\t".join(rows["lib/P.v"])])
        snapshot = self.snapshot()
        rc, out = self.refresh()
        self.assertEqual(rc, 1, out)
        self.assertIn("a run decides lib/P.v again, which the record accounts for as a file that carries licence lines",
                      out)
        self.assertEqual(self.snapshot(), snapshot)

    def test_left_bare_rows_and_the_row_of_a_left_bare_file_s_mit_tag(self):
        # case_bare_origin's run gives lib/O.v `left bare (overrules made from (block))`, and lib/P.v, a tagged file
        # that takes lib/O.v's decision, `left bare (Apache-2.0 OR MIT tag becomes MIT)`; lib/L.v, declared, of its own
        # code, is plain `left bare`.  --apply leaves a file left bare as it is, so a run gives its row again.  It
        # gives lib/P.v the MIT tag, after which no run decides lib/P.v: its row starts with `left bare` and is not
        # given again
        self.case_bare_origin()
        self.files("", dict(L=2), L=code("l", 10))
        self.declared.append(("lib/L.v", "ours: written for this test"))
        rows, _ = self.out()
        for p, decision, again in (("lib/L.v", mf.LEFT_BARE, True),
                                   ("lib/O.v", "left bare (overrules made from (block))", True),
                                   ("lib/P.v", "left bare (Apache-2.0 OR MIT tag becomes MIT)", False)):
            with self.subTest(path=p):
                row = "\t".join(rows[p])
                self.assertEqual(rows[p][6], decision)
                self.assertIs(mf.given_again(row), again, row)
                self.assertIs(mf.regenerable(row), again, row)

    def test_record_refusal_unwritten_left_bare_mit_tag(self):
        # the record holds its header alone.  The run gives lib/O.v `left bare (overrules made from (block))`, a row a
        # run gives again, and lib/P.v the MIT tag of a file left bare, a decision --apply carries out, for a file the
        # record keeps no row for.  --record without --apply refuses that row alone, says what the MIT tag cannot tell,
        # and writes nothing
        self.case_bare_origin()
        self.finish()
        self.put(self.layout.record, mf.HEADER + "\n")
        before = self.snapshot()
        rc, out = self.refresh()
        self.assertEqual(rc, 1, out)
        self.assertIn("for a file the record keeps no row for: lib/P.v, decided `left bare (Apache-2.0 OR MIT tag "
                      "becomes MIT)`.", out)
        self.assertIn("A file decided with the MIT tag keeps Anthropic's tag without Anthropic's copyright line", out)
        self.assertNotIn("lib/O.v, decided", out)
        self.assertEqual(self.snapshot(), before)

    def test_drift_a_new_file_beside_a_named_origin_s_applied_row(self):
        # after --apply the record keeps lib/P.v's `made from (named origin)` row, and a run decides lib/P.v no more.
        # A new file of its own code, with no licence lines and no origin, gives a `written here` row the record
        # lacks, for a path the record holds no row for: drift, and the line that says so comes right after that row
        self.short_origin()
        self.apply_then_check()
        self.files("", dict(W=3), W=code("w", 10))
        self.finish()
        self.assert_check(3, ["+ lib/W.v\t0\t0\t10\t0.000\t-\twritten here\t"])

    def test_no_drift_a_written_here_row_for_the_path_of_an_applied_row(self):
        # the record keeps lib/P.v's `made from (named origin)` row, and lib/P.v then loses its licence lines and its
        # derive_y line and holds code of its own, so the run finds it written here.  That `+` row is one a run gives
        # again, but for a path the record holds in a row of another kind: exit 1, not drift, since --record refuses
        # the run's row (back)
        self.short_origin()
        rows, _ = self.apply_then_check()
        self.assertEqual(rows["lib/P.v"][6], mf.NAMED)
        self.write("lib/P.v", code("p", 10))
        self.assert_check(1, ["+ lib/P.v\t0\t0\t10\t0.000\t-\twritten here\t"])


def chains(rows, before):
    """Each `made from` row's chain of sources, followed to a file with Anthropic's lines before the run (before): the
    chains, or AssertionError naming a chain that returns to a file of it or ends elsewhere."""
    source = {p: r[5] for p, r in rows.items() if r[6].startswith("made from")}
    out = {}
    for p in sorted(source):
        chain = [p]
        while chain[-1] in source:
            if source[chain[-1]] in chain:
                raise AssertionError("the chain %s returns to %s" % (chain, source[chain[-1]]))
            chain.append(source[chain[-1]])
        if chain[-1] not in before:
            raise AssertionError("the chain %s ends at a file without Anthropic's lines before the run" % chain)
        out[p] = chain
    return out


class OneAtATime(Cases):
    """The run licenses one file at a time, the strongest first, and a file it licenses is a source for each file
    still undecided (cases 12 to 14)."""

    def test_case_12_a_file_licensed_in_the_run_is_a_source(self):
        # lib/Q.v (31 distinctive lines of lib/R.v) joins first, being the stronger; then lib/P.v, which a run of 6
        # lines of lib/R.v alone makes `made from (run of 6)` lib/R.v, holds lib/Q.v's own block of 40 lines and is
        # made from it.  OSSV-400's generator decided both in its first loop over the files, whose
        # sources were only the files with Anthropic's lines before the run, and did not decide a `made from` file
        # again: lib/P.v was `made from (run of 6)` lib/R.v
        self.case12()
        rows, _ = self.out(apply=True)
        self.assertEqual(rows["lib/Q.v"][1:7], ["31", "31", "71", "0.437", "lib/R.v", "made from (block)"])
        self.assertEqual(rows["lib/P.v"][1:7], ["40", "40", "46", "0.870", "lib/Q.v", "made from (block)"])
        q = self.read("lib/Q.v").split("\n")
        made = ("(* Modified by Theorem Labs, 2026-11: made from proofs/demo/fuzz_demo/lib/Q.v; 6 of its 46 lines of "
                "code are new or changed and 31 lines of the source are left out. *)")
        self.assertEqual(rows["lib/P.v"][7], made)
        self.assertEqual(self.read("lib/P.v"), self.text(q[:3], [made], code("q", 40), code("r", 6)))

    def test_case_13_two_files_that_a_fixpoint_makes_name_each_other(self):
        # lib/P.v and lib/Q.v share a block lib/R.v lacks, and each holds a block of lib/R.v long enough to be made
        # from it.  OSSV-400's generator decided both from lib/R.v in its first loop over the files; a
        # plain loop to a fixpoint, deciding every file again until nothing changes, makes lib/P.v and lib/Q.v name
        # each other here
        self.case13()
        rows, _ = self.out()
        # lib/Q.v's block of lib/R.v is the longer: it joins first, and lib/P.v is made from it
        self.assertEqual(rows["lib/Q.v"][1:7], ["40", "40", "80", "0.500", "lib/R.v", "made from (block)"])
        self.assertEqual(rows["lib/P.v"][1:7], ["40", "40", "72", "0.556", "lib/Q.v", "made from (block)"])
        self.assertEqual(chains(rows, {"lib/R.v"}), {"lib/P.v": ["lib/P.v", "lib/Q.v", "lib/R.v"],
                                                     "lib/Q.v": ["lib/Q.v", "lib/R.v"]})
        # blocks of equal length: the first path is made from lib/R.v, and the other from it
        self.case13(equal=True)
        rows, _ = self.out()
        self.assertEqual(rows["lib/P.v"][1:7], ["40", "40", "80", "0.500", "lib/R.v", "made from (block)"])
        self.assertEqual(rows["lib/Q.v"][1:7], ["40", "40", "80", "0.500", "lib/P.v", "made from (block)"])
        self.assertEqual(chains(rows, {"lib/R.v"}), {"lib/P.v": ["lib/P.v", "lib/R.v"],
                                                     "lib/Q.v": ["lib/Q.v", "lib/P.v", "lib/R.v"]})

    def test_case_14_any_order_of_the_files_gives_the_same_record(self):
        for k, case in (("C1", self.case1), ("C6", self.case6), ("C8", self.case8), ("C10", self.case10),
                        ("C12", self.case12), ("C13", self.case13), ("D1", self.case_bare_origin),
                        ("D2", self.case_tagged_origin), ("F1", self.case_failed_history),
                        ("G1", self.case_late_history), ("G2", self.case_cycle), ("G3", self.case_broken_cycle),
                        ("G4", self.case_history_and_tagged_origin), ("G5", self.case_tagged_cycle),
                        ("G6", self.case_history_and_origin),
                        ("G7", lambda k: self.case_history_and_origin(k, bare=True)),
                        ("G8", self.case_tagged_origin_licensed)):
            case(k)
        # a file named in history-named.tsv whose history source the rule licenses in the run, and which the rule
        # also finds made from a file with Anthropic's lines: its history row waits, then decides it.  On OSSV-400's
        # generator its row was the rule's in path order and the history's in reversed order
        self.files("X", dict(R=1, S=2, T=1, H=2), R=ANTHROPIC + code("xa", 40), S=code("xa", 40),
                   T=ANTHROPIC + code("xb", 40), H=code("xb", 40))
        self.named.append(("lib/XH.v", "lib/XS.v"))
        self.finish()
        with contextlib.redirect_stderr(io.StringIO()):
            first = None
            for order in ("path", "reversed", 1, 2, 3):
                for shortcut in (True, False):
                    with self.subTest(order=order, shortcut=shortcut):
                        got = self.direct(order, shortcut)
                        first = first or got
                        self.assertEqual(got, first)
        result = first[0]
        self.assertEqual(result["lib/XH.v"][4:], ("lib/XS.v", "made from (history)"))
        self.assertEqual(result["lib/XS.v"][4:], ("lib/XR.v", "made from (block)"))
        self.assertEqual(result["lib/C12P.v"][4:], ("lib/C12Q.v", "made from (block)"))
        self.assertEqual(result["lib/C13P.v"][4:], ("lib/C13Q.v", "made from (block)"))
        self.assertEqual(result["lib/C1Copy.v"][4:], ("lib/C1Orig.v", "made from (named origin)"))
        self.assertEqual(result["lib/C10P.v"][4:], ("lib/C10Mid.v", "made from (named origin)"))
        self.assertEqual(result["lib/C8P.v"][4:], ("lib/C8H.v", "made from (history; it names lib/C8Orig.v)"))
        self.assertEqual(result["lib/C6P3.v"][5], "left bare")
        self.assertEqual(result["lib/D1P.v"][4:], (None, "left bare"))
        self.assertEqual(first[3]["lib/D1P.v"], "ours: not copied from lib/D1X.v")
        self.assertEqual(result["lib/D2P.v"][4:], ("lib/D2X.v", "made from (block)"))
        # two files whose history rows fail at one stall, the one's naming the other, and that name an origin: they
        # are decided together against one A, which holds lib/F1R.v and not lib/F1S.v, so both take their origin.
        # Deciding them one at a time, lib/F1P.v took lib/F1S.v by its history row when lib/F1S.v joined first, in
        # reversed order
        self.assertEqual(result["lib/F1P.v"][4:], ("lib/F1R.v", "made from (named origin)"))
        self.assertEqual(result["lib/F1S.v"][4:], ("lib/F1R.v", "made from (named origin)"))
        # a file left bare whose history row still waits at the end: its history source is not licensed, and its
        # origin is
        self.assertEqual(result["lib/F1B.v"], (30, 30, 40, 0.75, "lib/F1R.v",
                                               "left bare (overrules made from (named origin))"))
        self.assertEqual(first[3]["lib/F1B.v"], "ours: not copied from lib/F1R.v")
        # a failed history row, the file's one claim, decides it when the rule licenses its source after the stall
        self.assertEqual(result["lib/G1P.v"][4:], ("lib/G1X.v", "made from (block)"))
        self.assertEqual(result["lib/G1H.v"][4:], ("lib/G1P.v", "made from (block)"))
        self.assertEqual(result["lib/G1Q.v"][4:], ("lib/G1H.v", "made from (history)"))
        # a cycle of named origins: the rule licenses lib/G2A.v, and lib/G2B.v takes it as its origin
        self.assertEqual(result["lib/G2A.v"][4:], ("lib/G2X.v", "made from (block)"))
        self.assertEqual(result["lib/G2B.v"][4:], ("lib/G2A.v", "made from (named origin)"))
        # a cycle that the rule breaks, licensing lib/G3C.v: lib/G3A.v waits again, for lib/G3B.v, left bare, which
        # takes lib/G3C.v; and a file left bare whose history row decides it names no tagged origin that the run
        # does not license
        self.assertEqual(result["lib/G3C.v"][4:], ("lib/G3X.v", "made from (block)"))
        self.assertEqual(result["lib/G3B.v"][4:], ("lib/G3C.v", "left bare (overrules made from (named origin))"))
        self.assertEqual(result["lib/G3A.v"][4:], (None, "left bare (overrules made from (named origin))"))
        self.assertEqual(result["lib/G4B.v"][4:], ("lib/G4X.v", "left bare (overrules made from (history))"))
        # a cycle with a tagged file: lib/G5A.v stops waiting for lib/G5T.v, the tagged file, and the rule finds it
        # written here; lib/G5T.v and lib/G5C.v wait while lib/G5T.v is tagged, and take that decision
        self.assertEqual(result["lib/G5A.v"][4:], (None, "written here"))
        self.assertEqual(result["lib/G5C.v"][4:], ("lib/G5X.v", "written here"))
        self.assertEqual(result["lib/G5T.v"][4:], (None, "written here"))
        # a history source and a named origin both licensed: the history row comes first, for a file deferred and for
        # a file left bare
        self.assertEqual(result["lib/G6P.v"][4:], ("lib/G6H.v", "made from (history; it names lib/G6O.v)"))
        self.assertEqual(result["lib/G7P.v"][4:], ("lib/G7H.v",
                                                   "left bare (overrules made from (history; it names lib/G7O.v))"))
        # a file that waits for a tagged origin, which the rule licenses first: it takes it as its named origin
        self.assertEqual(result["lib/G8P.v"][4:], ("lib/G8O.v", "made from (named origin)"))
        # the command line, in two processes with two hash seeds
        self.assertIn(b"\tmade from (history)\t", self.outs_under_two_hash_seeds())


class Matches(Fixture):
    def test_record_made_before_apply_matches(self):
        # the rows of `made from` and of the tag becoming MIT cannot come again after --apply: they are not compared
        rc, out = self.check()
        self.assertEqual(rc, 0, out)
        self.assertIn("its 2 rows that a run gives again are the run's rows (its other 2 rows", out)

    def test_nothing_written(self):
        before = self.snapshot()
        self.assertEqual(self.check()[0], 0)
        self.assertEqual(before, self.snapshot())


class MatchesWithoutHistory(Matches):
    """The shape of curl/fuzz_bufq's unit file: HISTORY = None, so --check runs with no --history."""
    history = None


class Differs(Fixture):
    def test_file_added_after_the_record(self):
        # the defect cURL found: proof files added, the record not made again.  The run's row is `written here`, for
        # a path the record holds no row for: drift
        self.write("own_new/Proof.v", code("fresh", 3))
        self.assert_check(3, ["+ own_new/Proof.v\t0\t0\t3\t0.000\t-\twritten here\t"])

    def test_correct_row_appended_by_hand(self):
        # the defect fuzz_fnmatch's record had: a proof file added and its row typed in by hand at the end of the
        # record.  The row is the one the generator gives, but it puts it first, among the files sorted by path: the
        # row shows under both signs, and it is one a run gives again, so it is drift
        self.write("asan_new/Proof.v", code("fresh", 3))
        row = "asan_new/Proof.v\t0\t0\t3\t0.000\t-\twritten here\t"
        self.edit_record(lambda rows: rows + [row])
        self.assert_check(3, ["+ " + row, "- " + row])

    def test_row_at_another_place(self):
        mine = self.row("lib/Mine.v")
        self.edit_record(lambda rows: [r for r in rows if r != mine] + [mine])
        self.assert_check(3, ["+ " + mine, "- " + mine])

    def test_row_removed(self):
        mine = self.row("lib/Mine.v")
        self.edit_record(lambda rows: [r for r in rows if r != mine])
        self.assert_check(3, ["+ " + mine])

    def test_row_edited(self):
        own = self.row("lib/Own.v")
        edited = own.replace("\t10\t", "\t11\t", 1)
        self.assertNotEqual(edited, own)
        self.edit_record(lambda rows: [edited if r == own else r for r in rows])
        self.assert_check(3, ["- " + edited, "+ " + own])

    def test_row_for_a_file_that_is_not_there(self):
        gone = "lib/Gone.v\t0\t0\t4\t0.000\t-\twritten here\t"
        self.edit_record(lambda rows: rows + [gone])
        self.assert_check(3, ["- " + gone])

    def test_applied_file_no_longer_applied(self):
        """A file that took Anthropic's lines loses them: a run decides it again, and the output names what the
        reader must weigh before --apply, since the file is only one of the three things that can be wrong.  Exit 1,
        not drift: the run's row is `made from`, a row no run gives again, for a file the record holds as such."""
        copy = self.row("lib/Copy.v")   # the run gives the row that the record holds for the file, byte for byte
        self.write("lib/Copy.v", code("src", 40))
        out = self.assert_check(1, ["+ " + copy])
        self.assertIn("the `+` rows of lib/Copy.v are decisions --apply carries out, and those files do not carry "
                      "what the decision gives them", out)
        for cause in ("never got it (added or newly decided since the record)", "it lost it",
                      "the decision is wrong about the file"):
            self.assertIn(cause, out)

    def test_duplicate_path_check(self):
        """A record holding two rows for one file read as a match, because the run's row was among the rows
        compared and the other was not.  A record says one thing about each file.  The refusal is exit 1, never
        drift: it comes before the rows are compared."""
        own = self.row("lib/Own.v")
        self.edit_record(lambda rows: rows + [own.replace("\twritten here\t", "\tmade from (block)\t")])
        rc, out = self.check()
        self.assertEqual(rc, 1, out)
        self.assertIn("names lib/Own.v twice: a record says one thing about each file of the unit", out)
        self.assertNotIn(DRIFT_SAYS, out)


REASON = "ours: written for this unit"   # the reason of a row of left-bare.tsv


def interleaved(*parts):
    """The lines of parts taken in turn, one of each: two files that share one of these parts share no two
    consecutive lines, so the rule finds no run of RUN lines in them."""
    return [x for group in zip(*parts) for x in group]


class Drift(Fixture):
    """Each kind of row that can differ, on each side, by itself: exit 3 when the record names no path twice, every row
    that differs is one a run gives again (`written here`, `borderline: written here`, `left bare`, `left bare
    (overrules ...)`) and no such row names a path that the record holds in a row of another kind; exit 1 otherwise.

    What no case here can show, and why:
    - a `-` row of `made from ...`, of `... (Apache-2.0 OR MIT tag becomes MIT)`, of `Anthropic-licensed: tag
      Apache-2.0 becomes Apache-2.0 OR MIT` or of `carries licence lines since (was: ...)`, past the record's first
      row: --check compares no such row of the record (regenerable), so it is never a `-` row.  Such rows take part
      through the path rule only (the test_path_rule_ cases).  The record's first row --check takes for the header,
      whatever it holds (test_record_side_header).
    - a `+` row of fewer than 7 columns: a run writes 8 columns in every row.
    - a `+` row of `carries licence lines since (was: ...)`: only --record writes it, never a run.
    - the path rule for a `-` row: past the record's first row, the rows a run gives again are the record's own, and
      a record that names a path twice is refused (exit 1) before any row is compared, so such a `-` row never names
      a path of another row of the record.  A first row that is not the header comes with a `+` header, which is not
      drift by itself.  So the path rule matters only for a `+` row.
    - the path rule with a row of fewer than 7 columns, by itself: --check compares such a row, and it differs from
      every row a run gives, so it is always a `-` row too (test_path_rule_row_of_fewer_than_7_columns)."""

    def setUp(self):
        super().setUp()
        self.times = {"Copy": 2, "Mine": 2, "Own": 2, "Src": 1, "Tag": 2}

    def add(self, stem, lines, time=3):
        """lib/<stem>.v, first added at time (by default after every file of the fixture)."""
        self.write("lib/%s.v" % stem, lines)
        self.times[stem] = time
        self.born(**self.times)

    def declare(self, *paths):
        self.put(self.layout.left_bare_tsv, "path\treason\n" + "".join("%s\t%s\n" % (p, REASON) for p in paths))

    # the record's side: a row of the record that no run gives there

    def test_record_side_written_here(self):
        row = "lib/Gone.v\t0\t0\t4\t0.000\t-\twritten here\t"
        self.record_with(row)
        self.assert_check(3, ["- " + row])

    def test_record_side_borderline(self):
        row = "lib/Gone.v\t15\t15\t45\t0.333\tlib/Src.v\tborderline: written here\t"
        self.record_with(row)
        self.assert_check(3, ["- " + row])

    def test_record_side_left_bare(self):
        row = "lib/Gone.v\t0\t0\t4\t0.000\t-\tleft bare\t" + REASON
        self.record_with(row)
        self.assert_check(3, ["- " + row])

    def test_record_side_left_bare_overrules(self):
        row = "lib/Gone.v\t10\t10\t20\t0.500\tlib/Src.v\tleft bare (overrules made from (share))\t" + REASON
        self.record_with(row)
        self.assert_check(3, ["- " + row])

    def test_record_side_row_of_fewer_than_7_columns(self):
        # no row this generator writes: --check compares it, and it is not drift
        self.record_with("lib/Gone.v\t0\t0\t4\t0.000\t-")
        self.assert_check(1, ["- lib/Gone.v\t0\t0\t4\t0.000\t-"])

    def test_record_side_header(self):
        # --check takes the record's first row for its header, whatever it holds, and the run's header is no row a run
        # gives again: a header that is not the generator's, whatever its column 7 holds, `written here` included, or
        # a record with no header, is not drift
        rows = mf.rows_of(self.record)
        copy, mine, own = self.row("lib/Copy.v"), self.row("lib/Mine.v"), self.row("lib/Own.v")
        renamed = mf.HEADER.replace("\tdecision\t", "\tverdict\t")
        written = mf.HEADER.replace("\tdecision\t", "\twritten here\t")
        for case, record, signed in (("another column 7", [renamed] + rows[1:], ["- " + renamed, "+ " + mf.HEADER]),
                                     ("a column 7 of written here", [written] + rows[1:],
                                      ["- " + written, "+ " + mf.HEADER]),
                                     ("no header", rows[1:], ["- " + copy, "+ " + mf.HEADER]),
                                     ("no header, and a first row a run gives", [mine, own], ["+ " + mf.HEADER])):
            with self.subTest(case=case):
                self.edit_record(lambda _rows, record=record: record)
                self.assert_check(1, signed)

    # the run's side: a row that the run gives and the record does not hold there

    def test_run_side_written_here(self):
        self.add("New", code("new", 3))
        self.assert_check(3, ["+ lib/New.v\t0\t0\t3\t0.000\t-\twritten here\t"])

    def test_run_side_borderline(self):
        # 15 of its 45 lines are the source's, one at a time: share 0.333, below SHARE and above BORDER
        self.add("Near", interleaved(code("src", 15), code("near", 15), code("nearb", 15)))
        self.assert_check(3, ["+ lib/Near.v\t15\t15\t45\t0.333\tlib/Copy.v\tborderline: written here\t"])

    def test_run_side_left_bare(self):
        self.add("New", code("new", 3))
        self.declare("lib/New.v")
        self.assert_check(3, ["+ lib/New.v\t0\t0\t3\t0.000\t-\tleft bare\t" + REASON])

    def test_run_side_left_bare_overrules(self):
        self.add("Bare", code("src", 40) + code("bare", 40))
        self.declare("lib/Bare.v")
        self.assert_check(3, ["+ lib/Bare.v\t40\t40\t80\t0.500\tlib/Copy.v\tleft bare (overrules made from (block))\t"
                              + REASON])

    def test_run_side_made_from_block(self):
        self.add("Fresh", code("src", 40))
        self.assert_check(1, ["+ lib/Fresh.v\t40\t40\t40\t1.000\tlib/Copy.v\tmade from (block)\t(* Modified by "
                              "Theorem Labs, 2026-11: copied from proofs/demo/fuzz_demo/lib/Copy.v, with only its "
                              "comments or blank lines changed. *)"])

    def test_run_side_made_from_share(self):
        # 10 of its 20 lines are the source's, one at a time: share 0.5, with no block and no run
        self.add("Half", interleaved(code("src", 10), code("half", 10)))
        self.assert_check(1, ["+ lib/Half.v\t10\t10\t20\t0.500\tlib/Copy.v\tmade from (share)\t(* Modified by "
                              "Theorem Labs, 2026-11: made from proofs/demo/fuzz_demo/lib/Copy.v; 10 of its 20 lines "
                              "of code are new or changed and 30 lines of the source are left out. *)"])

    def test_run_side_made_from_run(self):
        # 8 consecutive lines of the source, then 20 of its own: share 0.286, below SHARE
        self.add("Run", code("src", 8) + code("runs", 20))
        self.assert_check(1, ["+ lib/Run.v\t8\t8\t28\t0.286\tlib/Copy.v\tmade from (run of 8)\t(* Modified by "
                              "Theorem Labs, 2026-11: made from proofs/demo/fuzz_demo/lib/Copy.v; 20 of its 28 lines "
                              "of code are new or changed and 32 lines of the source are left out. *)"])

    def test_run_side_made_from_history(self):
        self.add("Named", code("named", 5))
        self.put(self.layout.history, "path\tsource\nlib/Named.v\tlib/Src.v\n")
        self.assert_check(1, ["+ lib/Named.v\t0\t0\t5\t0.000\tlib/Src.v\tmade from (history)\t(* Modified by "
                              "Theorem Labs, 2026-11: made from proofs/demo/fuzz_demo/lib/Src.v; 5 of its 5 lines of "
                              "code are new or changed and 40 lines of the source are left out. *)"])

    def test_run_side_mit_tag(self):
        self.add("Tagged", [mf.APACHE_TAG] + code("tagged", 10))
        self.assert_check(1, ["+ lib/Tagged.v\t0\t0\t10\t0.000\t-\twritten here (Apache-2.0 OR MIT tag becomes MIT)\t"])

    def test_run_side_tag_pass(self):
        self.add("Old", [ANTHROPIC[0], mf.BUNDLE_TAG] + code("old", 10), time=1)
        self.assert_check(1, ["+ lib/Old.v\t-\t-\t-\t-\t-\tAnthropic-licensed: tag Apache-2.0 becomes Apache-2.0 OR "
                              "MIT\t"])

    # the path rule: a `+ written here` row, by itself a row a run gives again, for a file that the record holds in a
    # row of another kind

    def test_path_rule_made_from_row(self):
        self.write("lib/Copy.v", code("fresh", 9))
        self.assert_check(1, ["+ lib/Copy.v\t0\t0\t9\t0.000\t-\twritten here\t"])

    def test_path_rule_stamped_row(self):
        self.write("lib/Own.v", ANTHROPIC + code("own", 10))
        self.assertEqual(self.refresh()[0], 0)
        self.assertEqual(self.row("lib/Own.v").split("\t")[6], "carries licence lines since (was: written here)")
        self.write("lib/Own.v", code("own", 10))
        self.assert_check(1, ["+ lib/Own.v\t0\t0\t10\t0.000\t-\twritten here\t"])

    def test_path_rule_mit_tag_row(self):
        self.write("lib/Tag.v", code("tag", 10))
        self.assert_check(1, ["+ lib/Tag.v\t0\t0\t10\t0.000\t-\twritten here\t"])

    def test_path_rule_tag_pass_row(self):
        self.add("Old", [ANTHROPIC[0], mf.BUNDLE_TAG] + code("old", 10), time=1)
        self.assertEqual(self.refresh("--apply")[0], 0)
        self.assertEqual(self.row("lib/Old.v").split("\t")[6],
                         "Anthropic-licensed: tag Apache-2.0 becomes Apache-2.0 OR MIT")
        self.write("lib/Old.v", code("old", 10))
        self.assert_check(1, ["+ lib/Old.v\t0\t0\t10\t0.000\t-\twritten here\t"])

    def test_path_rule_row_of_fewer_than_7_columns(self):
        self.record_with("lib/Late.v\t0")
        self.add("Late", code("late", 4))
        self.assert_check(1, ["- lib/Late.v\t0", "+ lib/Late.v\t0\t0\t4\t0.000\t-\twritten here\t"])

    # a row at another place, and both kinds together

    def test_moved_row(self):
        # a `left bare` row moved to the end of the record by hand: it shows under both signs, and it is drift
        self.add("New", code("new", 3))
        self.declare("lib/New.v")
        self.assertEqual(self.refresh()[0], 0)
        new = self.row("lib/New.v")
        self.assertEqual(new, "lib/New.v\t0\t0\t3\t0.000\t-\tleft bare\t" + REASON)
        self.edit_record(lambda rows: [r for r in rows if r != new] + [new])
        self.assert_check(3, ["+ " + new, "- " + new])

    def test_compared_and_other_rows_together(self):
        self.add("New", code("new", 3))
        self.add("Fresh", code("src", 40))
        self.assert_check(1, ["+ lib/Fresh.v\t40\t40\t40\t1.000\tlib/Copy.v\tmade from (block)\t(* Modified by "
                              "Theorem Labs, 2026-11: copied from proofs/demo/fuzz_demo/lib/Copy.v, with only its "
                              "comments or blank lines changed. *)",
                              "+ lib/New.v\t0\t0\t3\t0.000\t-\twritten here\t"])


class MissingInput(Fixture):
    """An input that is missing or cannot be read, and oft lint's lexer when it does not load, is refused with exit 4,
    naming it, before any run and before any write, by --check and by a run alike.  A run left to fail on such an
    input would stop on an uncaught exception, which --check reports as a defect of the generator (exit 5) without
    naming the input; the refusal names it as what to fix."""
    # oft lint's lexer as a change could leave it, there and UTF-8 and not loading: (what it is, its text, what the
    # refusal says of it after "tools/oft/rocq.py cannot be loaded: ")
    BROKEN_LEXERS = (("a syntax error", "def tokens(:\n", "SyntaxError: "),
                     ("an error while it loads", "raise ValueError('no lexer here')\n", "ValueError: no lexer here"),
                     ("an exit while it loads", "import sys\nsys.exit(1)\n", "SystemExit: 1"),
                     ("no tokens", "def code(text):\n    return text\n", "ImportError: it has no callable tokens"),
                     ("tokens that is no function", "tokens = ()\n", "ImportError: it has no callable tokens"))

    def refused(self, how, says):
        """how() (check, run_plain, refresh, a cli call, or call or apply in this process) exits 4, its output holding
        says, and writes no file."""
        before = self.snapshot()
        rc, out = how()
        self.assertEqual(rc, 4, out)
        self.assertIn(says, out)
        self.assertEqual(self.snapshot(), before)
        return out

    @contextlib.contextmanager
    def away(self, rel):
        """rel moved out of the way, and back after."""
        path = os.path.join(self.top, rel)
        os.rename(path, path + ".away")
        try:
            yield
        finally:
            os.rename(path + ".away", path)

    @contextlib.contextmanager
    def lexer(self, text):
        """oft lint's lexer replaced by text, and back after; its bytecode cache taken away before and after, so each
        load reads the text it is given."""
        cache = os.path.join(self.top, os.path.dirname(mf.LEXER), "__pycache__")
        with self.away(mf.LEXER):
            shutil.rmtree(cache, ignore_errors=True)
            self.put(mf.LEXER, text)
            try:
                yield
            finally:
                os.remove(os.path.join(self.top, mf.LEXER))
                shutil.rmtree(cache, ignore_errors=True)

    def append(self, rel, data):
        with open(os.path.join(self.top, rel), "ab") as f:
            f.write(data)

    def remove_proofs(self):
        for p in mf.Unit(self.top, self.layout).files:
            os.remove(os.path.join(self.top, self.root, p))

    def put_bad_proof_file(self):
        with open(os.path.join(self.top, self.root, "lib/Bad.v"), "wb") as f:
            f.write(b"(* Copyright 2026 Anthropic PBC *)\n\xff\xfe not utf-8\n")

    def test_check_missing_input(self):
        # the record, first-added.tsv, the unit's HISTORY file, the images' dune file and oft lint's lexer
        for rel in (self.layout.record, self.layout.first_added, self.layout.history, self.layout.images_dune,
                    mf.LEXER):
            with self.subTest(missing=rel), self.away(rel):
                self.refused(self.check, "made_from.py --check: refusing the check: %s is missing" % rel)
        self.assertEqual(self.check()[0], 0)

    def test_check_missing_proofs_folder(self):
        # the record and the history outside the proofs folder, and a unit file at a unit's path in a second
        # checkout, since the unit file lives in the proofs folder
        record, history = os.path.join(self.top, "record.tsv"), os.path.join(self.top, "history.tsv")
        shutil.copy(self.record, record)
        self.put("history.tsv", "path\tsource\n")
        other = tempfile.mkdtemp(prefix="made_from-test-other-")
        self.addCleanup(shutil.rmtree, other)
        shutil.copytree(os.path.join(self.top, "dev"), os.path.join(other, "dev"))
        unit_file = os.path.join(other, self.licence, "made_from.py")
        os.makedirs(os.path.dirname(unit_file))
        shutil.copy(self.unit_file, unit_file)
        shutil.rmtree(os.path.join(self.top, self.root))
        out = self.refused(lambda: self.cli("--check", "--top", self.top, record, "--history", history,
                                            script=unit_file), "made_from.py --check: refusing the check: ")
        # first-added.tsv, which is in the proofs folder, is missing too: the refusal names every input it lacks
        self.assertIn("%s is missing" % self.root, out.strip().split("refusing the check: ", 1)[1].split("; "))

    def test_check_proofs_folder_without_a_v_file(self):
        # a checkout that holds the licence folder and none of the unit's proofs (a sparse checkout)
        self.remove_proofs()
        self.refused(self.check, "refusing the check: %s holds no .v file outside provenance/: this checkout does "
                                 "not hold the unit's proofs" % self.root)

    def test_check_record_that_is_a_folder(self):
        os.remove(self.record)
        os.mkdir(self.record)
        self.refused(self.check, "refusing the check: %s cannot be read: " % self.layout.record)

    def test_check_record_not_utf8(self):
        self.append(self.layout.record, b"lib/Own.v\t0\t0\t10\t0.000\t-\twritten here\tcaf\xe9\n")
        self.refused(self.check, "refusing the check: %s cannot be read: 'utf-8' codec can't decode byte 0xe9"
                     % self.layout.record)

    def test_check_malformed_first_added_line(self):
        self.append(self.layout.first_added, b"lib/Late.v\n")
        self.refused(self.check, "refusing the check: %s cannot be read: line 7 is not a path, a tab and a commit "
                                 "time: 'lib/Late.v'" % self.layout.first_added)

    def test_check_malformed_history_row(self):
        # the row a run once failed on, which --check reported as a check that cannot decide
        self.put(self.layout.history, "path\tsource\nlib/Own.v\n")
        self.refused(self.check, "refusing the check: %s cannot be read: line 2 is not a path, a tab and a source: "
                                 "'lib/Own.v'" % self.layout.history)

    def test_check_proof_file_not_utf8(self):
        self.put_bad_proof_file()
        self.refused(self.check, "refusing the check: %s/lib/Bad.v cannot be read: 'utf-8' codec can't decode"
                     % self.root)

    def test_check_no_file_with_anthropic_s_copyright_line(self):
        # every file that carried Anthropic's lines (lib/Src.v, and lib/Copy.v since --apply) has lost them.  A
        # run is not refused for it: that refusal is --check's alone
        self.write("lib/Src.v", code("src", 40))
        self.write("lib/Copy.v", code("src", 40))
        self.refused(self.check, "refusing the check: %s holds 5 .v file(s) outside provenance and none with "
                                 "Anthropic's copyright line: this checkout does not hold the unit's proofs, or "
                                 "every file lost that line" % self.root)
        rc, out = self.run_plain()
        self.assertEqual(rc, 0, out)

    def test_run_missing_input(self):
        # first-added.tsv, the --history given and the images' dune file (the lexer: Writes.test_missing_lexer)
        for rel in (self.layout.first_added, self.layout.history, self.layout.images_dune):
            with self.subTest(missing=rel), self.away(rel):
                self.refused(self.run_plain, "made_from.py: refusing the run: %s is missing" % rel)
        self.assertEqual(self.run_plain()[0], 0)

    def test_check_lexer_that_does_not_load(self):
        # in this process too, as the cases that patch main() run it: the lexer loaded before stays the one
        # comment_end and unclosed call
        loaded = mf.ROCQ
        for name, text, why in self.BROKEN_LEXERS:
            with self.subTest(lexer=name), self.lexer(text):
                says = "made_from.py --check: refusing the check: %s cannot be loaded: %s" % (mf.LEXER, why)
                self.refused(self.check, says)
                self.refused(lambda: self.call("--check", "--top", self.top), says)
                self.assertIs(mf.ROCQ, loaded)
        self.assertEqual(mf.unclosed("(* never closed"), "comment")
        self.assertEqual(self.check()[0], 0)

    def test_run_lexer_that_does_not_load(self):
        loaded = mf.ROCQ
        for name, text, why in self.BROKEN_LEXERS:
            with self.subTest(lexer=name), self.lexer(text):
                says = "made_from.py: refusing the run: %s cannot be loaded: %s" % (mf.LEXER, why)
                self.refused(self.run_plain, says)
                self.refused(self.apply, says)
                self.assertIs(mf.ROCQ, loaded)
        self.assertEqual(mf.unclosed("(* never closed"), "comment")
        self.assertEqual(self.run_plain()[0], 0)

    def test_run_proofs_folder_without_a_v_file(self):
        self.remove_proofs()
        self.refused(self.run_plain, "refusing the run: %s holds no .v file outside provenance/" % self.root)

    def test_run_proof_file_not_utf8(self):
        self.put_bad_proof_file()
        self.refused(self.run_plain, "refusing the run: %s/lib/Bad.v cannot be read: 'utf-8' codec can't decode"
                     % self.root)

    def test_refresh_without_its_record(self):
        # a refresh keeps the rows of the record no run gives again: without the record it would drop every row
        # --apply wrote
        os.remove(self.record)
        for extra in ([], ["--apply"]):
            with self.subTest(extra=extra):
                self.refused(lambda: self.refresh(*extra), "refusing the run: %s is missing" % self.layout.record)


class SecondRun(Fixture):
    """--check in this process, with its second run a script of the case's in place of the unit file (and its first,
    when the case gives one)."""

    def check_with(self, script, first=None):
        """(exit code, output) of --check in this process, its second run the Python script `script` and its first
        the Python script `first`, or the unit file's own run when first is None; a script runs with OUT, then the
        unit file's own command line (the unit file, --top, the top, OUT, --history)."""
        calls, real = [], mf.generate

        def generate(layout, top, history, out):
            calls.append(out)
            run = first if len(calls) == 1 else script
            if run is None:
                return real(layout, top, history, out)
            return subprocess.Popen([sys.executable, "-c", run, out, layout.unit_file, "--top", top, out]
                                    + (["--history", history] if history else []),
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

        with mock.patch.object(mf, "generate", generate):
            rc, out = self.call("--check", "--top", self.top)
        self.assertEqual(len(calls), 2)
        return rc, out


class CannotDecide(SecondRun):
    """--check exits 2 when every input is there and read, and a run fails for a cause outside the generator's code:
    it refuses (a sys.exit of its own), it is killed by a signal, or it cannot start.  A defect of the generator's own
    code is DEFECT, 5 (Defect)."""

    def test_run_fails(self):
        # the second of the two runs refuses, exiting 1 with its message, or is killed by SIGKILL (the memory guard's)
        for script, says in (("import sys; sys.exit('a run that fails')", "a run exited 1:\na run that fails"),
                             ("import os, signal; os.kill(os.getpid(), signal.SIGKILL)",
                              "a run was killed by signal %d:" % signal.SIGKILL)):
            with self.subTest(script=script):
                rc, out = self.check_with(script)
                self.assertEqual(rc, 2, out)
                self.assertIn("made_from.py --check: cannot decide: " + says, out)

    def test_a_run_that_cannot_start(self):
        def generate(layout, top, history, out):
            raise OSError("no run starts")

        with mock.patch.object(mf, "generate", generate):
            rc, out = self.call("--check", "--top", self.top)
        self.assertEqual(rc, 2, out)
        self.assertIn("made_from.py --check: cannot decide: a run cannot start, or its OUT cannot be read: no run "
                      "starts", out)


class Defect(SecondRun):
    """--check exits DEFECT (5) for a defect of the generator's own code, read from its runs' exit codes and OUT files:
    a run exits 0 and writes no OUT, writes an OUT that is not UTF-8, or the two runs differ; and when the check itself
    stops on an uncaught exception.  A run that stops on a Fault or another uncaught exception exits DEFECT, and --check
    with it (NamedOrigin's test_a_chain_of_named_origins_that_returns_to_its_file_is_a_fault and
    test_an_uncaught_exception_of_a_run_is_a_defect), whatever the other run does."""

    def test_run_fails(self):
        # the second of the two runs exits 0 and writes no OUT, or writes an OUT that is not UTF-8
        for script, says in (("pass", "a run exited 0 and wrote no OUT, a defect of this generator"),
                             ("import sys; open(sys.argv[1], 'wb').write(b'path\\xff\\n')",
                              "a run wrote an OUT that is not UTF-8, a defect of this generator")):
            with self.subTest(script=script):
                rc, out = self.check_with(script)
                self.assertEqual(rc, mf.DEFECT, out)
                self.assertIn("made_from.py --check: " + says, out)

    def test_two_runs_differ(self):
        # the second of the two runs gives one row more than the first
        rc, out = self.check_with(
            "import subprocess, sys; subprocess.run([sys.executable] + sys.argv[2:], check=True); "
            "open(sys.argv[1], 'a').write('lib/Extra.v\\t0\\t0\\t1\\t0.000\\t-\\twritten here\\t\\n')")
        self.assertEqual(rc, mf.DEFECT, out)
        self.assertIn("made_from.py --check: its two runs on the same tree differ, a defect of this generator", out)
        self.assertIn("\n+ lib/Extra.v\t", out)

    def test_a_defect_wins_over_a_refusal(self):
        # the first run refuses (exit 1, which alone gives 2) and the second exits DEFECT: --check reads both runs for
        # a defect before it reads either for another failure, so the defect is not passed over as a check that cannot
        # decide
        rc, out = self.check_with("import sys; sys.exit(%d)" % mf.DEFECT,
                                  first="import sys; sys.exit('a run that refuses')")
        self.assertEqual(rc, mf.DEFECT, out)
        self.assertIn("made_from.py --check: a run stopped on a defect of this generator", out)

    def test_an_uncaught_exception_of_the_check(self):
        # the check itself raises an exception that is no Fault, here where it reads its inputs
        with mock.patch.object(mf, "read_inputs", side_effect=RuntimeError("a defect of the check")):
            rc, out = self.call("--check", "--top", self.top)
        self.assertEqual(rc, mf.DEFECT, out)
        self.assertIn("Traceback (most recent call last):", out)
        self.assertIn("RuntimeError: a defect of the check", out)


class CheckC2(Fixture):
    """The cases of check C2 of OSSV-348, one each: the exit of --check by what differs, and by what it cannot read
    or run.  A refusal (4) and a check that cannot decide (2) come before the rows are compared, so on a tree whose
    record differs only in drift neither gives 0 or 3: each case that shows one ends with the check of that tree,
    which is 3."""
    NEW = "lib/New.v\t0\t0\t3\t0.000\t-\twritten here\t"   # the run's row for the file drift() adds

    def drift(self):
        """Make the record differ from a run only in drift: a file added since, which the run finds written here."""
        self.write("lib/New.v", code("new", 3))

    def assert_not_0_or_3(self, rc, out):
        self.assertNotIn(rc, (0, 3), out)
        self.assertNotIn(DRIFT_SAYS, out)

    def test_c2_compared_rows_only_exits_3(self):
        # a row of the record for a file that is not there, a row edited by hand, and a file added since
        gone = "lib/Gone.v\t0\t0\t4\t0.000\t-\twritten here\t"
        own = self.row("lib/Own.v")
        edited = own.replace("\t10\t", "\t11\t", 1)
        self.edit_record(lambda rows: [edited if r == own else r for r in rows])
        self.record_with(gone)
        self.drift()
        self.assert_check(3, ["- " + gone, "- " + edited, "+ " + self.NEW, "+ " + own])

    def test_c2_made_from_path_decided_written_here_exits_1(self):
        # the record holds lib/Copy.v as `made from`; the file at that path is now another file, which the run finds
        # written here.  That row is one a run gives again, but a refresh would not take it (--record refuses it)
        self.write("lib/Copy.v", code("fresh", 9))
        self.assert_check(1, ["+ lib/Copy.v\t0\t0\t9\t0.000\t-\twritten here\t"])

    def test_c2_new_file_decided_made_from_exits_1(self):
        self.write("lib/Fresh.v", code("src", 40))
        self.born(Copy=2, Fresh=3, Mine=2, Own=2, Src=1, Tag=2)
        self.assert_check(1, ["+ lib/Fresh.v\t40\t40\t40\t1.000\tlib/Copy.v\tmade from (block)\t(* Modified by "
                              "Theorem Labs, 2026-11: copied from proofs/demo/fuzz_demo/lib/Copy.v, with only its "
                              "comments or blank lines changed. *)"])

    def test_c2_difference_in_both_kinds_of_rows_exits_1(self):
        # a row of the record that a run gives again, and a row of the tag pass, which no run gives again once
        # --apply has written the file
        gone = "lib/Gone.v\t0\t0\t4\t0.000\t-\twritten here\t"
        self.record_with(gone)
        self.write("lib/Old.v", [ANTHROPIC[0], mf.BUNDLE_TAG] + code("old", 10))
        self.born(Copy=2, Mine=2, Old=1, Own=2, Src=1, Tag=2)
        self.assert_check(1, ["- " + gone, "+ lib/Old.v\t-\t-\t-\t-\t-\tAnthropic-licensed: tag Apache-2.0 becomes "
                                           "Apache-2.0 OR MIT\t"])

    def test_c2_missing_input_exits_4(self):
        # a missing input is refused (REFUSED, 4) before any run, so the check cannot be 0 or 3
        self.drift()
        first_added = os.path.join(self.top, self.layout.first_added)
        os.rename(first_added, first_added + ".away")
        rc, out = self.check()
        self.assertEqual(rc, 4, out)
        self.assertEqual(rc, mf.REFUSED)
        self.assert_not_0_or_3(rc, out)
        self.assertIn("made_from.py --check: refusing the check: %s is missing" % self.layout.first_added, out)
        os.rename(first_added + ".away", first_added)
        self.assert_check(3, ["+ " + self.NEW])

    def test_c2_run_that_fails_exits_2(self):
        # the second of the two runs exits non-zero: the check cannot decide, so it cannot be 0 or 3
        self.drift()
        real, calls = mf.generate, []

        def generate(layout, top, history, out):
            calls.append(out)
            if len(calls) == 1:
                return real(layout, top, history, out)
            return subprocess.Popen([sys.executable, "-c", "import sys; sys.exit('a run that fails')"],
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

        with mock.patch.object(mf, "generate", generate):
            rc, out = self.call("--check", "--top", self.top)
        self.assertEqual(len(calls), 2)
        self.assertEqual(rc, 2, out)
        self.assert_not_0_or_3(rc, out)
        self.assertIn("made_from.py --check: cannot decide: a run exited 1:\na run that fails", out)
        self.assert_check(3, ["+ " + self.NEW])

    def test_c2_refused_unit_file_exits_4(self):
        # a unit file that holds code is refused (REFUSED, 4) before any other file is read
        self.drift()
        good = unit_file_text(self.unit, self.donors, self.history)
        self.put_unit_file(good.replace("DONORS = ", "import os\nDONORS = "))
        rc, out = self.check()
        self.assertEqual(rc, 4, out)
        self.assert_not_0_or_3(rc, out)
        self.assertIn("refusing the unit file", out)
        self.assertIn("an import", out)
        self.put_unit_file(good)
        self.assert_check(3, ["+ " + self.NEW])


class Record(Fixture):
    """--record: a record brought up to date keeps the rows of what --apply wrote and takes the run's for the rest."""

    def test_refresh_after_a_file_is_added(self):
        self.write("own_new/Proof.v", code("fresh", 3))
        self.assert_check(3, ["+ own_new/Proof.v\t0\t0\t3\t0.000\t-\twritten here\t"])
        rc, out = self.refresh()
        self.assertEqual(rc, 0, out)
        self.assertIn("2 rows kept of files that carry licence lines", out)
        paths = [r[0] for r in self.rows()]
        self.assertEqual(self.decisions()["lib/Copy.v"], "made from (block)")             # kept
        self.assertEqual(self.decisions()["own_new/Proof.v"], "written here")             # the run's
        self.assertEqual(paths, sorted(paths))                                             # in path order
        self.assertEqual(self.check()[0], 0)

    def test_refresh_sorts_by_path_and_a_plain_run_does_not(self):
        self.write("lib/Old.v", [ANTHROPIC[0], mf.BUNDLE_TAG] + code("old", 10))
        self.born(Copy=2, Mine=2, Old=1, Own=2, Src=1, Tag=2)
        rc, out = self.run_plain()
        self.assertEqual(rc, 0, out)
        plain = [r[0] for r in self.rows(os.path.join(self.top, "out.tsv"))]
        self.assertEqual(plain, ["lib/Mine.v", "lib/Own.v", "lib/Old.v"])   # decided files, then the tag pass's
        self.assertEqual(self.refresh("--apply")[0], 0)
        paths = [r[0] for r in self.rows()]
        self.assertEqual(paths, sorted(paths))
        self.assertIn("lib/Old.v", paths)

    def test_refresh_changes_no_file(self):
        before = {p: t for p, t in self.snapshot().items() if not p.endswith(".tsv")}
        self.assertEqual(self.refresh()[0], 0)
        after = {p: t for p, t in self.snapshot().items() if not p.endswith(".tsv")}
        self.assertEqual(before, after)

    def test_record_refusal_back(self):
        """The record says lib/Copy.v took Anthropic's lines and the file no longer carries them: a refresh that took
        the run's row would hide it, and --check would pass.  --check exits 1, not drift: the run's row is `made
        from`, a row no run gives again."""
        copy = self.row("lib/Copy.v")   # the run gives the row that the record holds for the file, byte for byte
        self.write("lib/Copy.v", code("src", 40))
        before = self.record_bytes()
        rc, out = self.refresh()
        self.assertEqual(rc, 1, out)
        self.assertIn("a run decides lib/Copy.v again, which the record accounts for as a file that carries "
                      "licence lines", out)
        self.assertEqual(self.record_bytes(), before)
        self.assert_check(1, ["+ " + copy])

    def test_record_refusal_undone(self):
        """Declaring a file whose row says --apply wrote it, and stripping the file, must not let a refresh rewrite
        that row to `left bare`: undoing an --apply decision is a person's to do by hand."""
        self.write("lib/Copy.v", code("src", 40))
        self.put(self.layout.left_bare_tsv, "path\treason\nlib/Copy.v\tours, or so this row would claim\n")
        before = self.record_bytes()
        rc, out = self.refresh()
        self.assertEqual(rc, 1, out)
        self.assertIn("declares lib/Copy.v, whose row of this record says --apply wrote the file", out)
        self.assertEqual(self.record_bytes(), before)

    def test_record_refusal_unwritten(self):
        """--record must not write a `made from` row for a file that carries no licence lines: --check reports such
        a row for ever."""
        self.write("lib/Fresh.v", code("src", 40))
        self.born(Copy=2, Fresh=3, Mine=2, Own=2, Src=1, Tag=2)
        before = self.record_bytes()
        rc, out = self.refresh()
        self.assertEqual(rc, 1, out)
        self.assertIn("without --apply, this run gives the row of a decision --apply carries out for a file the record "
                      "keeps no row for: lib/Fresh.v, decided `made from (block)`.", out)
        self.assertEqual(self.record_bytes(), before)

    def write_tagged(self):
        """lib/Tagged.v: Anthropic's tag and no copyright line, a file the record holds no row for."""
        self.write("lib/Tagged.v", [mf.APACHE_TAG] + code("tagged", 10))
        self.born(Copy=2, Mine=2, Own=2, Src=1, Tag=2, Tagged=3)

    def test_record_refusal_unwritten_mit_tag(self):
        """--record alone must not write the row of a tag that becomes MIT, for a file it does not write: that row is
        one --apply carries out, and no run gives it again, so --check would report it on every run."""
        self.write_tagged()
        before = self.snapshot()
        rc, out = self.refresh()
        self.assertEqual(rc, 1, out)
        self.assertIn("without --apply, this run gives the row of a decision --apply carries out for a file the record "
                      "keeps no row for: lib/Tagged.v, decided `written here (Apache-2.0 OR MIT tag becomes MIT)`.",
                      out)
        self.assertEqual(self.snapshot(), before)

    def test_apply_record_writes_the_mit_tag_and_takes_its_row(self):
        # the same tree with --apply: the run writes the file, and the record keeps no row for it, so the refusal does
        # not count it
        self.write_tagged()
        rc, out = self.refresh("--apply")
        self.assertEqual(rc, 0, out)
        self.assertTrue(self.read("lib/Tagged.v").startswith(mf.MIT_TAG + "\n"))
        self.assertTrue(self.row("lib/Tagged.v").split("\t")[6].endswith("(Apache-2.0 OR MIT tag becomes MIT)"))
        self.assertEqual(self.check()[0], 0)

    def test_record_refusal_unwritten_tag_pass(self):
        """The tag pass: a file with Anthropic's copyright line and the tag `Apache-2.0` alone.  Its row is one
        --apply carries out, so --record alone refuses it and writes nothing."""
        self.write("lib/Old.v", [ANTHROPIC[0], mf.BUNDLE_TAG] + code("old", 10))
        self.born(Copy=2, Mine=2, Old=1, Own=2, Src=1, Tag=2)
        before = self.snapshot()
        rc, out = self.refresh()
        self.assertEqual(rc, 1, out)
        self.assertIn("without --apply, this run gives the row of a decision --apply carries out for a file the record "
                      "keeps no row for: lib/Old.v, decided `Anthropic-licensed: tag Apache-2.0 becomes Apache-2.0 OR "
                      "MIT`.", out)
        self.assertEqual(self.snapshot(), before)

    # the message of the refusal of the tag pass's row for a file the record keeps a row for, with %s for the file.
    # The tag pass's row is the one row of a decision --apply carries out that reaches that refusal: `back` refuses
    # first a file the run decides and does not leave bare, and a file left bare has a row a run gives again
    KEPT = ("this run gives the row of a decision --apply carries out for a file the record keeps a row for: %s, "
            "decided `Anthropic-licensed: tag Apache-2.0 becomes Apache-2.0 OR MIT`.")

    def refused_with_and_without_apply(self, says):
        """--record exits 1 and says says, without --apply and with it, and writes nothing."""
        for extra in ((), ("--apply",)):
            with self.subTest(extra=extra):
                before = self.snapshot()
                rc, out = self.refresh(*extra)
                self.assertEqual(rc, 1, out)
                self.assertIn(says, out)
                self.assertEqual(self.snapshot(), before)

    def test_record_refusal_kept_stamped_row(self):
        """lib/Own.v, written here, takes Anthropic's copyright line and the tag `Apache-2.0`: this refresh stamps its
        row, and the run gives the tag pass's row for it.  Taking that row would replace the stamped row, and without
        --apply --check would report it on every run."""
        self.write("lib/Own.v", [ANTHROPIC[0], mf.BUNDLE_TAG] + code("own", 10))
        self.refused_with_and_without_apply(self.KEPT % "lib/Own.v")

    def test_record_refusal_kept_made_from_row(self):
        """lib/Copy.v, which --apply made from lib/Src.v, has its tag set back to `Apache-2.0`: the run gives the tag
        pass's row for it.  Taking that row would replace the `made from` row, and the record would forget what
        --apply did."""
        text = self.read("lib/Copy.v")
        self.assertIn(mf.APACHE_TAG, text)
        self.put(os.path.join(self.root, "lib/Copy.v"), text.replace(mf.APACHE_TAG, mf.BUNDLE_TAG, 1))
        self.refused_with_and_without_apply(self.KEPT % "lib/Copy.v")

    def test_record_refusal_kept_mit_tag_row(self):
        """lib/Tag.v, whose tag --apply made MIT, takes Anthropic's lines again: the record keeps its MIT-tag row."""
        with self.subTest(tree="Anthropic's copyright line and the tag Apache-2.0"):
            # the run gives the tag pass's row for the file: the refusal of a row for a file the record keeps a row
            # for answers
            self.write("lib/Tag.v", [ANTHROPIC[0], mf.BUNDLE_TAG] + code("tag", 10))
            self.refused_with_and_without_apply(self.KEPT % "lib/Tag.v")
        with self.subTest(tree="Anthropic's tag alone, as before --apply"):
            # the run decides the file again: `back` answers
            self.write("lib/Tag.v", ANTHROPIC[1:] + code("tag", 10))
            self.refused_with_and_without_apply("a run decides lib/Tag.v again, which the record accounts for as a "
                                                "file that carries licence lines")

    def test_record_refusal_undone_mit_tag_and_tag_pass(self):
        """The rows of the MIT tag and of the tag pass are applied rows too: once --apply has written the file, taking
        its licence lines off and declaring it in left-bare.tsv is refused, with --apply and without, and nothing is
        written, as for a `made from` row (test_record_refusal_undone)."""
        self.write_tagged()
        self.write("lib/Old.v", [ANTHROPIC[0], mf.BUNDLE_TAG] + code("old", 10))
        self.born(Copy=2, Mine=2, Old=1, Own=2, Src=1, Tag=2, Tagged=3)
        rc, out = self.refresh("--apply")
        self.assertEqual(rc, 0, out)
        for path, decision, stripped in (
                ("lib/Tagged.v", "written here (Apache-2.0 OR MIT tag becomes MIT)", code("tagged", 10)),
                ("lib/Old.v", "Anthropic-licensed: tag Apache-2.0 becomes Apache-2.0 OR MIT", code("old", 10))):
            with self.subTest(row=decision):
                self.assertEqual(self.row(path).split("\t")[6], decision)
                applied = self.read(path)
                self.write(path, stripped)                               # no licence lines at all
                self.put(self.layout.left_bare_tsv, "path\treason\n%s\t%s\n" % (path, REASON))
                self.refused_with_and_without_apply("declares %s, whose row of this record says --apply wrote the file"
                                                    % path)
                self.put(os.path.join(self.root, path), applied)         # as --apply wrote it, for the next case

    def test_stamped_rows_kept_by_record(self):
        """A file this generator decided when the record was written and does not decide now carries licence lines
        today: the refresh keeps its row, saying so, rather than dropping it and forgetting the file.  When the file
        loses those lines, --check exits 1, not drift: the run's `written here` row is for a file that the record
        holds in a stamped row, which no run gives again."""
        self.write("lib/Own.v", ANTHROPIC + code("own", 10))   # stamped by some other change
        rc, out = self.refresh()
        self.assertEqual(rc, 0, out)
        row = self.row("lib/Own.v")
        self.assertEqual(row.split("\t")[6], "carries licence lines since (was: written here)")
        self.assertEqual(row.split("\t")[:6], ["lib/Own.v", "0", "0", "10", "0.000", "-"])
        self.assertEqual(self.check()[0], 0)
        self.assertEqual(self.refresh()[0], 0)                 # a second refresh leaves it alone
        self.assertEqual(self.row("lib/Own.v"), row)
        self.write("lib/Own.v", code("own", 10))               # and its lines cannot be refreshed away
        self.assert_check(1, ["+ lib/Own.v\t0\t0\t10\t0.000\t-\twritten here\t"])
        rc, out = self.refresh()
        self.assertEqual(rc, 1, out)
        self.assertIn("a run decides lib/Own.v again", out)

    def test_declaration_retires_a_stamped_row(self):
        """lib/Own.v's row is stamped, then the file loses its lines again and a row of left-bare.tsv declares it: the
        declaration retires the stamped row.  --check exits 1, not drift, since the run's `left bare` row is for a file
        the record holds in a stamped row; a refresh takes that row in the stamped row's place, and --check passes."""
        self.write("lib/Own.v", ANTHROPIC + code("own", 10))   # stamped by some other change
        rc, out = self.refresh()
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.row("lib/Own.v").split("\t")[6], "carries licence lines since (was: written here)")
        self.write("lib/Own.v", code("own", 10))               # its lines taken off again
        self.put(self.layout.left_bare_tsv, "path\treason\nlib/Own.v\t%s\n" % REASON)
        self.assert_check(1, ["+ lib/Own.v\t0\t0\t10\t0.000\t-\tleft bare\t" + REASON])
        rc, out = self.refresh()
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.row("lib/Own.v").split("\t")[6], "left bare")
        self.assertEqual(self.check()[0], 0)

    def test_refresh_cannot_tell_a_strip_of_a_file_it_never_decided(self):
        """The gap of "What neither can see", pinned: the record holds no row for a file that already carried
        Anthropic's lines when it was written, so a refresh after a strip takes the run's row.  --check reports the
        strip as drift (exit 3): the run finds the file written here, a row a run gives again, and the record holds
        no row for it."""
        self.write("lib/Extra.v", ANTHROPIC + code("extra", 9))
        self.born(Copy=2, Extra=2, Mine=2, Own=2, Src=1, Tag=2)
        self.assertEqual(self.refresh()[0], 0)
        self.assertNotIn("lib/Extra.v", self.decisions())
        self.write("lib/Extra.v", code("extra", 9))
        self.assert_check(3, ["+ lib/Extra.v\t0\t0\t9\t0.000\t-\twritten here\t"])
        self.assertEqual(self.refresh()[0], 0)
        self.assertEqual(self.check()[0], 0)

    def test_refresh_and_a_file_deleted_then_written_again(self):
        os.remove(os.path.join(self.top, self.root, "lib/Copy.v"))
        rc, out = self.refresh()
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.row("lib/Copy.v").split("\t")[6], "made from (block)")
        self.assertEqual(self.check()[0], 0)
        self.write("lib/Copy.v", code("fresh", 9))
        rc, out = self.refresh()
        self.assertEqual(rc, 1, out)
        self.assertIn("a run decides lib/Copy.v again", out)
        self.put(self.layout.left_bare_tsv, "path\treason\nlib/Copy.v\tours: a new file, not the one deleted\n")
        rc, out = self.refresh()
        self.assertEqual(rc, 1, out)
        self.assertIn("declares lib/Copy.v, whose row of this record says --apply wrote the file", out)
        old = self.row("lib/Copy.v")
        self.edit_record(lambda rows: [r for r in rows if r != old])   # the person's edit
        rc, out = self.refresh()
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.row("lib/Copy.v").split("\t")[6], "left bare")
        self.assertEqual(self.check()[0], 0)

    def test_refresh_with_a_record_row_of_too_few_columns(self):
        """A row of fewer than 7 columns is no row this generator writes: --check compares it and exits 1, not drift,
        and a refresh drops it."""
        self.edit_record(lambda rows: rows + ["lib/Short.v\t0"])
        self.assert_check(1, ["- lib/Short.v\t0"])
        self.assertEqual(self.refresh()[0], 0)
        self.assertNotIn("lib/Short.v", self.decisions())
        self.assertEqual(self.check()[0], 0)

    def test_apply_record_keeps_every_kept_row_and_adds_the_written_rows(self):
        # one run writes the file the record lacks lines for and the record: the kept rows (what --apply wrote,
        # and a stamped row) stay, the written file's row is added, and --check then passes
        self.write("lib/Own.v", ANTHROPIC + code("own", 10))   # its row becomes a stamped row
        self.assertEqual(self.refresh()[0], 0)
        kept = {p: r for p, r in ((r.split("\t")[0], r) for r in mf.rows_of(self.record)[1:])
                if not mf.regenerable(r)}
        self.assertEqual(sorted(kept), ["lib/Copy.v", "lib/Own.v", "lib/Tag.v"])
        self.write("lib/Fresh.v", code("src", 40))
        self.born(Copy=2, Fresh=3, Mine=2, Own=2, Src=1, Tag=2)
        rc, out = self.refresh("--apply")
        self.assertEqual(rc, 0, out)
        rows = {r.split("\t")[0]: r for r in mf.rows_of(self.record)[1:]}
        for p, r in kept.items():
            self.assertEqual(rows[p], r, p)
        self.assertTrue(rows["lib/Fresh.v"].split("\t")[6].startswith("made from"), rows["lib/Fresh.v"])
        self.assertEqual(sorted(rows), ["lib/Copy.v", "lib/Fresh.v", "lib/Mine.v", "lib/Own.v", "lib/Tag.v"])
        self.assertEqual(list(rows), sorted(rows))
        self.assertTrue(self.read("lib/Fresh.v").startswith("\n".join(ANTHROPIC) + "\n"))
        self.assertEqual(self.check()[0], 0)

    def test_apply_record_refuses_before_any_write(self):
        # a refusal of --record with --apply: neither the record nor a .v file is written
        self.write("lib/Copy.v", code("src", 40))               # the `back` refusal
        self.write("lib/Fresh.v", code("src", 40))              # a file the run would write
        self.born(Copy=2, Fresh=3, Mine=2, Own=2, Src=1, Tag=2)
        before = self.snapshot()
        rc, out = self.refresh("--apply")
        self.assertEqual(rc, 1, out)
        self.assertIn("a run decides lib/Copy.v again", out)
        self.assertEqual(self.snapshot(), before)


class LeftBare(Fixture):
    """A bare file the rule finds made from a source, which left-bare.tsv declares is bare on purpose.  Where the
    declaration goes, the run's row for the file is `made from (block)`, a row no run gives again, so --check exits 1,
    not drift."""
    # the run's row for lib/Bare.v when no row of left-bare.tsv declares it
    UNDECLARED = ("lib/Bare.v\t40\t40\t80\t0.500\tlib/Copy.v\tmade from (block)\t(* Modified by Theorem Labs, 2026-11: "
                  "made from proofs/demo/fuzz_demo/lib/Copy.v; 40 of its 80 lines of code are new or changed. *)")

    def setUp(self):
        super().setUp()
        self.write("lib/Bare.v", code("src", 40) + code("bare", 40))
        self.born(Bare=2, Copy=2, Mine=2, Own=2, Src=1, Tag=2)
        self.declare("lib/Bare.v\tours: copied from the bare lib/Bare.v of another unit, not from lib/Src.v")
        self.remake_record()

    def declare(self, *rows):
        self.put(self.layout.left_bare_tsv, "path\treason\n" + "".join(r + "\n" for r in rows))

    def remake_record(self):
        rc, out = self.refresh()
        self.assertEqual(rc, 0, out)
        return self.decisions()

    def probe(self):
        return self.cli(os.path.join(self.top, "probe.tsv"), "--top", self.top, *self.history_args())

    def test_left_bare_file_matches_and_keeps_no_licence_lines(self):
        decisions = self.remake_record()
        self.assertEqual(decisions["lib/Bare.v"], "left bare (overrules made from (block))")
        self.assertIn(self.row("lib/Bare.v").split("\t")[5], ("lib/Copy.v", "lib/Src.v"))
        self.assertIn("not from lib/Src.v", self.row("lib/Bare.v").split("\t")[7])
        self.assertEqual(self.check()[0], 0)
        self.assertTrue(mf.headerless(self.read("lib/Bare.v")))
        self.assertEqual(self.refresh("--apply")[0], 0)        # --apply writes nothing to it
        self.assertTrue(mf.headerless(self.read("lib/Bare.v")))

    def test_left_bare_file_is_no_source_for_another_file(self):
        self.write("lib/FromBare.v", code("bare", 40))
        self.born(Bare=2, Copy=2, FromBare=3, Mine=2, Own=2, Src=1, Tag=2)
        decisions = self.remake_record()
        self.assertEqual(decisions["lib/FromBare.v"], "written here")
        self.assertEqual(self.row("lib/FromBare.v").split("\t")[5], "-")
        self.declare()
        rc, out = self.probe()
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.decisions(os.path.join(self.top, "probe.tsv"))["lib/FromBare.v"], "made from (block)")

    def test_left_bare_declaration_taken_away(self):
        """Exit 1, not drift: the run's row is `made from (block)`."""
        bare = self.row("lib/Bare.v")
        self.declare()
        out = self.assert_check(1, ["- " + bare, "+ " + self.UNDECLARED])
        self.assertIn("the `+` rows of lib/Bare.v are decisions --apply carries out", out)

    def test_left_bare_file_deleted(self):
        """Exit 1, not drift: the run's row is `made from (block)`."""
        bare = self.row("lib/Bare.v")
        os.remove(os.path.join(self.top, self.layout.left_bare_tsv))
        self.assert_check(1, ["- " + bare, "+ " + self.UNDECLARED])

    def test_left_bare_reason_edited_by_hand_in_the_record(self):
        # both rows are `left bare (overrules made from (block))`, rows a run gives again, for a file the record holds
        # in no other row: drift
        row = self.row("lib/Bare.v")
        edited = row.rsplit("\t", 1)[0] + "\tbecause I say so"
        self.edit_record(lambda rows: [edited if r == row else r for r in rows])
        self.assert_check(3, ["- " + edited, "+ " + row])

    def test_left_bare_row_that_cannot_be_read(self):
        """Exit 1, not drift: the row declares nothing, so the run's row is `made from (block)`."""
        bare = self.row("lib/Bare.v")
        path = os.path.join(self.top, self.layout.left_bare_tsv)
        with open(path, "wb") as f:
            f.write(b"path\treason\nlib/Bare.v\tours: caf\xe9, not UTF-8\n")
        self.assert_check(1, ["- " + bare, "+ " + self.UNDECLARED])
        rc, out = self.probe()
        self.assertEqual(rc, 0, out)
        self.assertIn("line 2: not UTF-8", out)

    def test_left_bare_mistakes(self):
        """Each mistake declares nothing and the run goes on, saying so: the file is decided by the rule alone, so
        its row is not the record's, and --check exits 1, not drift: the run's row is `made from (block)`."""
        bare, mine = self.row("lib/Bare.v"), self.row("lib/Mine.v")
        lost = ["- " + bare, "+ " + self.UNDECLARED]
        # in the last case the second row declares lib/Mine.v, and that row is no mistake: lib/Mine.v is left bare,
        # with its reason
        mine_too = ["- " + bare, "- " + mine, "+ " + self.UNDECLARED,
                    "+ lib/Mine.v\t0\t0\t10\t0.000\t-\tleft bare\tours"]
        for row, says, signed in (("lib/Nowhere.v\tours", "lib/Nowhere.v is no .v file of this unit", lost),
                                  ("lib/Bare.v\t", "lib/Bare.v gives no reason", lost),
                                  ("lib/Bare.v", "1 column(s), not one path and one reason", lost),
                                  ("lib/Bare.v\tours\tand more", "3 column(s), not one path and one reason", lost),
                                  ("lib/Bare.v\tours\nlib/Bare.v\tours again", "lib/Bare.v is named twice", lost),
                                  ("lib/Bare.v\t\nlib/Bare.v\tours", "lib/Bare.v is named twice", lost),
                                  ("lib/Bare.v\tours\nlib/Mine.v\tours\nlib/Bare.v\tours", "lib/Bare.v is named twice",
                                   mine_too)):
            with self.subTest(row=row):
                self.declare(row)
                self.assert_check(1, signed)
                rc, out = self.probe()
                self.assertEqual(rc, 0, out)
                self.assertIn(says, out)
        # a row naming a file that carries licence lines, or only Modified by lines, is a mistake of the same kind
        for path, lines in (("lib/Src.v", None), ("lib/Mod.v", [OWN] + code("mod", 3))):
            with self.subTest(path=path):
                if lines:
                    self.write(path, lines)
                self.declare("%s\tours" % path)
                rc, out = self.probe()
                self.assertEqual(rc, 0, out)
                self.assertIn("%s carries licence lines --" % path, out)


class UnitFile(Tree):
    """The unit file: data and the fixed block, checked before any other file is read; exit 4 names the part."""

    def setUp(self):
        super().setUp()
        self.write("lib/Src.v", ANTHROPIC + code("src", 40))
        self.born(Src=1)
        self.good = unit_file_text(self.unit, self.donors, self.history)
        # a .v file that cannot be read: a run that read the tree before the unit file's check would refuse that
        # file, not the unit file
        with open(os.path.join(self.top, self.root, "lib/Unreadable.v"), "wb") as f:
            f.write(b"\xff\xfe not UTF-8\n")

    def refused(self, text, says, path=None, runs=True):
        """The unit file text at path (default the unit's) is refused: by a run, by --check and by --unit-file,
        each with exit 4 and the part named.  runs=False: by --unit-file alone, for a fixed block that no longer
        calls the generator (it never reaches the check; the made-from job runs --unit-file first)."""
        unit_file = path or self.unit_file
        os.makedirs(os.path.dirname(unit_file), exist_ok=True)
        with open(unit_file, "w", encoding="utf-8", newline="") as f:
            f.write(text)
        runs_of = (["--top", self.top, os.path.join(self.top, "out.tsv")], ["--check"], ["--check", "--apply"])
        for args in runs_of if runs else ():
            with self.subTest(args=args):
                rc, out = self.cli(*args, script=unit_file)
                self.assertEqual(rc, 4, out)
                self.assertIn("refusing the unit file", out)
                self.assertIn(says, out)
                self.assertFalse(os.path.exists(os.path.join(self.top, "out.tsv")))
        rc, out = self.cli("--unit-file", unit_file, script=os.path.join(self.top, "dev/licence/made_from.py"))
        self.assertEqual(rc, 4, out)
        self.assertIn(says, out)

    def test_unit_file_def(self):
        self.refused(self.good.replace("DONORS = ", "def f():\n    pass\n\n\nDONORS = "), "line 5: a def")

    def test_unit_file_def_after_the_docstring(self):
        doc_end = self.good.index('"""\n', 30) + 4
        self.refused(self.good[:doc_end] + "def f(): pass\n" + self.good[doc_end:], "line 4: a def")

    def test_unit_file_import(self):
        self.refused(self.good.replace("DONORS = ", "import os\nDONORS = "), "line 5: an import")

    def test_unit_file_computed_value_a_call(self):
        self.refused(self.good.replace("DONORS = ()", "DONORS = tuple(['curl/fuzz_bufq'])"),
                     "DONORS is a computed value (a call)")

    def test_unit_file_history_str_none(self):
        self.refused(self.good.replace("HISTORY = 'history-named.tsv'", "HISTORY = str(None)"),
                     "HISTORY is a computed value (a call)")

    def test_unit_file_computed_value_a_name_or_operator(self):
        self.refused(self.good.replace("HISTORY = 'history-named.tsv'", "HISTORY = DONORS"),
                     "HISTORY is a computed value (a name)")
        self.refused(self.good.replace("HISTORY = 'history-named.tsv'", "HISTORY = 'history' + '.tsv'"),
                     "HISTORY is a computed value (an operator)")

    def test_unit_file_data_of_the_wrong_shape(self):
        self.refused(self.good.replace("DONORS = ()", "DONORS = ('fuzz_bufq',)"),
                     "not a \"<project>/<harness>\" string literal")
        self.refused(self.good.replace("DONORS = ()", "DONORS = ['curl/fuzz_bufq']"), "DONORS is a computed value")
        self.refused(self.good.replace("'history-named.tsv'", "'../history-named.tsv'"),
                     "not the name of a file in the unit's licence directory")

    def test_unit_file_changed_fixed_block_line(self):
        self.refused(self.good.replace("    sys.exit(4)\n", "    sys.exit(1)\n"), "is not line 17 of the fixed block")

    def test_unit_file_fixed_block_line_with_a_comment_appended(self):
        self.refused(self.good.replace("_MAIN(__file__)\n", "_MAIN(__file__) # x\n"),
                     "is not line 18 of the fixed block: '_MAIN(__file__) # x'")
        self.refused(self.good.replace("import sys\n", "import sys # x\n"), "is not line 5 of the fixed block")

    def test_unit_file_fixed_block_missing_or_followed_by_text(self):
        first = mf.FIXED_BLOCK.split("\n", 1)[0]
        self.refused(self.good.replace(first + "\n", "# a changed first line\n"), "it has no fixed block")
        self.refused(self.good + "print('more')\n", "text after the fixed block")
        self.refused(self.good[:-1], "inside the fixed block: FIXED_BLOCK goes on to its line 18 and its last "
                                     "newline")
        self.refused(self.good[:-len("_MAIN(__file__)\n")], "is not line 18 of the fixed block: ''", runs=False)

    def test_unit_file_unknown_name(self):
        self.refused(self.good.replace("HISTORY = ", "OTHER = 1\nHISTORY = "), "the unknown name OTHER")

    def test_unit_file_data_names_in_order_and_once(self):
        self.refused(self.good.replace("HISTORY = 'history-named.tsv'\n", "HISTORY = 'history-named.tsv'\n"
                                       "DONORS = ()\n"), "DONORS is given a second time")
        lines = self.good.split("\n")
        i, j = lines.index("DONORS = ()"), lines.index("HISTORY = 'history-named.tsv'")
        lines[i], lines[j] = lines[j], lines[i]
        self.refused("\n".join(lines), "HISTORY before DONORS")
        self.refused(self.good.replace("HISTORY = 'history-named.tsv'\n", ""), "it gives no HISTORY")

    def test_unit_file_text_beside_a_statement(self):
        self.refused(self.good.replace("DONORS = ()\n", "DONORS = ();\n"), "is not a comment line")

    def test_unit_file_coding_declaration(self):
        # a coding declaration (PEP 263) makes Python read the file as another text than the check reads: under
        # utf-7 the comment line below holds a newline and a statement, which Python runs before the fixed block,
        # while the check, which reads the file as UTF-8, sees a comment line.  So --unit-file, which the made-from
        # job runs before each --check, would pass a unit file whose --check runs code of its own
        text = self.good.replace("#!/usr/bin/env python3\n", "#!/usr/bin/env python3\n# -*- coding: utf-7 -*-\n", 1)
        text = text.replace("HISTORY = ", "# a note+AAo-X = 1\nHISTORY = ", 1)
        self.refused(text, "refusing the unit file")

    def test_unit_file_coding_declaration_utf_8_on_line_1(self):
        # utf-8 too: a unit file needs no declaration, and refusing every one leaves no encoding name to judge
        self.refused(self.good.replace("#!/usr/bin/env python3\n", "# -*- coding: utf-8 -*-\n", 1),
                     "line 1: a coding declaration ('# -*- coding: utf-8 -*-')")

    def test_unit_file_coding_declaration_after_a_lone_carriage_return(self):
        # Python breaks lines at a lone \r as well as at \n, so the declaration below is its line 2, and Python reads
        # the file in the encoding it names, which can give another text than the check reads; a unit file needs none
        text = self.good.replace("#!/usr/bin/env python3\n", "#!/usr/bin/env python3\r# -*- coding: utf-8 -*-\n", 1)
        self.refused(text, "line 2: a coding declaration ('# -*- coding: utf-8 -*-')")
        # a blank line 1 ended by a lone \r: broken at \n alone, line 1 starts with \r and is no comment line, so
        # only the reading that breaks at \r too finds the declaration
        self.refused(self.good.replace("#!/usr/bin/env python3\n", "\r# -*- coding: utf-8 -*-\n", 1),
                     "line 2: a coding declaration ('# -*- coding: utf-8 -*-')")

    def test_unit_file_byte_order_mark(self):
        # Python drops a byte order mark at the start of the file, so it reads another text than the check reads; a
        # unit file needs none
        self.refused("\ufeff" + self.good, "line 1: a byte order mark (U+FEFF)")

    def test_unit_file_missing_docstring(self):
        self.refused(self.good.replace(docstring(self.unit), "# no docstring\n"), "it has no docstring")

    def test_unit_file_docstring_of_the_wrong_kind(self):
        self.refused(self.good.replace("dev/licence/made_from.py, which", "the shared generator, which"),
                     "the docstring does not name dev/licence/made_from.py")
        self.refused(self.good.replace("lines each takes.", "lines each takes. And more."),
                     "the docstring is not one sentence")

    def test_unit_file_wrong_path(self):
        # seven directories below the top, so the fixed block finds the generator, but not a unit's licence folder
        wrong = os.path.join(self.top, self.root, "elsewhere", "evidence", "licence", "made_from.py")
        self.assertEqual(os.path.normpath(os.path.join(os.path.dirname(wrong), *[os.pardir] * 7)),
                         os.path.normpath(self.top))
        self.refused(self.good, "its path is not projects/<p>/<h>/proofs/provenance/evidence/licence/made_from.py",
                     path=wrong)

    def test_unit_file_cli_accepts_each_unit_file_of_the_checkout(self):
        # every unit file this checkout holds: a release carries only the units it releases (a unit of a project with
        # `release: private` is cut), and dev/licence/ with them, so the test names no unit
        found = sorted(glob.glob(os.path.join(glob.escape(REPO), "projects", "*", "*", "proofs", "provenance",
                                              "evidence", "licence", "made_from.py")))
        self.assertTrue(found, "no unit file under %s/projects" % REPO)
        for path in found:
            unit = tuple(os.path.relpath(path, os.path.join(REPO, "projects")).split(os.sep)[:2])
            with self.subTest(unit="/".join(unit)):
                rc, out = self.cli("--unit-file", path, script=SCRIPT)
                self.assertEqual(rc, 0, out)
                self.assertIn("is the unit file of %s/%s: data only" % unit, out)
                layout = mf.layout_of(path)
                self.assertEqual(layout.unit, unit)
                self.assertEqual(os.path.normpath(layout.top), os.path.normpath(REPO))

    def test_unit_file_cli_needs_its_option(self):
        rc, out = self.cli(script=os.path.join(self.top, "dev/licence/made_from.py"))
        self.assertEqual(rc, 2, out)
        self.assertIn("--unit-file", out)
        rc, out = self.cli("--unit-file", os.path.join(self.top, "nowhere", "made_from.py"),
                           script=os.path.join(self.top, "dev/licence/made_from.py"))
        self.assertEqual(rc, 4, out)

    def test_fixed_block_exits_4_when_the_generator_cannot_load(self):
        generator = os.path.join(self.top, "dev/licence/made_from.py")
        for name, text in (("missing", None), ("a syntax error", "def (:\n"), ("an error", "raise ValueError('x')\n"),
                           ("an exit while it loads", "import sys\nsys.exit(1)\n"), ("no main", "X = 1\n")):
            with self.subTest(generator=name):
                if os.path.exists(generator):
                    os.remove(generator)
                shutil.rmtree(os.path.join(self.top, "dev/licence/__pycache__"), ignore_errors=True)
                if text is not None:
                    with open(generator, "w", encoding="utf-8") as f:
                        f.write(text)
                rc, out = self.cli("--check")
                self.assertEqual(rc, 4, out)
                self.assertIn("cannot load the shared generator %s" % os.path.normpath(generator), out)
        os.remove(generator)
        shutil.copy(SCRIPT, generator)
        self.assertEqual(self.cli("--unit-file", self.unit_file, script=generator)[0], 0)


class CommandLine(Tree):
    def test_check_refuses_apply_record_and_record_first_added(self):
        for extra in (["--apply"], ["--record"], ["--record-first-added"]):
            with self.subTest(extra=extra):
                rc, out = self.check(*extra)
                self.assertEqual(rc, 2, out)
                self.assertIn("--check writes no file of the tree: it takes no --apply, --record or "
                              "--record-first-added", out)

    def test_a_run_needs_its_out(self):
        rc, out = self.cli()
        self.assertEqual(rc, 2, out)
        self.assertIn("the TSV to write is required (or --check)", out)

    def test_refused_is_exit_4(self):
        self.assertEqual(mf.REFUSED, 4)

    def test_defect_is_exit_5(self):
        """A defect of the generator's own code is 5: not 3, which is drift and which pr.yml's made-from job warns on
        for a unit that only a change to its proofs names, and not 4, a refusal."""
        self.assertEqual(mf.DEFECT, 5)

    def test_only_check_exits_3(self):
        """No code of the generator writes exit(3) or return 3.  DRIFT is 3, and no code but check() reads it, so no
        path but --check exits 3."""
        with open(SCRIPT, encoding="utf-8") as f:
            source = f.read()
        self.assertNotRegex(source, r"\bexit\s*\(\s*3\s*\)")
        self.assertNotRegex(source, r"\breturn\s+3\b")
        self.assertEqual(mf.DRIFT, 3)
        readers = []   # the innermost def or class around each read of the name DRIFT

        def visit(node, owner):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                owner = node.name
            elif isinstance(node, ast.Lambda):
                owner = "a lambda"
            if isinstance(node, ast.Name) and node.id == "DRIFT" and isinstance(node.ctx, ast.Load):
                readers.append(owner)
            for child in ast.iter_child_nodes(node):
                visit(child, owner)

        visit(ast.parse(source), "the module")
        self.assertTrue(readers, "no code reads DRIFT")
        self.assertEqual(set(readers), {"check"}, readers)


def python_install():
    paths = {sys.prefix, sys.base_prefix, sys.exec_prefix, sys.base_exec_prefix} | set(sysconfig.get_paths().values())
    return tuple(os.path.realpath(p) + os.sep for p in paths if p)


class Coupling(Fixture):
    """R5's coupling: the files the generator reads outside a unit are dev/licence/made_from.py and READS, and
    MADE_FROM_READS, in the reach step of pr.yml, names dev/licence/ and each path of READS: a change under one of them
    makes the made-from job check every unit with a record."""

    def test_files_read_outside_the_unit_are_the_generator_and_reads(self):
        seen, active = [], [False]

        def hook(event, args):
            if not active[0]:
                return
            if event == "open" and isinstance(args[0], (str, bytes)):
                seen.append(os.fsdecode(args[0]))
            elif event == "import" and len(args) > 1 and isinstance(args[1], str):
                seen.append(args[1])

        def source(path):
            """A module's cache read (or looked for) is a read of that module's source."""
            try:
                return importlib.util.source_from_cache(path) if path.endswith(".pyc") else path
            except ValueError:
                return path

        sys.addaudithook(hook)
        self.write("lib/Late.v", code("src", 40))             # a file this run writes
        self.born(Copy=2, Late=3, Mine=2, Own=2, Src=1, Tag=2)
        out = os.path.join(self.top, self.licence, "run.tsv")
        argv = [self.unit_file, "--top", self.top, out, "--apply"] + self.history_args()
        with mock.patch.object(sys, "argv", argv), mock.patch.object(sys, "dont_write_bytecode", True), \
                contextlib.redirect_stderr(io.StringIO()), contextlib.redirect_stdout(io.StringIO()):
            active[0] = True
            try:
                runpy.run_path(self.unit_file, run_name="__main__")
            finally:
                active[0] = False
        self.assertTrue(self.read("lib/Late.v").startswith(ANTHROPIC[0]))   # the run ran and wrote
        top = os.path.realpath(self.top) + os.sep
        unit = os.path.realpath(os.path.join(self.top, "projects", *self.unit)) + os.sep
        install = python_install()
        outside = {os.path.relpath(p, top) for p in (os.path.realpath(source(p)) for p in seen)
                   if not p.startswith(unit) and not p.startswith(install)}
        self.assertEqual(outside, {"dev/licence/made_from.py"} | set(mf.READS))

    def test_pr_yml_made_from_reads_names_dev_licence_and_reads(self):
        # the reach step of the made-from job holds the generator's reads on one shell line, read here as text
        path = os.path.join(REPO, ".github", "workflows", "pr.yml")
        with open(path, encoding="utf-8") as f:
            found = re.findall(r"^\s*MADE_FROM_READS='([^']*)'\s*$", f.read(), re.M)
        self.assertEqual(len(found), 1, "%s holds %d lines MADE_FROM_READS='...', not one: the made-from job must "
                                        "name dev/licence/ and %s" % (path, len(found), " ".join(mf.READS)))
        reads = found[0].split()
        self.assertEqual(len(reads), len(set(reads)), reads)
        self.assertEqual(set(reads), {"dev/licence/"} | set(mf.READS))


PR_YML = os.path.join(REPO, ".github", "workflows", "pr.yml")
STRIP_STEP = "a proof file of a unit with a licence record keeps Anthropic's copyright line (the strip check)"
# the rules that the strip step writes again, which this generator gives
STRIP_RULES = ("HEADER_LINES", "ANTHROPIC", "LICENCE", "PROGRAM")
# A step whose whole `run:` runs .github/scripts/pr/<name>.sh holds its text in that file, byte for byte (Dispatch
# issue OSSV-841): the strip step is one.
SCRIPT_CALL = re.compile(
    r'run: exec bash --noprofile --norc -eo pipefail "\$GITHUB_WORKSPACE/head/(\.github/scripts/pr/[a-z0-9-]+\.sh)"')


def strip_steps():
    """The text of each step named STRIP_STEP in .github/workflows/pr.yml of this checkout, from its `- name:` line
    to the next step, and the text of the script it runs when its run is a script of .github/scripts/pr/; none when
    the file is not there or holds no such step (the public repository's pr.yml)."""
    if not os.path.isfile(PR_YML):
        return []
    with open(PR_YML, encoding="utf-8") as f:
        lines = f.read().split("\n")
    out = []
    for i, line in enumerate(lines):
        if line.strip() == "- name: " + STRIP_STEP:
            indent = line[:len(line) - len(line.lstrip())]
            end = next((j for j in range(i + 1, len(lines))
                        if lines[j].strip() and not lines[j].startswith(indent + " ")), len(lines))
            text = "\n".join(lines[i:end])
            m = SCRIPT_CALL.search(text)
            if m:
                with open(os.path.join(REPO, m.group(1)), encoding="utf-8") as f:
                    text += "\n" + f.read()
            out.append(text)
    return out


def regex_of(node):
    """The pattern that the call node `re.compile(<a string literal>[, <flags of re, joined by |>])` compiles;
    ValueError for a node of any other form."""
    def flags(x):
        if isinstance(x, ast.BinOp) and isinstance(x.op, ast.BitOr):
            return flags(x.left) | flags(x.right)
        if (isinstance(x, ast.Attribute) and isinstance(x.value, ast.Name) and x.value.id == "re"
                and isinstance(getattr(re, x.attr, None), re.RegexFlag)):
            return getattr(re, x.attr)
        raise ValueError("%s is not a flag of re" % ast.unparse(x))

    if not (isinstance(node, ast.Call) and ast.unparse(node.func) == "re.compile" and not node.keywords
            and 1 <= len(node.args) <= 2):
        raise ValueError("%s is not re.compile(<a string literal>[, <flags>])" % ast.unparse(node))
    pattern = ast.literal_eval(node.args[0])
    if not isinstance(pattern, str):
        raise ValueError("%s is not a string literal" % ast.unparse(node.args[0]))
    return re.compile(pattern, flags(node.args[1]) if len(node.args) == 2 else 0)


@unittest.skipUnless(strip_steps(), "this checkout's .github/workflows/pr.yml holds no strip step (the step %r of "
                                    "its lint job): the public repository's pr.yml has none" % STRIP_STEP)
class StripCheck(unittest.TestCase):
    """The strip step of the lint job of .github/workflows/pr.yml writes the rules of this generator again, since it
    runs no file of the change: its HEADER_LINES, ANTHROPIC, LICENCE and PROGRAM are the generator's.  Where the step
    is there, a constant that differs, or that this case cannot read, fails the case."""

    def test_strip_step_rules_are_the_generator_s(self):
        steps = strip_steps()
        self.assertEqual(len(steps), 1, "%s holds %d steps named %r, not one" % (PR_YML, len(steps), STRIP_STEP))
        lines = steps[0].split("\n")
        opens = [i for i, line in enumerate(lines) if line.strip() == "python3 - <<'EOF'"]
        self.assertEqual(len(opens), 1, "the strip step holds %d lines python3 - <<'EOF', not one" % len(opens))
        end = next((j for j in range(opens[0] + 1, len(lines)) if lines[j].strip() == "EOF"), None)
        self.assertIsNotNone(end, "the strip step's python3 - <<'EOF' has no line EOF")
        try:
            program = ast.parse(textwrap.dedent("\n".join(lines[opens[0] + 1:end])))
        except SyntaxError as e:
            self.fail("the strip step's program is not Python: %s" % e)
        given = {}
        for stmt in program.body:
            if (isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name)
                    and stmt.targets[0].id in STRIP_RULES):
                name = stmt.targets[0].id
                self.assertNotIn(name, given, "the strip step gives %s twice" % name)
                given[name] = stmt.value
        self.assertEqual(sorted(given), sorted(STRIP_RULES), "the strip step does not give each of %s"
                                                             % ", ".join(STRIP_RULES))
        try:
            header_lines = ast.literal_eval(given["HEADER_LINES"])
            theirs = {name: regex_of(given[name]) for name in STRIP_RULES[1:]}
        except ValueError as e:
            self.fail("a rule of the strip step cannot be read: %s" % e)
        self.assertEqual(header_lines, mf.HEADER_LINES, "HEADER_LINES")
        for name, regex in theirs.items():
            ours = getattr(mf, name)
            self.assertEqual((regex.pattern, regex.flags), (ours.pattern, ours.flags), name)


if __name__ == "__main__":
    unittest.main()
