"""oft/tests/tmpdir.py: a run of these tests leaves no scratch behind (INFRA-1547).

`oft check` keeps its work directory on purpose and prints `work files in ...`, so a test that reaches the checker
adds an `oft-check-*` directory to whatever TMPDIR it inherited; 2,828 of them had piled up in one shared box's
temporary directory by 2026-11-07, 1,049 of them traceable to the trees these tests make.  Importing `oft.tests`
gives the process a TMPDIR of its own and removes it when the process ends.  These cases hold both ends: the
directory is made where it should be, and a child process that leaves work files in its TMPDIR -- read-only ones
too, and when it is killed with SIGTERM -- leaves nothing in the caller's.
"""
import os
import signal
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import oft.tests
from oft.tests import tmpdir

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.dirname(os.path.dirname(HERE))          # tools/oft/tests -> tools

# A child that imports oft.tests the way a test runner does, then keeps a work directory in its TMPDIR as
# `oft check` keeps one.  It prints the run's TMPDIR and that work directory, so a case can say where they went.
#
#   read-only    leave behind a directory this process may not write, holding a file it may not write, as a built
#                switch and a dune build do.  `shutil.rmtree(..., ignore_errors=True)` leaves both where they are.
#   fork         fork children and stop them with SIGTERM, as `lint.forked_map`'s pool stops its workers, then
#                write in the TMPDIR again: a stopped child must not have taken it away, and must have died.
#   atexit-fork  fork a child that ends normally, so that the atexit registration it inherited runs in it.
#   sleep        stay alive after printing, for a case that sends a signal.
LEAVES_WORK = """
import multiprocessing, os, sys, tempfile, time
sys.path.insert(0, sys.argv[1])
import oft.tests
work = tempfile.mkdtemp(prefix="oft-check-")       # as oft/check.py does, and never removes
open(os.path.join(work, "dune.log"), "w").close()
if "read-only" in sys.argv[2:]:
    built = os.path.join(work, "view", "_build")
    os.makedirs(built)
    with open(os.path.join(built, "log"), "w") as f:
        f.write("built\\n")
    os.chmod(os.path.join(built, "log"), 0o444)
    os.chmod(built, 0o555)
    os.chmod(os.path.dirname(built), 0o555)
if "fork" in sys.argv[2:]:
    assert "fork" in multiprocessing.get_all_start_methods(), "no fork on this platform"
    ctx = multiprocessing.get_context("fork")
    outlived = []
    for _ in range(20):      # 20, because an inherited handler loses the signal about half the time, not always
        stopped = ctx.Process(target=time.sleep, args=(300,))
        stopped.start()
        stopped.terminate()                        # SIGTERM, as lint.forked_map's pool stops a worker
        # 5 s, not 60: SIG_DFL is the kernel's to deliver and needs no scheduling, so a child still alive after
        # it is the defect.  Twenty slow joins would outlast the caller's own timeout, and the case would fail
        # as that timeout rather than by saying what it found.
        stopped.join(5)
        if stopped.is_alive():                     # never leave one running: this process's exit joins it forever
            stopped.kill()
            stopped.join(5)
            outlived.append(stopped.pid)
    os.mkdir(os.path.join(oft.tests.TMPDIR, "after-the-fork"))   # ENOENT if a stopped child removed it
    assert not outlived, "forked children outlived the SIGTERM that stopped them: %s" % outlived
if "atexit-fork" in sys.argv[2:]:
    sys.stdout.flush()                             # nothing buffered for the child to print a second time
    forked = os.fork()
    if forked == 0:
        sys.exit(0)                                # a normal end, so the inherited atexit registration runs
    assert os.waitpid(forked, 0)[1] == 0
    os.mkdir(os.path.join(oft.tests.TMPDIR, "after-the-atexit-fork"))   # ENOENT if that child removed it
print(oft.tests.TMPDIR)
print(work)
sys.stdout.flush()
if "sleep" in sys.argv[2:]:
    time.sleep(300)
"""


class OwnTmpdir(unittest.TestCase):
    def setUp(self):
        self.outer = tempfile.mkdtemp(prefix="oft-tests-case-")
        self.addCleanup(tmpdir.remove_tree, self.outer)
        self.given = os.path.join(self.outer, "tmpdir")
        os.mkdir(self.given)
        self.script = os.path.join(self.outer, "leaves_work.py")
        with open(self.script, "w", encoding="utf-8") as f:
            f.write(LEAVES_WORK)

    def start(self, *flags, **variables):
        """The child, started with self.given as its TMPDIR, its stdout a pipe."""
        env = dict(os.environ, TMPDIR=self.given, PYTHONPATH=os.pathsep.join([TOOLS, os.environ.get("PYTHONPATH", "")]),
                   **variables)
        return subprocess.Popen([sys.executable, self.script, TOOLS, *flags], env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)

    def leaves_work(self, *flags, **variables):
        """Run the child to its end: (the run's TMPDIR, the work directory it kept, its whole output)."""
        child = self.start(*flags, **variables)
        out, err = child.communicate(timeout=300)
        self.assertEqual(child.returncode, 0, out + err)
        run, work = out.strip().splitlines()[-2:]
        self.assertEqual(os.path.dirname(run), self.given, run)
        self.assertEqual(os.path.dirname(work), run, work)
        return run, work, out + err

    def test_a_directory_is_made_under_the_tmpdir_it_is_given(self):
        environ = {"TMPDIR": self.given}
        work = tmpdir.own_tmpdir(environ)
        self.assertEqual(environ["TMPDIR"], work)
        self.assertTrue(os.path.isdir(work))
        self.assertEqual(os.path.dirname(work), self.given)
        self.assertTrue(os.path.basename(work).startswith("oft-tests-run-"))

    def test_a_tmpdir_that_is_not_there_is_fallen_back_from(self):
        """A TMPDIR a reboot or a sweep took away must not be the end of a run."""
        gone = os.path.join(self.outer, "taken-away")
        environ = {"TMPDIR": gone}
        work = tmpdir.own_tmpdir(environ)
        self.assertTrue(os.path.isdir(work))
        self.assertNotEqual(os.path.dirname(work), gone)
        os.rmdir(work)

    def test_importing_the_package_points_tmpdir_at_a_directory_of_its_own(self):
        self.assertEqual(os.environ["TMPDIR"], oft.tests.TMPDIR)
        self.assertEqual(tempfile.gettempdir(), oft.tests.TMPDIR)
        self.assertTrue(os.path.isdir(oft.tests.TMPDIR))

    def test_a_second_call_in_one_process_makes_no_second_directory(self):
        """One process, one scratch directory: nesting one per call would grow every path a later case makes."""
        self.assertEqual(tmpdir.own_tmpdir(), oft.tests.TMPDIR)
        self.assertEqual([n for n in os.listdir(oft.tests.TMPDIR) if n.startswith("oft-tests-run-")], [])

    def test_a_run_leaves_nothing_in_the_tmpdir_it_was_given(self):
        run, work, out = self.leaves_work()
        self.assertFalse(os.path.exists(work), out)
        self.assertEqual(os.listdir(self.given), [], out)

    def test_a_run_that_leaves_a_read_only_tree_leaves_nothing_in_the_tmpdir_it_was_given(self):
        """`shutil.rmtree(..., ignore_errors=True)` abandons a 0o555 directory and says nothing; this does not."""
        run, work, out = self.leaves_work("read-only")
        self.assertFalse(os.path.exists(work), out)
        self.assertEqual(os.listdir(self.given), [], out)
        self.assertNotIn("could not be removed", out)

    def test_a_forked_child_stopped_with_sigterm_does_not_take_the_tmpdir_with_it(self):
        """A forked child owns no part of the directory, and it still dies of the signal that stopped it.

        `lint.forked_map` stops its pool's workers with SIGTERM, and test_lint.py's Memory cases do exactly that.
        Two things went wrong there and both are held here: a stopped worker that runs the inherited cleanup
        removes the TMPDIR its parent is still working in, and a worker that inherits the SIGTERM handler at all
        survives the signal about half the time, because `os.fork()` clears the interpreter's pending-signal flags
        in the child and a signal that lands in that window is dropped.
        """
        run, work, out = self.leaves_work("fork")
        self.assertFalse(os.path.exists(work), out)
        self.assertEqual(os.listdir(self.given), [], out)

    def test_a_forked_child_that_ends_normally_does_not_take_the_tmpdir_with_it(self):
        """The other half of the guard: a plain `os.fork()` child runs the atexit registration it inherited.

        `multiprocessing` ends its children with `os._exit`, which skips atexit, so only the signal path is
        exercised by the case above.  A child of a bare fork that returns normally does run it, and the pid it was
        registered under is what stops it removing its parent's directory.
        """
        run, work, out = self.leaves_work("atexit-fork")
        self.assertFalse(os.path.exists(work), out)
        self.assertEqual(os.listdir(self.given), [], out)

    def test_sigterm_removes_the_run_s_tmpdir(self):
        """SIGTERM is how `timeout -s TERM`, a cancelled job and the OOM killer end a run; atexit does not see it."""
        child = self.start("sleep")
        try:
            run = child.stdout.readline().strip()
            work = child.stdout.readline().strip()
            self.assertEqual(os.path.dirname(run), self.given, run)
            child.send_signal(signal.SIGTERM)
            self.assertEqual(child.wait(timeout=300), -signal.SIGTERM)
        finally:
            child.kill()
            child.communicate()
        self.assertFalse(os.path.exists(work))
        self.assertEqual(os.listdir(self.given), [])

    def test_the_kept_tmpdir_is_left_behind_and_named(self):
        """OSSV_KEEP_TMPDIR is the way to look at what a failing run left: the directory stays, and its path is said."""
        run, work, out = self.leaves_work(OSSV_KEEP_TMPDIR="1")
        self.assertEqual(os.listdir(self.given), [os.path.basename(run)])
        self.assertIn(run, out)
        self.assertTrue(os.path.isfile(os.path.join(work, "dune.log")))

    def test_what_could_not_be_removed_is_reported(self):
        """The one entry that cannot go is named, and it does not save the entries beside it.

        `make_removable` is stood down for this case.  The only directory it cannot repair is one this process does
        not own, and a test owns everything it makes; standing it down leaves the shape of the real thing, which is
        the root-owned tree the container stand-in of test_fetch_check.py can leave behind.  Every error has to be
        collected rather than raised for `goes` to go: a remover that raises at `locked/file` never reaches it, and
        never reaches the last `rmdir` of `top` either, which is why the count of what is reported is held here and
        not only its content.
        """
        top = os.path.join(self.outer, "top")
        locked = os.path.join(top, "locked")
        os.makedirs(locked)
        os.makedirs(os.path.join(top, "goes", "under"))
        with open(os.path.join(locked, "file"), "w", encoding="utf-8") as f:
            f.write("x")
        os.chmod(locked, 0o555)
        try:
            with mock.patch.object(tmpdir, "make_removable"):
                left = tmpdir.remove_tree(top)
            self.assertFalse(os.path.exists(os.path.join(top, "goes")))     # what could go, went
            self.assertEqual(os.listdir(top), ["locked"])
            self.assertEqual(sorted(os.path.basename(p) for p, _ in left), ["file", "locked", "top"])
        finally:
            os.chmod(locked, 0o755)

    def test_a_symbolic_link_out_of_the_tree_is_neither_followed_nor_chmoded(self):
        """What a link points at is not ours: it keeps its mode and its files, and only the link goes."""
        outside = os.path.join(self.outer, "outside")
        os.makedirs(os.path.join(outside, "under"))
        with open(os.path.join(outside, "under", "file"), "w", encoding="utf-8") as f:
            f.write("x")
        os.chmod(os.path.join(outside, "under"), 0o500)
        top = os.path.join(self.outer, "top")
        os.mkdir(top)
        os.symlink(outside, os.path.join(top, "link"))
        try:
            self.assertEqual(tmpdir.remove_tree(top), [])
            self.assertFalse(os.path.exists(top))
            self.assertTrue(os.path.isfile(os.path.join(outside, "under", "file")))
            self.assertEqual(stat.S_IMODE(os.stat(os.path.join(outside, "under")).st_mode), 0o500)
        finally:
            os.chmod(os.path.join(outside, "under"), 0o700)

    def test_the_directory_is_this_user_s_alone(self):
        """0o700, where the shared temporary directory a box exports is open to every user."""
        work = tmpdir.own_tmpdir({"TMPDIR": self.given})
        self.assertEqual(stat.S_IMODE(os.stat(work).st_mode), 0o700)
