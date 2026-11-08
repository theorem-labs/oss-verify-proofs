"""A TMPDIR of each test process's own, removed when that process ends (INFRA-1547).

`oft check` makes its work directory with `tempfile.mkdtemp(prefix="oft-check-")` and keeps it on purpose, printing
`work files in ...`, so that a farm job can copy a failure's logs out of a container that is about to be removed.  On
a farm pod that directory dies with the pod.  On a box it does not, and nothing reads it after the run that made it:
2,828 `oft-check-*` directories had piled up in one shared box's temporary directory by 2026-11-07, and 1,049 of them
are traceable to the trees these tests make -- 856 to `helpers.Tree`, 132 to the stand-in docker of
test_fetch_check.py, 61 to plain `mkdtemp()` end-to-end cases.  A lane session runs these tests in its own clone on
the box and leaves them behind.

So `oft/tests/__init__.py` calls `own_tmpdir()`, which every runner of these tests imports before a test module:
`python3 -B -m unittest discover -s oft/tests -t .` (oft/README.md), `python -B -m oft.tests.parallel` (the tests job
of .github/workflows/pr.yml) and pytest alike.  A checker, a container stand-in or a git a test starts inherits that
TMPDIR and leaves its files inside it, and the whole subtree goes when the process does.  A conftest.py would hold
only the pytest runs, and the runner this repository's own CI uses is unittest.

The same thing, for the tests of dev/stream/, is dev/stream/conftest.py.  The two cannot share a file: a deploy of
the stream tools copies dev/stream/ alone, and a check job copies tools/ alone.  Keep them in step.

OSSV_KEEP_TMPDIR, set to a non-empty value, leaves the directory where it is and prints its path, for somebody
looking at what a failing run left behind.
"""
import atexit
import os
import shutil
import signal
import stat
import sys
import tempfile

# The directory this process made for itself, as "<pid>:<path>", so that a second call in one process -- a test that
# loads this module, or a stream conftest that ran first -- gives back the one directory instead of nesting another
# inside it.  The pid is in the value because a child inherits the variable: its pid differs, so it makes a directory
# of its own under ours and removes that one, never the one its parent is still using.
OWN_TMPDIR = "OSSV_TESTS_TMPDIR"


def make_removable(top):
    """Give this process the right to empty every directory of the tree at top, top itself included.

    A file is unlinked by writing the directory that holds it, not the file, so repairing the directories is enough
    for a read-only file too.  A symbolic link is left alone: what it points at is not ours to change, and os.walk
    does not follow one.
    """
    def repair(path):
        try:
            mode = os.lstat(path).st_mode
        except OSError:
            return
        if stat.S_ISDIR(mode) and stat.S_IMODE(mode) & stat.S_IRWXU != stat.S_IRWXU:
            try:
                os.chmod(path, stat.S_IMODE(mode) | stat.S_IRWXU)
            except OSError:
                pass

    repair(top)
    # topdown, so each directory is repaired before the walk reads it: one it could not have been entered otherwise
    # is entered.
    for parent, dirs, _ in os.walk(top, topdown=True):
        for name in dirs:
            path = os.path.join(parent, name)
            if not os.path.islink(path):
                repair(path)


def remove_tree(top):
    """Remove top and all it holds; give back [(path, error)] for whatever is left, which is [] when it is gone.

    `shutil.rmtree(top, ignore_errors=True)` is not enough, and says nothing when it is not: a directory this
    process cannot write cannot be emptied, so it walks away from that subtree without a word.  A checker's work
    directory holds an opam switch and a dune build, both of which hold read-only directories.  So the permissions
    are repaired first; then every error is collected rather than raised, since raising on the first one would
    leave behind everything the walk had not reached yet, and the caller reports them.
    """
    if not os.path.exists(top):
        return []
    make_removable(top)
    left = []
    shutil.rmtree(top, onexc=lambda _function, path, error: left.append((path, error)))
    return left


# At most this many lines about one failed removal: an unreadable tree of thousands would otherwise bury the run's
# own output under its own error report.
REPORT_LIMIT = 20


def remove_own_tmpdir(top):
    """Remove this run's TMPDIR, and say on stderr what was left behind rather than pass silently."""
    left = remove_tree(top)
    for path, error in left[:REPORT_LIMIT]:
        print("oft.tests: this run's TMPDIR %s keeps %s: %s" % (top, path, error), file=sys.stderr)
    if len(left) > REPORT_LIMIT:
        print("oft.tests: and %d more under %s" % (len(left) - REPORT_LIMIT, top), file=sys.stderr)


def keep_nothing_behind(top):
    """Remove top when this process ends, by exit or by SIGTERM.

    atexit covers a normal end and an exception.  It does not cover SIGTERM, which is how `timeout -s TERM`, a
    cancelled lane job and the OOM killer end a run, so that signal is caught and the process then dies of it,
    leaving a caller the status it sent.  SIGKILL cannot be caught.  SIGINT needs nothing: it raises
    KeyboardInterrupt and the interpreter exits through atexit.

    A forked child must not be left holding either one.  It owns no part of the directory, so the atexit
    registration it inherits is answered by the pid it was made under.  The handler is worse than useless there and
    is taken down for the length of every fork: `os.fork()` clears the interpreter's pending-signal flags in the
    child (`_PySignal_AfterFork`), so a SIGTERM that lands in that window is dropped instead of killing the child --
    and `terminate()` on a process that has only just started is exactly that window.  Measured on sami-devbox, a
    fork and an immediate `terminate()`, 200 times each: with the handler inherited **about half the children
    outlived their SIGTERM** (91 of 200 in one run, 106 of 200 in another); with SIG_DFL across the fork, and with
    no handler at all, none did.  `lint.forked_map` stops its pool's workers that way, and a pool that cannot stop
    a worker is a hung run -- a worse failure than the one this exists to fix.  The cost of taking it down is the
    fork itself: a SIGTERM to the parent in that window leaves the directory behind, as it was left before this
    file existed.

    `after_in_child` is not redundant beside `before`: a fork off a thread that is not the main one cannot change
    the disposition in the parent (`signal.signal` raises there), and the child would keep the handler.  In the
    child it can, because the surviving thread becomes the main one.
    """
    owner = os.getpid()

    def remove_if_ours():
        if os.getpid() == owner:
            remove_own_tmpdir(top)

    atexit.register(remove_if_ours)

    def on_sigterm(signum, frame):
        remove_if_ours()
        signal.signal(signum, signal.SIG_DFL)
        os.kill(os.getpid(), signum)

    def listen(to):
        try:
            signal.signal(signal.SIGTERM, to)
        except ValueError:      # a fork from a thread that is not the main one; nothing to do there
            pass

    try:
        if signal.getsignal(signal.SIGTERM) is not signal.SIG_DFL:
            return              # somebody else's handler; atexit still holds the normal end
        signal.signal(signal.SIGTERM, on_sigterm)
    except ValueError:          # not the main thread
        return
    os.register_at_fork(before=lambda: listen(signal.SIG_DFL),
                        after_in_parent=lambda: listen(on_sigterm),
                        after_in_child=lambda: listen(signal.SIG_DFL))


def own_tmpdir(environ=None):
    """Make a scratch directory under environ's TMPDIR, point TMPDIR at it, and give back its path.

    Called again in the same process, it gives back the directory that process already made.  `tempfile.tempdir` is
    set as well, because `tempfile.gettempdir()` caches the first value it reads and would otherwise hand later
    callers in this process the old one.
    """
    live = environ is None
    environ = os.environ if live else environ
    if live:
        mine = (environ.get(OWN_TMPDIR) or "").split(":", 1)
        if len(mine) == 2 and mine[0] == str(os.getpid()) and os.path.isdir(mine[1]):
            environ["TMPDIR"] = mine[1]
            tempfile.tempdir = mine[1]
            return mine[1]
    # The directory is made under the ambient TMPDIR, not under /tmp, so scratch stays on the filesystem the box
    # chose for it, which is the one with the room for it.  A TMPDIR naming a directory that is not there -- one a
    # reboot or a sweep took away -- is no reason to run nothing: the run goes where tempfile would have put it
    # without the variable, and says so.
    named = environ.get("TMPDIR")
    parent = named if named and os.path.isdir(named) else tempfile.gettempdir()
    if named and parent != named:
        print("oft.tests: TMPDIR names %s, which is not a directory; this run's scratch goes under %s"
              % (named, parent), file=sys.stderr)
    work = tempfile.mkdtemp(prefix="oft-tests-run-", dir=parent)
    environ["TMPDIR"] = work
    if live:
        environ[OWN_TMPDIR] = "%d:%s" % (os.getpid(), work)
        tempfile.tempdir = work
        if environ.get("OSSV_KEEP_TMPDIR"):
            print("oft.tests: OSSV_KEEP_TMPDIR is set; this run's TMPDIR %s is left behind" % work)
        else:
            keep_nothing_behind(work)
    return work
