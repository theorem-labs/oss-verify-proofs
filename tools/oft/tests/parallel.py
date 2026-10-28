"""The tools' tests across processes: one process per test class.

    cd tools && python3 -m oft.tests.parallel [--jobs N]

`python3 -B -m unittest discover -s oft/tests -t .` runs the same tests in one
process and is what to use for one class or one test.  This runner is for CI,
where the serial run sits on the critical path of every push: it runs each test
class discovery finds in a process of its own, prints every class's output
whole in one order (the class names, sorted) whatever order the processes
finish in, and exits 1 naming every test that failed.  A class whose process
writes no report -- it was killed, or `unittest` could not import its module --
is itself named as a failure, so nothing is lost without the step failing.

The standard library only: the tests job installs tools/oft/requirements.txt
and nothing else.
"""
import argparse
import concurrent.futures
import json
import os
import subprocess
import sys
import tempfile
import time
import unittest

from oft import lint

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.dirname(os.path.dirname(HERE))          # tools/oft/tests -> tools
# the id unittest gives a module it could not import: the module stands for itself, as its own "class"
FAILED_IMPORT = "unittest.loader._FailedTest."


def _flatten(suite):
    for x in suite:
        if isinstance(x, unittest.TestSuite):
            yield from _flatten(x)
        else:
            yield x


def class_names(start=HERE, top=TOOLS):
    """Every test class `unittest discover` finds under start, sorted, with the number of tests it found in each."""
    suite = unittest.TestLoader().discover(start_dir=start, top_level_dir=top)
    names = {}
    for t in _flatten(suite):
        ident = t.id()
        name = ident[len(FAILED_IMPORT):] if ident.startswith(FAILED_IMPORT) else ident.rsplit(".", 1)[0]
        names[name] = names.get(name, 0) + 1
    return dict(sorted(names.items()))


def _worker(name, report):
    """One test class, in this process: its output to stdout, its counts and every failing test's id to `report`."""
    result = unittest.TextTestRunner(stream=sys.stdout, verbosity=2).run(
        unittest.TestLoader().loadTestsFromName(name))
    failed = [t.id() for t, _ in result.errors + result.failures] + [t.id() for t in result.unexpectedSuccesses]
    with open(report, "w", encoding="utf-8") as f:
        json.dump({"tests": result.testsRun, "skipped": len(result.skipped), "failed": failed}, f)
    return 0 if result.wasSuccessful() else 1


def _spawn(name, expected, reports, out, top=TOOLS):
    """Run one class in a process of its own; return (name, seconds, its whole output, its report)."""
    report = os.path.join(reports, name)
    path = os.pathsep.join(p for p in (top, TOOLS if top != TOOLS else None, os.environ.get("PYTHONPATH")) if p)
    env = dict(os.environ, PYTHONPATH=path)
    started = time.monotonic()
    # -B and stderr into stdout: no .pyc beside the tests (oft lint reports a derived file), and one stream, so the
    # class's output is printed in the order it was written
    r = subprocess.run([sys.executable, "-B", "-m", "oft.tests.parallel", "--one", name, "--report", report],
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=env)
    seconds = time.monotonic() - started
    try:
        with open(report, encoding="utf-8") as f:
            got = json.load(f)
    except (OSError, ValueError):
        # no report, whatever the exit status: a sys.exit(0) or os._exit(0) on the way ends the process silently
        got = {"tests": 0, "skipped": 0, "failed": ["%s (its process exited %d and wrote no report; see its output above)"
                                                    % (name, r.returncode)]}
    if r.returncode != 0 and not got["failed"]:
        got["failed"] = ["%s (its process exited %d; see its output above)" % (name, r.returncode)]
    if got["tests"] < expected and not got["failed"]:
        got["failed"] = ["%s (ran %d of the %d test(s) discovery found)" % (name, got["tests"], expected)]
    print("%-4s %6.1fs  %s" % ("FAIL" if got["failed"] else "ok", seconds, name), file=out, flush=True)
    return name, seconds, r.stdout, got


def run(jobs=None, out=sys.stdout, progress=sys.stderr, start=HERE, top=TOOLS):
    names = class_names(start, top)
    if not names:
        # `unittest discover`, which this replaces, exits 5 when no test ran
        print("no test class found under %s" % start, file=out)
        return 1
    jobs = jobs or lint.default_jobs()
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="oft-tests-") as reports:
        with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:   # each thread waits on one process
            done = list(pool.map(lambda kv: _spawn(kv[0], kv[1], reports, progress, top), names.items()))
    wall = time.monotonic() - started
    tests = skipped = 0
    failed = []
    for name, seconds, output, got in done:
        print("%s\n%s (%d test(s), %.1f s)\n%s" % ("=" * 70, name, got["tests"], seconds, "=" * 70), file=out)
        out.write(output)
        tests += got["tests"]
        skipped += got["skipped"]
        failed += got["failed"]
    print("\nran %d test(s) in %d class(es) over %d process(es) in %.1f s (%d skipped)"
          % (tests, len(names), jobs, wall, skipped), file=out)
    if failed:
        print("FAILED (%d):" % len(failed), file=out)
        for ident in failed:
            print("    %s" % ident, file=out)
        return 1
    print("OK", file=out)
    return 0


def _processes(text):
    n = int(text)
    if n < 1:
        raise argparse.ArgumentTypeError("at least one process")
    return n


def main(argv=None):
    p = argparse.ArgumentParser(prog="oft.tests.parallel", description=__doc__.split("\n\n")[0])
    p.add_argument("--jobs", type=_processes,
                   help="processes to run at once (default: every CPU this process may run on)")
    p.add_argument("--one", metavar="CLASS", help=argparse.SUPPRESS)      # one worker, started by run()
    p.add_argument("--report", help=argparse.SUPPRESS)
    a = p.parse_args(argv)
    if a.one:
        return _worker(a.one, a.report)
    return run(a.jobs)


if __name__ == "__main__":
    sys.exit(main())
