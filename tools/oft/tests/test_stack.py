"""oft check's stack (OSSV-162 T4).  The rule is the CI/CD lead's (2026-11-01 06:57Z, and its answer of 08:36Z to the
plan's item (h)) and the stream lead's (07:16Z): the soft limit becomes min(hard, STACK_NEEDED), an unlimited hard limit
counted as infinite; no hard limit is refused; the stack a process gets is measured and printed, with the runtime the
gate's test names; and a step that runs out of stack fails as "stack exhausted", apart from a proof that does not
compile.  Each test's docstring or first comment says how today's check.py fails it."""
import io
import os
import re
import resource
import shutil
import signal
import subprocess
import sys
import tempfile
import tracemalloc
import types
import unittest
from unittest import mock

from oft import check, facts
from oft.tests import test_fetch_check   # its Check's helpers; importing the class would run its tests here too
from oft.tests.helpers import tree
from oft.tests.test_fetch_check import HAVE_ZSTD, run

STACK, INF = resource.RLIMIT_STACK, resource.RLIM_INFINITY
MIB, GIB = 1 << 20, 1 << 30
TOOLS = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
UNIT = "zlib/checksum_fuzzer"
PROOF = "proofs/zlib/checksum_fuzzer/plain_halts"
OVERFLOW = "File \"./Proof.v\", line 1, characters 0-20:\nError: Stack overflow.\n"
TYPE_ERROR = 'Error: The term "x" has type "nat" while it is expected to have type "bool".\n'


def lowered(hard):
    """A preexec_fn that lowers the stack's hard limit to hard (any process may lower its own), the soft one with it."""
    return lambda: resource.setrlimit(STACK, (min(8 * MIB, hard), hard))


def can_lower_to(hard):
    """Whether this process's hard limit is at least hard, so that a child can be given hard."""
    now = resource.getrlimit(STACK)[1]
    return now == INF or (hard != INF and now >= hard)


def child_env(**more):
    """This process's environment for a Python child that imports these tools: tools/ first on PYTHONPATH, and the
    rest of it kept (the runner image puts the tools' dependencies there)."""
    return dict(os.environ, PYTHONPATH=os.pathsep.join([TOOLS] + [p for p in os.environ.get("PYTHONPATH", "").split(
        os.pathsep) if p]), **more)


class Limits(unittest.TestCase):
    """raise_stack_limit, one test for each case of the rule, against a stand-in getrlimit and setrlimit."""

    def limits(self, soft, hard):
        """(what raise_stack_limit returns, the limits it set) when the process starts with soft and hard."""
        put = []
        with mock.patch.object(resource, "getrlimit", return_value=(soft, hard)), \
                mock.patch.object(resource, "setrlimit", side_effect=lambda r, l: put.append((r, l))):
            got = check.raise_stack_limit()
        return got, put

    def test_an_unlimited_hard_limit_gets_the_finite_stack_needed(self):
        # today: setrlimit(STACK, (INF, INF))
        self.assertEqual(self.limits(8 * MIB, INF), ((8 * MIB, INF, check.STACK_NEEDED, INF),
                                                      [(STACK, (check.STACK_NEEDED, INF))]))

    def test_a_large_finite_hard_limit_gets_the_finite_stack_needed(self):
        # today: soft = hard, 64 GiB under the old `ulimit -s 67108864`, which broke zstd's thread pool
        for hard in (check.STACK_NEEDED, 4 * GIB, 64 * GIB):
            with self.subTest(hard=hard):
                self.assertEqual(self.limits(8 * MIB, hard)[1], [(STACK, (check.STACK_NEEDED, hard))])

    def test_a_small_finite_hard_limit_keeps_soft_equal_to_hard(self):
        # today: CheckError "the stack's hard limit is ... bytes; Rocq needs at least 1073741824"
        for hard in (8 * MIB, 128 * MIB, check.STACK_NEEDED - 1):
            with self.subTest(hard=hard):
                self.assertEqual(self.limits(min(8 * MIB, hard), hard), ((min(8 * MIB, hard), hard, hard, hard),
                                                                         [(STACK, (hard, hard))]))

    def test_a_thread_starts_under_the_limit_oft_sets(self):
        """A process oft starts can start a thread: glibc gives each new thread a stack of the soft limit's size, so
        the soft limit must stay finite and well below the memory.  Under a 4 TiB hard limit today's soft = hard
        makes that thread's stack 4 TiB, which a host with less memory than that refuses."""
        script = ("import resource, subprocess, sys\n"
                  "resource.setrlimit(resource.RLIMIT_STACK, (8 << 20, %s))\n"
                  "from oft import check\n"
                  "check.raise_stack_limit()\n"
                  "sys.exit(subprocess.run([sys.executable, '-c', 'import threading; t = threading.Thread(target=int);"
                  " t.start(); t.join()']).returncode)\n")
        for hard in (INF, 4 << 40):
            with self.subTest(hard=hard):
                if not can_lower_to(hard):
                    self.skipTest("this host's stack hard limit is below %s" % hard)
                r = subprocess.run([sys.executable, "-c", script % ("resource.RLIM_INFINITY" if hard == INF else hard)],
                                   capture_output=True, text=True, env=child_env())
                self.assertEqual(r.returncode, 0, r.stdout + r.stderr)


class Words(unittest.TestCase):
    def test_a_stack_overflow_is_stack_exhausted_and_a_type_error_is_not(self):
        # today: check has no stack_exhausted (AttributeError)
        self.assertTrue(check.stack_exhausted("File x\nError: Stack overflow.\n", 1))
        self.assertTrue(check.stack_exhausted("FAIL a/b: p: stack exhausted at 7 MiB (see l)\n", 1))
        self.assertTrue(check.stack_exhausted("", -signal.SIGSEGV))
        self.assertTrue(check.stack_exhausted("", 139))
        # rocq under dune (compile_lib): dune says how the process it ran died, and exits 1
        self.assertTrue(check.stack_exhausted("sh x (got signal SEGV)\n", 1))
        self.assertFalse(check.stack_exhausted(TYPE_ERROR, 1))
        self.assertFalse(check.stack_exhausted("", -signal.SIGKILL))

    def test_the_words_are_found_in_a_large_log_without_reading_it_whole(self):
        """_failed_run asks stack_exhausted_in, which reads the log in pieces: a build that fails after hours of
        output leaves a log with no bound of its own, and reading it whole took about two bytes of memory for each
        byte of log.  The word is at the end, so the whole file is read, and it is found across a piece boundary."""
        size = 64 * MIB
        with tempfile.TemporaryDirectory() as d:
            log = os.path.join(d, "compile.log")
            with open(log, "wb") as f:
                f.write(b"a line of a build that says nothing\n" * (size // 36))
                # the word itself straddles the boundary of the last piece: a reader without the overlap misses it
                at = f.tell()
                f.write(b"x" * (-(at + 14) % check.STACK_CHUNK) + b"dune: sh (got signal SEGV)\n")
            self.assertGreater(os.path.getsize(log), 4 * check.STACK_CHUNK)
            # through _failed_run, the caller: it must ask for the log in pieces, as stack_exhausted_in reads it
            tracemalloc.start()
            try:
                said = str(check._failed_run("a/B.v", log, 1, d))
                peak = tracemalloc.get_traced_memory()[1]
            finally:
                tracemalloc.stop()
            self.assertTrue(check.stack_exhausted_in(log, 1))
            self.assertRegex(said, r"^a/B\.v: stack exhausted ")
            # the pieces and their overlap, not the log: well under the 128 MiB that reading it whole takes
            self.assertLess(peak, 8 * MIB, peak)
            # a log without the words, read the same way
            plain = os.path.join(d, "plain.log")
            with open(plain, "wb") as f:
                f.write(b"a line of a build that says nothing\n" * (size // 36))
            self.assertFalse(check.stack_exhausted_in(plain, 1))
            # the returncode alone decides for a log that is not there
            self.assertTrue(check.stack_exhausted_in(os.path.join(d, "none.log"), -signal.SIGSEGV))
            self.assertFalse(check.stack_exhausted_in(os.path.join(d, "none.log"), 1))

    def test_a_stack_exhausted_failure_quotes_the_log_too(self):
        """_failed_run's two parts are one message: the stack-exhausted wording of stack_exhausted_words, and after
        it the log's Error: blocks (log_errors)."""
        with tempfile.TemporaryDirectory() as d:
            log = os.path.join(d, "compile.log")
            with open(log, "w") as f:
                f.write('File "a/B.v", line 3, characters 0-5:\nError: Stack overflow.\n')
            e = check._failed_run("a/B.v", log, 1, d)
            first, rest = str(e).split("\n", 1)
            self.assertRegex(first, r"^a/B\.v: stack exhausted .*\(see .*compile\.log\)$")
            self.assertIn("  | Error: Stack overflow.", rest)

    def test_no_cc_gives_not_measured(self):
        # today: check has no measure_stack
        with tempfile.TemporaryDirectory() as d, mock.patch.dict(os.environ, {"PATH": d}):
            self.assertEqual(check.measure_stack(d), (None, "not measured (no cc on PATH)"))

    @unittest.skipUnless(shutil.which("cc"), "no C compiler here; the hosted runners have one")
    def test_the_probe_measures_the_soft_limit(self):
        """The probe faults at the soft limit (less what the process's start used), and stops at its ceiling."""
        script = ("import resource, sys\nresource.setrlimit(resource.RLIMIT_STACK, (%d, resource.getrlimit("
                  "resource.RLIMIT_STACK)[1]))\nfrom oft import check\nprint(repr(check.measure_stack(sys.argv[1])))\n")
        cases = [(32 * MIB, lambda n, text: self.assertTrue(24 * MIB <= n <= 32 * MIB and text == "%d MiB" % (n >> 20),
                                                             (n, text)))]
        if can_lower_to(512 * MIB):
            cases.append((512 * MIB, lambda n, text: self.assertEqual((n, text), (256 * MIB, "at least 256 MiB"))))
        for soft, judge in cases:
            with self.subTest(soft=soft), tempfile.TemporaryDirectory() as d:
                r = subprocess.run([sys.executable, "-c", script % soft, d], capture_output=True, text=True,
                                   env=child_env())
                self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
                judge(*eval(r.stdout))


class Stack(unittest.TestCase):
    """The stack line and the failure class, through oft check."""

    _check = test_fetch_check.Check
    ready, tools, _proof, _two_proofs_and_a_library = (_check.ready, _check.tools, _check._proof,
                                                       _check._two_proofs_and_a_library)

    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.old_path = os.environ["PATH"]
        self.limits = resource.getrlimit(STACK)
        env = mock.patch.dict(os.environ)
        env.start()
        self.addCleanup(env.stop)
        os.environ.pop("OFT_STACK_USABLE", None)
        measured = getattr(check, "_MEASURED", [])   # no process measure left from another test
        measured.clear()
        self.addCleanup(measured.clear)

    def tearDown(self):
        resource.setrlimit(STACK, self.limits)
        os.environ["PATH"] = self.old_path
        self.d.cleanup()

    def rocq(self, says, bin_dir=None):
        """A rocq first on PATH whose `dep -sort` lists the files it is given and whose `compile` of a proof's file
        prints says and exits 1; any other call goes to the rocq already on PATH (Tools' stand-in), if any."""
        bin_dir = bin_dir or os.path.join(self.d.name, "overflow-bin")
        os.makedirs(bin_dir, exist_ok=True)
        with open(os.path.join(bin_dir, "says.txt"), "w") as f:
            f.write(says)
        path = os.path.join(bin_dir, "rocq")
        with open(path, "w") as f:
            f.write('#!/bin/sh\n'
                    'if [ "$1" = dep ]; then for a in "$@"; do case "$a" in *.v) echo "$a" ;; esac; done; exit 0; fi\n'
                    'case "$*" in compile*/Proof.v) cat "%s"; exit 1 ;; esac\n'
                    'PATH="${PATH#*:}" exec rocq "$@"\n' % os.path.join(bin_dir, "says.txt"))
        os.chmod(path, 0o755)
        if not os.environ["PATH"].startswith(bin_dir + os.pathsep):
            os.environ["PATH"] = bin_dir + os.pathsep + os.environ["PATH"]

    def check_proof_error(self, t):
        """check_proof's CheckError for the fixture's plain_halts proof."""
        st = next(x for x in facts.load(t.root).statements() if x.id == UNIT + "/plain_halts")
        work = tempfile.mkdtemp(dir=self.d.name)
        with self.assertRaises(check.CheckError) as e:
            # the OLD call, as the two gate-job scripts make it: no counter
            check.check_proof(t.root, st, st.proof, set(), work, io.StringIO(), {})
        return str(e.exception)

    def test_a_compile_that_overflows_is_reported_with_the_measured_size(self):
        # today: "does not compile" for both
        with tree() as t:
            self._proof(t)
            os.environ["OFT_STACK_USABLE"] = "7 MiB"
            self.rocq(OVERFLOW)
            said = self.check_proof_error(t)
            self.assertIn("%s: stack exhausted at 7 MiB (see " % PROOF, said)
            self.assertNotIn("does not compile", said)
            self.rocq(TYPE_ERROR)
            said = self.check_proof_error(t)
            self.assertIn("%s: does not compile (see " % PROOF, said)
            self.assertNotIn("stack exhausted", said)

    def test_a_failure_with_no_prepared_stack_still_has_a_defined_text(self):
        # today: "does not compile"
        with tree() as t, mock.patch.object(check, "measure_stack", create=True,
                                            return_value=(None, "not measured (no cc on PATH)")):
            self._proof(t)
            self.rocq(OVERFLOW)
            self.assertIn("stack exhausted (the stack was not measured: no cc on PATH)", self.check_proof_error(t))
            os.environ["OFT_STACK_USABLE"] = "at least 256 MiB"
            self.assertIn("stack exhausted with at least 256 MiB usable", self.check_proof_error(t))

    def test_a_library_build_that_overflows_is_stack_exhausted(self):
        """compile_lib builds the library with dune, which prints what rocq said, or how it died, and exits 1."""
        # today: "does not compile" for each
        bin_dir = os.path.join(self.d.name, "dune-bin")
        os.makedirs(bin_dir)
        os.environ["PATH"] = bin_dir + os.pathsep + os.environ["PATH"]
        os.environ["OFT_STACK_USABLE"] = "7 MiB"
        lib = "proofs/zlib/checksum_fuzzer/lib"
        for says, words in ((OVERFLOW, "stack exhausted at 7 MiB"), ("sh x (got signal SEGV)\n", "stack exhausted at 7 MiB"),
                            (TYPE_ERROR, "does not compile")):
            with self.subTest(says=says), tree() as t:
                t.write(lib + "/Base.v", "Definition one := 1.\n")
                self._proof(t)
                with open(os.path.join(bin_dir, "says.txt"), "w") as f:
                    f.write(says)
                with open(os.path.join(bin_dir, "dune"), "w") as f:
                    f.write('#!/bin/sh\ncat "%s"\nexit 1\n' % os.path.join(bin_dir, "says.txt"))
                os.chmod(os.path.join(bin_dir, "dune"), 0o755)
                h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
                with self.assertRaises(check.CheckError) as e:
                    check.compile_lib(t.root, h, tempfile.mkdtemp(dir=self.d.name), {}, io.StringIO())
                self.assertIn("%s: %s (see " % (lib, words), str(e.exception))

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_proof_jobs_name_a_child_s_stack_failure(self):
        """Each statement's process writes rocq's output into its own compile.log, so the parent reads the child's
        `: stack exhausted ` line, and each child takes the parent's measure (--stack-from-parent).  Today the parent's
        line is "its process exited 1"."""
        real_popen = subprocess.Popen
        for library in (True, False):
            with self.subTest(library=library), tree() as t:
                self.d.cleanup()
                self.d = tempfile.TemporaryDirectory()   # each case its own assets, stand-ins and logs
                os.environ["PATH"] = self.old_path
                self.ready(t)
                if library:
                    self._two_proofs_and_a_library(t)
                else:
                    self._proof(t)
                    self._proof(t, "Theorem plain_halts_may_fail_holds : True. Proof. exact I. Qed.\n",
                                s="plain_halts_may_fail")
                self.tools()
                self.rocq(OVERFLOW)
                started = []

                def popen(cmd, *a, **kw):
                    if "oft.check" in cmd:
                        started.append(cmd)
                    return real_popen(cmd, *a, **kw)

                os.environ.pop("OFT_STACK_USABLE", None)
                with mock.patch.object(check, "measure_stack", create=True, return_value=(7 * MIB, "7 MiB")), \
                        mock.patch.object(subprocess, "Popen", side_effect=popen):
                    rc, out = run(check.run, t.root, [UNIT], parts="proofs", proof_jobs=2)
                self.assertEqual(rc, 1, out)
                fails = [line for line in out.splitlines() if line.startswith("FAIL ")]
                self.assertEqual(len(fails), 2, out)
                for line in fails:
                    self.assertRegex(line, r"^FAIL proofs/zlib/checksum_fuzzer/plain_halts(_may_fail)?: stack exhausted "
                                           r"at 7 MiB \(see .*\.log\)$")
                self.assertEqual(len(started), 2, started)
                self.assertTrue(all("--stack-from-parent" in cmd for cmd in started), started)
                self.assertTrue(all(("--lib" in cmd) == library for cmd in started), started)
                self.assertIn("  | stack: 7 MiB usable (", out)

    def test_the_stack_line_is_no_oft_check_line(self):
        # today: no "stack: " line
        with tree() as t, mock.patch.object(check, "measure_stack", create=True, return_value=(7 * MIB, "7 MiB")):
            t.write("toolchain/allowed-axioms.txt", "Corelib.Init.Something.prim\n")
            rc, out = run(check.run, t.root, [UNIT], parts="proofs")   # the unit has no proof: it fails, and says so
            lines = out.splitlines()
            self.assertEqual([l for l in lines if l.startswith("stack: ")][0][:len("stack: 7 MiB usable (soft ")],
                             "stack: 7 MiB usable (soft ")
            self.assertEqual(len([l for l in lines if l.startswith("stack: ")]), 1, out)
            self.assertEqual(len([l for l in lines if l.startswith("oft check: ")]), 1, out)
            self.assertEqual(os.environ["OFT_STACK_USABLE"], "7 MiB")

    def prepare(self, release, child=False, soft=8 * MIB, hard=INF):
        """prepare_stack's line, on a kernel whose release is release, in a process that starts with soft and hard."""
        state = [(soft, hard)]
        out = io.StringIO()
        with mock.patch.object(resource, "getrlimit", side_effect=lambda r: state[-1]), \
                mock.patch.object(resource, "setrlimit", side_effect=lambda r, l: state.append(l)), \
                mock.patch.object(os, "uname", return_value=types.SimpleNamespace(release=release)), \
                mock.patch.object(check, "measure_stack", create=True, return_value=(7 * MIB, "7 MiB")):
            check.prepare_stack(self.d.name, out, child=child)
        return out.getvalue()

    def test_the_stack_line_names_the_runtime_by_the_gate_s_test(self):
        # today: no prepare_stack, no line
        self.assertEqual(self.prepare("4.19.0-gvisor"), "stack: 7 MiB usable (soft 2147483648, hard unlimited; started "
                                                        "with soft 8388608, hard unlimited; runtime gvisor)\n")
        self.assertEqual(self.prepare("6.8.0-1017-gcp", soft=8 * MIB, hard=128 * MIB),
                         "stack: 7 MiB usable (soft 134217728, hard 134217728; started with soft 8388608, hard "
                         "134217728; runtime linux)\n")

    def test_a_top_level_check_measures_its_own_stack(self):
        """A check prints its own measure even when it inherited another's, and a statement's process its parent's."""
        os.environ["OFT_STACK_USABLE"] = "999 MiB"
        self.assertTrue(self.prepare("6.8.0").startswith("stack: 7 MiB usable ("))
        self.assertEqual(os.environ["OFT_STACK_USABLE"], "7 MiB")
        os.environ["OFT_STACK_USABLE"] = "999 MiB"
        self.assertTrue(self.prepare("6.8.0", child=True).startswith("stack: 999 MiB usable ("))

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_small_finite_hard_limit_runs(self):
        """`oft check` in a process whose hard limit is 128 MiB, or just below 2 GiB, checks the unit and prints the
        limits it ran with.  Today it exits 1: "FAIL the stack's hard limit is 134217728 bytes; Rocq needs at least
        1073741824"."""
        with tree() as t:
            self.ready(t)
            self._proof(t)
            self.tools()
            argv = [sys.executable, "-m", "oft.check", "--root", t.root, UNIT, "--parts", "proofs"]
            for hard in (128 * MIB, check.STACK_NEEDED - 1):
                with self.subTest(hard=hard):
                    if not can_lower_to(hard):
                        self.skipTest("this host's stack hard limit is below %d" % hard)
                    r = subprocess.run(argv, env=child_env(PYTHONDONTWRITEBYTECODE="1"),
                                       capture_output=True, text=True, preexec_fn=lowered(hard))
                    self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
                    line = [l for l in r.stdout.splitlines() if l.startswith("stack: ")]
                    self.assertEqual(len(line), 1, r.stdout)
                    self.assertIn(" (soft %d, hard %d; started with soft %d, hard %d; runtime " % (
                        hard, hard, min(8 * MIB, hard), hard), line[0])
                    if shutil.which("cc"):   # below the probe's ceiling it names a size, at or above it "at least"
                        m = re.match(r"stack: (?:(\d+) MiB|at least (\d+) MiB) usable ", line[0])
                        self.assertTrue(m, line[0])
                        if m.group(1):
                            self.assertLessEqual(int(m.group(1)), hard >> 20, line[0])
                        else:
                            self.assertGreater(hard, check.STACK_PROBE_CEILING, line[0])
                    self.assertIn("1 step(s) passed, 0 failed", r.stdout)


if __name__ == "__main__":
    unittest.main()
