"""Option D (OSSV-299): dune builds each proof directory
once, with a cache of its own, after the library; check_proof compiles no proof file and audits the dune-built .vo
through a wrapper of oft's own, with oft's own flags.  dune and rocq are stand-ins: check._run is patched, but for the
deadline tests (Deadline), whose stand-in dune is a real process with real children, as dune's rocq workers are."""
import contextlib
import hashlib
import io
import os
import shutil
import sys
import tempfile
import time
import unittest
from unittest import mock

from oft import check, facts
from oft.tests import test_classifier_images as ci
from oft.tests.helpers import tree

PD = "proofs/zlib/checksum_fuzzer/plain_halts"
PD2 = "proofs/zlib/checksum_fuzzer/plain_halts_may_fail"
PD3 = "proofs/zlib/checksum_fuzzer/ubsan_halts"
LIB = "proofs/zlib/checksum_fuzzer/lib"
TRACE = os.path.join("_build", "trace.csexp")


def atom(s):
    b = s.encode()
    return b"%d:%s" % (len(b), b)


def sexp(x):
    return b"(" + b"".join(sexp(y) for y in x) + b")" if isinstance(x, list) else atom(x)


def trace(*compiles, env_secret="TOKEN=secret"):
    """A _build/trace.csexp as dune 3.23.0 writes it: a config event with the environment, then one process start
    per rocq compile (prog, dir _build/default, process_args)."""
    out = sexp(["config", "init", "1", ["version", "3.23.0"], ["env", [env_secret]]])
    for i, args in enumerate(compiles):
        out += sexp(["process", "start", str(i), ["process_args", ["compile"] + args], ["pid", "1"],
                     ["prog", "/opt/bin/rocq"], ["dir", "_build/default"]])
    return out


DEFAULT_FLAGS = ["-q", "-w", "-deprecated-native-compiler-option", "-native-output-dir", ".", "-native-compiler", "on",
                 "-nI", "/opt/lib/rocq-runtime/kernel", "-nI", PD, "-boot", "-R", "/opt/lib/coq/theories", "Corelib",
                 "-Q", "theories", "OssFuzzTheorems.Core", "-R", PD, "P"]


class Fake:
    """check._run: dune makes each explicit .vo target in root/_build/default (but those in `broken`), writes `log` into
    its log and, when `trace_bytes` is given, root/_build/trace.csexp; the wrapper's rocq compile writes
    assumptions.out."""

    def __init__(self, root, broken=(), log="", trace_bytes=None, assumptions="Axioms:\nCorelib.Init.X.prim : Prop\n"):
        self.root, self.broken, self.log, self.trace = root, broken, log, trace_bytes
        self.assumptions, self.calls = assumptions, []

    def __call__(self, cmd, cwd, log, timeout=None, env=None, watch=None):
        self.calls.append((list(cmd), env))
        with open(log, "a", encoding="utf-8") as f:
            f.write("$ %s\n" % " ".join(cmd))
            if cmd[0] == "dune":
                f.write(self.log)
        if cmd[0] == "dune":
            for a in cmd:
                if a.endswith(".vo") and not any(b in a for b in self.broken):
                    p = os.path.join(self.root, a)
                    os.makedirs(os.path.dirname(p), exist_ok=True)
                    open(p, "w").close()
            if self.trace is not None and any(a.startswith("_build/default/proofs/") for a in cmd):
                os.makedirs(os.path.join(self.root, "_build"), exist_ok=True)
                with open(os.path.join(self.root, TRACE), "wb") as f:
                    f.write(self.trace)
            return 1 if any(b in " ".join(cmd) for b in self.broken) else 0
        if cmd[:2] == ["rocq", "compile"] and cmd[-1].endswith("Wrapper.v"):
            with open(os.path.join(cwd, "assumptions.out"), "w") as f:
                f.write(self.assumptions)
        return 0

    def dune(self):
        return [(c, e) for c, e in self.calls if c[0] == "dune"]

    def rocq(self):
        return [c for c, _ in self.calls if c[0] == "rocq"]


class Audit(unittest.TestCase):
    def setUp(self):
        self.ctx = tree()
        self.t = self.ctx.__enter__()
        self.addCleanup(self.ctx.__exit__, None, None, None)
        self.work = self.t.path("_work")
        os.makedirs(self.work)

    def proof(self, s="plain_halts", body=None, bound=None):
        t = self.t
        st = next(x for x in facts.load(t.root).statements() if x.id == "zlib/checksum_fuzzer/" + s)
        y = {"schema": "oss-fuzz-theorems/proof/1", "proves": st.id, "fingerprint": st.fingerprint}
        if bound is not None:
            y["bound"] = bound
        t.put_yaml("proofs/zlib/checksum_fuzzer/%s/proof.yaml" % s, y)
        t.write("proofs/zlib/checksum_fuzzer/%s/Proof.v" % s, body or "Theorem %s_holds : True. Proof. exact I. Qed.\n" % s)
        self.assertEqual(t.generate(), 0, t.last_output)

    def two(self, lib=False):
        if lib:
            self.t.write(LIB + "/Base.v", "Definition one := 1.\n")
        self.proof()
        self.proof("plain_halts_may_fail")

    def pinned_binaries(self):
        """Put a stand-in at each published build's path of zlib/checksum_fuzzer and make harness.yaml pin exactly
        those bytes, as a fetched tree has them: check.run compares every published build with its pin before a part
        that compiles them (PARTS_THAT_COMPILE_THE_BINARIES)."""
        rel = "projects/zlib/checksum_fuzzer/harness.yaml"
        y = self.t.yaml(rel)
        for b, _ in self.harness().builds():
            content = "stand-in %s\n" % b
            self.t.write(self.harness().elf_path(b), content)
            y["builds"][b]["bytes"] = len(content.encode())
            y["builds"][b]["sha256"] = hashlib.sha256(content.encode()).hexdigest()
        self.t.put_yaml(rel, y)

    def harness(self):
        return facts.load(self.t.root).projects["zlib"].harnesses["checksum_fuzzer"]

    def build(self, fake, dirs=(PD, PD2)):
        out, libs = io.StringIO(), {}
        with mock.patch.object(check, "_run", fake):
            got = check.build_proof_dirs(self.t.root, self.harness(), self.work, out, list(dirs), libs)
        return got, libs, out.getvalue()

    def audit(self, fake, s="plain_halts", libs=None):
        h = self.harness()
        st = h.statements[s]
        out = io.StringIO()
        with mock.patch.object(check, "_run", fake):
            if libs is None:
                libs = {}
                check.build_proof_dirs(self.t.root, h, self.work, io.StringIO(), [st.proof.path], libs)
            check.check_proof(self.t.root, st, st.proof, {"Corelib.Init.X.prim"}, self.work, out, libs)
        return out.getvalue()

    # ---------------------------------------------------------------- the build

    def test_build_proof_dirs_passes_explicit_vo_targets_for_every_v_with_own_cache_after_the_library(
            self):
        self.two(lib=True)
        self.t.write(PD + "/Helper.v", "Definition h := 1.\n")
        fake = Fake(self.t.root, log="        rocq %s/Proof.{glob,vo}\n        rocq %s/Proof.{glob,vo}\n" % (PD, PD2),
                    trace_bytes=trace(DEFAULT_FLAGS + [PD + "/Proof.v"], DEFAULT_FLAGS + [PD2 + "/Proof.v"]))
        got, _, out = self.build(fake)
        self.assertEqual(got, {PD: None, PD2: None})
        (s_cmd, s_env), (lib_cmd, lib_env), (cmd, env) = fake.dune()
        self.assertIn("@@theories/default", s_cmd, "the statement side the library reads is built first")
        self.assertTrue(s_env["DUNE_CACHE_ROOT"].startswith(self.work + os.sep), "in a cache of its own")
        self.assertTrue(any(a.startswith(LIB) for a in lib_cmd), "then the library")
        self.assertIsNone(lib_env, "the library build keeps the caller's DUNE_CACHE")
        self.assertEqual(env.get("DUNE_CACHE"), os.environ.get("DUNE_CACHE"), "the library's DUNE_CACHE")
        self.assertTrue(env["DUNE_CACHE_ROOT"].startswith(self.work + os.sep), "a cache of its own")
        targets = [a for a in cmd if a.endswith(".vo")]
        self.assertEqual(targets, ["_build/default/%s/Helper.vo" % PD, "_build/default/%s/Proof.vo" % PD,
                                   "_build/default/%s/Proof.vo" % PD2])
        self.assertFalse([a for a in cmd if a.startswith("@")], "no alias: @@dir/default would build no proof")
        self.assertIn("2 proof director", out)

    def test_the_proof_build_width_is_the_one_place_that_decides_dune_s(self):
        """check._jobs (#1785): the cgroup's CPU quota, OFT_JOBS over it, at most this process's affinity."""
        self.two()
        fake = Fake(self.t.root)
        with mock.patch.object(check, "_jobs", return_value=7):
            self.build(fake)
        cmd = fake.dune()[-1][0]
        self.assertEqual(cmd[cmd.index("-j") + 1], "7")

    def test_a_dune_failure_in_one_proof_directory_fails_that_statement_only(self):
        self.two()
        log = ("        rocq %s/Proof.{glob,vo} (exit 1)\n"
               "File \"%s/Proof.v\", line 1, characters 30-31:\nError: nope\n"
               "        rocq %s/Proof.{glob,vo}\n") % (PD, PD, PD2)
        fake = Fake(self.t.root, broken=(PD + "/",), log=log,
                    trace_bytes=trace(DEFAULT_FLAGS + [PD + "/Proof.v"], DEFAULT_FLAGS + [PD2 + "/Proof.v"]))
        got, libs, _ = self.build(fake)
        self.assertIsNone(got[PD2])
        self.assertIn("Error: nope", got[PD])
        self.assertNotIn(PD2, got[PD])
        with self.assertRaises(check.CheckError) as cm:
            self.audit(fake, libs=libs)
        self.assertIn("Error: nope", str(cm.exception))
        self.assertIn("proves zlib/checksum_fuzzer/plain_halts_may_fail", self.audit(fake, "plain_halts_may_fail",
                                                                                     libs=libs))

    def test_a_proof_file_in_a_subdirectory_fails_its_statement_only(self):
        """dune 3.23.0 has no rule for a .v below a proof directory (its generated dune file has no include_subdirs:
        `Don't know how to build`, and that error stops the whole build), so the guard refuses that directory alone."""
        self.two()
        self.t.write(PD + "/sub/Q.v", "Definition q := 3.\n")
        fake = Fake(self.t.root)
        got, _, _ = self.build(fake)
        self.assertIn("%s/sub/Q.v" % PD, got[PD])
        self.assertIsNone(got[PD2])
        self.assertNotIn("_build/default/%s/sub/Q.vo" % PD, fake.dune()[-1][0])

    def test_build_file_guard_walks_each_proof_directory_as_lib_targets_does(self):
        cases = {
            "a hand-edited proof dune": (PD + "/dune", "(rocq.theory (name X) (flags -type-in-type))\n"),
            "dune-workspace at the root": ("dune-workspace", "(lang dune 3.23)\n"),
            "a dune-project in a subdirectory": (PD + "/sub/dune-project", "(lang dune 3.23)\n"),
            "a dune in a subdirectory": (PD + "/sub/dune", "(rule)\n"),
            "a dune-file beside Proof.v": (PD + "/dune-file", "(rule)\n"),
            "a build file above": ("proofs/zlib/dune", "(env (_ (rocq (flags -type-in-type))))\n"),
        }
        for why, (path, text) in cases.items():
            with self.subTest(why):
                self.setUp()
                self.two()
                self.t.write(path, text)
                got, _, _ = self.build(Fake(self.t.root), dirs=(PD,))
                self.assertIn(path, got[PD])
        for kind in ("file", "directory"):
            with self.subTest(kind):
                self.setUp()
                self.two()
                target = self.t.path(PD2 + "/Proof.v") if kind == "file" else self.t.path(PD2)
                os.symlink(target, self.t.path(PD + "/Link" + (".v" if kind == "file" else "")))
                got, _, _ = self.build(Fake(self.t.root), dirs=(PD,))
                self.assertIn("symbolic link", got[PD])

    # ---------------------------------------------------------------- the flags dune ran

    def test_a_proof_directory_rocq_argv_in_the_trace_outside_the_allowlist_refuses_the_unit(self):
        log = "        rocq %s/Proof.{glob,vo}\n" % PD
        for flag in (["-type-in-type"], ["-impredicative-set"], ["-allow-rewrite-rules"], ["-indices-matter"],
                     ["-noinit"], ["-load-vernac-source", "x.v"], ["-set", "Foo"]):
            with self.subTest(flag=flag):
                self.setUp()
                self.two()
                fake = Fake(self.t.root, log=log, trace_bytes=trace(DEFAULT_FLAGS + flag + [PD + "/Proof.v"]))
                got, _, _ = self.build(fake)
                for d in (PD, PD2):
                    self.assertIn(flag[0], got[d])
                    self.assertIn(PD, got[d])
        with self.subTest("the generated set"):
            self.setUp()
            self.two()
            fake = Fake(self.t.root, log=log, trace_bytes=trace(DEFAULT_FLAGS + [PD + "/Proof.v"]))
            got, _, _ = self.build(fake)
            self.assertEqual(got, {PD: None, PD2: None})

    def test_a_proof_rule_the_log_names_without_a_compile_in_the_trace_refuses_the_unit(self):
        self.two()
        fake = Fake(self.t.root, log="        rocq %s/Proof.{glob,vo}\n" % PD, trace_bytes=trace())
        got, _, _ = self.build(fake)
        self.assertIn("no rocq compile", got[PD])

    def test_the_trace_s_environment_is_never_printed(self):
        self.two()
        fake = Fake(self.t.root, log="        rocq %s/Proof.{glob,vo}\n" % PD,
                    trace_bytes=trace(DEFAULT_FLAGS + ["-noinit", PD + "/Proof.v"], env_secret="TOKEN=hunter2"))
        got, _, out = self.build(fake)
        self.assertNotIn("hunter2", out + "".join(v or "" for v in got.values()))

    def test_a_second_run_in_the_same_work_directory_judges_only_its_own_log(self):
        """The logs are appended to: the second, up-to-date run must not read the first run's rule lines (on
        coturn/FuzzStunClient it did, and refused every directory for want of a compile in the second trace)."""
        self.two()
        first = Fake(self.t.root, log="        rocq %s/Proof.{glob,vo}\n        rocq %s/Proof.{glob,vo}\n" % (PD, PD2),
                     trace_bytes=trace(DEFAULT_FLAGS + [PD + "/Proof.v"], DEFAULT_FLAGS + [PD2 + "/Proof.v"]))
        self.assertEqual(self.build(first)[0], {PD: None, PD2: None})
        got, _, out = self.build(Fake(self.t.root, log="", trace_bytes=trace()))
        self.assertEqual(got, {PD: None, PD2: None})
        self.assertIn("0 rules run", out)

    def test_an_up_to_date_second_run_with_nothing_rebuilt_and_no_argv_in_the_trace_still_passes(self):
        self.two()
        fake = Fake(self.t.root, log="", trace_bytes=trace())
        got, libs, _ = self.build(fake)
        self.assertEqual(got, {PD: None, PD2: None})
        self.assertIn("proves zlib/checksum_fuzzer/plain_halts", self.audit(fake, libs=libs))

    # ---------------------------------------------------------------- the audit

    def test_check_proof_compiles_no_proof_file_and_reads_assumptions_against_dune_built_vo(self):
        self.two()
        fake = Fake(self.t.root)
        out = self.audit(fake)
        compiles = [c for c in fake.rocq() if c[1] == "compile"]
        self.assertEqual(len(compiles), 1, compiles)
        self.assertTrue(compiles[0][-1].endswith("/Wrapper.v"))
        built = self.t.path("_build", "default", PD)
        self.assertIn(["-Q", built, "OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.plain_halts"],
                      [compiles[0][i:i + 3] for i in range(len(compiles[0]))])
        self.assertFalse([c for c in fake.rocq() if c[1] == "dep"], "no rocq dep")
        self.assertIn("proves zlib/checksum_fuzzer/plain_halts; assumptions: 1 axioms, all allowed", out)

    def test_check_proof_applies_a_classifier_bound_statement_to_its_bound_and_a_halts_statement_to_none(self):
        """wrapper_args: a classifier-bound statement takes its b first (shapes.takes_bound), as a bound statement
        does, so the wrapper applies it to the b its proof.yaml names; a halts statement takes no argument."""
        ci.with_images(self.t)
        self.proof()
        self.proof("asan_bound_diff", bound="1/2")
        self.assertEqual(self.harness().statements["asan_bound_diff"].kind, "classifier-bound")
        for s, args in (("asan_bound_diff", " (1 # 2)"), ("plain_halts", "")):
            with self.subTest(s):
                fake = Fake(self.t.root)
                out = self.audit(fake, s)
                (wrap,) = [c for c in fake.rocq() if c[-1].endswith("Wrapper.v")]
                with open(wrap[-1], encoding="utf-8") as f:
                    wrapper = f.read()
                self.assertIn("Definition certified : %s.Statements.%s%s := " % (self.harness().data["rocq"], s, args),
                              wrapper)
                self.assertIn("proves zlib/checksum_fuzzer/%s%s; assumptions: 1 axioms, all allowed" % (s, args), out)

    def test_a_missing_built_vo_fails_naming_it(self):
        self.two()
        fake = Fake(self.t.root)
        _, libs, _ = self.build(fake)
        os.remove(self.t.path("_build", "default", PD, "Proof.vo"))
        with self.assertRaises(check.CheckError) as cm:
            self.audit(fake, libs=libs)
        self.assertIn("%s/Proof.vo" % PD, str(cm.exception))

    def test_check_proof_without_a_build_fails(self):
        self.two()
        with self.assertRaises(check.CheckError) as cm:
            self.audit(Fake(self.t.root), libs={})
        self.assertIn("build_proof_dirs", str(cm.exception))

    def test_the_wrapper_keeps_ofts_fixed_flags_and_load_path_and_takes_no_argv_from_dune(self):
        self.two(lib=True)
        fake = Fake(self.t.root, log="        rocq %s/Proof.{glob,vo}\n" % PD,
                    trace_bytes=trace(DEFAULT_FLAGS + [PD + "/Proof.v"]))
        self.audit(fake)
        (wrap,) = [c for c in fake.rocq() if c[-1].endswith("Wrapper.v")]
        b = self.t.path("_build", "default")
        h = self.harness()
        want = (["rocq", "compile", "-w", "-all"] + check._loadpath(b, h)
                + ["-Q", os.path.join(b, LIB), "OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib",
                   "-Q", os.path.join(b, PD), "OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.plain_halts"])
        self.assertEqual(wrap[:len(want)], want)
        self.assertEqual(wrap[len(want)], "-Q")
        self.assertFalse(set(wrap) & {"-boot", "-native-compiler", "-q"}, "nothing taken from dune's argv")

    def test_the_proof_claim_line_is_unchanged(self):
        self.two()
        out = self.audit(Fake(self.t.root))
        st = self.harness().statements["plain_halts"]
        self.assertEqual(check.proof_claim(st, out),
                         "%s: proves zlib/checksum_fuzzer/plain_halts; assumptions: 1 axioms, all allowed" % PD)

    def test_run_builds_the_proof_directories_once_after_the_statements(self):
        self.pinned_binaries()
        self.two(lib=True)
        self.t.write("toolchain/allowed-axioms.txt", "Corelib.Init.X.prim\n")
        fake, out = Fake(self.t.root), io.StringIO()
        # raise_stack_limit returns (soft, hard) before and after it; a bare MagicMock unpacks to nothing
        with mock.patch.object(check, "_run", fake), \
                mock.patch.object(check, "raise_stack_limit", return_value=(8 << 20, 8 << 20, 8 << 20, 8 << 20)):
            rc = check.run(self.t.root, ["zlib/checksum_fuzzer"], parts="proofs", out=out)
        self.assertEqual(rc, 0, out.getvalue())
        proof_builds = [c for c, e in fake.dune() if any(a.startswith("_build/default/proofs/") for a in c)]
        self.assertEqual(len(proof_builds), 1)


# A stand-in dune for Deadline: for each target _build/default/<dir>/Proof.vo, in order, at most -j at once, it
# starts a child whose argv is a rocq worker's (`--kind=compile ... <dir>/Proof.v`, as dune 3.23.0 runs rocqworker):
# a directory named in $FAKE_SLOW sleeps 120 s, one in $FAKE_FAIL exits 1, one in $FAKE_SLOWISH sleeps 3 s, any
# other exits 0.  It writes the .vo of each child that exited 0, a --display short line per rule, the
# _build/trace.csexp process start of each `rocq compile`, and exits 1 if any failed: dune 3.23.0 goes on with the
# other targets when one rule fails or its worker is killed (read 2026-11-02: a killed worker prints
# `(got signal KILL)`).
STUB_DUNE = r'''import os, subprocess, sys
args = sys.argv[1:]
root = args[args.index("--root") + 1]
jobs = int(args[args.index("-j") + 1])
want = {k: set(filter(None, os.environ.get(k, "").split(":"))) for k in ("FAKE_SLOW", "FAKE_FAIL", "FAKE_SLOWISH")}
def atom(s):
    return b"%d:%s" % (len(s.encode()), s.encode())
def sexp(x):
    return b"(" + b"".join(sexp(y) for y in x) + b")" if isinstance(x, list) else atom(x)
pending = [t for t in args if t.startswith("_build/default/") and t.endswith(".vo")]
running, trace, bad = [], b"", 0
while pending or running:
    while pending and len(running) < jobs:
        t = pending.pop(0)
        d = os.path.dirname(t[len("_build/default/"):])
        code = ("import time; time.sleep(120)" if d in want["FAKE_SLOW"] else "import sys; sys.exit(1)"
                if d in want["FAKE_FAIL"] else "import time; time.sleep(3)" if d in want["FAKE_SLOWISH"] else "pass")
        running.append((t, d, subprocess.Popen([sys.executable, "-c", code, "--kind=compile", "-q", d + "/Proof.v"])))
        trace += sexp(["process", "start", "1", ["process_args", ["compile", "-q", d + "/Proof.v"]],
                       ["prog", "/opt/bin/rocq"], ["dir", "_build/default"]])
    t, d, p = running.pop(0)
    rc = p.wait()
    tail = "" if rc == 0 else " (got signal KILL)" if rc == -9 else " (exit %d)" % rc
    print("        rocq %s/Proof.{glob,vo}%s" % (d, tail), flush=True)
    if rc == 0:
        os.makedirs(os.path.join(root, os.path.dirname(t)), exist_ok=True)
        open(os.path.join(root, t), "w").close()
    else:
        bad = 1
os.makedirs(os.path.join(root, "_build"), exist_ok=True)
with open(os.path.join(root, "_build", "trace.csexp"), "wb") as f:
    f.write(trace)
sys.exit(bad)
'''


class Deadline(unittest.TestCase):
    """deadline_s: a proof directory whose compiles run past the job's deadline is stopped and fails alone; the others
    build."""

    def setUp(self):
        self.ctx = tree()
        self.t = self.ctx.__enter__()
        self.addCleanup(self.ctx.__exit__, None, None, None)
        self.work = self.t.path("_work")
        os.makedirs(self.work)
        Audit.proof(self)
        Audit.proof(self, "plain_halts_may_fail")
        bin_ = tempfile.mkdtemp(prefix="stub-dune-", dir=self.work)
        with open(os.path.join(bin_, "dune"), "w") as f:
            f.write("#!%s\n%s" % (sys.executable, STUB_DUNE))
        os.chmod(os.path.join(bin_, "dune"), 0o755)
        p = mock.patch.dict(os.environ, {"PATH": bin_ + os.pathsep + os.environ["PATH"]})
        p.start()
        self.addCleanup(p.stop)

    def build(self, deadline_in, dirs=(PD, PD2), jobs=None, **fake):
        h = facts.load(self.t.root).projects["zlib"].harnesses["checksum_fuzzer"]
        out = io.StringIO()
        t0 = time.monotonic()
        with mock.patch.dict(os.environ, fake), contextlib.ExitStack() as stack:
            if jobs is not None:
                stack.enter_context(mock.patch.object(check, "_jobs", return_value=jobs))
            got = check.build_proof_dirs(self.t.root, h, self.work, out, list(dirs), {},
                                         deadline_s=None if deadline_in is None else t0 + deadline_in)
        return got, time.monotonic() - t0, out.getvalue()

    def test_a_directory_that_starts_late_is_stopped_at_the_job_s_deadline(self):
        """Three directories, one job at a time: the first two take 3 s each, so the third starts at about 6 s and runs
        past the job's deadline (15 s).  Only the third is stopped."""
        Audit.proof(self, "ubsan_halts")
        got, wall, out = self.build(15, dirs=(PD, PD2, PD3), jobs=1, FAKE_SLOWISH=PD + ":" + PD2, FAKE_SLOW=PD3)
        self.assertEqual((got[PD], got[PD2]), (None, None), got)
        self.assertIn("%s: stopped by the job's deadline" % PD3, got[PD3])
        self.assertLess(wall, 60, "the late directory was stopped at the deadline, not waited for")
        self.assertIn("1 stopped by the job's deadline", out)

    def test_a_slow_directory_is_stopped_at_the_deadline_and_the_one_beside_it_builds(self):
        got, wall, out = self.build(3, FAKE_SLOW=PD)
        self.assertIsNone(got[PD2], got)
        self.assertIn("%s: stopped by the job's deadline" % PD, got[PD])
        self.assertLess(wall, 60, "the slow compile was killed, not waited for")
        self.assertFalse(os.path.exists(self.t.path("_build", "default", PD, "Proof.vo")))
        self.assertTrue(os.path.exists(self.t.path("_build", "default", PD2, "Proof.vo")))
        self.assertIn("1 stopped by the job's deadline", out)

    def test_a_failing_directory_fails_alone_and_the_one_beside_it_builds(self):
        got, _, out = self.build(30, FAKE_FAIL=PD)
        self.assertIsNone(got[PD2], got)
        self.assertIn("%s: dune built no %s/Proof.vo" % (PD, PD), got[PD])
        self.assertIn("(exit 1)", got[PD])
        self.assertNotIn("deadline", got[PD])
        self.assertNotIn("stopped", out)

    def test_a_directory_done_before_the_deadline_is_not_stopped(self):
        got, _, out = self.build(10, FAKE_SLOWISH=PD)
        self.assertEqual(got, {PD: None, PD2: None})
        self.assertNotIn("stopped", out)

    def test_without_a_deadline_nothing_is_stopped(self):
        got, _, out = self.build(None, FAKE_SLOWISH=PD)
        self.assertEqual(got, {PD: None, PD2: None})
        self.assertNotIn("stopped", out)


class Run(unittest.TestCase):
    """check._run: a timeout bounds an unwatched run, a watch watches a run, and the two together are refused, since a
    watched run applies no timeout."""

    def setUp(self):
        d = tempfile.mkdtemp(prefix="oft-run-")
        self.addCleanup(shutil.rmtree, d)
        self.d, self.log = d, os.path.join(d, "log")

    def test_a_timeout_with_a_watch_raises_and_runs_nothing(self):
        with self.assertRaises(ValueError):
            check._run([sys.executable, "-c", "pass"], self.d, self.log, timeout=5, watch=lambda p: None)
        self.assertFalse(os.path.exists(self.log), "nothing ran")

    def test_a_timeout_alone_bounds_the_run(self):
        self.assertEqual(check._run([sys.executable, "-c", "print('hi')"], self.d, self.log, timeout=30), 0)
        with self.assertRaises(check.subprocess.TimeoutExpired):
            check._run([sys.executable, "-c", "import time; time.sleep(30)"], self.d, self.log, timeout=1)

    def test_a_watch_alone_is_called_while_the_run_lasts(self):
        seen = []
        rc = check._run([sys.executable, "-c", "import time; time.sleep(2.5)"], self.d, self.log,
                        watch=lambda p: seen.append(p.pid))
        self.assertEqual(rc, 0)
        self.assertTrue(seen, "watch was called at least once")



if __name__ == "__main__":
    unittest.main()
