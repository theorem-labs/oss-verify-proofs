"""check_statements and compile_lib under the dune store (OSSV-299 S1, C3): the statement side always builds with a dune
cache of its own and says how many rules it ran; the library build counts the targets dune compiled and takes its width
from check._jobs (the cgroup's CPU quota, #1785); every build keeps the caller's DUNE_CACHE (OneCacheModePerTree).
dune itself is a stand-in: check._run is patched to record each command and its environment and to write a given
`--display short` log, but for one test, which runs a real dune."""
import contextlib
import io
import os
import re
import shutil
import subprocess
import unittest
from unittest import mock

from oft import check, facts, fetch
from oft.tests.helpers import tree

UNIT_DIR = "projects/zlib/checksum_fuzzer"
LIB = "proofs/zlib/checksum_fuzzer/lib"
PD = "proofs/zlib/checksum_fuzzer/plain_halts"


class FakeRun:
    """Stands in for check._run: records (cmd, env) and writes `log_text` into the log of each dune call."""

    def __init__(self, log_text=""):
        self.calls, self.log_text = [], log_text

    def __call__(self, cmd, cwd, log, timeout=None, env=None, watch=None):
        self.calls.append((cmd, env))
        with open(log, "a", encoding="utf-8") as f:
            f.write("$ %s\n" % " ".join(cmd))
            if cmd[0] == "dune":
                f.write(self.log_text)
        return 0

    def dune(self):
        return [(c, e) for c, e in self.calls if c[0] == "dune"]


class StatementSide(unittest.TestCase):
    def check(self, t, log_text="", jobs=None):
        h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
        fake, out = FakeRun(log_text), io.StringIO()
        work = t.path("_work")
        os.makedirs(work)
        with mock.patch.object(check, "_run", fake), mock.patch.object(check, "check_defined"), \
                mock.patch.object(fetch, "verify_builds", return_value=(None, [])), \
                contextlib.ExitStack() as stack:
            if jobs is not None:
                stack.enter_context(mock.patch.object(check, "_jobs", return_value=jobs))
            check.check_statements(t.root, h, set(), work, out)
        return fake, out.getvalue()

    def test_check_statements_runs_dune_with_a_cache_of_its_own_over_the_statement_side_only(self):
        """Never h.dir's own default alias: in the per-project layout dune 3.23.0 builds the proofs folder under it
        (coturn/FuzzStunClient: its library's 1,091 rules and each proof directory's ran in the statement step)."""
        with tree() as t:
            t.write(UNIT_DIR + "/counterexamples/x/A.v", "")
            t.write(UNIT_DIR + "/proofs/s/Proof.v", "")
            t.write(UNIT_DIR + "/findings/f/F.v", "")
            # a width of its own, so a build that went back to this process's affinity count would not pass here
            fake, _ = self.check(t, jobs=13)
            (cmd, env), = fake.dune()
            self.assertEqual(env.get("DUNE_CACHE"), os.environ.get("DUNE_CACHE"), "the caller's DUNE_CACHE is kept")
            self.assertTrue(env["DUNE_CACHE_ROOT"].startswith(t.path("_work") + os.sep), env["DUNE_CACHE_ROOT"])
            self.assertEqual(env.get("PATH"), os.environ.get("PATH"), "the rest of the environment is kept")
            self.assertEqual(cmd[cmd.index("-j") + 1], "13")
            targets = cmd[cmd.index("-j") + 2:]
            self.assertEqual(targets, ["@@theories/default"] + ["%s/%s.vo" % (UNIT_DIR, m) for m in (
                "Characterise", "Distribution", "Images", "Statements", "Symbols")] + ["@@%s/images/default" % UNIT_DIR])
            self.assertIn("--display", cmd)

    def test_check_statements_prints_the_rules_run_and_those_under_theories(self):
        log = ("        rocq theories/.OssFuzzTheorems.Core.theory.d\n"
               "        rocq theories/Shapes.{glob,vo},theories/NOssFuzzTheorems_Core_Shapes.{cmi,cmxs}\n"
               "        rocq %s/.x.theory.d\n"
               "  elf-snapshot %s/images/Plain.v,%s/images/Plain_seg_000.hex\n"
               "        rocq %s/Statements.{glob,vo}\n"
               "File \"%s/Statements.v\", line 1, characters 0-1:\n"
               "Warning: something\n") % ((UNIT_DIR,) * 5)
        with tree() as t:
            _, out = self.check(t, log)
            self.assertRegex(out, r"statements compiled, each of the \d+ listed defined; 5 rules run, 2 under "
                                  r"theories/\n")

    def test_the_rule_count_reads_only_this_call_s_log(self):
        """Two units checked in one work directory: the second's count is its own."""
        with tree() as t:
            h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
            work = t.path("_work")
            os.makedirs(work)
            fake, out = FakeRun("        rocq theories/Shapes.{glob,vo}\n"), io.StringIO()
            with mock.patch.object(check, "_run", fake), mock.patch.object(check, "check_defined"), \
                    mock.patch.object(fetch, "verify_builds", return_value=(None, [])):
                check.check_statements(t.root, h, set(), work, out)
                check.check_statements(t.root, h, set(), work, out)
            self.assertEqual(out.getvalue().count("; 1 rules run, 1 under theories/\n"), 2, out.getvalue())


class LibrarySide(unittest.TestCase):
    def lib(self, t, log_text="", env=None):
        t.write(LIB + "/Base.v", "Definition one := 1.\n")
        t.write(LIB + "/Sub/Deep.v", "Definition two := 2.\n")
        t.write(LIB + "/Sub/Other.v", "Definition three := 3.\n")
        t.write(LIB + "/Four.v", "")
        t.write(LIB + "/Five.v", "")
        h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
        fake, out = FakeRun(log_text), io.StringIO()
        work = t.path("_work")
        os.makedirs(work)
        with mock.patch.object(check, "_run", fake), mock.patch.dict(os.environ, env or {}):
            check.compile_lib(t.root, h, work, {}, out)
        return fake, out.getvalue()

    def test_compile_lib_builds_the_statement_side_in_a_cache_of_its_own_then_the_library_in_the_caller_s(self):
        with tree() as t:
            fake, _ = self.lib(t)
            (s_cmd, s_env), (cmd, env) = fake.dune()
            stmts = check.statement_targets(t.root, facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"])
            self.assertEqual(s_cmd[-len(stmts):], stmts)
            self.assertTrue(s_env["DUNE_CACHE_ROOT"].startswith(t.path("_work") + os.sep), s_env["DUNE_CACHE_ROOT"])
            self.assertTrue(cmd[-1].startswith(LIB + "/"), cmd)
            self.assertIsNone(env, "dune runs in this process's environment, with the caller's DUNE_CACHE")

    def test_a_statement_side_that_does_not_compile_fails_the_library_before_its_build(self):
        with tree() as t:
            t.write(LIB + "/Base.v", "Definition one := 1.\n")
            h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
            fake = FakeRun()
            work = t.path("_work")
            os.makedirs(work)

            def run(cmd, cwd, log, timeout=None, env=None, watch=None):
                fake(cmd, cwd, log, timeout, env, watch)
                return 1 if "@@theories/default" in cmd else 0

            with mock.patch.object(check, "_run", run), self.assertRaises(check.CheckError) as cm:
                check.compile_lib(t.root, h, work, {}, io.StringIO())
            self.assertIn("the statement side it reads does not compile", str(cm.exception))
            self.assertEqual(len(fake.dune()), 1, "no library build")

    def test_compile_lib_counts_rules_the_short_log_names(self):
        log = ("        rocq %s/.OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.theory.d\n"
               "        rocq %s/Base.{glob,vo},%s/NBase.{cmi,cmxs}\n"
               "        rocq %s/Sub/Deep.{glob,vo}\n") % ((LIB,) * 4)
        with tree() as t:
            _, out = self.lib(t, log)
            self.assertIn("%s: 2 of 5 library targets compiled (log " % LIB, out)
            self.assertNotIn("taken from dune's cache", out)

    def test_a_unit_without_a_library_returns_empty_and_prints_nothing(self):
        with tree() as t:
            h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
            fake, out = FakeRun(), io.StringIO()
            with mock.patch.object(check, "_run", fake):
                self.assertEqual(check.compile_lib(t.root, h, t.root, {}, out), [])
            self.assertEqual((fake.calls, out.getvalue()), ([], ""))

    def test_compile_lib_takes_j_from_the_one_place_that_decides_dune_s_width(self):
        """check._jobs: the cgroup's CPU quota, OFT_JOBS over it, at most this process's affinity (#1785, and
        test_check_jobs.py).  compile_lib asks it and passes the answer to both of its builds."""
        with tree() as t, mock.patch.object(check, "_jobs", return_value=13):
            fake, _ = self.lib(t)
            for cmd, _env in fake.dune():
                self.assertEqual(cmd[cmd.index("-j") + 1], "13")
        with tree() as t:
            fake, _ = self.lib(t)
            cmd = fake.dune()[-1][0]
            self.assertEqual(cmd[cmd.index("-j") + 1], str(check._jobs()))


class OneCacheModePerTree(unittest.TestCase):
    """check builds a unit's statement side, then its library, then its proof directories, each with one dune build in
    the same _build.  dune 3.23.0 digests each rule together with whether the rule may go in the shared cache, which
    DUNE_CACHE decides (bin/common.ml sets can_go_in_shared_cache_default from it; src/dune_engine/build_system.ml's
    compute_rule_digest digests it), so a build under another DUNE_CACHE than the build before it runs every rule of
    that build again.  Under the store (DUNE_CACHE=enabled) the proof build so compiled the whole library a second time
    with the cache off, after the store had supplied it, and left in _build .vo files that the store's entries do not
    name, so the push skipped those entries and the next build missed them (zlib/checksum_fuzzer, 2026-11-02: 16 of 407
    library targets compiled on a warm store, and 421 rules in the proof build).  So every build keeps the caller's
    DUNE_CACHE, and the statement side and the proof directories, which never read or write the caller's cache, each
    get an empty DUNE_CACHE_ROOT of their own.  A `--parts proofs` run (N6's proof shards) calls no check_statements, so
    compile_lib builds the statement side first, in a cache of its own: else the library build, the first build of that
    _build, took the statement side from the caller's cache, and with equal digests the proof build kept it (REVIEW.md
    M1)."""

    ROLE_TARGET = {"statements": "s.txt", "library": "l.txt", "proofs": "p.txt"}

    def builds(self, t, statements=True):
        """[(role, environment, entries of its DUNE_CACHE_ROOT when dune starts)] of each dune build of check_statements
        (unless not statements: a `--parts proofs` run) and of build_proof_dirs, which builds the library first, under
        DUNE_CACHE=enabled and DUNE_CACHE_ROOT=t's _store.  role (statements, library or proofs) is read from the
        build's targets."""
        t.write(LIB + "/Base.v", "Definition one := 1.\n")
        st = next(x for x in facts.load(t.root).statements() if x.id == "zlib/checksum_fuzzer/plain_halts")
        t.put_yaml(PD + "/proof.yaml", {
            "schema": "oss-fuzz-theorems/proof/1", "proves": st.id, "fingerprint": st.fingerprint})
        t.write(PD + "/Proof.v", "Theorem plain_halts_holds : True. Proof. exact I. Qed.\n")
        self.assertEqual(t.generate(), 0, t.last_output)
        h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
        work, store = t.path("_work"), t.path("_store")
        os.makedirs(work)
        os.makedirs(store)
        fake, seen = FakeRun(), []

        def run(cmd, cwd, log, timeout=None, env=None, watch=None):
            if cmd[0] == "dune":
                env = dict(os.environ) if env is None else env
                root = env.get("DUNE_CACHE_ROOT", "")
                role = ("statements" if "@@theories/default" in cmd else
                        "library" if any(a.startswith(LIB + "/") for a in cmd) else "proofs")
                seen.append((role, env, sorted(os.listdir(root)) if os.path.isdir(root) else None))
            return fake(cmd, cwd, log, timeout, env, watch)

        with mock.patch.object(check, "_run", run), mock.patch.object(check, "check_defined"), \
                mock.patch.object(fetch, "verify_builds", return_value=(None, [])), \
                mock.patch.dict(os.environ, {"DUNE_CACHE": "enabled", "DUNE_CACHE_STORAGE_MODE": "copy",
                                             "DUNE_CACHE_ROOT": store}):
            if statements:
                check.check_statements(t.root, h, set(), work, io.StringIO())
            check.build_proof_dirs(t.root, h, work, io.StringIO(), [PD], {})
        return seen, work, store

    def workspace(self, t):
        """A dune workspace of three rules: the statement side's, the library's, which reads it, and the proof's, which
        reads the library's."""
        ws = t.path("_dune")
        os.makedirs(ws)
        rule = "(rule (targets %s) (deps %s) (action (with-stdout-to %s (run cat %s))))\n"
        for name, text in (("dune-project", "(lang dune 3.0)\n"), ("src.txt", "statement\n"),
                           ("dune", "".join(rule % (out, src, out, src) for out, src in (
                               ("s.txt", "src.txt"), ("l.txt", "s.txt"), ("p.txt", "l.txt"))))):
            with open(os.path.join(ws, name), "w") as f:
                f.write(text)
        return ws

    def dune(self, ws, env, target):
        """The targets of each rule a real dune build of target in env ran."""
        p = subprocess.run(["dune", "build", "--root", ws, "--display", "short", "./" + target], cwd=ws, env=env,
                           capture_output=True, text=True)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        return sorted(line.split()[-1] for line in (p.stdout + p.stderr).splitlines() if line.strip())

    def test_every_build_keeps_the_caller_s_dune_cache_and_only_the_library_build_its_cache_root(self):
        for statements in (True, False):
            with self.subTest(statements=statements), tree() as t:
                seen, work, store = self.builds(t, statements)
                self.assertEqual([role for role, _, _ in seen],
                                 ["statements"] * (2 if statements else 1) + ["library", "proofs"])
                for role, env, entries in seen:
                    self.assertEqual(env.get("DUNE_CACHE"), "enabled", role)
                    self.assertEqual(env.get("PATH"), os.environ.get("PATH"), "the rest of the environment is kept")
                    if role == "library":
                        self.assertEqual(env["DUNE_CACHE_ROOT"], store)
                    else:
                        self.assertTrue(env["DUNE_CACHE_ROOT"].startswith(work + os.sep), env["DUNE_CACHE_ROOT"])
                        self.assertEqual(entries, [], "the cache root is empty when dune starts")
                roots = [env["DUNE_CACHE_ROOT"] for role, env, _ in seen if role != "library"]
                self.assertEqual(len(set(roots)), len(roots), "a new cache root for each build")

    @unittest.skipUnless(shutil.which("dune"), "dune is not installed")
    def test_in_these_environments_dune_runs_each_rule_once_and_the_store_gets_the_library_s_alone(self):
        """A real dune, one build in each environment of a statements-and-proofs run, in their order."""
        with tree() as t:
            seen, _, store = self.builds(t)
            ws = self.workspace(t)
            ran = [self.dune(ws, env, self.ROLE_TARGET[role]) for role, env, _ in seen]
            self.assertEqual(ran, [["s.txt"], [], ["l.txt"], ["p.txt"]], "each build runs its own rule and none again")
            metas = b""
            for dp, _, fn in os.walk(os.path.join(store, "db", "meta")):
                for f in fn:
                    with open(os.path.join(dp, f), "rb") as fh:
                        metas += fh.read()
            self.assertIn(b"5:l.txt32:", metas)
            self.assertNotIn(b"5:s.txt32:", metas, "the statement side never goes into the caller's cache")
            self.assertNotIn(b"5:p.txt32:", metas, "nor does a proof")

    @unittest.skipUnless(shutil.which("dune"), "dune is not installed")
    def test_a_proofs_only_run_never_keeps_a_statement_file_from_the_caller_s_cache(self):
        """A real dune.  A store build of the library also leaves the statement side's entry in the store, and its file
        is then forged there (dev/stream/tests/store-attack.sh's swap).  A fresh _build, built in each environment of a
        `--parts proofs` run in their order, ends with the statement file compiled here, not the forged one."""
        with tree() as t:
            seen, _, store = self.builds(t, statements=False)
            ws = self.workspace(t)
            self.dune(ws, next(env for role, env, _ in seen if role == "library"), "l.txt")
            forged = 0
            for dp, _, fn in os.walk(os.path.join(store, "db", "meta")):
                for f in fn:
                    with open(os.path.join(dp, f), "rb") as fh:
                        m = re.search(rb"5:s\.txt32:([0-9a-f]{32})", fh.read())
                    if m:
                        digest = m.group(1).decode()
                        path = os.path.join(store, "db", "files", "v4", digest[:2], digest)
                        os.chmod(path, 0o644)
                        with open(path, "w") as out:
                            out.write("FORGED\n")
                        forged += 1
            self.assertEqual(forged, 1, "the store holds the statement side's entry")
            shutil.rmtree(os.path.join(ws, "_build"))
            for role, env, _ in seen:
                self.dune(ws, env, self.ROLE_TARGET[role])
            with open(os.path.join(ws, "_build", "default", "s.txt")) as f:
                self.assertEqual(f.read(), "statement\n")


if __name__ == "__main__":
    unittest.main()
