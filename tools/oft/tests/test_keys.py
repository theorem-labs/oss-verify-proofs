"""keys.py and plan.py: a part's key changes exactly when what its check reads changes, and a plan checks a part only
when, judged against a base, its key differs from the base's, and when its key has no recorded pass."""
import glob
import io
import json
import os
import resource
import shutil
import subprocess
import sys
import tempfile
import unittest

from oft import check, facts, keys, plan, rules, yamlio
from oft.tests.helpers import REPO, add_findings, tree
from oft.tests.test_fetch_check import HAVE_ZSTD, make_release, withdraw_every_statement, withhold_checksum_fuzzer

GIT = ["git", "-c", "user.name=oft-tests", "-c", "user.email=oft-tests" + "@" + "example.invalid",
       "-c", "commit.gpgsign=false"]
GIT_ENV = dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")
TOOLS = os.path.dirname(os.path.dirname(os.path.abspath(keys.__file__)))
UNIT = "zlib/checksum_fuzzer"
CX_UNIT = "json/fuzzer-parse_bjdata"


def git(t, *args):
    r = subprocess.run(GIT + ["-C", t.root, *args], env=GIT_ENV, capture_output=True, text=True)
    if r.returncode != 0:
        raise AssertionError("git %s: %s" % (" ".join(args), r.stderr))
    return r.stdout.strip()


def commit(t):
    git(t, "add", "-A")
    git(t, "commit", "-q", "--allow-empty", "-m", "x")
    return git(t, "rev-parse", "HEAD")


def repo(t):
    """t as a git repository with a checker (tools/oft/check.py) and a file no check opens (tools/oft/lint.py), a
    counterexample and a finding; its first commit."""
    add_findings(t)
    t.write("tools/oft/check.py", "check\n")
    t.write("tools/oft/lint.py", "lint\n")
    t.write(".gitattributes", "* text=auto eol=lf\n")
    git(t, "init", "-q")
    return commit(t)


def all_keys(t, facts_commit, change=None, tools=None):
    """{(unit, part): key} of every part the tree at t has to check."""
    change = change or facts_commit
    got = keys.keys(t.root, keys.wanted(facts.load(t.root)), facts_commit, change, tools or change)
    return {up: k for up, (k, _c) in got.items()}


def changed(a, b):
    return sorted(up for up in a if a[up] != b.get(up))


class Keys(unittest.TestCase):
    def test_the_fixture_has_every_part(self):
        with tree() as t:
            repo(t)
            wanted = set(keys.wanted(facts.load(t.root)))
            self.assertLessEqual({(UNIT, "build"), (UNIT, "findings"), (CX_UNIT, "counterexamples")}, wanted)

    def test_a_change_to_a_file_no_check_opens_changes_no_key(self):
        with tree() as t:
            first = repo(t)
            t.write("tools/oft/lint.py", "lint, changed\n")
            t.write("docs/x.md", "docs\n")
            t.write(".github/workflows/pr.yml", "on: push\n")
            # the images are keyed by the digests release.yaml pins, not by the files they are built from
            t.write("toolchain/runner.Dockerfile", "FROM scratch\n")
            t.write("toolchain/toolchain.lock", "checker: x\n")
            second = commit(t)
            self.assertEqual(changed(all_keys(t, first), all_keys(t, second)), [])

    def test_a_change_to_the_planner_changes_no_key(self):
        """plan.py holds images_differ, which pr.yml's reach step runs, because keys.NOT_THE_CHECKER names it: a
        change to it re-checks no fuzz target."""
        self.assertTrue(keys.NOT_THE_CHECKER.fullmatch("plan.py"))
        with tree() as t:
            t.write("tools/oft/plan.py", "plan\n")
            first = repo(t)
            t.write("tools/oft/plan.py", "plan, changed\n")
            second = commit(t)
            self.assertEqual(changed(all_keys(t, first), all_keys(t, second)), [])

    def test_a_test_repository_runs_no_background_git(self):
        """git's automatic maintenance after a commit could write into .git/objects while tree() deletes it."""
        with tree() as t:
            repo(t)
            for key, value in (("maintenance.auto", "false"), ("gc.auto", "0")):
                with self.subTest(key=key):
                    self.assertEqual(git(t, "config", "--get", key), value)

    def test_a_change_to_the_checker_changes_every_key(self):
        """The checker is every file of tools/ a check job puts on PYTHONPATH, with its checkout attributes."""
        changes = {"tools/oft/check.py": ("tools/oft/check.py", "check, changed\n"),
                   "a module beside oft/": ("tools/sitecustomize.py", "import os\n"),
                   "an attribute of a checker file": (".gitattributes",
                                                      "* text=auto eol=lf\ntools/oft/check.py -text\n")}
        for name, (path, text) in changes.items():
            with self.subTest(change=name), tree() as t:
                first = repo(t)
                t.write(path, text)
                second = commit(t)
                before, after = all_keys(t, first), all_keys(t, second)
                self.assertEqual(changed(before, after), sorted(before))

    def test_a_proof_changes_the_build_of_its_unit_alone(self):
        with tree() as t:
            first = repo(t)
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem x : True. Proof. exact I. Qed.\n")
            second = commit(t)
            self.assertEqual(changed(all_keys(t, first), all_keys(t, second)), [(UNIT, "build")])

    def test_the_shared_proof_library_changes_every_build_and_nothing_else(self):
        with tree() as t:
            first = repo(t)
            t.write("proofs/lib/Common.v", "Definition zero := 0.\n")
            second = commit(t)
            before = all_keys(t, first)
            self.assertEqual(changed(before, all_keys(t, second)), sorted(up for up in before if up[1] == "build"))

    def test_dune_project_changes_the_builds_of_the_projects_whose_stanzas_change(self):
        """Enrolling a project adds its package stanzas to dune-project, and re-checks no other project's builds."""
        with tree() as t:
            first = repo(t)
            before = all_keys(t, first)
            builds = sorted(up for up in before if up[1] == "build")
            text = t.read("dune-project")
            t.write("dune-project", text + '\n(package\n (name rocq-oss-fuzz-theorems-newproj)\n'
                                           ' (synopsis "Theorem statements about newproj (a project)")\n'
                                           ' (depends rocq-oss-fuzz-theorems-core))\n; a comment with a ( in it\n')
            self.assertEqual(changed(before, all_keys(t, commit(t))), [])
            self.assertIn("(name rocq-oss-fuzz-theorems-zlib)", text)
            t.write("dune-project", text.replace("(name rocq-oss-fuzz-theorems-zlib)",
                                                 "(name rocq-oss-fuzz-theorems-zlib)\n (tags (zlib))"))
            self.assertEqual(changed(before, all_keys(t, commit(t))),
                             [up for up in builds if up[0].startswith("zlib/")])
            t.write("dune-project", text.replace("(using rocq", "(using  rocq", 1))
            self.assertEqual(changed(before, all_keys(t, commit(t))), builds)

    def test_a_hand_written_dune_file_that_could_shadow_a_theory_gives_no_key(self):
        """A dune file oft generate does not write, wherever lint admits one, could declare a theory a build finds
        before the installed one, or bring in what this reader cannot see.  So could one under projects/<p>/bin/,
        which lint never reads (paths.IGNORED_PATTERNS) and a pattern of two name segments would take for a
        harness's generated dune file: it is refused once it is tracked."""
        paths = ("tests/shadow/dune", "docs/dune", "counterexamples/dune", "projects/%s/source/dune" % UNIT,
                 "proofs/%s/plain_halts/classifier/dune" % UNIT, "proofs/%s/provenance/recipe/dune" % UNIT,
                 "proofs/%s/provenance/LICENSES/dune" % UNIT, "projects/zlib/bin/dune",
                 "projects/zlib/bin/images/dune")
        texts = {"a shadow of the model": "(rocq.theory (name LinuxProcessSemantics))\n",
                 "a shadow of the core": "(coq.theory (name OssFuzzTheorems.Core))\n",
                 "a theory with no name": "(rocq.theory (theories Stdlib))\n",
                 "an include": "(include ../shadow.inc)\n",
                 "a subdir": "(subdir s (rocq.theory (name LinuxProcessSemantics)))\n",
                 "a library": "(library (name zarith))\n",
                 "the tests' name in a line comment": "(rocq.theory ; (name OssFuzzTheorems.Tests)\n"
                                                      " (name LinuxProcessSemantics))\n",
                 # '#|' is not a comment to dune: its atoms around a stanza hide nothing
                 "a theory between '#|' and '|#' atoms": "(rule (alias hide) (action (echo #|)))\n"
                                                         "(rocq.theory (name LinuxProcessSemantics))\n"
                                                         "(rule (alias hide2) (action (echo |#)))\n",
                 # a block string runs to the end of its line, so the stanza after it is live
                 "a theory after a block string": '(rule (alias hide) (action (echo "\\| x\n)))\n'
                                                  "(rocq.theory (name LinuxProcessSemantics))\n"
                                                  '; ")))\n',
                 "the tests' name in a string": '(rocq.theory (synopsis "(name OssFuzzTheorems.Tests)")'
                                                ' (name LinuxProcessSemantics))\n',
                 "two names": "(rocq.theory (name OssFuzzTheorems.Tests) (name LinuxProcessSemantics))\n"}
        for path in paths:
            for what, text in texts.items():
                with self.subTest(path=path, what=what), tree() as t:
                    repo(t)
                    t.write(path, text)
                    git(t, "add", "-f", path)
                    with self.assertRaisesRegex(keys.NoKey, "^%s: a hand-written dune file" % path):
                        all_keys(t, commit(t))

    def test_what_a_hand_written_dune_file_may_hold_changes_no_key(self):
        """The tests' own theory and rules, as tests/ has them: none of it reaches another build."""
        with tree() as t:
            first = repo(t)
            t.write("tests/dune", "(include_subdirs qualified)\n(data_only_dirs negative)\n"
                                  "(rocq.theory\n (name OssFuzzTheorems.Tests)\n (theories OssFuzzTheorems.Core))\n")
            t.write("tests/toy/dune", '(rule (targets x.v) (deps %{project_root}/docs/x.md) (action (copy %{deps} '
                                      '%{targets})))\n(alias (name toy))\n')
            t.write("tests/Model.v", "Definition x := 0.\n")
            self.assertEqual(changed(all_keys(t, first), all_keys(t, commit(t))), [])

    def test_theories_dune_holds_only_the_core_s_theory(self):
        """theories/ is in every build's key; a rule there could build the core from a file outside it."""
        with tree() as t:
            repo(t)
            t.write("theories/dune", "(rocq.theory (name OssFuzzTheorems.Core))\n"
                                     "(rule (targets X.v) (action (copy ../docs/x X.v)))\n")
            with self.assertRaisesRegex(keys.NoKey, "^theories/dune: a hand-written dune file with a rule stanza"):
                all_keys(t, commit(t))

    def test_a_counterexample_and_a_finding_change_their_own_part(self):
        with tree() as t:
            first = repo(t)
            cx = next(os.path.join(dp, f) for dp, _d, fs in os.walk(t.path("counterexamples", CX_UNIT))
                      for f in fs if f.endswith(".yaml"))
            with open(cx, "a") as f:
                f.write("# x\n")
            second = commit(t)
            self.assertEqual(changed(all_keys(t, first), all_keys(t, second)), [(CX_UNIT, "counterexamples")])
            t.write("findings/zlib/unpatched.yaml", t.read("findings/zlib/unpatched.yaml") + "# x\n")
            third = commit(t)
            self.assertEqual(changed(all_keys(t, second), all_keys(t, third)), [(UNIT, "findings")])

    def test_a_harness_yaml_changes_every_part_of_its_project_alone(self):
        """`oft fetch` unpacks a project's archive only when every harness's builds are in it."""
        with tree() as t:
            first = repo(t)
            t.write("projects/zlib/api-driver/harness.yaml", t.read("projects/zlib/api-driver/harness.yaml") + "#\n")
            second = commit(t)
            before = all_keys(t, first)
            self.assertEqual(changed(before, all_keys(t, second)),
                             sorted(up for up in before if up[0].startswith("zlib/")))

    def test_a_project_s_generated_files_change_no_key_and_its_facts_change_its_parts(self):
        """A proof re-renders projects/<p>/README.md; no check reads it or the .opam file."""
        with tree() as t:
            first = repo(t)
            for path in ("projects/zlib/README.md", "projects/zlib/rocq-oss-fuzz-theorems-zlib.opam"):
                t.write(path, (t.read(path) if os.path.exists(t.path(path)) else "") + "\nchanged\n")
            second = commit(t)
            self.assertEqual(changed(all_keys(t, first), all_keys(t, second)), [])
            t.write("projects/zlib/project.yaml", t.read("projects/zlib/project.yaml") + "# x\n")
            before = all_keys(t, second)
            self.assertEqual(changed(before, all_keys(t, commit(t))),
                             sorted(up for up in before if up[0].startswith("zlib/")))

    def test_theories_and_the_toolchain_change_every_build_and_nothing_else(self):
        for path, text in (("theories/Extra.v", "Definition x := 0.\n"),
                           ("toolchain/allowed-axioms.txt", "Corelib.Init.Something.prim\n")):
            with self.subTest(path=path), tree() as t:
                first = repo(t)
                t.write(path, text)
                second = commit(t)
                before = all_keys(t, first)
                self.assertEqual(changed(before, all_keys(t, second)),
                                 sorted(up for up in before if up[1] == "build"))

    def test_each_image_changes_the_parts_that_run_in_it(self):
        for image, parts in (("runner", ("counterexamples", "findings")), ("checker", ("build",))):
            with self.subTest(image=image), tree() as t:
                first = repo(t)
                r = t.yaml("release.yaml")
                r["images"][image] = r["images"][image].split("@")[0] + "@sha256:" + "4" * 64
                t.put_yaml("release.yaml", r)
                second = commit(t)
                before = all_keys(t, first)
                self.assertEqual(changed(before, all_keys(t, second)), sorted(up for up in before if up[1] in parts))

    def test_rocqchk_changes_every_build_and_nothing_else(self):
        with tree() as t:
            head = repo(t)
            wanted = keys.wanted(facts.load(t.root))
            plain = {up: k for up, (k, _c) in keys.keys(t.root, wanted, head, head, head).items()}
            checked = {up: k for up, (k, _c) in keys.keys(t.root, wanted, head, head, head, rocqchk=True).items()}
            self.assertEqual(changed(plain, checked), sorted(up for up in plain if up[1] == "build"))

    def test_an_attribute_that_changes_the_bytes_of_one_units_files_changes_that_unit_alone(self):
        """release/libreac's case: a .gitattributes line that gives one harness's files another attribute leaves
        every blob as it was."""
        with tree() as t:
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem x : True. Proof. exact I. Qed.\n")
            first = repo(t)
            t.write(".gitattributes", "* text=auto eol=lf\nproofs/%s/** -text\n" % UNIT)
            second = commit(t)
            self.assertEqual(changed(all_keys(t, first), all_keys(t, second)), [(UNIT, "build")])


class Checker(unittest.TestCase):
    def opened(self, t, module, *args):
        """`python3 -m <module> --root <t> <args>`, run as check-units.sh runs it: (the files of tools/oft/ it opens,
        what it prints).  A module Python loads from its cached bytecode (written by any earlier run without -B, in
        __pycache__ or under PYTHONPYCACHEPREFIX) counts as its source file, so the audit sees it whether or not a
        cache exists.  A .pyc that names no source (source_from_cache refuses it) stays as it is: an audit hook that
        raised would end the run."""
        hook = ("import sys, os, runpy, importlib.util\n"
                "seen = set()\n"
                "def hook(ev, args):\n"
                "    if ev == 'open' and isinstance(args[0], str):\n"
                "        p = args[0]\n"
                "        if p.endswith('.pyc'):\n"
                "            try:\n"
                "                p = importlib.util.source_from_cache(p)\n"
                "            except ValueError:\n"
                "                pass\n"
                "        seen.add(os.path.abspath(p))\n"
                "sys.addaudithook(hook)\n"
                "if os.environ.get('OFT_TEST_STACK_STAND_IN'):\n"
                "    # as in test_fetch_check.Check: this host's stack hard limit is below what oft check refuses,\n"
                "    # and a test cannot raise it, so report no hard limit and raise the soft limit to the real one\n"
                "    import resource\n"
                "    get, put, STACK = resource.getrlimit, resource.setrlimit, resource.RLIMIT_STACK\n"
                "    hard = get(STACK)[1]\n"
                "    resource.getrlimit = lambda r: (hard, resource.RLIM_INFINITY) if r == STACK else get(r)\n"
                "    resource.setrlimit = lambda r, l: put(r, (hard, hard) if r == STACK else l)\n"
                "sys.argv = [sys.argv[1]] + sys.argv[2:]\n"
                "try:\n"
                "    runpy.run_module(sys.argv[0], run_name='__main__')\n"
                "except SystemExit:\n"
                "    pass\n"
                "with open(os.environ['AUDIT_OPENED'], 'w') as f:\n"
                "    f.write('\\n'.join(sorted(seen)))\n")
        hard = resource.getrlimit(resource.RLIMIT_STACK)[1]
        low = hard != resource.RLIM_INFINITY and hard < check.STACK_NEEDED
        with tempfile.NamedTemporaryFile("r") as listed:
            pythonpath = TOOLS + os.pathsep + os.environ.get("PYTHONPATH", "")
            done = subprocess.run([sys.executable, "-c", hook, module, "--root", t.root, *args], capture_output=True,
                                  text=True, env=dict(os.environ, PYTHONPATH=pythonpath, AUDIT_OPENED=listed.name,
                                                      OFT_TEST_STACK_STAND_IN="1" if low else ""))
            paths = listed.read().splitlines()
        oft = os.path.join(TOOLS, "oft") + os.sep
        return {p[len(oft):] for p in paths if p.startswith(oft) and "__pycache__" not in p}, done.stdout + done.stderr

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_check_and_its_fetch_open_no_file_outside_the_checker(self):
        """`python3 -m oft.check` and `python3 -m oft.fetch`, as check-units.sh runs them, fetch, unpack and check a
        tree without opening any file of tools/oft/ that keys.NOT_THE_CHECKER leaves out of every key."""
        with tree() as t, tempfile.TemporaryDirectory() as assets:
            add_findings(t)
            make_release(t, assets)
            # a proof whose fingerprint is current and an allowlist, so that the check enters the proof's step
            t.write("toolchain/allowed-axioms.txt", "Corelib.Init.Something.prim\n")
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "(* stand-in *)\n")
            t.write("proofs/%s/lib/L.v" % UNIT, "(* stand-in *)\n")
            fingerprint = next(st for h in facts.load(t.root).harnesses() for st in h.statements.values()
                               if st.id == "%s/plain_halts" % UNIT).fingerprint
            t.put_yaml("proofs/%s/plain_halts/proof.yaml" % UNIT, {
                "schema": "oss-fuzz-theorems/proof/1", "proves": "%s/plain_halts" % UNIT, "fingerprint": fingerprint})
            runs = {"fetch --list": self.opened(t, "oft.fetch", "--list", "zlib"),
                    "fetch --findings --list": self.opened(t, "oft.fetch", "--findings", "--list", "zlib"),
                    "fetch --source": self.opened(t, "oft.fetch", "--source", assets, "zlib"),
                    # a step may fail for want of dune, rocq, qemu or a binary, after the check has entered it; the
                    # counterexample's unit has no proof, so it is checked by itself (naming proofs refuses it)
                    "check": self.opened(t, "oft.check", "--parts", "statements,proofs,counterexamples,findings",
                                         UNIT),
                    "check counterexamples": self.opened(t, "oft.check", "--parts", "counterexamples", CX_UNIT)}
            self.assertTrue(os.listdir(t.path("projects", "zlib", "bin")), "fetch --source unpacked nothing")
            said = runs["check"][1] + runs["check counterexamples"][1]
            for step in ("statements", "proofs/%s/plain_halts" % UNIT, "counterexamples/%s/" % CX_UNIT,
                         "findings/%s/" % UNIT):
                self.assertIn(step, said, "the check never reached this step")
            self.assertIn("check.py", runs["check"][0])
            for name, (opened, _said) in runs.items():
                with self.subTest(run=name):
                    self.assertIn("facts.py", opened)
                    self.assertEqual(sorted(p for p in opened if keys.NOT_THE_CHECKER.fullmatch(p)), [])


class Plan(unittest.TestCase):
    def plan(self, t, **kw):
        buf = io.StringIO()
        plan.plan(t.root, out=buf, **kw)
        return json.loads(buf.getvalue())

    def checked(self, p):
        return sorted((r["unit"], r["part"]) for r in p["parts"] if r["check"])

    def test_a_change_is_checked_on_what_it_changes(self):
        with tree() as t:
            base = repo(t)
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem x : True. Proof. exact I. Qed.\n")
            t.write("tools/oft/check.py", "check, changed\n")
            head = commit(t)
            p = self.plan(t, change=head, base=base, kind="maintainer")
            self.assertEqual(self.checked(p), [(UNIT, "build")])
            row = next(r for r in p["parts"] if r["check"])
            self.assertEqual(row["why"], "changed: proofs")
            self.assertEqual(p["units"], [UNIT])
            # a job's whole shape: the fields the workflows read (pr.yml, release-check.yml and weekly.yml read index,
            # check_units, proof_units, projects, counterexamples, findings, runner and timeout_minutes), the job's
            # units, and no key, which the parts carry.  The Proof.v above has no proof.yaml, so facts sees no proof
            # and proof_units is empty; check-times.tsv has no peak for this unit, so its job keeps the 16-core runner,
            # and its 13.9 minutes there give it the floor of 30.
            self.assertEqual(p["jobs"], [{"index": 0, "units": UNIT, "check_units": UNIT, "proof_units": "",
                                          "projects": "zlib", "counterexamples": "", "findings": "",
                                          "runner": "ubuntu-24.04-16core", "timeout_minutes": 30}])

    def test_a_job_takes_the_standard_runner_only_when_every_unit_is_small_and_the_sum_short(self):
        times = {"a/small": (40.0, 12.0), "b/small": (100.0, 13.9), "c/big": (30.0, 14.0),
                 "d/no_peak": (10.0, None), "e/no_minutes": (None, 1.0)}
        self.assertEqual(plan.runner(["a/small"], times), "ubuntu-24.04")
        # 140 minutes summed, both under 14 GiB
        self.assertEqual(plan.runner(["a/small", "b/small"], times), "ubuntu-24.04")
        # a peak of 14 GiB is not under 14
        self.assertEqual(plan.runner(["a/small", "c/big"], times), "ubuntu-24.04-16core")
        # 180 minutes summed
        self.assertEqual(plan.runner(["a/small", "a/small", "b/small"], times), "ubuntu-24.04-16core")
        # what was not measured counts as over the threshold
        for unit in ("d/no_peak", "e/no_minutes", "f/unlisted"):
            self.assertEqual(plan.runner(["a/small", unit], times), "ubuntu-24.04-16core", unit)

    def test_the_measured_table_reads(self):
        """check-times.tsv reads, and its rows decide as the rule says."""
        times = plan.check_times()
        self.assertEqual(times["openssl/hashtable"], (360.4, None))
        self.assertEqual(plan.runner(["fast_float/from_chars"], times), "ubuntu-24.04")
        self.assertEqual(plan.runner(["coturn/FuzzStunClient"], times), "ubuntu-24.04-16core")
        # every measured unit's own job ends before GitHub's 6-hour cap
        for unit in times:
            self.assertLess(plan.timeout_minutes([unit], times, plan.runner([unit], times)), 360, unit)

    def test_a_job_s_time_limit_is_its_measured_minutes_on_its_runner_and_half_again(self):
        times = {"a/x": (40.0, 12.0), "b/y": (100.0, 20.0), "c/z": (None, 1.0), "d/w": (5.0, 1.0)}
        self.assertEqual(plan.timeout_minutes(["b/y"], times, "ubuntu-24.04-16core"), 150)
        # 2.2 times as long on the standard runner: 40 x 2.2 x 1.5 = 132
        self.assertEqual(plan.timeout_minutes(["a/x"], times, "ubuntu-24.04"), 132)
        # the sum of the job's units
        self.assertEqual(plan.timeout_minutes(["a/x", "b/y"], times, "ubuntu-24.04-16core"), 210)
        self.assertEqual(plan.timeout_minutes(["d/w"], times, "ubuntu-24.04-16core"), 30)
        self.assertEqual(plan.timeout_minutes(["a/x", "b/y", "b/y"], times, "ubuntu-24.04-16core"), 340)
        # what was not measured gets the cap
        for unit in ("c/z", "e/unlisted"):
            self.assertEqual(plan.timeout_minutes(["d/w", unit], times, "ubuntu-24.04-16core"), 340, unit)

    def test_a_full_plan_of_the_measured_table_has_no_job_over_its_limit(self):
        """Every unit of check-times.tsv, packed: each unit is in one job or offloaded, no job holds more measured
        minutes than its time limit allows under the cap (1.5 x 2.2 x minutes on the standard runner, 1.5 x minutes on
        the 16-core one), and the offloaded units are those too long for a job even alone."""
        times = plan.check_times()
        jobs, away = plan.pack(sorted(times), times, set(times))
        self.assertEqual(sorted([u for _on, us in jobs for u in us] + away), sorted(times))
        for on, units in jobs:
            minutes = [times[u][0] for u in units]
            self.assertNotIn(None, minutes, units)
            factor = plan.SLOWER if on == plan.STANDARD else 1
            self.assertLessEqual(plan.MARGIN * factor * sum(minutes), plan.CAP, (on, units))
            self.assertEqual(on, plan.runner(units, times), units)
        self.assertEqual(away, ["cgif/cgif_rgb_fuzzer", "openssl/hashtable", "zstd/simple_decompress"])

    def test_units_are_packed_longest_first_into_the_first_job_they_fit(self):
        times = {"a/l1": (200.0, 30.0), "b/l2": (100.0, 30.0), "c/l3": (26.0, 30.0), "d/s1": (90.0, 10.0),
                 "e/s2": (20.0, 10.0), "f/over": (300.0, 30.0), "g/s_long": (120.0, 10.0)}
        jobs, away = plan.pack(sorted(times) + ["h/unmeasured"], times, set(times))
        self.assertEqual(jobs, [
            # 200 + 26 fits in 226.7; 100 does not, nor the unmeasured unit's 3 after them
            ("ubuntu-24.04-16core", ["a/l1", "c/l3"]),
            # a unit the rule puts on the standard runner, too long for its room there (103.0), takes 16 cores; an
            # unmeasured unit with no proof is packed as plan.UNMEASURED minutes on 16 cores: 120 + 100 + 3
            ("ubuntu-24.04-16core", ["b/l2", "g/s_long", "h/unmeasured"]),
            ("ubuntu-24.04", ["d/s1"]),
            ("ubuntu-24.04", ["e/s2"])])
        # over the 16-core room alone: in no job
        self.assertEqual(away, ["f/over"])

    def test_an_unmeasured_unit_with_a_proof_gets_a_job_of_its_own(self):
        """A proof's check is not a statements-only one (the measured ones took 13.9 to 360 minutes): a proved unit
        with no row in check-times.tsv is never packed beside another unit, whose verdict its limit would take with it.
        An unmeasured unit with no proof still shares a job at its 3 minutes."""
        times = {"a/l1": (220.0, 30.0)}
        jobs, away = plan.pack(["a/l1", "n/new_proof", "s/statements"], times, {"a/l1", "n/new_proof"})
        self.assertEqual(jobs, [("ubuntu-24.04-16core", ["n/new_proof"]),
                                ("ubuntu-24.04-16core", ["a/l1", "s/statements"])])
        self.assertEqual(away, [])
        self.assertEqual(plan.timeout_minutes(["n/new_proof"], times, "ubuntu-24.04-16core"), plan.CAP)

    def test_a_plan_gives_a_new_proof_with_no_measurement_a_job_of_its_own(self):
        """In a plan, a harness of the fixture with a committed proof and no row in the table is alone in its job."""
        with tree() as t:
            repo(t)
            st = next(x for x in facts.load(t.root).statements() if x.id == UNIT + "/plain_halts")
            t.put_yaml("proofs/%s/plain_halts/proof.yaml" % UNIT, {
                "schema": "oss-fuzz-theorems/proof/1", "proves": st.id, "fingerprint": st.fingerprint})
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem plain_halts_holds : True. Qed.\n")
            p = self.plan(t, change=commit(t), times={})
            mine = [j for j in p["jobs"] if UNIT in j["units"].split()]
            self.assertEqual([j["units"] for j in mine], [UNIT])
            self.assertEqual(mine[0]["timeout_minutes"], plan.CAP)
            self.assertTrue(any(len(j["units"].split()) > 1 for j in p["jobs"]), "the unproved harnesses share jobs")

    @unittest.skipUnless(os.path.isfile(os.path.join(REPO, "index", "harnesses.tsv")),
                         "no index/harnesses.tsv beside tools/")
    def test_a_plan_of_every_harness_of_this_tree_fits_one_matrix(self):
        """Every harness of the repository (2,148 on 2 November 2026, of which check-times.tsv measures 61), packed:
        each is in exactly one job or offloaded, the jobs fit one matrix, and no job's estimate is over its room."""
        with open(os.path.join(REPO, "index", "harnesses.tsv"), encoding="utf-8") as f:
            rows = [line.rstrip("\n").split("\t") for line in list(f)[1:]]
        units = sorted({"%s/%s" % (r[0], r[1]) for r in rows})
        # the proved column: harnesses with a proof, which an unmeasured one would put in a job of its own
        proved = {"%s/%s" % (r[0], r[1]) for r in rows if int(r[6]) > 0}
        self.assertGreater(len(units), 2000)
        times = plan.check_times()
        jobs, away = plan.pack(units, times, proved)
        packed = [u for _on, us in jobs for u in us]
        self.assertEqual(sorted(packed + away), units)
        self.assertEqual(len(packed), len(set(packed)))
        self.assertLessEqual(len(jobs), plan.MATRIX)
        self.assertEqual(away, ["cgif/cgif_rgb_fuzzer", "openssl/hashtable", "zstd/simple_decompress"])
        for on, us in jobs:
            estimate = sum(plan.UNMEASURED if times.get(u, (None, None))[0] is None else times[u][0] for u in us)
            self.assertLessEqual(estimate, plan.ROOM[on], (on, us))

    def _offloaded_tree(self, t):
        """A tree in which UNIT is too long for a check job, and the rows of its parts' keys at the commit."""
        head = repo(t)
        wanted = keys.wanted(facts.load(t.root))
        times = {u: (10.0, 20.0) for u, _part in wanted}
        times[UNIT] = (300.0, 20.0)
        mine = [r for r, _c, _o in plan.rows(t.root, [w for w in wanted if w[0] == UNIT], change=head)]
        self.assertTrue(mine)
        return head, times, mine

    def cite(self, t, cited):
        t.write(plan.OFFLOADED, "\t".join(plan.OFFLOADED_COLUMNS) + "\n" + "".join(
            "%s\t%s\t%s\tjob-1\t%s\t2026-11-02\n" % (unit, part, key, "0" * 64) for unit, part, key in cited))

    def failed_plan(self, t, **kw):
        out, err = io.StringIO(), io.StringIO()
        self.assertEqual(plan.plan(t.root, out=out, err=err, **kw), 1)
        self.assertEqual(out.getvalue(), "", "a failed plan prints no plan")
        return err.getvalue()

    def test_a_unit_checked_on_the_build_service_at_its_key_is_in_no_job(self):
        with tree() as t:
            _head, times, mine = self._offloaded_tree(t)
            self.cite(t, [(r["unit"], r["part"], r["key"]) for r in mine])
            # the citation file is not the checker: committed, it changes no key
            p = self.plan(t, change=commit(t), times=times)
            self.assertNotIn(UNIT, p["units"])
            self.assertNotIn(UNIT, " ".join(j["units"] for j in p["jobs"]).split())
            self.assertEqual([(o["unit"], o["part"], o["key"], o["job"]) for o in p["offloaded"]],
                             [(r["unit"], r["part"], r["key"], "job-1") for r in mine])

    def test_a_unit_too_long_for_a_job_and_not_checked_on_the_build_service_fails_the_plan(self):
        with tree() as t:
            head, times, mine = self._offloaded_tree(t)
            err = self.failed_plan(t, change=head, times=times)
            for r in mine:
                self.assertIn("%s %s: key %s has no check on the build service" % (r["unit"], r["part"], r["key"]), err)

    def test_a_check_on_the_build_service_at_another_key_fails_the_plan(self):
        with tree() as t:
            head, times, mine = self._offloaded_tree(t)
            self.cite(t, [(r["unit"], r["part"], "f" * 64) for r in mine])
            err = self.failed_plan(t, change=head, times=times)
            for r in mine:
                self.assertIn("%s %s: key %s has no check" % (r["unit"], r["part"], r["key"]), err)
                self.assertIn("its rows are for key %s, checks of other bytes" % ("f" * 64), err)

    def test_a_malformed_citation_fails_the_plan(self):
        """Each column is held to its form, and the unit and part to what the tree has to check, so a row cannot cite
        what it does not name; every bad row is named, by its line."""
        good = {"unit": UNIT, "part": "build", "key": "a" * 64, "job": "job-1", "result_sha256": "b" * 64,
                "date": "2026-11-02"}
        bad = {
            "key": ("A" * 64, "key %r is not 64 lowercase hex digits" % ("A" * 64)),
            "result_sha256": ("b" * 63, "result_sha256 %r is not 64 lowercase hex digits" % ("b" * 63)),
            "date": ("2026-02-30", "date '2026-02-30' is not a date YYYY-MM-DD"),
            "part": ("proofs", "part 'proofs' is not one of build, counterexamples, findings"),
            "unit": ("zlib/no_such_fuzzer", "unit 'zlib/no_such_fuzzer' is no harness of this tree"),
        }
        for column, (value, message) in bad.items():
            with self.subTest(column=column), tree() as t:
                head, times, _mine = self._offloaded_tree(t)
                row = dict(good, **{column: value})
                t.write(plan.OFFLOADED, "# a comment\n" + "\t".join(plan.OFFLOADED_COLUMNS) + "\n"
                        + "\t".join(row[c] for c in plan.OFFLOADED_COLUMNS) + "\n")
                err = self.failed_plan(t, change=head, times=times)
                self.assertIn("1 bad row(s):\n  line 3: " + message, err)
        with tree() as t:
            head, times, _mine = self._offloaded_tree(t)
            # a harness of the tree and a part it has nothing to check in
            loaded = facts.load(t.root)
            have = set(keys.wanted(loaded))
            unit, part = next((h.project.name + "/" + h.name, p) for h in loaded.harnesses() for p in keys.PARTS
                              if (h.project.name + "/" + h.name, p) not in have)
            row = dict(good, unit=unit, part=part)
            t.write(plan.OFFLOADED, "\t".join(plan.OFFLOADED_COLUMNS) + "\n"
                    + "\t".join(row[c] for c in plan.OFFLOADED_COLUMNS) + "\n")
            self.assertIn("line 2: %s has no %s part to check" % (unit, part),
                          self.failed_plan(t, change=head, times=times))
            t.write(plan.OFFLOADED, "\t".join(plan.OFFLOADED_COLUMNS) + "\n" + "%s\tbuild\t%s\n" % (UNIT, "a" * 64))
            self.assertIn("line 2: a row has 6 non-empty columns, tab-separated",
                          self.failed_plan(t, change=head, times=times))

    def test_a_repeated_citation_fails_the_plan_and_two_keys_of_a_part_are_both_rows(self):
        """A second row of the same unit, part and key is refused, not taken in place of the first.  Rows of one part at
        two keys are two checks: the old key's row still cites the tree as it is while the new key's row waits on
        main for the change that gives the part that key."""
        with tree() as t:
            head, times, mine = self._offloaded_tree(t)
            r = mine[0]
            self.cite(t, [(r["unit"], r["part"], r["key"]), (r["unit"], r["part"], r["key"])])
            err = self.failed_plan(t, change=head, times=times)
            self.assertIn("line 3: line 2 already cites %s %s at key %s" % (r["unit"], r["part"], r["key"]), err)
            self.cite(t, [(r["unit"], r["part"], "f" * 64)] + [(x["unit"], x["part"], x["key"]) for x in mine])
            p = self.plan(t, change=commit(t), times=times)
            self.assertEqual(sorted((o["unit"], o["part"], o["key"]) for o in p["offloaded"]),
                             sorted((x["unit"], x["part"], x["key"]) for x in mine))

    def test_a_row_only_in_the_change_does_not_cite(self):
        """pr.yml gives the base's file (cited_from) for a change that is not a release: a row the change itself adds,
        at the key it gives the part, is not a citation until it is on the base, and the plan says to merge it first.
        The base's row at that key cites."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            head, times, mine = self._offloaded_tree(t)
            self.cite(t, [(r["unit"], r["part"], r["key"]) for r in mine])
            base_file = os.path.join(d, "offloaded-checks.tsv")
            with open(base_file, "w", encoding="utf-8") as f:
                f.write("\t".join(plan.OFFLOADED_COLUMNS) + "\n")
            err = self.failed_plan(t, change=head, times=times, cited_from=base_file)
            for r in mine:
                self.assertIn("%s %s: key %s has no check on the build service (builds-ossv) in %s; this change adds "
                              "its row, which cites only once it is on the base" % (r["unit"], r["part"], r["key"],
                                                                                    base_file), err)
            with open(base_file, "a", encoding="utf-8") as f:
                f.write("".join("%s\t%s\t%s\tjob-1\t%s\t2026-11-02\n" % (r["unit"], r["part"], r["key"], "0" * 64)
                                for r in mine))
            out, err = io.StringIO(), io.StringIO()
            self.assertEqual(plan.plan(t.root, change=head, times=times, cited_from=base_file, out=out, err=err), 0,
                             err.getvalue())
            self.assertEqual(len(json.loads(out.getvalue())["offloaded"]), len(mine))

    def test_a_change_that_adds_a_shadowing_dune_file_fails_its_own_plan(self):
        """A change that is not a release is checked on the base's tests/, but its own dune files reach main."""
        for kind in ("maintainer", "contributor"):
            with self.subTest(kind=kind), tree() as t:
                base = repo(t)
                t.write("tests/x/dune", "(env (_ (flags (:standard -type-in-type))))\n")
                head = commit(t)
                with self.assertRaisesRegex(keys.NoKey, "^tests/x/dune: a hand-written dune file with a env stanza"):
                    self.plan(t, change=head, base=base, kind=kind)

    def test_a_change_that_is_not_a_release_is_checked_on_the_bases_statements(self):
        with tree() as t:
            base = repo(t)
            t.write("projects/zlib/project.yaml", t.read("projects/zlib/project.yaml") + "# x\n")
            head = commit(t)
            self.assertEqual(self.checked(self.plan(t, change=head, base=base, kind="contributor")), [])
            self.assertEqual({u for u, _ in self.checked(self.plan(t, change=head, base=base, kind="release"))},
                             {u for u, _ in keys.wanted(facts.load(t.root)) if u.startswith("zlib/")})

    def test_a_recorded_pass_is_not_checked_again(self):
        with tree() as t:
            base = repo(t)
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem x : True. Proof. exact I. Qed.\n")
            head = commit(t)
            key = next(r["key"] for r in self.plan(t, change=head, base=base)["parts"] if r["check"])
            git(t, "checkout", "-q", "--orphan", keys.STORE_BRANCH)
            git(t, "rm", "-rq", "--cached", ".")
            t.write(keys.record_path(UNIT, "build", key), "{}\n")
            git(t, "add", keys.record_path(UNIT, "build", key))
            git(t, "commit", "-q", "-m", "record")
            store = git(t, "rev-parse", "HEAD")
            git(t, "checkout", "-q", "-f", head)
            p = self.plan(t, change=head, base=base, store=store)
            self.assertEqual(self.checked(p), [])
            self.assertIn("recorded pass", [r["why"] for r in p["parts"] if r["unit"] == UNIT])

    def test_a_finding_on_a_harness_that_withholds_every_build_adds_no_build_and_no_fetch_to_its_job(self):
        """pr.yml runs a check job for it and required wants it to pass; check-units.sh fetches only its unpatched
        binaries."""
        with tree() as t:
            repo(t)
            withhold_checksum_fuzzer(t)
            p = self.plan(t, change=commit(t))
            self.assertNotIn((UNIT, "build"), self.checked(p))
            job = next(j for j in p["jobs"] if UNIT in j["units"].split())
            # packed with other units, it adds only its finding to the job: no build to check, and no project's
            # binaries to fetch for it (the job's projects are its builds' and counterexamples' alone)
            self.assertIn(UNIT, job["findings"].split())
            self.assertNotIn(UNIT, job["check_units"].split() + job["counterexamples"].split())
            built = job["check_units"].split() + job["counterexamples"].split()
            self.assertEqual(job["projects"].split(), sorted({u.split("/")[0] for u in built}))

    def test_with_no_base_every_part_without_a_recorded_pass_is_checked(self):
        with tree() as t:
            head = repo(t)
            p = self.plan(t, change=head)
            self.assertTrue(p["all"])
            self.assertEqual(self.checked(p), keys.wanted(facts.load(t.root)))
            self.assertEqual({r["why"] for r in p["parts"]}, {"no recorded pass"})

    def test_a_harness_whose_every_statement_is_withdrawn_has_no_build_to_check(self):
        """Its builds are published, but its Statements.v defines no statement, so no check job builds it."""
        with tree() as t:
            repo(t)
            withdraw_every_statement(t, "checksum_fuzzer")
            p = self.plan(t, change=commit(t))
            self.assertNotIn((UNIT, "build"), keys.wanted(facts.load(t.root)))
            self.assertNotIn(UNIT, p["check_units"])
            self.assertIn(("zlib/api-driver", "build"), self.checked(p))

    def test_a_harness_with_published_builds_and_no_statement_to_check_is_an_error_of_the_facts(self):
        """wanted leaves a harness with no statement Statements.v carries out of every check, so the facts may not
        reach that state by mistake: an empty or missing statements map, or every statement withheld while a build is
        published.  Withdrawing every one, each with its reason, is the one way there, and it is no error."""
        rel = "projects/zlib/checksum_fuzzer/harness.yaml"

        def errors(t):
            tree_ = facts.load(t.root)
            rules.check(tree_)
            return [e for e in tree_.errors if e.startswith(rel)]

        def withhold(y):
            for st in y["statements"].values():
                for k in ("basis", "reason", "witness", "withheld", "gap"):
                    st.pop(k, None)
                st.update(status="withheld", withheld="not-yet-published")

        for name, change, want in (("empty", lambda y: y.update(statements={}), "expected a non-empty mapping"),
                                   ("missing", lambda y: y.pop("statements"), "missing key 'statements'"),
                                   ("withheld", withhold, "publishes a build, but every statement is withheld")):
            with self.subTest(statements=name), tree() as t:
                y = t.yaml(rel)
                change(y)
                t.put_yaml(rel, y)
                self.assertTrue(any(want in e for e in errors(t)), errors(t))
        with tree() as t:
            withdraw_every_statement(t, "checksum_fuzzer")
            self.assertEqual(errors(t), [])

    def test_each_job_lists_its_units_with_a_proof(self):
        """check-units.sh checks proof_units with their proofs and the other check_units on their statements."""
        with tree() as t:
            repo(t)
            st = next(x for x in facts.load(t.root).statements() if x.id == UNIT + "/plain_halts")
            t.put_yaml("proofs/%s/plain_halts/proof.yaml" % UNIT, {
                "schema": "oss-fuzz-theorems/proof/1", "proves": st.id, "fingerprint": st.fingerprint})
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem plain_halts_holds : True. Qed.\n")
            # every unit measured on the 16-core runner and short, so that they pack into one job
            times = {u: (10.0, 20.0) for u, _part in keys.wanted(facts.load(t.root))}
            p = self.plan(t, change=commit(t), times=times)
            self.assertEqual(len(p["jobs"]), 1)
            self.assertIn("zlib/api-driver", p["jobs"][0]["check_units"].split())
            self.assertEqual(p["jobs"][0]["proof_units"], UNIT)

    def test_explain_marks_what_differs_from_the_base(self):
        with tree() as t:
            base = repo(t)
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem x : True. Proof. exact I. Qed.\n")
            head = commit(t)
            buf = io.StringIO()
            self.assertEqual(plan.explain(t.root, UNIT, change=head, base=base, out=buf), 0)
            lines = buf.getvalue().splitlines()
            self.assertIn("%s build" % UNIT, [" ".join(l.split()[:2]) for l in lines if not l.startswith(" ")])
            self.assertEqual([l.split()[1] for l in lines if l.startswith("  *")], ["proofs"])

    def workflow(self, t, d):
        """A bare remote of t's repository with a clone of it, as a workflow's plan job has them: (remote, clone)."""
        remote, clone = os.path.join(d, "remote.git"), os.path.join(d, "head")
        subprocess.run(GIT + ["clone", "-q", "--bare", t.root, remote], env=GIT_ENV, check=True)
        subprocess.run(GIT + ["clone", "-q", remote, clone], env=GIT_ENV, check=True)
        os.mkdir(os.path.join(d, "bin"))
        with open(os.path.join(d, "bin", "python"), "w") as f:
            f.write('#!/bin/sh\nexec "%s" "$@"\n' % sys.executable)
        os.chmod(os.path.join(d, "bin", "python"), 0o755)
        return remote, clone

    def run_step(self, d, workflow, cwd, ok=True, **env):
        """The step with id plan of the workflow, run as GitHub runs it in cwd: (its plan.json, its outputs), or, when
        ok is False, (its exit status, its output).  The test is skipped where the workflow is not, as in the runner
        image, whose build runs these tests with tools/oft alone (toolchain/runner.Dockerfile)."""
        path = os.path.join(REPO, ".github", "workflows", workflow)
        if not os.path.exists(path):
            self.skipTest("no .github/workflows/%s beside tools/oft" % workflow)
        step = next(s for s in yamlio.load_file(path)["jobs"]["plan"]["steps"] if s.get("id") == "plan")
        tmp = tempfile.mkdtemp(dir=d)
        with open(os.path.join(tmp, "plan.sh"), "w") as f:
            f.write(step["run"])
        env = dict(GIT_ENV, PATH=os.path.join(d, "bin") + os.pathsep + os.environ["PATH"], RUNNER_TEMP=tmp,
                   GITHUB_OUTPUT=os.path.join(tmp, "output"), GITHUB_STEP_SUMMARY=os.path.join(tmp, "summary"), **env)
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", os.path.join(tmp, "plan.sh")],
                           cwd=cwd, env=env, capture_output=True, text=True)
        if not ok:
            return r.returncode, r.stdout + r.stderr
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        with open(os.path.join(tmp, "plan.json")) as f, open(os.path.join(tmp, "output")) as o:
            return json.load(f), o.read()

    def record(self, t, remote, back, entries):
        """Push a check-results commit holding a pass of each (unit, part, key) of entries, then check out back."""
        git(t, "checkout", "-q", "--orphan", keys.STORE_BRANCH)
        git(t, "rm", "-rq", "--cached", ".")
        for unit, part, key in entries:
            t.write(keys.record_path(unit, part, key), "{}\n")
            git(t, "add", keys.record_path(unit, part, key))
        git(t, "commit", "-q", "-m", "record")
        git(t, "push", "-q", "-f", remote, "%s:refs/heads/%s" % (keys.STORE_BRANCH, keys.STORE_BRANCH))
        git(t, "checkout", "-q", "-f", back)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_pr_plan_step_checks_a_changed_proof_whatever_check_results_holds(self):
        """pr.yml's plan step over a remote with the base and the change, the base's tools in base/.  Nothing protects
        a branch check-results yet, so a pass pushed there must not skip the proof."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = repo(t)
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem x : True. Proof. exact I. Qed.\n")
            head = commit(t)
            remote, _clone = self.workflow(t, d)
            os.makedirs(os.path.join(d, "base"))
            os.symlink(TOOLS, os.path.join(d, "base", "tools"))
            got, output = self.run_step(d, "pr.yml", d, KIND="maintainer", BASE=base)
            self.assertEqual((got["units"], "units=1\n" in output), ([UNIT], True), output)
            key = next(r["key"] for r in got["parts"] if r["check"])
            self.record(t, remote, head, [(UNIT, "build", key)])
            got, output = self.run_step(d, "pr.yml", d, KIND="maintainer", BASE=base)
            self.assertEqual((got["units"], "units=1\n" in output), ([UNIT], True), output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_pr_plan_step_of_a_push_to_main_plans_only_harnesses_release_check_does_not(self):
        """release-check.yml's run of a push to main checks every harness with a committed proof or finding that the
        push re-keys; pr.yml's run of the same push checks the others, so each re-keyed harness is checked once."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = repo(t)
            t.write("projects/zlib/project.yaml", t.read("projects/zlib/project.yaml") + "# x\n")
            commit(t)
            self.workflow(t, d)
            os.makedirs(os.path.join(d, "base"))
            os.symlink(TOOLS, os.path.join(d, "base", "tools"))
            every, _output = self.run_step(d, "pr.yml", d, KIND="release", BASE=base)
            got, _output = self.run_step(d, "pr.yml", d, KIND="release", BASE=base, GITHUB_EVENT_NAME="push")
            head = os.path.join(d, "head")
            covered = {"/".join(p.split(os.sep)[-4:-2])
                       for top, name in (("proofs", "proof.yaml"), ("findings", "finding.yaml"))
                       for p in glob.glob(os.path.join(head, top, "*", "*", "*", name))}
            self.assertIn(UNIT, every["units"])
            self.assertIn(UNIT, covered)
            self.assertEqual(got["units"], [u for u in every["units"] if u not in covered])
            self.assertTrue(got["units"], "the push still checks the re-keyed harnesses with no proof or finding")

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_pr_plan_step_cites_the_base_s_rows_never_the_change_s(self):
        """pr.yml's plan step for a change that is not a release, with UNIT too long for a check job (the base's
        check-times.tsv says so): the change's own row at UNIT's new key does not cite, and the plan fails naming the
        key; the same row on the base cites."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = repo(t)
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem x : True. Proof. exact I. Qed.\n")
            commit(t)
            self.workflow(t, d)
            tools = os.path.join(d, "base", "tools")
            shutil.copytree(TOOLS, tools, ignore=shutil.ignore_patterns("__pycache__"))
            header = "\t".join(plan.OFFLOADED_COLUMNS) + "\n"
            with open(os.path.join(tools, "oft", "offloaded-checks.tsv"), "w", encoding="utf-8") as f:
                f.write(header)
            got, _output = self.run_step(d, "pr.yml", d, KIND="maintainer", BASE=base)
            key = next(r["key"] for r in got["parts"] if r["check"] and r["unit"] == UNIT)
            with open(os.path.join(tools, "oft", "check-times.tsv"), "a", encoding="utf-8") as f:
                f.write("%s\t300.0\t20.0\n" % UNIT)
            row = "%s\tbuild\t%s\tjob-1\t%s\t2026-11-02\n" % (UNIT, key, "0" * 64)
            os.makedirs(os.path.join(d, "head", "tools", "oft"), exist_ok=True)
            with open(os.path.join(d, "head", plan.OFFLOADED), "w", encoding="utf-8") as f:
                f.write(header + row)
            rc, output = self.run_step(d, "pr.yml", d, ok=False, KIND="maintainer", BASE=base)
            self.assertNotEqual(rc, 0, output)
            self.assertIn("%s build: key %s has no check on the build service (builds-ossv) in "
                          "base/tools/oft/offloaded-checks.tsv; this change adds its row" % (UNIT, key), output)
            with open(os.path.join(tools, "oft", "offloaded-checks.tsv"), "a", encoding="utf-8") as f:
                f.write(row)
            got, output = self.run_step(d, "pr.yml", d, KIND="maintainer", BASE=base)
            self.assertNotIn(UNIT, got["units"])
            self.assertEqual([(o["unit"], o["key"]) for o in got["offloaded"]], [(UNIT, key)])

    def release_check(self, t, d, **env):
        """release-check.yml's plan step, run in a clone of t's last commit with this tools/: (its plan, outputs).
        env carries what the workflow puts in the job's environment: EVENT_BASE, the commit the push is judged
        against; without it the step plans every part."""
        _remote, clone = self.workflow(t, d)
        shutil.rmtree(os.path.join(clone, "tools"))
        # this tools/, with no citation of a check on the build service: the rows of this repository's
        # offloaded-checks.tsv name its harnesses, which the fixture does not have, and the plan refuses such a row
        shutil.copytree(TOOLS, os.path.join(clone, "tools"), ignore=shutil.ignore_patterns("__pycache__"))
        with open(os.path.join(clone, plan.OFFLOADED), "w", encoding="utf-8") as f:
            f.write("\t".join(plan.OFFLOADED_COLUMNS) + "\n")
        return self.run_step(d, "release-check.yml", clone, **env)

    def released(self, t):
        """A release tree's first commit: a committed proof of CX_UNIT and the fixture's finding on UNIT, so that
        both harnesses have a part to check."""
        proved = "%s/plain_halts" % CX_UNIT
        st = next(st for h in facts.load(t.root).harnesses() for st in h.statements.values() if st.id == proved)
        t.write("proofs/%s/Proof.v" % proved, "(* stand-in *)\n")
        t.put_yaml("proofs/%s/proof.yaml" % proved, {
            "schema": "oss-fuzz-theorems/proof/1", "proves": proved, "fingerprint": st.fingerprint})
        return repo(t)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_checks_every_part_of_each_harness_with_a_proof_or_a_finding(self):
        """A harness with a committed finding is planned, also when it withholds every build and has no proof, and
        only the harnesses with published builds are built; no other harness is planned."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            proved = "%s/plain_halts" % CX_UNIT
            st = next(st for h in facts.load(t.root).harnesses() for st in h.statements.values() if st.id == proved)
            t.write("proofs/%s/Proof.v" % proved, "(* stand-in *)\n")
            t.put_yaml("proofs/%s/proof.yaml" % proved, {
                "schema": "oss-fuzz-theorems/proof/1", "proves": proved, "fingerprint": st.fingerprint})
            withhold_checksum_fuzzer(t)
            repo(t)
            got, output = self.release_check(t, d)
            self.assertEqual(got["units"], [CX_UNIT, UNIT])
            self.assertEqual(got["check_units"], [CX_UNIT])
            self.assertEqual(" ".join(j["findings"] for j in got["jobs"]).split(), [UNIT])
            self.assertEqual(sorted((r["unit"], r["part"]) for r in got["parts"] if r["check"]),
                             [up for up in keys.wanted(facts.load(t.root)) if up[0] in (CX_UNIT, UNIT)])
            self.assertIn("units=2\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_plans_findings_in_a_tree_with_no_proofs(self):
        """The cross-model review's case: a tree with a finding and no proofs/ directory plans that finding."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            repo(t)
            self.assertFalse(os.path.exists(t.path("proofs")))
            got, output = self.release_check(t, d)
            self.assertEqual(got["units"], [UNIT])
            self.assertEqual(" ".join(j["findings"] for j in got["jobs"]).split(), [UNIT])
            self.assertIn("units=1\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_plans_nothing_for_a_changelog_or_docs_only_commit(self):
        """A commit that changes only CHANGELOG.md or docs/ changes no key, so it plans no proof job."""
        for path, text in (("CHANGELOG.md", "## 2026.11.0\n\nnothing\n"), ("docs/why.md", "why\n")):
            with self.subTest(path=path), tree() as t, tempfile.TemporaryDirectory() as d:
                base = self.released(t)
                t.write(path, text)
                commit(t)
                got, output = self.release_check(t, d, EVENT_BASE=base)
                self.assertEqual((got["units"], got["jobs"]), ([], []), output)
                self.assertIn("units=0\n", output)
                self.assertIn("full=false\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_checks_the_one_unit_whose_proof_changed(self):
        """A commit that changes one unit's proofs re-checks that unit's build, and nothing else."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.released(t)
            t.write("proofs/%s/plain_halts/Proof.v" % CX_UNIT, "(* another stand-in *)\n")
            commit(t)
            got, output = self.release_check(t, d, EVENT_BASE=base)
            self.assertEqual(got["units"], [CX_UNIT], output)
            self.assertEqual([(r["unit"], r["part"]) for r in got["parts"] if r["check"]], [(CX_UNIT, "build")])
            self.assertIn("units=1\n", output)
            self.assertIn("full=false\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_plans_nothing_for_a_release_version_and_date(self):
        """release.yaml's version and date name no input of a check: the release commit itself plans no proof job."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.released(t)
            release = t.yaml("release.yaml")
            release["release"], release["date"] = "2026.12.0", "2026-12-07"
            t.put_yaml("release.yaml", release)
            commit(t)
            got, output = self.release_check(t, d, EVENT_BASE=base)
            self.assertEqual((got["units"], got["jobs"]), ([], []), output)
            self.assertIn("units=0\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_rechecks_every_build_when_the_checker_pin_changes(self):
        """The checker image is in every build key: a new pin re-checks every build, and only the builds (the
        counterexamples and the findings run in the runner image, which did not change)."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.released(t)
            release = t.yaml("release.yaml")
            release["images"]["checker"] = "ghcr.io/theorem-labs/oss-fuzz-theorems-checker@sha256:" + "4" * 64
            t.put_yaml("release.yaml", release)
            commit(t)
            got, output = self.release_check(t, d, EVENT_BASE=base)
            self.assertEqual(got["units"], [CX_UNIT, UNIT], output)
            self.assertEqual(sorted((r["unit"], r["part"]) for r in got["parts"] if r["check"]),
                             [(CX_UNIT, "build"), (UNIT, "build")])
            self.assertIn("units=2\n", output)
            self.assertIn("full=false\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_plans_every_part_for_a_change_to_the_checker_tools(self):
        """No key can tell a change to the tools the check job runs (one tools/ id on both sides of a comparison),
        so the step plans every part outright, as it does for toolchain/ and .github/."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.released(t)
            t.write("tools/oft/check.py", "check, with a fix\n")
            commit(t)
            got, output = self.release_check(t, d, EVENT_BASE=base)
            self.assertEqual(got["units"], [CX_UNIT, UNIT], output)
            self.assertEqual(sorted((r["unit"], r["part"]) for r in got["parts"] if r["check"]),
                             [up for up in keys.wanted(facts.load(t.root)) if up[0] in (CX_UNIT, UNIT)])
            self.assertIn("units=2\n", output)
            self.assertIn("full=true\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_plans_no_proof_for_a_change_a_check_never_opens(self):
        """A change to a file of tools/oft/ that keys.NOT_THE_CHECKER names (the lint, the tests) leaves the checker
        id where it was, so the step plans by key and nothing is checked; only the files the full-plan pattern names
        by hand, keys.py and plan.py, take the full plan from under tools/oft/."""
        for path in ("tools/oft/lint.py", "tools/oft/tests/test_lint.py"):
            with self.subTest(path=path), tree() as t, tempfile.TemporaryDirectory() as d:
                t.write(path, "# the file as it was\n")
                base = self.released(t)
                t.write(path, "# the file, changed\n")
                commit(t)
                got, output = self.release_check(t, d, EVENT_BASE=base)
                self.assertEqual((got["units"], got["jobs"]), ([], []), output)
                self.assertIn("units=0\n", output)
                self.assertIn("full=false\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_plans_no_proof_for_a_workflow_only_commit(self):
        """A commit under .github/workflows/, alone or with a CHANGELOG note (the shape of the commit that carries
        this router to the public repository), plans no proof: pr.yml's run of the same push lints the tree and runs
        the tools' own tests, which read these workflow files."""
        for paths in ((".github/workflows/release-check.yml",),
                      (".github/workflows/release-check.yml", "CHANGELOG.md")):
            with self.subTest(paths=paths), tree() as t, tempfile.TemporaryDirectory() as d:
                for p in paths:
                    t.write(p, "# a note\n")
                base = self.released(t)
                for p in paths:
                    t.write(p, "# a note, changed\n")
                commit(t)
                got, output = self.release_check(t, d, EVENT_BASE=base)
                self.assertEqual((got["units"], got["jobs"]), ([], []), output)
                self.assertIn("units=0\n", output)
                self.assertIn("full=false\n", output)

