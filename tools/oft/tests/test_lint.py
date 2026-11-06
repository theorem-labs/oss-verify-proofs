"""Every rule of `oft lint`, each with a planted positive that must fail it,
and the clean fixture and this repository itself, which must pass."""
import contextlib
import datetime
import glob
import hashlib
import html
import io
import json
import multiprocessing
import os
import shlex
import shutil
import subprocess
import sys
import tempfile
import textwrap
import time
import unittest
from unittest import mock

from oft import facts, layout, lint, names, nsrename, paths, port, symbols, urls, yamlio
from oft.tests.helpers import (FIXTURE_RECIPE, NEXT_RECIPE, OTHER_OWN_RECIPE, OWN_RECIPE, REPO, Tree, add_findings,
                               build_record, edit, errors, git_repo, later_release, older_shape, own_recipe, port_built,
                               recipe_file, recipe_only_rebuild, rename_namespace, rules_of, tree)
from oft.tests.test_facts_review_gate import evaluate
from oft.tests.test_layout import old_layout_tree
from oft.tests.test_release_tree import add_proof

INTERNAL = "theorem-labs/oss-verify-proofs" + "-internal"


def pr_yml_jobs(test):
    """The jobs of .github/workflows/pr.yml; the test is skipped where there is none, as in the runner image, whose
    build runs these tests with tools/oft alone (toolchain/runner.Dockerfile)."""
    path = os.path.join(REPO, ".github", "workflows", "pr.yml")
    if not os.path.exists(path):
        test.skipTest("no .github/workflows/pr.yml beside tools/oft")
    return yamlio.load_file(path)["jobs"]


class Clean(unittest.TestCase):
    def test_fixture_is_clean(self):
        with tree() as t:
            self.assertEqual([str(f) for f in t.lint()], [])

    # pr.yml sets OFT_SKIP_REPOSITORY_LINT=1 when the change leaves tools/ as it is but for test data (no Python
    # file) under tests/, ci/ and the README: its lint job has then run the same code over this same tree, with
    # --changed and --pr-kind on top, and, into main, with --changed-only, which reads every file the change
    # touches and leaves every other file the verdict it has at the base.  It sets it on a pull request that a
    # merge queue checks again as well, whatever the change: that group's own run is where this test runs
    # (TestsJobCheckout).
    @unittest.skipIf(os.environ.get("OFT_SKIP_REPOSITORY_LINT") == "1",
                     "pr.yml's lint ran the same code over this tree")
    def test_this_repository_is_clean(self):
        """Every finding fails but an expired licence-pending entry's: no pull request's lint fails on one that its
        change does not touch, so this test prints it instead, and the release cut stays the hard stop."""
        found = lint.run(REPO, skeleton=True)
        for f in found:
            if lint.is_expired(f):
                print("expired %s" % f)
        self.assertEqual([str(f) for f in found if not lint.is_expired(f)], [])
        self.assertGreater(len(lint.walk(REPO)), 20, "examined almost nothing")

    def test_a_scan_that_examines_nothing_fails(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(rules_of(lint.run(d, skeleton=True)), ["paths"])

    def test_a_git_worktree_skips_what_gitignore_excludes(self):
        """In a `git worktree` checkout .git is a file, not a directory; ignored files are still not linted."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            t.write(".gitignore", "*.pyc\n")
            git = ["git", "-c", "user.name=t", "-c", "user.email=t@t", "-C"]
            subprocess.run(git + [t.root, "init", "-q"], check=True)
            subprocess.run(git + [t.root, "add", "-A"], check=True)
            subprocess.run(git + [t.root, "commit", "-q", "-m", "fixture"], check=True)
            wt = os.path.join(d, "wt")
            subprocess.run(git + [t.root, "worktree", "add", "-q", "--detach", wt], check=True)
            with open(os.path.join(wt, "tools.pyc"), "w") as f:
                f.write("x")
            self.assertTrue(os.path.isfile(os.path.join(wt, ".git")))
            self.assertNotIn("tools.pyc", lint.walk(wt))
            self.assertIn(".gitignore", lint.walk(wt))


class TestsJobCheckout(unittest.TestCase):
    """pr.yml's tests job runs the whole-tree lint test (test_this_repository_is_clean, OFT_SKIP_REPOSITORY_LINT=0)
    and checks the tree out whole exactly where that test is the check of record: wherever no merge queue checks
    the change again.  That is a merge queue group, a push to main, a pull request into a base other than main,
    and every pull request on theorem-labs/oss-verify-proofs, whose main merges with no queue (the `QUEUED`
    condition of pr.yml's `required` job, negated).  On a pull request into this repository's main it does not
    run: the group's own run is that check, and a tools change that breaks the whole-tree lint fails the group and
    takes the head out of the queue.  Every other run checks out every file but the proof libraries of both
    layouts (proofs/*/*/lib/ and projects/*/*/proofs/lib/), with plan's own checkout inputs: the whole-tree lint
    test is the one that reads a proof library, so a job that skips it need not wait for the 4.56 GB of them."""
    LINTED = ("needs.plan.outputs.repository_lint == 'true'"
              " && (github.event_name != 'pull_request' || github.event.pull_request.base.ref != 'main'"
              " || github.repository == 'theorem-labs/oss-verify-proofs')")
    SPARSE = ("filter", "sparse-checkout-cone-mode", "sparse-checkout")
    # the condition of the checkouts for the publishing tools' tests: they run only where tools/publish/tests is
    PUBLISH_TESTS = "hashFiles('head/tools/publish/tests/*.py') != ''"
    INTERNAL = "theorem-labs/oss-verify-proofs" + "-internal"   # split, as line 30 is: the private-data rule
    PUBLIC = "theorem-labs/oss-verify-proofs"
    #: (the github context, what it is) over every event, base and repository the workflow runs on
    WHERE = (({"event_name": "pull_request", "repository": INTERNAL,
               "event": {"pull_request": {"base": {"ref": "main"}}}}, "a pull request into this main, queued"),
             ({"event_name": "pull_request", "repository": INTERNAL,
               "event": {"pull_request": {"base": {"ref": "release/9.2"}}}}, "a pull request into another base"),
             ({"event_name": "pull_request", "repository": PUBLIC,
               "event": {"pull_request": {"base": {"ref": "main"}}}}, "a pull request on the public repository"),
             ({"event_name": "merge_group", "repository": INTERNAL, "event": {}}, "a merge queue group"),
             ({"event_name": "push", "repository": INTERNAL, "event": {}}, "a push to main"))

    def setUp(self):
        self.jobs = pr_yml_jobs(self)

    @staticmethod
    def checkouts(job):
        return [s for s in job["steps"] if s.get("uses", "").startswith("actions/checkout@")]

    def test_the_skip_and_the_checkout_read_the_same_answer(self):
        step = next(s for s in self.jobs["tests"]["steps"] if s.get("run") == "python -B -m oft.tests.parallel")
        self.assertEqual(" ".join(step["env"]["OFT_SKIP_REPOSITORY_LINT"].split()),
                         "${{ %s && '0' || '1' }}" % self.LINTED)
        self.assertEqual(" ".join(self.jobs["tests"]["runs-on"].split()),
                         "${{ %s && 'ubuntu-24.04-16core' || 'ubuntu-24.04' }}" % self.LINTED)

    def test_the_whole_tree_is_checked_out_exactly_when_it_is_linted(self):
        plan = next(s["with"] for s in self.checkouts(self.jobs["plan"]) if "sparse-checkout" in s["with"])
        self.assertEqual(plan["sparse-checkout"].split(), ["/*", "!/proofs/*/*/lib/", "!/projects/*/*/proofs/lib/"])
        # the publishing tools' checkouts carry PUBLISH_TESTS, each into a path of its own, never head
        tree, publish = [], []
        for s in self.checkouts(self.jobs["tests"]):
            (publish if s.get("if") == self.PUBLISH_TESTS else tree).append(s)
        for s in publish:
            self.assertNotEqual(s["with"]["path"], "head")
        for github, what in self.WHERE:
            for value in ("true", "false", ""):
                needs = {"plan": {"result": "success", "outputs": {"repository_lint": value}},
                         "lint": {"result": "success"}}
                # a checkout with no `if:` would run beside the others: s["if"] fails on it rather than counting it
                ran = [s["with"] for s in tree if evaluate(s["if"], needs, github=github)]
                with self.subTest(where=what, repository_lint=value):
                    self.assertEqual(len(ran), 1, "exactly one checkout runs")
                    self.assertEqual((ran[0]["path"], ran[0]["persist-credentials"]), ("head", False))
                    if evaluate(self.LINTED, needs, github=github):
                        self.assertEqual([k for k in self.SPARSE if k in ran[0]], [], "the whole tree")
                    else:
                        self.assertEqual({k: ran[0].get(k) for k in self.SPARSE}, {k: plan[k] for k in self.SPARSE})

    def test_only_a_pull_request_a_queue_checks_again_leaves_the_whole_tree_lint_test_to_it(self):
        """Everywhere else the change can reach a main without a group of its own, so the test runs here."""
        needs = {"plan": {"result": "success", "outputs": {"repository_lint": "true"}},
                 "lint": {"result": "success"}}
        for github, what in self.WHERE:
            queued = (github["event_name"] == "pull_request"
                      and github["event"]["pull_request"]["base"]["ref"] == "main"
                      and github["repository"] != self.PUBLIC)
            self.assertEqual(evaluate(self.LINTED, needs, github=github), not queued, what)

    def test_the_rule_is_the_required_job_s_queued_condition(self):
        """pr.yml's `required` job decides the same question for its own verdict; one rule, written once."""
        required = next(s for s in self.jobs["required"]["steps"] if "QUEUED" in s.get("env", {}))
        queued = " ".join(required["env"]["QUEUED"].split())
        self.assertEqual(queued, "${{ github.event_name == 'pull_request' "
                                 "&& github.event.pull_request.base.ref == 'main' "
                                 "&& github.repository != 'theorem-labs/oss-verify-proofs' }}")
        needs = {"plan": {"result": "success", "outputs": {"repository_lint": "true"}},
                 "lint": {"result": "success"}}
        for github, what in self.WHERE:
            self.assertEqual(evaluate(self.LINTED, needs, github=github),
                             not evaluate(queued, needs, github=github), what)


class LintJobCheckout(unittest.TestCase):
    """pr.yml's lint job checks the tree out whole except for a pull request's lint that reads only the changed files
    (the plan's lint_files_left_out): that one leaves out the proof libraries but their generated dune files, on the
    standard runner, and checks out the left-out files that changed before lint runs."""
    SPARSE = ["/*", "!/proofs/*/*/lib/*", "/proofs/*/*/lib/dune", "!/projects/*/*/proofs/lib/*",
              "/projects/*/*/proofs/lib/dune"]

    def setUp(self):
        self.jobs = pr_yml_jobs(self)

    def test_exactly_one_checkout_runs_and_only_a_left_out_one_is_sparse(self):
        for value in ("true", "false", ""):
            needs = {"plan": {"result": "success", "outputs": {"lint_files_left_out": value}}}
            ran = [s["with"] for s in TestsJobCheckout.checkouts(self.jobs["lint"]) if evaluate(s["if"], needs)]
            with self.subTest(lint_files_left_out=value):
                self.assertEqual(len(ran), 1, "exactly one checkout runs")
                self.assertEqual(ran[0]["path"], "head")
                if value == "true":
                    self.assertEqual(ran[0]["sparse-checkout"].split(), self.SPARSE)
                    self.assertEqual(ran[0]["filter"], "blob:none")
                else:
                    self.assertEqual([k for k in TestsJobCheckout.SPARSE if k in ran[0]], [], "the whole tree")

    def test_the_left_out_files_that_changed_are_checked_out_before_lint(self):
        names = [s.get("name") for s in self.jobs["lint"]["steps"]]
        self.assertLess(names.index("the left-out files lint reads"), names.index("lint, by the base's rules"))
        self.assertGreater(names.index("the left-out files lint reads"),
                           names.index("the tree of the last passing lint, when its record holds"))


class QueueCheckedPush(unittest.TestCase):
    """A main that takes commits through a merge queue becomes the very commits the groups' runs tested, so pr.yml's
    push run of them checks nothing again when every commit the push brings has a merge queue run that passed on it,
    made on its parent: queue_run finds those runs, plan, lint and every job after them are skipped, and required and
    main-gate run and pass by naming those runs.  release-check.yml's plan job runs the same walk (its queue step)."""
    SHA, BEFORE, OTHER, MID = "e" * 40, "b" * 40, "f" * 40, "c" * 40
    QUEUE_STEP = "a merge queue run of this workflow passed main-gate on each commit this push brings"
    RELEASE_CHECK_QUEUE_STEP = "a merge queue run of pr.yml passed main-gate on each commit this push brings"

    def setUp(self):
        self.jobs = pr_yml_jobs(self)

    @staticmethod
    def github(event, base, head_repo="acme/proofs"):
        """The github context main-gate's and prove's conditions read: a pull request names its base and its head's
        repository; a merge queue group names its own base (github.base_ref is empty on it), and a push names none."""
        return {"event_name": event, "repository": "acme/proofs", "base_ref": base if event == "pull_request" else "",
                "event": {"pull_request": {"base": {"ref": base}, "head": {"repo": {"full_name": head_repo}}}}
                if event == "pull_request"
                else {"merge_group": {"base_ref": "refs/heads/" + base}} if event == "merge_group" else {}}

    def results(self, event, checked="", failed=(), base="main", outputs=None, head_repo="acme/proofs"):
        """Each job's result in a run of this event, in the order of its needs, with GitHub's rules for a skipped
        ancestor (evaluate()); queue_run's output `checked`, the jobs in `failed` failing when they run, and `base` the
        pull request's or the merge queue's base.  A job that runs sets every output that starts a later job."""
        done = {"queue_run": {"result": "success", "outputs": {"checked": checked}} if event == "push"
                else {"result": "skipped", "outputs": {}}}
        self.assertEqual(self.jobs["queue_run"]["if"], "github.event_name == 'push'")

        def needs_of(name):
            n = self.jobs[name].get("needs", [])
            return [n] if isinstance(n, str) else n

        while len(done) < len(self.jobs):
            ready = [n for n in self.jobs if n not in done and all(need in done for need in needs_of(n))]
            self.assertTrue(ready, "the jobs' needs make a cycle")
            for name in ready:
                # success() and failure() read every ancestor, not only the direct needs: a skipped queue_run skips
                # tests, check and controls although plan and lint ran (seen in a run), unless !cancelled() or
                # always() says otherwise.  `needs.<job>` names a direct need only; any other job is an error.
                ancestors, todo = set(), list(needs_of(name))
                while todo:
                    a = todo.pop()
                    if a not in ancestors:
                        ancestors.add(a)
                        todo.extend(needs_of(a))
                direct = set(needs_of(name))

                class Needs(dict):
                    def __getitem__(self, job):
                        if job not in direct:
                            raise KeyError("needs.%s: not a need of %s" % (job, name))
                        return dict.__getitem__(self, job)
                # every job but queue_run (seeded above from the event), main-gate (which reads the event's name and
                # base), prove (which runs on a pull request from this repository alone) and rekey (on a pull request
                # and a merge queue group alone) reads needs.* alone in its `if:`: an expression that read the event
                # would fail evaluate()
                runs = evaluate(self.jobs[name].get("if", "success()"), Needs({n: done[n] for n in ancestors}),
                                github=self.github(event, base, head_repo)
                                if name in ("main-gate", "prove", "rekey") else None)
                done[name] = {"result": ("failure" if name in failed else "success") if runs else "skipped",
                              "outputs": {} if name in failed or not runs else
                              dict({"tests": "true", "units": "1", "controls": "true", "repository_lint": "true",
                                    "stream_tools": "true", "farm_tests": "true", "draft_legs": '["x"]',
                                    "hold": "none"}, **(outputs or {}))}
        return {n: r["result"] for n, r in done.items()}

    def test_a_push_the_queue_checked_runs_only_queue_run_and_the_verdict_jobs(self):
        got = self.results("push", checked="true")
        self.assertEqual({n for n, r in got.items() if r != "skipped"}, {"queue_run", "required", "main-gate"}, got)

    def test_every_other_run_runs_every_job(self):
        """A pull request or a merge queue group (queue_run skipped) and a push the queue did not check run every
        job: the default rule would skip the jobs after plan and lint for a skipped ancestor.  prove runs on a pull
        request alone, and rekey on a pull request and a merge queue group alone."""
        for event, checked in (("pull_request", ""), ("merge_group", ""), ("push", "false"), ("push", "")):
            with self.subTest(event=event, checked=checked):
                got = self.results(event, checked)
                want = {n for n in self.jobs
                        if (n != "queue_run" or event == "push") and (n != "prove" or event == "pull_request")
                        and (n != "rekey" or event != "push")}
                self.assertEqual({n for n, r in got.items() if r == "success"}, want, got)

    def test_prove_runs_on_a_pull_request_from_this_repository_alone(self):
        """A fork's pull request gets a read-only token, which cannot post the check: prove is skipped there, and
        nothing else changes."""
        got = self.results("pull_request", head_repo="someone/proofs")
        self.assertEqual({n for n, r in got.items() if r == "skipped"}, {"queue_run", "prove"}, got)
        self.assertEqual((got["required"], got["main-gate"]), ("success", "success"), got)

    def test_a_failed_plan_or_lint_starts_no_later_job_and_required_judges(self):
        for failed in ("plan", "lint"):
            with self.subTest(failed=failed):
                got = self.results("pull_request", failed=(failed,))
                self.assertEqual({n: got[n] for n in ("tests", "check", "controls")},
                                 {"tests": "skipped", "check": "skipped", "controls": "skipped"}, got)
                self.assertEqual((got["required"], got["main-gate"]), ("success", "success"), got)

    def test_required_always_runs(self):
        """No condition may skip required: a skipped job reports success, and the final job always runs and
        collects."""
        self.assertEqual(" ".join(self.jobs["required"]["if"].split()), "always()")

    def test_a_held_pull_request_runs_every_job_but_check_and_a_draft_no_lint(self):
        """The plan job's hold answer holds back check and the fetch-drafts legs that feed it: on no label `check`
        nothing else, and on a draft lint too, and with it every job that waits for lint (tests, controls,
        stream_tools, rekey); plan, required and main-gate run and report.  check runs only on the answer none: an
        empty or other answer holds it back, and required fails on it.  A merge queue group and a push are never held
        (the hold step), so check runs there."""
        for hold, held in (("label", {"check", "fetch-drafts"}),
                           ("draft", {"lint", "tests", "check", "fetch-drafts", "controls", "stream_tools", "rekey",
                                      "farm_tests"})):
            with self.subTest(hold=hold):
                got = self.results("pull_request", outputs={"hold": hold})
                self.assertEqual({n for n, r in got.items() if r == "skipped"}, {"queue_run"} | held, got)
                self.assertEqual((got["required"], got["main-gate"]), ("success", "success"), got)
        for answer in ("", "yes", "false"):
            with self.subTest(answer=answer):
                self.assertEqual(self.results("pull_request", outputs={"hold": answer})["check"], "skipped")
        for event, checked in (("merge_group", ""), ("push", "false")):
            with self.subTest(event=event):
                self.assertEqual(self.results(event, checked)["check"], "success")

    def test_main_gate_runs_on_every_push_group_and_pull_request_into_main(self):
        """main-gate is what main's ruleset requires, and a skipped job reports success: it runs, whatever required
        gave, on a push, on a merge queue group (whose github.base_ref is empty) and on a pull request into main (or
        Main: GitHub's == ignores case, and its base step does not)."""
        for event, base in (("push", "main"), ("merge_group", "main"), ("pull_request", "main"),
                            ("pull_request", "Main")):
            for failed in ((), ("required",), ("plan",)):
                with self.subTest(event=event, base=base, failed=failed):
                    got = self.results(event, checked="false" if event == "push" else "", failed=failed, base=base)
                    self.assertNotEqual(got["main-gate"], "skipped", got)
                    self.assertEqual(got["required"], "failure" if "required" in failed else "success", got)

    def test_main_gate_is_skipped_under_another_name_into_any_other_base(self):
        """On a pull request into another base main-gate is skipped, required (which still runs) being that run's
        verdict; under another name, so that the head has no main-gate to carry into the merge queue when the pull
        request is retargeted at main.  Its name and its `if:` read the same condition."""
        gate = self.jobs["main-gate"]
        cond = "(github.event_name != 'pull_request' || github.event.pull_request.base.ref == 'main')"
        self.assertEqual(" ".join(gate["if"].split()), "always() && " + cond)
        self.assertEqual(" ".join(gate["name"].split()),
                         "${{ %s && 'main-gate' || 'main-gate (skipped: the base is not main)' }}" % cond)
        for base in ("ossv/candidates", "lane", "main-next", ""):
            for failed in ((), ("required",)):
                with self.subTest(base=base, failed=failed):
                    got = self.results("pull_request", failed=failed, base=base)
                    self.assertEqual(got["main-gate"], "skipped", got)
                    self.assertEqual(got["required"], "failure" if failed else "success", got)

    def gh_step(self, workflow, job, step_name, data, **env):
        """A workflow step that asks gh about this commit, run as GitHub runs it, with a gh that answers from `data`
        as the API does and applies the step's own --jq with jq: `runs` (each with id, event, head_sha, head_branch,
        conclusion; None: the list call fails), `jobs` {run id: [{name, conclusion}]} and `parents` {sha: [parent
        shas]}.  (its exit, its output, the outputs it wrote)."""
        path = os.path.join(REPO, ".github", "workflows", workflow)
        if not os.path.exists(path):
            self.skipTest("no .github/workflows/%s beside tools/oft" % workflow)
        if not shutil.which("jq"):
            self.skipTest("jq is not installed")
        step = next(s for s in yamlio.load_file(path)["jobs"][job]["steps"] if s.get("name") == step_name)
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, "gh.json"), "w") as f:
                json.dump(data, f)
            os.mkdir(os.path.join(d, "bin"))
            with open(os.path.join(d, "bin", "gh"), "w") as f:
                f.write("#!/bin/sh\nexec %s %s \"$@\"\n"
                        % (shlex.quote(sys.executable), shlex.quote(os.path.join(d, "gh.py"))))
            with open(os.path.join(d, "gh.py"), "w") as f:
                f.write(FAKE_GH_API % repr(os.path.join(d, "gh.json")))
            os.chmod(os.path.join(d, "bin", "gh"), 0o755)
            out = os.path.join(d, "output")
            env = dict(os.environ, PATH=os.path.join(d, "bin") + os.pathsep + os.environ["PATH"], GITHUB_OUTPUT=out,
                       GITHUB_STEP_SUMMARY=os.path.join(d, "summary"), GITHUB_REPOSITORY="example/repository",
                       GITHUB_SHA=self.SHA, RUNNER_TEMP=d, **env)
            r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", step["run"]], cwd=d,
                               env=env, capture_output=True, text=True)
            got = {}
            if os.path.exists(out):
                with open(out) as f:
                    got = dict(line.rstrip("\n").split("=", 1) for line in f if "=" in line)
            return r.returncode, r.stdout + r.stderr, got

    def run_of(self, run_id, event, sha=None, conclusion="success", base=None, branch=None):
        branch = branch or {"push": "main",
                            "merge_group": "gh-readonly-queue/main/pr-1-" + (base or self.BEFORE)}.get(event, "x")
        return {"id": run_id, "event": event, "head_sha": sha or self.SHA, "head_branch": branch,
                "conclusion": conclusion}

    @staticmethod
    def gate(main_gate, queue_run=None):
        jobs = [{"name": "required", "conclusion": main_gate}, {"name": "main-gate", "conclusion": main_gate}]
        return jobs + ([{"name": "queue_run", "conclusion": queue_run}] if queue_run else [])

    def queue_cases(self):
        """(name, gh data, (checked, runs)) for the queue walk, which pr.yml's queue_run and release-check.yml's queue
        step run alike."""
        one_parent = {self.SHA: [self.BEFORE]}
        passed = {"runs": [self.run_of(11, "merge_group")], "jobs": {"11": self.gate("success")},
                  "parents": one_parent}
        # a queue that merged two groups in one push: MID (made on BEFORE) and SHA (made on MID)
        batch = {"runs": [self.run_of(11, "merge_group", self.MID, base=self.BEFORE),
                          self.run_of(12, "merge_group", self.SHA, base=self.MID)],
                 "jobs": {"11": self.gate("success"), "12": self.gate("success")},
                 "parents": {self.SHA: [self.MID], self.MID: [self.BEFORE]}}
        long_line = {"runs": [], "jobs": {}, "parents": {}}
        line = [self.SHA] + ["%040x" % (i + 1) for i in range(20)] + [self.BEFORE]
        for i, commit in enumerate(line[:-1]):
            long_line["parents"][commit] = [line[i + 1]]
            long_line["runs"].append(self.run_of(100 + i, "merge_group", commit, base=line[i + 1]))
            long_line["jobs"][str(100 + i)] = self.gate("success")
        return [
            ("this commit's merge queue run passed", passed, ("true", "11")),
            # only main's own queue: another branch's queue, or any branch that only ends with the parent, is not it
            ("a passed run of another branch's queue", dict(passed, runs=[self.run_of(
                11, "merge_group", branch="gh-readonly-queue/lane/pr-1-" + self.BEFORE)]), ("false", "")),
            ("a passed run of a branch that ends with the parent", dict(passed, runs=[self.run_of(
                11, "merge_group", branch="topic-" + self.BEFORE)]), ("false", "")),
            ("its main-gate failed", dict(passed, jobs={"11": self.gate("failure")}), ("false", "")),
            ("its main-gate was skipped", dict(passed, jobs={"11": self.gate("skipped")}), ("false", "")),
            ("a later run passed", dict(passed, runs=[self.run_of(11, "merge_group"), self.run_of(12, "merge_group")],
                                        jobs={"11": self.gate("failure"), "12": self.gate("success")}), ("true", "12")),
            ("only another commit's run passed", dict(passed, runs=[self.run_of(11, "merge_group", self.OTHER)]),
             ("false", "")),
            ("only a push run of this commit", dict(passed, runs=[self.run_of(11, "push")]), ("false", "")),
            ("the run did not succeed", dict(passed, runs=[self.run_of(11, "merge_group", conclusion="failure")]),
             ("false", "")),
            ("the run's group was made on another base", dict(passed, runs=[self.run_of(11, "merge_group",
                                                                                        base=self.OTHER)]),
             ("false", "")),
            ("the push moved main past a commit whose parents cannot be read",
             dict(passed, parents={self.SHA: [self.OTHER]}), ("false", "")),
            ("this commit is a merge", dict(passed, parents={self.SHA: [self.BEFORE, self.OTHER]}), ("false", "")),
            ("the parents cannot be read", dict(passed, parents={}), ("false", "")),
            ("the run list cannot be read", dict(passed, runs=None), ("false", "")),
            ("a job list cannot be read", dict(passed, jobs={}), ("false", "")),
            # the release line's fetch-drafts legs (up to 256) can put main-gate past the first page of 100 jobs
            ("main-gate is on the second page of jobs",
             dict(passed, jobs={"11": [{"name": "fetch-drafts %d" % i, "conclusion": "success"} for i in range(100)]
                                + self.gate("success")}), ("true", "11")),
            ("two groups merged in one push, each passed on its own parent", batch, ("true", "11 12")),
            ("two groups, the first one's main-gate failed",
             dict(batch, jobs=dict(batch["jobs"], **{"11": self.gate("failure")})),
             ("false", "")),
            ("two groups, the second one's run made on main before the push, not on the first",
             dict(batch, runs=[batch["runs"][0], self.run_of(12, "merge_group", self.SHA, base=self.BEFORE)]),
             ("false", "")),
            # a commit pushed to main past the queue, then a queue group on it: the unqueued commit has no run
            ("a line with one commit no merge queue run checked", dict(batch, runs=[batch["runs"][1]]), ("false", "")),
            ("a line with a merge commit in it",
             dict(batch, parents={self.SHA: [self.MID], self.MID: [self.BEFORE, self.OTHER]}), ("false", "")),
            ("more than 20 commits, each checked", long_line, ("false", "")),
        ]

    def test_queue_run_answers_true_only_when_every_commit_of_the_push_passed_its_own_merge_queue_run(self):
        for workflow, job, step in (("pr.yml", "queue_run", self.QUEUE_STEP),
                                    ("release-check.yml", "plan", self.RELEASE_CHECK_QUEUE_STEP)):
            for name, data, want in self.queue_cases():
                with self.subTest(workflow=workflow, case=name):
                    rc, output, got = self.gh_step(workflow, job, step, data, BEFORE=self.BEFORE)
                    self.assertEqual(rc, 0, output)
                    self.assertEqual((got.get("checked"), got.get("runs")), want, output)
            # a push that made the branch has no `before` to walk back to
            with self.subTest(workflow=workflow, case="a push that made the branch"):
                rc, output, got = self.gh_step(workflow, job, step, {"runs": [], "jobs": {}, "parents": {self.SHA: []}},
                                               BEFORE="0" * 40)
                self.assertEqual((rc, got.get("checked"), got.get("runs")), (0, "false", ""), output)
            # a rewind (BEFORE is no ancestor of the pushed commit): the walk stops after 20 commits and says why it
            # may have, and the push is checked by its own change
            with self.subTest(workflow=workflow, case="a rewind"):
                line = [self.SHA] + ["%040x" % (i + 1) for i in range(25)]
                rewind = {"runs": [], "jobs": {}, "parents": {c: [line[i + 1]] for i, c in enumerate(line[:-1])}}
                rc, output, got = self.gh_step(workflow, job, step, rewind, BEFORE=self.BEFORE)
                self.assertEqual((rc, got.get("checked"), got.get("runs")), (0, "false", ""), output)
                self.assertIn("is no ancestor of it (a rewind or a force push)", output)

    def test_pr_yml_and_release_check_yml_walk_the_queue_with_the_same_text(self):
        def chain(workflow, job, step_name):
            path = os.path.join(REPO, ".github", "workflows", workflow)
            if not os.path.exists(path):
                self.skipTest("no .github/workflows/%s beside tools/oft" % workflow)
            step = next(s for s in yamlio.load_file(path)["jobs"][job]["steps"] if s.get("name") == step_name)
            text = step["run"]
            self.assertEqual(text.count("# queue chain\n"), 1, workflow)
            return text[text.index("# queue chain\n"):text.index("# end of queue chain")]
        self.assertEqual(chain("pr.yml", "queue_run", self.QUEUE_STEP),
                         chain("release-check.yml", "plan", self.RELEASE_CHECK_QUEUE_STEP))

    def test_pr_yml_reads_the_vm_evidence_comment_with_the_same_text_in_both_steps(self):
        """The plan job's elsewhere step and required's held-check acceptance read merge-pr.sh's comment by one
        rule: the text between `# vm evidence` and `# end of vm evidence`, which both hold, up to the indentation
        each sits at."""
        path = os.path.join(REPO, ".github", "workflows", "pr.yml")

        def marker(job, step_name):
            step = next(s for s in yamlio.load_file(path)["jobs"][job]["steps"] if s.get("name") == step_name)
            text = step["run"]
            self.assertEqual(text.count("# vm evidence\n"), 1, step_name)
            start = text.rfind("\n", 0, text.index("# vm evidence\n")) + 1
            return textwrap.dedent(text[start:text.index("# end of vm evidence")])
        self.assertEqual(marker("plan", "the parts a check of record outside this run checked"),
                         marker("required",
                                "every job green, and something checked when the plan named anything"))

    def required_step(self, name, env):
        """required's step of this name, run as GitHub runs it with this environment (its `env:` values), with a gh
        whose every call fails, so a step that reads the pull request's comments reads none: (its exit, its output)."""
        step = next(s for s in self.jobs["required"]["steps"] if s.get("name") == name)
        with tempfile.TemporaryDirectory() as d:
            os.mkdir(os.path.join(d, "bin"))
            with open(os.path.join(d, "bin", "gh"), "w") as f:
                f.write("#!/bin/sh\necho 'gh: HTTP 404' >&2\nexit 1\n")
            os.chmod(os.path.join(d, "bin", "gh"), 0o755)
            env = dict(os.environ, GITHUB_SHA=self.SHA, GITHUB_STEP_SUMMARY=os.path.join(d, "summary"),
                       GITHUB_SERVER_URL="https://github.com", GITHUB_REPOSITORY="example/repository",
                       PATH=os.path.join(d, "bin") + os.pathsep + os.environ["PATH"], **env)
            r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", step["run"]], cwd=d, env=env,
                               capture_output=True, text=True)
            return r.returncode, r.stdout + r.stderr

    def test_required_names_the_merge_queue_runs_on_a_push_the_queue_checked(self):
        """On a push whose jobs queue_run skipped, required still runs and passes only by naming the merge queue runs
        queue_run found; on any other run its step that collects every job's result runs instead."""
        queued = "a push the merge queue checked, by the merge queue runs of its commits"
        collect = "every job green, and something checked when the plan named anything"
        steps = {s.get("name"): " ".join(s.get("if", "").split()) for s in self.jobs["required"]["steps"]}
        self.assertIn("queue_run", self.jobs["required"]["needs"])
        # how queue_run's finding reaches the step: its job outputs, and the step's env
        self.assertEqual(self.jobs["queue_run"]["outputs"], {"checked": "${{ steps.queue.outputs.checked }}",
                                                             "runs": "${{ steps.queue.outputs.runs }}"})
        # the step whose outputs those are: a rename of its name or its id fails here rather than leaving `checked`
        # empty, which would run the full check
        ids = {s.get("name"): s.get("id") for s in self.jobs["queue_run"]["steps"]}
        self.assertEqual(ids.get(self.QUEUE_STEP), "queue", ids)
        step = next(s for s in self.jobs["required"]["steps"] if s.get("name") == queued)
        self.assertEqual((step["env"]["QUEUE_RESULT"], step["env"]["QUEUE_RUNS"]),
                         ("${{ needs.queue_run.result }}", "${{ needs.queue_run.outputs.runs }}"))
        self.assertEqual(steps[queued], "needs.queue_run.outputs.checked == 'true'")
        self.assertEqual(steps[collect], "needs.queue_run.outputs.checked != 'true'")
        for runs in ("40000000011", "40000000012 40000000013"):
            rc, output = self.required_step(queued, {"QUEUE_RESULT": "success", "QUEUE_RUNS": runs})
            self.assertEqual(rc, 0, output)
            for run in runs.split():
                self.assertIn("merge queue run %s passed main-gate" % run, output)
        for result, runs in (("success", ""), ("success", "not-a-run"), ("success", "1  2"), ("success", "1 "),
                             ("failure", "40000000011"), ("skipped", "40000000011")):
            with self.subTest(result=result, runs=runs):
                rc, output = self.required_step(queued, {"QUEUE_RESULT": result, "QUEUE_RUNS": runs})
                self.assertEqual(rc, 1, output)

    def test_required_fails_on_a_router_answer_it_cannot_read(self):
        """The router's answers decide which jobs had to run; an empty or other answer (a step that wrote nothing, a
        renamed output) must fail required rather than read as "not needed" and pass a job that never ran."""
        collect = "every job green, and something checked when the plan named anything"
        step = next(s for s in self.jobs["required"]["steps"] if s.get("name") == collect)
        self.assertEqual(step["env"], {
            "DRAFTS_LISTED": "${{ needs.plan.outputs.draft_legs != '[]' }}",
            "FETCH_DRAFTS_RESULT": "${{ needs.fetch-drafts.result }}",
            "PLAN_RESULT": "${{ needs.plan.result }}", "TESTS": "${{ needs.plan.outputs.tests }}",
            "CONTROLS": "${{ needs.plan.outputs.controls }}",
            "REPOSITORY_LINT": "${{ needs.plan.outputs.repository_lint }}", "UNITS": "${{ needs.plan.outputs.units }}",
            "HOLD": "${{ needs.plan.outputs.hold }}",
            "QUEUED": "${{ github.event_name == 'pull_request' && github.event.pull_request.base.ref == 'main' "
                      "&& github.repository != 'theorem-labs/oss-verify-proofs' }}",
            "PLANNED_TOOLS": "${{ needs.plan.outputs.tools }}",
            "LINT_RESULT": "${{ needs.lint.result }}", "TESTS_RESULT": "${{ needs.tests.result }}",
            "CONTROLS_RESULT": "${{ needs.controls.result }}", "CHECK_RESULT": "${{ needs.check.result }}",
            "STREAM_TOOLS": "${{ needs.plan.outputs.stream_tools }}",
            "STREAM_TOOLS_RESULT": "${{ needs.stream_tools.result }}",
            "FARM_TESTS": "${{ needs.plan.outputs.farm_tests }}",
            "FARM_TESTS_RESULT": "${{ needs.farm_tests.result }}",
            # merge-pr.sh's evidence comment, for a check held for the label (test_workflow_verdicts.PrHoldTest)
            "GH_TOKEN": "${{ github.token }}", "PR": "${{ github.event.pull_request.number }}",
            "HEAD_SHA": "${{ github.event.pull_request.head.sha }}", "VM_EVIDENCE_BY": "sjawhar-agent[bot]",
            # the parts a check of record outside this run checked: the pinned tree's deferred check, or a merge
            # queue group checked on a VM (test_workflow_verdicts.CollectTest)
            "CHECKED_ELSEWHERE": "${{ needs.plan.outputs.checked_elsewhere }}",
            "CHECKED_ELSEWHERE_NOTE": "${{ needs.plan.outputs.checked_elsewhere_note }}"})
        # no draft listed, so fetch-drafts was skipped, as the release line's own step requires
        nothing = {"DRAFTS_LISTED": "false", "FETCH_DRAFTS_RESULT": "skipped",
                   "PLAN_RESULT": "success", "TESTS": "false", "CONTROLS": "false", "REPOSITORY_LINT": "false",
                   "UNITS": "0", "HOLD": "none", "QUEUED": "true", "PLANNED_TOOLS": "base", "LINT_RESULT": "success",
                   "TESTS_RESULT": "skipped", "CONTROLS_RESULT": "skipped", "CHECK_RESULT": "skipped",
                   "GH_TOKEN": "t", "PR": "7", "HEAD_SHA": "c" * 40, "VM_EVIDENCE_BY": "sjawhar-agent[bot]",
                   "CHECKED_ELSEWHERE": "false", "CHECKED_ELSEWHERE_NOTE": "",
                   "STREAM_TOOLS": "false", "STREAM_TOOLS_RESULT": "skipped",
                   "FARM_TESTS": "false", "FARM_TESTS_RESULT": "skipped"}
        everything = dict(nothing, TESTS="true", CONTROLS="true", REPOSITORY_LINT="true", UNITS="3",
                          TESTS_RESULT="success", CONTROLS_RESULT="success", CHECK_RESULT="success",
                          STREAM_TOOLS="true", STREAM_TOOLS_RESULT="success",
                          FARM_TESTS="true", FARM_TESTS_RESULT="success")
        # a draft: lint, and every job after it, skipped (lint's `if:`)
        draft = dict(everything, HOLD="draft", LINT_RESULT="skipped", TESTS_RESULT="skipped",
                     CONTROLS_RESULT="skipped", CHECK_RESULT="skipped", STREAM_TOOLS_RESULT="skipped",
                     FARM_TESTS_RESULT="skipped")
        unlabelled = dict(everything, HOLD="label", CHECK_RESULT="skipped")
        for name, env in (("nothing needed", nothing), ("everything needed and green", everything),
                          ("the base pins this change's tools", dict(everything, PLANNED_TOOLS="head")),
                          ("a merge queue group", dict(everything, QUEUED="false")),
                          ("a draft into main: lint skipped", draft),
                          ("no label check, into main: check skipped", unlabelled),
                          ("a draft that plans nothing: lint skipped", dict(draft, TESTS="false", CONTROLS="false",
                                                                           REPOSITORY_LINT="false", UNITS="0",
                                                                           STREAM_TOOLS="false", FARM_TESTS="false")),
                          ("no label, plans nothing, no queue", dict(nothing, HOLD="label", QUEUED="false")),
                          ("the farm runner's tests alone needed and green",
                           dict(nothing, FARM_TESTS="true", FARM_TESTS_RESULT="success"))):
            with self.subTest(case=name):
                rc, output = self.required_step(collect, env)
                self.assertEqual(rc, 0, output)
                self.assertEqual("checks skipped: " in output, "check skipped" in name, output)
                self.assertEqual("lint skipped: a draft" in output, "lint skipped" in name, output)
        # with no merge queue after the pull request (another base, or the public repository), a held check never
        # looks green, and neither does a draft
        rc, output = self.required_step(collect, dict(unlabelled, QUEUED="false"))
        self.assertEqual(rc, 1, output)
        self.assertIn("planned checks not run at this head", output)
        self.assertIn("add the label `check` and re-run all jobs", output)
        rc, output = self.required_step(collect, dict(draft, QUEUED="false"))
        self.assertEqual(rc, 1, output)
        self.assertIn("a draft: lint and the jobs after it did not run at this head; mark it ready for review", output)
        bad = [("plan failed", dict(nothing, PLAN_RESULT="failure")),
               ("no tests answer", dict(nothing, TESTS="")), ("no controls answer", dict(nothing, CONTROLS="")),
               ("no repository_lint answer", dict(nothing, REPOSITORY_LINT="")),
               ("a tests answer of another word", dict(nothing, TESTS="yes")),
               ("no units answer", dict(nothing, UNITS="")), ("units not a count", dict(nothing, UNITS="1 2")),
               ("no tools answer", dict(nothing, PLANNED_TOOLS="")),
               ("a tools answer of another word", dict(nothing, PLANNED_TOOLS="base/tools")),
               ("repository_lint without tests", dict(nothing, REPOSITORY_LINT="true")),
               ("lint failed", dict(nothing, LINT_RESULT="failure")),
               ("tests needed, not run", dict(everything, TESTS_RESULT="skipped")),
               ("tests needed, failed", dict(everything, TESTS_RESULT="failure")),
               ("controls needed, not run", dict(everything, CONTROLS_RESULT="skipped")),
               ("check needed, cancelled", dict(everything, CHECK_RESULT="cancelled")),
               ("tests not needed, yet ran", dict(nothing, TESTS_RESULT="success")),
               ("no harness planned, yet check ran", dict(nothing, CHECK_RESULT="success")),
               ("no hold answer", dict(everything, HOLD="")),
               ("a hold answer of another word", dict(nothing, HOLD="false")),
               ("held, yet check ran", dict(unlabelled, CHECK_RESULT="success")),
               ("a draft, check failed", dict(draft, CHECK_RESULT="failure")),
               ("no stream_tools answer", dict(nothing, STREAM_TOOLS="")),
               ("a stream_tools answer of another word", dict(nothing, STREAM_TOOLS="yes")),
               ("the stream tools needed, not run", dict(everything, STREAM_TOOLS_RESULT="skipped")),
               ("the stream tools needed, failed", dict(everything, STREAM_TOOLS_RESULT="failure")),
               ("the stream tools not needed, yet ran", dict(nothing, STREAM_TOOLS_RESULT="success")),
               ("no farm_tests answer", dict(nothing, FARM_TESTS="")),
               ("a farm_tests answer of another word", dict(nothing, FARM_TESTS="yes")),
               ("the farm runner's tests needed, not run", dict(everything, FARM_TESTS_RESULT="skipped")),
               ("the farm runner's tests needed, one leg failed", dict(everything, FARM_TESTS_RESULT="failure")),
               ("the farm runner's tests needed, cancelled", dict(everything, FARM_TESTS_RESULT="cancelled")),
               ("the farm runner's tests not needed, yet ran", dict(nothing, FARM_TESTS_RESULT="success")),
               ("a draft, yet the farm runner's tests ran", dict(draft, FARM_TESTS_RESULT="success"))]
        for name, env in bad:
            with self.subTest(case=name):
                rc, output = self.required_step(collect, env)
                self.assertEqual(rc, 1, output)


class ScheduledProofCheck(unittest.TestCase):
    """weekly.yml is the one workflow that checks proofs on a schedule. A publication checks only the parts whose keys
    it changes (pr.yml and release-check.yml also check each change by its own diff), so weekly.yml's Monday run is
    what checks again every proof that no change touched (docs/versioning.md). A scheduled check publishes nothing."""

    def workflows(self):
        d = os.path.join(REPO, ".github", "workflows")
        if not os.path.isdir(d):
            self.skipTest("no .github/workflows beside tools/oft")
        return {name: yamlio.load_file(os.path.join(d, name)) for name in sorted(os.listdir(d))}

    def test_only_weekly_checks_proofs_on_a_schedule(self):
        """A workflow checks proofs when a step of it runs check-units.sh, or when a job of it calls (`uses:`) a
        workflow of this repository that does, as release.yml calls weekly.yml."""
        flows = self.workflows()
        checking = {name for name, w in flows.items()
                    if any("check-units.sh" in s.get("run", "") for job in w["jobs"].values()
                           for s in job.get("steps", []))}
        while True:
            callers = {name for name, w in flows.items() if name not in checking
                       and any(job.get("uses", "").removeprefix("./.github/workflows/") in checking
                               for job in w["jobs"].values())}
            if not callers:
                break
            checking |= callers
        self.assertTrue({"pr.yml", "release-check.yml", "weekly.yml", "release.yml"} <= checking, checking)
        for name in sorted(checking - {"weekly.yml"}):
            with self.subTest(workflow=name):
                self.assertNotIn("schedule", flows[name]["on"])
        self.assertEqual(flows["weekly.yml"]["on"].get("schedule"), [{"cron": "17 3 * * 1"}])

    def test_a_scheduled_weekly_run_checks_every_unit(self):
        """A scheduled run has no inputs, so the plan step's UNITS is empty and it plans every unit of the tree. It runs
        in the public repository (id 1430054678) only: there plan's condition holds on a schedule (test_workflow_verdicts
        tests the condition in each repository)."""
        plan = self.workflows()["weekly.yml"]["jobs"]["plan"]
        self.assertEqual(plan["if"], "github.event_name != 'schedule' || github.repository_id == '1430054678'")
        step = next(s for s in plan["steps"] if s.get("id") == "plan")
        self.assertEqual(step["env"]["UNITS"], "${{ inputs.units }}")
        self.assertIn("jq -r '.units[]' \"$RUNNER_TEMP/all.json\" > \"$RUNNER_TEMP/units.txt\"", step["run"])

    def test_release_check_s_check_job_runs_no_tool_outside_the_checker(self):
        """release-check.yml plans no proof for a change to the files keys.NOT_THE_CHECKER names, so its check job
        may not run them: it runs oft.fetch and check-units.sh (oft.check), never `python -m oft`, whose __main__
        imports the lint, the planner and the rest."""
        job = self.workflows()["release-check.yml"]["jobs"]["check"]
        runs = " ".join(s.get("run", "") for s in job["steps"])
        self.assertIn("python -m oft.fetch", runs)
        self.assertNotRegex(runs, r"python3? -m oft\s")


# A gh stand-in for the calls of pr.yml's queue_run: the runs of a workflow, filtered by the query as GitHub filters
# them (event, head_sha, branch, status), one run's jobs, and one commit's parents.
# A list is paged as the API pages it (per_page, default 30): without --paginate gh reads the first page only, and
# with it every page, each through the step's own --jq.  Anything else is an error.
FAKE_GH_API = r'''import json, subprocess, sys, urllib.parse
with open(%s) as f:
    data = json.load(f)
args = sys.argv[1:]
paginate = "--paginate" in args
args = [a for a in args if a != "--paginate"]
url = urllib.parse.urlparse(args[1])
query = dict(urllib.parse.parse_qsl(url.query))
jq = args[args.index("--jq") + 1] if "--jq" in args else "."
parts = url.path.strip("/").split("/")
key = None
if parts[-1] == "jobs":
    if parts[-2] not in data["jobs"]:
        sys.exit("gh: no jobs for run " + parts[-2])
    key, items = "jobs", data["jobs"][parts[-2]]
elif parts[-2] == "commits":
    if parts[-1] not in data["parents"]:
        sys.exit("gh: no commit " + parts[-1])
    bodies = [{"sha": parts[-1], "parents": [{"sha": p} for p in data["parents"][parts[-1]]]}]
elif parts[-1] == "runs" and "workflows" in parts:
    if data["runs"] is None:
        sys.exit("gh: the run list cannot be read")
    key, items = "workflow_runs", [r for r in data["runs"]
        if all(str(r[k]) == query[q] for q, k in (("event", "event"), ("head_sha", "head_sha"),
                                                   ("branch", "head_branch"), ("status", "conclusion"))
               if q in query)]
else:
    sys.exit("gh: no answer for " + args[1])
if key:
    size = int(query.get("per_page", 30))
    pages = [items[i:i + size] for i in range(0, len(items), size)] or [[]]
    bodies = [{"total_count": len(items), key: page} for page in (pages if paginate else pages[:1])]
for body in bodies:
    rc = subprocess.run(["jq", "-r", jq], input=json.dumps(body), text=True).returncode
    if rc:
        sys.exit(rc)
'''


def restores_a_dune_cache(step):
    """A step that would put a dune cache on the runner: actions/cache/restore, and the combined actions/cache, which
    restores at the start of the job and saves at its end.  actions/cache/save only writes, so it is not one."""
    uses = step.get("uses", "")
    if not (uses.startswith("actions/cache@") or uses.startswith("actions/cache/restore@")):
        return False
    return "dune" in str(step.get("with", {}).get("path", ""))


class NoDuneCache(unittest.TestCase):
    """dune restores a cache entry without hashing the bytes it copies, and the kernel does not check a compiled file
    again when a proof loads it: a valid Statements.vo of a weaker statement put in a restored cache made doctored
    proofs pass check-units.sh (27 October 02:22Z).  And a cache that one unit's check writes and another's reads lets
    the first change the second's result.  So no workflow restores or saves a dune cache, and check-units.sh runs dune
    with its cache off, in a container of each unit's own."""
    CACHE = "actions/cache@5a3ec84eff668545956fd18022155c47e93e2684"
    RESTORE = "actions/cache/restore@5a3ec84eff668545956fd18022155c47e93e2684"
    SAVE = "actions/cache/save@5a3ec84eff668545956fd18022155c47e93e2684"

    def test_no_workflow_restores_or_saves_a_dune_cache(self):
        d = os.path.join(REPO, ".github", "workflows")
        if not os.path.isdir(d):
            self.skipTest("no .github/workflows beside tools/oft")
        for name in sorted(os.listdir(d)):
            for job_name, job in yamlio.load_file(os.path.join(d, name))["jobs"].items():
                for s in job.get("steps", []):
                    if s.get("uses", "").startswith("actions/cache"):
                        with self.subTest(workflow=name, job=job_name, step=s.get("name")):
                            self.assertNotIn("dune", str(s["with"]), "a dune cache step")

    def test_no_workflow_restores_a_dune_cache(self):
        d = os.path.join(REPO, ".github", "workflows")
        if not os.path.isdir(d):
            self.skipTest("no .github/workflows beside tools/oft")
        for name in sorted(os.listdir(d)):
            for job_name, job in yamlio.load_file(os.path.join(d, name))["jobs"].items():
                for s in job.get("steps", []):
                    with self.subTest(workflow=name, job=job_name, step=s.get("name", s.get("uses"))):
                        self.assertFalse(restores_a_dune_cache(s), "a step that restores a dune cache")

    def test_a_dune_cache_restore_is_caught_however_it_is_written(self):
        """The planted positives of the rule above: the combined action is a restore too, and a job that only saves
        the cache, or caches something else, is not."""
        dune = {"path": "${{ runner.temp }}/dune-cache", "key": "k"}
        for uses in (self.CACHE, self.RESTORE):
            with self.subTest(uses=uses):
                self.assertTrue(restores_a_dune_cache({"uses": uses, "with": dune}))
        for step in ({"uses": self.SAVE, "with": dune},
                     {"uses": self.CACHE, "with": {"path": "${{ runner.temp }}/assets", "key": "k"}},
                     {"uses": self.RESTORE, "with": {"path": "~/.cache/pip", "key": "k"}},
                     {"uses": "actions/checkout@v4", "with": {"path": "dune-cache"}},
                     {"run": "echo no uses at all"}):
            with self.subTest(step=step):
                self.assertFalse(restores_a_dune_cache(step))

    def test_check_units_runs_dune_with_its_cache_off(self):
        with open(os.path.join(REPO, "tools", "oft", "ci", "check-units.sh")) as f:
            script = f.read()
        self.assertIn("-e DUNE_CACHE=disabled", script)
        self.assertNotIn("XDG_CACHE_HOME", script)
        self.assertNotIn("CACHE:", script)


class Paths(unittest.TestCase):
    def test_a_stray_path(self):
        with tree() as t:
            t.write("projects/zlib/checksum_fuzzer/scratch/x.log", "a stray file\n")
            self.assertIn("paths", rules_of(t.lint()))

    def test_the_stream_s_operational_tools_are_hand_written_files_of_their_own_top_level(self):
        """dev/stream/ is a top level of its own, outside tools/, so that keys.checker (which lists tools/ alone) holds
        no file of it in any unit's key (dev/stream/README.md).  The paths table must still name it, or every file of
        the stream's tools would be a finding of this rule."""
        for rel in ("dev/stream/README.md", "dev/stream/bin/ossv-tools", "dev/stream/lane/claim.py",
                    "dev/stream/tests/test_x.py"):
            self.assertEqual([c for c, _, _ in paths.classify(rel)], ["hand"], rel)
        with tree() as t:
            t.write("dev/stream/bin/ossv-tools", "#!/bin/sh\necho deployed\n")
            t.write("dev/stream/README.md", "# stream\n")
            self.assertNotIn("paths", rules_of(t.lint()))

    def test_another_top_level_directory_is_still_a_finding(self):
        """Only dev/stream/ is added: a file at any other unlisted top level is reported, as it was before."""
        with tree() as t:
            t.write("streaming/x.md", "a top level the table does not name\n")
            self.assertIn("paths streaming/x.md: matches no path pattern", [str(f) for f in t.lint()])

    def test_a_derived_file(self):
        with tree() as t:
            t.write("projects/zlib/checksum_fuzzer/Statements.vo", "x")
            self.assertIn("paths", rules_of(t.lint()))

    def test_the_rows_of_the_prove_tools(self):
        """The paths the prove tools add each have one owner before the tools arrive, so that a pull request into
        main that adds them passes lint by the base's rules: ./theorem, a change's ledger, a build's symbol fact and
        the Symbols.v rendered from it.  A harness named Symbols.v is no harness."""
        for rel, owner in (("theorem", "hand"), ("changes/libreac-35/ledger.tsv", "hand"),
                           ("changes/tools/journal.md", "hand"),
                           ("projects/zlib/checksum_fuzzer/symbols/plain.tsv", "facts"),
                           ("projects/zlib/checksum_fuzzer/Symbols.v", "gen")):
            self.assertEqual([c for c, _, _ in paths.classify(rel)], [owner], rel)
        self.assertEqual(paths.classify("projects/zlib/Symbols.v/harness.yaml"), [])

    def test_a_name_git_quotes(self):
        # a path a source pattern admits, so that only the name is wrong
        for name in ('a"b.c', "a\\b.c", "a\tb.c"):
            with tree() as t:
                t.write("projects/zlib/checksum_fuzzer/source/" + name, "int x;\n")
                found = [f for f in t.lint() if f.rule == "paths"]
                self.assertTrue(any("control character" in f.msg for f in found), (name, [str(f) for f in found]))

    def test_paths_equal_up_to_case(self):
        """Two files, or two directories, whose paths differ only in case collide on a case-insensitive checkout."""
        for a, b in (("lib/Ab.v", "lib/aB.v"), ("lib/X/a.v", "lib/x/b.v")):
            with tree() as t:
                for name in (a, b):
                    t.write("proofs/zlib/checksum_fuzzer/" + name, "Lemma x : True.\nProof. exact I. Qed.\n")
                entries = os.listdir(t.path("proofs/zlib/checksum_fuzzer/lib"))
                if not {a.split("/")[1], b.split("/")[1]} <= set(entries):
                    self.skipTest("a case-insensitive file system holds only one of the two spellings")
                found = [str(f) for f in t.lint() if "equal up to case" in f.msg]
                self.assertEqual(len(found), 1, (a, b, found))

    def test_paths_that_differ_in_more_than_case(self):
        with tree() as t:
            for name in ("lib/Ab.v", "lib/Ab_c1.v", "lib/X/a.v", "lib/Y/a.v"):
                t.write("proofs/zlib/checksum_fuzzer/" + name, "Lemma x : True.\nProof. exact I. Qed.\n")
            self.assertFalse([str(f) for f in t.lint() if "equal up to case" in f.msg])

    def test_an_elf_file(self):
        with tree() as t:
            t.write("projects/zlib/checksum_fuzzer/source/a.out", "\x7fELF\x02\x01\x01")
            found = t.lint()
            self.assertTrue(any("an ELF file" in f.msg for f in found))

    NUL = "a NUL byte: binary data is a release asset, not a file in git"

    def test_a_nul_byte_anywhere_in_a_file(self):
        """Past the first 8 KiB too, where the text rules would still read the file as text."""
        for at in (0, 9000):
            with self.subTest(at=at), tree() as t:
                t.write("notes/json.md", "x" * at + "\0 notes\n")
                self.assertIn("paths notes/json.md: " + self.NUL, [str(f) for f in t.lint()])

    def test_binary_data_where_it_belongs(self):
        """A counterexample's and a finding's runs, and the tests' fixtures, are bytes."""
        with tree() as t:
            add_findings(t)
            t.write("tools/oft/tests/fixtures/x.bin", "\0\1\2")
            self.assertTrue(os.path.getsize(t.path("counterexamples/json/fuzzer-parse_bjdata/plain_halts/input.bin")))
            self.assertFalse(any(self.NUL in f.msg for f in t.lint()))
            t.write("counterexamples/json/fuzzer-parse_bjdata/plain_halts/expect.yaml", "\0", "a")
            self.assertTrue(any(self.NUL in str(f) and "expect.yaml" in str(f) for f in t.lint()))

    def test_binary_data_where_it_belongs_in_the_per_project_layout(self):
        """The runs of a counterexample and of a finding in projects/<p>/<h>/ are bytes as in the old layout."""
        with tree() as t:
            add_findings(t)
            self.assertEqual(port.port_worktree(t.root, out=io.StringIO()), 0)
            self.assertEqual(t.generate(), 0, t.last_output)
            cx = "projects/json/fuzzer-parse_bjdata/counterexamples/plain_halts/"
            runs = [cx + "input.bin"] + [os.path.relpath(p, t.root) for p in glob.glob(
                t.path("projects/zlib/checksum_fuzzer/findings/*/input.bin"))]
            self.assertEqual(len(runs), 2, runs)
            for rel in runs:
                t.write(rel, "\0", "a")
            self.assertFalse([str(f) for f in t.lint() if self.NUL in f.msg])
            t.write(cx + "expect.yaml", "\0", "a")
            self.assertEqual([str(f) for f in t.lint() if self.NUL in f.msg],
                             ["paths %sexpect.yaml: %s" % (cx, self.NUL)])

    def test_a_mutant_runs_input_kept_as_evidence_is_bytes(self):
        """A mutant run's input under a fuzz target's provenance/evidence/mutants/<m>/ is a fuzz input, bytes as a
        counterexample's; any other file of that folder, or an input.bin elsewhere in the evidence, is not."""
        with tree() as t:
            self.assertEqual(port.port_worktree(t.root, out=io.StringIO()), 0)
            self.assertEqual(t.generate(), 0, t.last_output)
            ev = "projects/zlib/checksum_fuzzer/proofs/provenance/evidence/"
            t.write(ev + "mutants/len/input.bin", "\0\1\2")
            self.assertFalse([str(f) for f in t.lint() if self.NUL in f.msg])
            for rel in (ev + "mutants/len/run.log", ev + "other/len/input.bin", ev + "mutants/input.bin"):
                t.write(rel, "\0")
            self.assertEqual(sorted(str(f) for f in t.lint() if self.NUL in f.msg),
                             sorted("paths %s: %s" % (rel, self.NUL) for rel in (
                                 ev + "mutants/len/run.log", ev + "other/len/input.bin", ev + "mutants/input.bin")))

    def classifier(self, t, elf, pinned):
        """A classifier proof of zlib/checksum_fuzzer/plain_halts whose proof.yaml pins `pinned` as its program's
        SHA-256; the program's bytes are elf."""
        d = "proofs/zlib/checksum_fuzzer/plain_halts/"
        t.put_yaml(d + "proof.yaml", {
            "schema": "oss-fuzz-theorems/proof/1", "proves": "zlib/checksum_fuzzer/plain_halts",
            "fingerprint": next(s for s in facts.load(t.root).statements()
                                if s.id == "zlib/checksum_fuzzer/plain_halts").fingerprint,
            "classifier": {"source": "classifier/c.c", "elf": "classifier/c", "sha256": pinned}})
        t.write(d + "Proof.v", "Theorem plain_halts_holds : True. Proof. exact I. Qed.\n")
        t.write(d + "classifier/c.c", "int main(void) { return 0; }\n")
        t.write(d + "classifier/c", elf, "wb")
        self.assertEqual(t.generate(), 0, t.last_output)
        return [str(f) for f in t.lint() if f.rule == "paths"]

    def test_a_classifier_program_its_proof_pins(self):
        elf = b"\x7fELF\x02\x01\x01\0\0 a classifier"
        with tree() as t:
            self.assertEqual(self.classifier(t, elf, hashlib.sha256(elf).hexdigest()), [])
        with tree() as t:
            self.assertEqual(self.classifier(t, elf, "0" * 64), [
                "paths proofs/zlib/checksum_fuzzer/plain_halts/classifier/c: a classifier program whose SHA-256 is not "
                "the classifier.sha256 of proofs/zlib/checksum_fuzzer/plain_halts/proof.yaml"])

    def test_an_elf_file_under_classifier_that_no_proof_pins(self):
        with tree() as t:
            t.write("proofs/zlib/checksum_fuzzer/plain_halts/classifier/other", "\x7fELF\x02\x01\x01\0")
            found = [str(f) for f in t.lint()]
            self.assertIn("paths proofs/zlib/checksum_fuzzer/plain_halts/classifier/other: an ELF file: binaries are "
                          "release assets, not files in git", found)

    PUBLISHING = {"tools/publish/needles.txt": "/" + "home/someone/x\nsomeone" + "@example.com\n",
                  "tools/publish/tests/test_scan.py": "NEEDLE = 'https://github.com/theorem-labs/" + "internal'\n",
                  ".github/workflows/publish.yml": "name: publish\n",
                  ".github/workflows/publish-gate.yml": "name: publish-gate\n"}

    def test_the_internal_paths_have_an_owner_and_their_text_is_not_read(self):
        """tools/publish/ holds the scanner's needles, host paths and addresses on purpose; no release carries it, so
        the text rules read it for secrets alone (test_a_secret_in_an_internal_path_is_a_finding)."""
        with tree() as t:
            for rel, text in self.PUBLISHING.items():
                t.write(rel, text)
            self.assertEqual([str(f) for f in t.lint()], [])

    def test_an_internal_path_is_still_held_to_the_path_rules(self):
        with tree() as t:
            t.write("tools/publish/blob", "\x7fELF\x02\x01\x01")
            self.assertIn("paths tools/publish/blob: an ELF file: binaries are release assets, not files in git",
                          [str(f) for f in t.lint()])

    def test_a_secret_in_an_internal_path_is_a_finding(self):
        """The text rules read an internal path for a private key or an access token alone: a secret in tools/enroll/
        or tools/publish/ is as bad as one in a shipped file, while tools/publish/'s host paths and addresses are not
        read (test_the_internal_paths_have_an_owner_and_their_text_is_not_read)."""
        token = "gh" + "p_" + "a" * 36
        key = "-----BEGIN " + "OPENSSH PRIVATE KEY-----"
        with tree() as t:
            t.write("tools/enroll/creds.txt", "x\n" + token + "\n")
            t.write("tools/publish/key.txt", key + "\n")
            t.write("tools/publish/needles.txt", "/" + "home/someone/x\n")
            found = sorted((f.where, f.msg) for f in t.lint() if f.rule == "private-data")
            self.assertEqual(found, [("tools/enroll/creds.txt:2", "an access token"),
                                     ("tools/publish/key.txt:1", "a private key")])

    def test_only_a_maintainer_changes_an_internal_path(self):
        with tree() as t:
            for rel, text in self.PUBLISHING.items():
                t.write(rel, text)
            changed = sorted(self.PUBLISHING)
            self.assertEqual(len([f for f in t.lint(changed=changed, pr_kind="contributor") if f.rule == "paths"]),
                             len(changed))
            self.assertEqual(t.lint(changed=changed, pr_kind="maintainer"), [])

    def test_the_elf_fixture_of_the_tools_tests(self):
        """The four small ELF files test_symbols reads, built as tools/oft/tests/fixtures/elf/README.md says; any
        other ELF file is still a finding, beside them and under tools/oft/tests/ too."""
        with tree() as t:
            t.write("tools/oft/tests/fixtures/elf/two.stripped", "\x7fELF\x02\x01\x01")
            t.write("tools/oft/tests/fixtures/elf/two.unstripped", "\x7fELF\x02\x01\x01")
            t.write("tools/oft/tests/fixtures/elf/computed_goto_global.elf", "\x7fELF\x02\x01\x01")
            t.write("tools/oft/tests/fixtures/elf/computed_goto_biased.elf", "\x7fELF\x02\x01\x01")
            t.write("tools/oft/tests/fixtures/elf/three.stripped", "\x7fELF\x02\x01\x01")
            t.write("tools/oft/tests/fixtures/tree/a.out", "\x7fELF\x02\x01\x01")
            self.assertEqual([str(f) for f in t.lint() if "an ELF file" in f.msg],
                             ["paths %s: an ELF file: binaries are release assets, not files in git" % rel
                              for rel in ("tools/oft/tests/fixtures/elf/three.stripped",
                                          "tools/oft/tests/fixtures/tree/a.out")])

    def test_an_lfs_pointer(self):
        with tree() as t:
            t.write("notes/json.md", "version https://git-lfs.github.com/spec/v1\noid sha256:00\n")
            self.assertTrue(any("LFS" in f.msg for f in t.lint()))

    def test_gitattributes_that_change_what_a_checkout_holds(self):
        """A checkout that differs from the blobs: an LFS filter, and a working-tree-encoding (a file checked out in
        UTF-16 has NUL bytes, so the text rules would skip it, while GitHub serves its UTF-8 blob)."""
        for line, msg in (("*.bin filter=lfs diff=lfs merge=lfs -text", "an LFS filter"),
                          ("notes/*.md working-tree-encoding=UTF-16LE", "a working-tree-encoding")):
            with self.subTest(line=line), tree() as t:
                t.write(".gitattributes", line + "\n")
                self.assertIn("paths .gitattributes: " + msg, [str(f) for f in t.lint()])

    def test_a_non_release_change_to_facts(self):
        with tree() as t:
            changed = ["projects/zlib/checksum_fuzzer/harness.yaml"]
            self.assertIn("paths", rules_of(t.lint(changed=changed, pr_kind="maintainer")))
            self.assertEqual(t.lint(changed=changed, pr_kind="release"), [])

    def test_a_contributor_outside_proofs(self):
        with tree() as t:
            self.assertIn("paths", rules_of(t.lint(changed=["tools/oft/lint.py"], pr_kind="contributor")))
            self.assertEqual(t.lint(changed=["docs/proving.md"], pr_kind="contributor"), [])

    def test_a_size_cap(self):
        with tree() as t:
            t.write("notes/json.md", "x" * (facts.MAX_BYTES + 1))
            self.assertTrue(any("cap" in f.msg for f in t.lint()))

    # main's cap table before facts.CAPS (lint.CAPS, matched by paths.py's globs: `*` is any part, `**` any number of
    # parts, none included), with the per-project layout's rows that L1 (ossv/recipes #400) added to it
    GLOB_CAPS = [
        ("index/*.tsv", 64 << 20),
        ("projects/*/*/source/**", 256 << 10),
        ("counterexamples/**", 64 << 10),
        ("projects/*/*/counterexamples/**", 64 << 10),
        ("findings/*/*/*/input.bin", 1 << 20),
        ("projects/*/*/findings/*/input.bin", 1 << 20),
        ("findings/*/*/*/control.bin", 1 << 20),
        ("projects/*/*/findings/*/control.bin", 1 << 20),
        ("findings/**", 64 << 10),
        ("projects/*/*/findings/**", 64 << 10),
        ("projects/*/unpatched.yaml", 64 << 10),
        ("proofs/*/*/*/classifier/**", 1 << 20),
        ("projects/*/*/proofs/*/classifier/**", 1 << 20),
    ]

    def test_each_file_s_size_cap(self):
        """facts.CAPS: the first pattern that matches the whole path gives the cap, else facts.MAX_BYTES.  It gives
        every path the cap main's glob table gave it: for each row, a path it matches with each `*` filled and `**`
        filled by no part (a file named like the cap's directory: the gate round's B2), one part and two, and the same
        path with its last part changed, a part more or a part less at either end."""
        finding = "findings/zlib/checksum_fuzzer/stand-in-abort/"
        for rel, cap in (("index/statements.tsv", 64 << 20), ("index/sub/statements.tsv", facts.MAX_BYTES),
                         ("projects/zlib/checksum_fuzzer/source/sub/fuzz.c", 256 << 10),
                         ("projects/zlib/checksum_fuzzer/harness.yaml", facts.MAX_BYTES),
                         ("counterexamples/zlib/checksum_fuzzer/asan_halts/expect.yaml", 64 << 10),
                         (finding + "input.bin", 1 << 20), (finding + "control.bin", 1 << 20),
                         (finding + "0001-stand-in.patch", 64 << 10), ("findings/zlib/checksum_fuzzer/series", 64 << 10),
                         ("proofs/zlib/checksum_fuzzer/asan_halts/classifier/run.v", 1 << 20),
                         ("proofs/zlib/checksum_fuzzer/asan_halts/classifier", 1 << 20),
                         ("patches/zlib/0001-stand-in.patch", facts.MAX_BYTES), ("notes/zlib.md", facts.MAX_BYTES)):
            with self.subTest(rel=rel):
                self.assertEqual(facts.file_cap(rel), cap)
        probes = set()
        for pattern, _ in self.GLOB_CAPS:
            filled = [[]]
            for part in pattern.split("/"):
                filled = [f + more for f in filled
                          for more in (([], ["a"], ["a", "b.v"]) if part == "**" else ([part.replace("*", "x")],))]
            for f in filled:
                probes.update("/".join(p) for p in (f, f[:-1] + [f[-1] + "x"], f + ["y"], ["z"] + f, f[1:], f[:-1])
                              if p)
        for rel in sorted(probes):
            glob = next((cap for pattern, cap in self.GLOB_CAPS
                         if paths.match(pattern, rel) is not None), facts.MAX_BYTES)
            with self.subTest(rel=rel):
                self.assertEqual(facts.file_cap(rel), glob)

    def lint_in_a_child(self, t):
        """oft lint over t in a child process, so a read that blocks fails the test instead of hanging it."""
        tools = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
        try:
            r = subprocess.run([sys.executable, "-B", "-m", "oft", "--root", t.root, "lint"], cwd=tools,
                               env=dict(os.environ, PYTHONPATH=tools), capture_output=True, text=True, timeout=60)
        except subprocess.TimeoutExpired:
            self.fail("oft lint blocked reading a file")
        return r.stdout

    def test_a_symlink_is_reported_and_never_read(self):
        """A link to a file outside the tree is not read for text: its target's host path is not reported."""
        with tree() as t, tempfile.TemporaryDirectory() as outside:
            target = os.path.join(outside, "target.md")
            with open(target, "w") as f:
                f.write("see /" + "data/someone/x\n")
            os.remove(t.path("notes/zlib.md"))
            os.symlink(target, t.path("notes/zlib.md"))
            out = self.lint_in_a_child(t)
            self.assertIn("paths notes/zlib.md: a symbolic link", out)
            self.assertNotIn("private-data notes/zlib.md", out)

    def test_a_lane_link_is_allowed_and_every_other_link_is_still_a_finding(self):
        """dev/stream/lane/ mirrors `cold/tools` on the lane VM path for path, links included, and the drift check
        compares a live path with its lane path directly, so flattening one breaks the mirror.  The rule stays
        everywhere else, because what it protects is a released tree and `oft release-tree` cuts this directory
        whole (496, round 5.2, R5-2).  One link of each kind: allowed, outside the lane, escaping the lane,
        dangling inside it, naming another link, and naming itself.

        The last two are a gap in the rule as first written rather than a slip in the code: "resolves inside
        lane/ and names a tracked file" is satisfied by a cycle, because a link is itself a tracked file, and a
        self-loop measured ALLOWED (the review of 669, N2).  The target must be a regular file.
        """
        from oft import release_tree
        self.assertTrue(any(lint.LINKS_ALLOWED.startswith(p) for p in lint.INTERNAL_ONLY), lint.LINKS_ALLOWED)
        self.assertTrue(any(lint.LINKS_ALLOWED.startswith(cut.rstrip("/") + "/") for cut in release_tree.INTERNAL),
                        lint.LINKS_ALLOWED)
        leaves = "a symbolic link whose target leaves %s or is no file of the index" % lint.LINKS_ALLOWED
        not_a_file = "a symbolic link whose target is not a regular file of %s" % lint.LINKS_ALLOWED
        for name, link, target, expected in (
                ("a lane link", "dev/stream/lane/tools/cb", "cb-90203d09.sh", None),
                ("outside the lane", "dev/stream/bin/ossv-cb", "../lane/tools/cb-90203d09.sh", "a symbolic link"),
                ("escaping the lane", "dev/stream/lane/tools/out", "../../bin/ossv-agent", leaves),
                ("dangling in the lane", "dev/stream/lane/tools/gone", "never-imported.sh", leaves),
                ("naming another link", "dev/stream/lane/tools/chain", "cb-link", not_a_file),
                ("naming itself", "dev/stream/lane/tools/loop", "loop", not_a_file)):
            with self.subTest(case=name), tree() as t:
                t.write("dev/stream/bin/ossv-agent", "#!/bin/sh\necho agent\n")
                t.write("dev/stream/lane/tools/cb-90203d09.sh", "#!/bin/sh\necho cb\n")
                os.symlink("cb-90203d09.sh", t.path("dev/stream/lane/tools/cb-link"))
                if link != "dev/stream/lane/tools/cb-link":
                    os.symlink(target, t.path(link))
                found = [f for f in t.lint() if f.rule == "paths" and f.where == link]
                self.assertEqual([f.msg for f in found], [] if expected is None else [expected],
                                 [str(f) for f in t.lint()])

    def test_dev_streams_own_checker_scopes_its_lints_to_the_same_lane(self):
        """The third application of the lane's one rule: dev/stream/'s own checker does not judge the lane's bytes
        with ruff or shellcheck either, for the reason the link and derived-file rules stop at it (the lane is
        internal, never released, and mirrors the box).  That checker runs on a box with no tools/ beside it, so it
        cannot import LINKS_ALLOWED; its LANE_MIRROR is named relative to dev/stream/, and this holds the two equal
        so that neither moves alone.  CI runs this test on a change under tools/ only, so its twin in
        dev/stream/tests/test_repo_checks.py asserts the same on a change under dev/stream/ (the review of 698, F1).
        A released tree carries no dev/stream/ (release_tree.INTERNAL)."""
        import ast
        checker = os.path.join(REPO, "dev", "stream", "src", "ossv", "tools_check.py")
        if not os.path.isfile(checker):
            self.skipTest("no dev/stream/ in this tree: a released tree cuts it")
        with open(checker, encoding="utf-8") as f:
            module = ast.parse(f.read())
        mirror = [node.value.value for node in module.body if isinstance(node, ast.Assign)
                  and [getattr(target, "id", None) for target in node.targets] == ["LANE_MIRROR"]]
        self.assertEqual(["dev/stream/" + name for name in mirror], [lint.LINKS_ALLOWED])
        self.assertEqual(lint.DERIVED_ALLOWED, lint.LINKS_ALLOWED)

    def test_a_link_under_another_cut_directory_is_still_a_finding(self):
        """`release_tree` lets the cut past a link inside any directory it removes whole, `tools/enroll/` among
        them, because nothing reads such a path and rmtree unlinks it.  This rule is the other question -- what
        may be committed -- and it allows links in `dev/stream/lane/` alone, so a link under `tools/enroll/`
        never reaches main for the cut to meet (the review of 669, (a))."""
        with tree() as t:
            t.write("tools/enroll/ci/entry.py", "VALUE = 1\n")
            os.symlink("entry.py", t.path("tools/enroll/ci/entry-link.py"))
            found = [f for f in t.lint() if f.rule == "paths" and f.where == "tools/enroll/ci/entry-link.py"]
            self.assertEqual([f.msg for f in found], ["a symbolic link"], [str(f) for f in t.lint()])

    def test_a_lane_derived_file_is_allowed_and_every_other_one_is_still_a_finding(self):
        """The same scope as the link rule, for the same reason (669, and the review of 672).

        dev/stream/lane/ mirrors `cold/tools` on the lane VM path for path, and the drift check of
        pull request 666 reports a file the box holds and the lane does not as held by no object,
        so leaving a live control out of the lane reopens the count rather than tidying it.
        `twin-controls/C_reac_ctrl_build_asLib.6df2c242679.glob` is such a control: the tracked
        README beside it names it as one of the two the twin test reads.  Everywhere else the rule
        stands, including every path a release can carry, and a `__pycache__` directory is a
        finding wherever it is -- the lane's own checker refuses it and `*.pyc` there as well.
        """
        from oft import release_tree

        self.assertTrue(any(lint.DERIVED_ALLOWED.startswith(p) for p in lint.INTERNAL_ONLY), lint.DERIVED_ALLOWED)
        self.assertTrue(any(lint.DERIVED_ALLOWED.startswith(cut.rstrip("/") + "/") for cut in release_tree.INTERNAL),
                        lint.DERIVED_ALLOWED)
        derived = "a derived file (.vo, .hex, .pyc, ...): these are never stored"
        for name, rel, expected in (
                ("the lane control", "dev/stream/lane/tools/twin-controls/C_x.6df2c242679.glob", None),
                ("a .vo in the lane", "dev/stream/lane/tools/twin-controls/C_x.vo", None),
                ("outside the lane", "dev/stream/bin/C_x.glob", derived),
                ("under tools/", "tools/enroll/ci/C_x.glob", derived),
                ("a cache directory in the lane", "dev/stream/lane/tools/__pycache__/x.pyc", derived)):
            with self.subTest(case=name), tree() as t:
                t.write(rel, "derived bytes\n")
                found = [f for f in t.lint() if f.rule == "paths" and f.where == rel]
                self.assertEqual([f.msg for f in found], [] if expected is None else [expected],
                                 [str(f) for f in t.lint()])

    def test_a_git_that_will_not_list_the_files_fails_the_lint_by_name(self):
        """An error must not become a permission, and it must not be an exit code either.

        `walk` ran `git ls-files` with `check=True`, so a git that would not answer ended `oft lint` with git's
        exit 128 and no message of this tool's -- and took with it the refusal in `_link_refusal` written for
        exactly that case, which could then never be reached through `oft lint`: a guard against an error
        becoming a permission that could not itself run (the review of 673).  `oft lint` now reports it.
        """
        with tempfile.TemporaryDirectory() as raw:
            self.assertIsNone(lint.index_files(raw))           # no .git: no index to disagree with
            with open(os.path.join(raw, ".git"), "w") as f:
                f.write("gitdir: /nowhere/at/all\n")
            self.assertIs(lint.index_files(raw), lint.INDEX_UNREADABLE)
            with self.assertRaises(lint.IndexUnreadable):
                lint.walk(raw)
            found = lint.run(raw)
            self.assertEqual([f.rule for f in found], ["paths"], [str(f) for f in found])
            self.assertIn("git could not list this checkout's files", found[0].msg)

    def test_a_git_that_refuses_with_nothing_on_stderr_still_says_so(self):
        """The fallback in that message could never appear, so the quiet case said nothing at all.

        `% (err or "no message")` tests the exception object, and an exception instance is always truthy, so
        a git that failed with an empty stderr printed `git could not list this checkout's files (), so
        nothing was examined` -- a message written to explain a failure, whose explanation was unreachable.
        """
        with tempfile.TemporaryDirectory() as raw, mock.patch.object(
            lint, "walk", side_effect=lint.IndexUnreadable("")
        ):
            found = lint.run(raw)
        self.assertEqual([f.rule for f in found], ["paths"], [str(f) for f in found])
        self.assertIn("no message", found[0].msg)

    def test_an_index_that_cannot_be_read_refuses_a_lane_link_rather_than_allowing_it(self):
        """The second line, for a git that fails after `walk` answered: the link rule's own refusal."""
        with tree() as t:
            t.write("dev/stream/lane/tools/cb-90203d09.sh", "#!/bin/sh\necho cb\n")
            link = "dev/stream/lane/tools/cb"
            os.symlink("cb-90203d09.sh", t.path(link))
            # the same link the rule allows when the index can be read
            self.assertIsNone(lint._link_refusal(t.path(link), link, {"dev/stream/lane/tools/cb-90203d09.sh"}))
            self.assertEqual(lint._link_refusal(t.path(link), link, lint.INDEX_UNREADABLE),
                             "a symbolic link whose target could not be checked against git's index")

    def test_a_link_to_a_fifo_or_a_fifo_never_blocks_lint(self):
        for kind in ("link", "fifo"):
            with self.subTest(kind=kind), tree() as t, tempfile.TemporaryDirectory() as outside:
                os.remove(t.path("notes/zlib.md"))
                fifo = os.path.join(outside, "fifo") if kind == "link" else t.path("notes/zlib.md")
                os.mkfifo(fifo)
                if kind == "link":
                    os.symlink(fifo, t.path("notes/zlib.md"))
                out = self.lint_in_a_child(t)
                self.assertIn("paths notes/zlib.md: %s" % ("a symbolic link" if kind == "link" else "not a regular file"),
                              out)

    def test_a_file_over_its_cap_is_reported_and_not_read_for_text(self):
        with tree() as t:
            t.write("notes/zlib.md", "see /" + "data/someone/x\n" + "x" * facts.MAX_BYTES)
            found = [str(f) for f in t.lint()]
            self.assertTrue(any(f.startswith("paths notes/zlib.md: ") and "cap" in f for f in found), found)
            self.assertFalse(any(f.startswith("private-data notes/zlib.md") for f in found), found)


class Changes(unittest.TestCase):
    FINDING = "findings/zlib/checksum_fuzzer/stand-in-abort"
    YAML = FINDING + "/finding.yaml"

    def test_a_finding_is_never_deleted_by_any_pull_request_kind(self):
        for kind in ("contributor", "maintainer", "release"):
            with self.subTest(kind=kind), tree() as t:
                add_findings(t)
                shutil.rmtree(t.path(self.FINDING))
                found = [str(f) for f in t.lint(changed=[self.YAML], pr_kind=kind)]
                self.assertIn("paths %s: a finding is never deleted: %s" % (self.YAML, self.YAML), found)

    def test_pruning_a_finding_with_an_agreeing_record_is_not_a_deletion(self):
        for kind in ("maintainer", "release"):
            with self.subTest(kind=kind), tree() as t:
                add_findings(t)
                y = t.yaml(self.YAML)
                y["state"] = "pruned"
                y["input"] = {b: dict(r) for b, r in y["control"].items()}
                t.put_yaml(self.YAML, y)
                t.write("findings/zlib/checksum_fuzzer/series", "")
                self.assertEqual([str(f) for f in t.lint(changed=[self.YAML], pr_kind=kind)], [])

    def test_unpatched_pins_are_not_deleted_while_the_base_has_a_finding(self):
        rel = "findings/zlib/unpatched.yaml"
        for kind in ("contributor", "maintainer", "release"):
            with self.subTest(kind=kind), tree() as base, tree() as t:
                add_findings(base)
                add_findings(t)
                os.remove(t.path(rel))
                found = [str(f) for f in t.lint(changed=[rel], pr_kind=kind, base=base.root)]
                self.assertIn("paths %s: a finding's unpatched pins are never deleted: %s" % (rel, rel), found)

    def test_a_finding_moved_away_is_deleted_though_the_diff_names_only_where_it_went(self):
        """A diff that detects renames lists a moved file only at its new path, so the base's ledger is walked."""
        moved = "findings/zlib/checksum_fuzzer/stand-in-abort.yaml"
        with tree() as base, tree() as t:
            add_findings(base)
            add_findings(t)
            os.rename(t.path(self.YAML), t.path(moved))
            found = [str(f) for f in t.lint(changed=[moved], pr_kind="maintainer", base=base.root)]
            self.assertIn("paths %s: a finding is never deleted: %s" % (self.YAML, self.YAML), found)

    def test_removing_a_whole_project_ledger_deletes_every_record_and_its_pins(self):
        with tree() as base, tree() as t:
            add_findings(base)
            base.write("findings/zlib/bin/zlib-unpatched-bin.tar.zst", "fetched, not tracked")
            found = [str(f) for f in t.lint(changed=[], pr_kind="release", base=base.root)]
            deleted = sorted(f.split(": ", 1)[0] for f in found if "never deleted" in f)
            self.assertEqual(deleted, ["paths findings/zlib/checksum_fuzzer/stand-in-abort/" + name for name in
                                       ("0001-stand-in.patch", "control.bin", "finding.yaml", "input.bin")]
                             + ["paths findings/zlib/unpatched.yaml"])

    def test_a_base_without_findings_judges_only_the_diff(self):
        with tree() as base, tree() as t:
            add_findings(t)
            self.assertEqual([str(f) for f in t.lint(changed=[self.YAML], pr_kind="maintainer", base=base.root)], [])

    def ledger_change(self, change, runner=None):
        """The findings of a maintainer change to the fixture's finding, judged against a base that has it.  runner:
        the proposed tree's images.runner, which only a release pull request changes."""
        with tree() as base, tree() as t:
            add_findings(base)
            add_findings(t)
            changed = change(t)
            if runner:
                y = t.yaml("release.yaml")
                y["images"]["runner"] = runner
                t.put_yaml("release.yaml", y)
                changed.append("release.yaml")
            kind = "release" if runner else "maintainer"
            return [str(f) for f in t.lint(changed=changed, pr_kind=kind, base=base.root)]

    def runs_changed(self, which_builds):
        return ["paths %s: a finding's recorded runs are never changed: %s %s" % (self.YAML, self.YAML, wb)
                for wb in which_builds]

    def test_a_recorded_input_is_never_rewritten(self):
        """The gate's case: the input replaced by the control, its runs copied, the finding marked pruned and its
        patch taken out of the series.  Every rule of the record passes; only the ledger refuses it."""
        rel = self.FINDING + "/input.bin"

        def rewrite(t):
            shutil.copyfile(t.path(self.FINDING, "control.bin"), t.path(rel))
            y = t.yaml(self.YAML)
            y["state"] = "pruned"
            y["input"] = {b: dict(r) for b, r in y["control"].items()}
            t.put_yaml(self.YAML, y)
            t.write("findings/zlib/checksum_fuzzer/series", "")
            return [rel, self.YAML, "findings/zlib/checksum_fuzzer/series"]
        self.assertEqual(self.ledger_change(rewrite), ["paths %s: a finding's input.bin is never changed: %s" % (rel, rel)]
                         + self.runs_changed(["input.asan", "input.asan-ubsan"]))

    def test_a_recorded_control_is_never_rewritten(self):
        rel = self.FINDING + "/control.bin"

        def rewrite(t):
            t.write(rel, "\0\0\0\0\0\0\nanother control\n")
            return [rel]
        self.assertEqual(self.ledger_change(rewrite),
                         ["paths %s: a finding's control.bin is never changed: %s" % (rel, rel)])

    def test_a_recorded_input_over_64_kib_is_never_rewritten(self):
        """The base comparison reads input.bin and control.bin up to the finding input cap, as the loader does, so a
        full-payload input is compared too."""
        for name in ("input.bin", "control.bin"):
            rel = self.FINDING + "/" + name
            long_input = b"\0\0\0\0\0\0" + b"x" * (64 << 10)
            with self.subTest(name=name), tree() as base, tree() as t:
                add_findings(base)
                add_findings(t)
                base.write(rel, long_input, "wb")
                t.write(rel, long_input, "wb")
                self.assertEqual([str(f) for f in t.lint(changed=[rel], pr_kind="maintainer", base=base.root)], [])
                t.write(rel, long_input[:-1] + b"y", "wb")
                self.assertEqual([str(f) for f in t.lint(changed=[rel], pr_kind="maintainer", base=base.root)],
                                 ["paths %s: a finding's %s is never changed: %s" % (rel, name, rel)])

    def test_the_statements_a_finding_shows_false_only_grow(self):
        """Narrowed to asan_agrees, with the asan-ubsan runs dropped beside it, the record meets every rule; the base
        narrowed the same way, the proposed tree's two statements are a stronger claim, which CI checks."""
        def narrow(t):
            y = t.yaml(self.YAML)
            y["statements"] = ["asan_agrees"]
            for runs in (y["input"], y["control"]):
                del runs["asan-ubsan"]
            t.put_yaml(self.YAML, y)
            return [self.YAML]
        self.assertEqual(self.ledger_change(narrow),
                         ["paths %s: a finding's statements only grow: %s no longer names asan_ubsan_agrees"
                          % (self.YAML, self.YAML)] + self.runs_changed(["input.asan-ubsan", "control.asan-ubsan"]))
        with tree() as base, tree() as t:
            add_findings(base)
            add_findings(t)
            narrow(base)
            self.assertEqual([str(f) for f in t.lint(changed=[self.YAML], pr_kind="maintainer", base=base.root)], [])

    def test_a_finding_never_returns_to_open(self):
        """For an enrolled project an open finding holds back only its statements, so setting a patched one back to
        open would release most of the hold while the pinned build still carries the patch."""
        def reopen(t):
            y = t.yaml(self.YAML)
            y["state"] = "open"
            t.put_yaml(self.YAML, y)
            t.write("findings/zlib/checksum_fuzzer/series", "")
            return [self.YAML, "findings/zlib/checksum_fuzzer/series"]
        self.assertEqual(self.ledger_change(reopen),
                         ["paths %s: a finding's state never returns to open: %s was patched" % (self.YAML, self.YAML)])

    def test_an_open_finding_may_move_on(self):
        with tree() as base, tree() as t:
            add_findings(base)
            add_findings(t)
            y = base.yaml(self.YAML)
            y["state"] = "open"
            base.put_yaml(self.YAML, y)
            base.write("findings/zlib/checksum_fuzzer/series", "")
            self.assertEqual([str(f) for f in t.lint(changed=[self.YAML], pr_kind="maintainer", base=base.root)], [])

    def test_the_unpatched_pins_of_a_harness_with_a_finding_never_change(self):
        rel = "findings/zlib/unpatched.yaml"

        def repin(t):
            y = t.yaml(rel)
            y["harnesses"]["checksum_fuzzer"]["asan"]["sha256"] = "8" * 64
            t.put_yaml(rel, y)
            return [rel]
        self.assertEqual(self.ledger_change(repin),
                         ["paths %s: a finding's unpatched pins are never changed: %s harnesses.checksum_fuzzer.asan"
                          % (rel, rel)])

    def test_a_pin_for_a_build_no_base_finding_ran_may_be_added_or_changed(self):
        """The base finding runs plain, asan and asan-ubsan, so only those pins are frozen."""
        rel = "findings/zlib/unpatched.yaml"
        with tree() as base, tree() as t:
            add_findings(base)
            add_findings(t)
            y = base.yaml(rel)
            del y["harnesses"]["checksum_fuzzer"]["ubsan"]
            base.put_yaml(rel, y)
            self.assertEqual([str(f) for f in t.lint(changed=[rel], pr_kind="maintainer", base=base.root)], [])
            y = t.yaml(rel)
            y["harnesses"]["checksum_fuzzer"]["ubsan"]["sha256"] = "9" * 64
            t.put_yaml(rel, y)
            self.assertEqual([str(f) for f in t.lint(changed=[rel], pr_kind="maintainer", base=base.root)], [])

    def prune(self, t):
        """The finding pruned with its input.bin kept, its input's runs those of its control."""
        y = t.yaml(self.YAML)
        y["state"] = "pruned"
        y["input"] = {b: dict(r) for b, r in y["control"].items()}
        t.put_yaml(self.YAML, y)
        t.write("findings/zlib/checksum_fuzzer/series", "")
        return [self.YAML, "findings/zlib/checksum_fuzzer/series"]

    def test_a_base_finding_s_runs_never_change_with_the_same_runner(self):
        """The adversarial gate's M2lin, judged by lint: the base has the finding and no asan or asan-ubsan pin; the
        change pins those builds to the fixed binaries and prunes the finding with its input kept.  The same prune
        where the base pins every build is refused too: the same binaries in the same runner give the same runs."""
        rel = "findings/zlib/unpatched.yaml"

        def prune_onto_fixed(t):
            u = t.yaml(rel)
            for b in ("asan", "asan-ubsan"):
                u["harnesses"]["checksum_fuzzer"][b]["sha256"] = "e" * 64
            t.put_yaml(rel, u)
            return self.prune(t) + [rel]
        with tree() as base, tree() as t:
            add_findings(base)
            add_findings(t)
            u = base.yaml(rel)
            for b in ("asan", "asan-ubsan"):
                del u["harnesses"]["checksum_fuzzer"][b]
            base.put_yaml(rel, u)
            found = [str(f) for f in t.lint(changed=prune_onto_fixed(t), pr_kind="maintainer", base=base.root)]
            self.assertEqual(found, self.runs_changed(["input.asan", "input.asan-ubsan"]))
        self.assertEqual(self.ledger_change(self.prune), self.runs_changed(["input.asan", "input.asan-ubsan"]))

    def test_a_new_runner_may_record_a_base_finding_s_runs_again(self):
        """The base is checked, so its runs are what its runner gave on its pins: a change that pins another runner
        image may record them again, or prune the finding, and CI's re-run in that runner checks the new runs."""
        runner = "ghcr.io/theorem-labs/oss-fuzz-theorems-runner@sha256:" + "3" * 64
        self.assertEqual(self.ledger_change(self.prune, runner=runner), [])

        def rerecord(t):
            """The new runner prints the control's stdout otherwise, on every build alike."""
            y = t.yaml(self.YAML)
            for run in y["control"].values():
                run["stdout_sha256"] = "0" * 64
            t.put_yaml(self.YAML, y)
            return [self.YAML]
        self.assertEqual(self.ledger_change(rerecord, runner=runner), [])

    def test_a_finding_s_state_summary_upstream_and_archive_may_change(self):
        """CI re-runs the record against inputs and binaries that stay fixed, so what it says of them may change."""
        def edit(t):
            y = t.yaml(self.YAML)
            y.update(state="reported", upstream="https://bugs.example.org/1", summary="A stand-in finding, reported.")
            t.put_yaml(self.YAML, y)
            u = t.yaml("findings/zlib/unpatched.yaml")
            u["asset"]["sha256"] = "5" * 64
            t.put_yaml("findings/zlib/unpatched.yaml", u)
            return [self.YAML, "findings/zlib/unpatched.yaml"]
        self.assertEqual(self.ledger_change(edit), [])


class Schemas(unittest.TestCase):
    def test_an_unknown_key(self):
        with tree() as t:
            t.write("projects/abseil-py/project.yaml", "colour: {shade: blue}\n", "a")
            self.assertIn("schema", rules_of(t.lint()))

    def test_a_repeated_key(self):
        with tree() as t:
            t.write("projects/abseil-py/project.yaml", "status: available\n", "a")
            self.assertTrue(any("duplicate key" in f.msg for f in t.lint()))

    def test_a_bad_digest(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["builds"]["plain"]["sha256"] = "77b4a5be"
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertIn("schema", rules_of(t.lint()))

    def test_a_statement_whose_name_its_fields_contradict(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["statements"]["asan_agrees"]["builds"] = ["plain", "ubsan"]
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertTrue(any("give the name ubsan_agrees" in f.msg for f in t.lint()))

    def test_the_exit_guard_fields(self):
        """failure_handlers, exit_reaches_guard and an exit_status that is any C int load; other values do not."""
        def schema_findings(**change):
            with tree() as t:
                y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
                y["failure_handlers"] = change.get("failure_handlers", "none")
                y["checks"].append({"kind": "algebraic", "strength": "full", "stops_with": "exit",
                                    "exit_status": change.get("exit_status", -1),
                                    "exit_reaches_guard": change.get("exit_reaches_guard", True), "live": True,
                                    "where": "source/checksum_fuzzer.c:17", "what": "An exit check."})
                t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
                # Only what the schema says of the three keys: what a value means for a statement is not this test's.
                keys = ("failure_handlers", "exit_reaches_guard", "exit_status")
                return [str(f) for f in t.lint() if f.rule == "schema" and any(k in f.msg for k in keys)]
        self.assertEqual(schema_findings(), [])
        for change in ({"exit_status": 256}, {"exit_status": -2147483648}, {"exit_status": 2147483647},
                       {"failure_handlers": "present"}, {"failure_handlers": "unknown"},
                       {"exit_reaches_guard": False}, {"exit_reaches_guard": "unknown"}):
            with self.subTest(change=change):
                self.assertEqual(schema_findings(**change), [])
        for change in ({"exit_status": 2147483648}, {"exit_status": -2147483649}, {"failure_handlers": "maybe"},
                       {"exit_reaches_guard": "maybe"}, {"exit_reaches_guard": "true"}):
            with self.subTest(change=change):
                self.assertNotEqual(schema_findings(**change), [])

    def test_a_second_pin_of_the_images_is_refused(self):
        # release.yaml's images: is the one place an image is pinned; toolchain/toolchain.lock repeated it until it was
        # removed, and the paths rule refuses it now, even when it agrees
        with tree() as t:
            img = t.yaml("release.yaml")["images"]
            t.write("toolchain/toolchain.lock", "checker=%s\nrunner=%s\n" % (img["checker"], img["runner"]))
            self.assertTrue(any(f.rule == "paths" and "toolchain/toolchain.lock" in str(f) for f in t.lint()))

    def test_a_project_builder_release_yaml_does_not_pin(self):
        with tree() as t:
            img = t.yaml("release.yaml")["images"]
            y = t.yaml("projects/json/project.yaml")
            self.assertEqual(y["build"]["builder"], img["builder"][0])
            self.assertEqual([f for f in t.lint() if f.rule == "schema"], [])
            y["build"]["builder"] = img["runner"]
            t.put_yaml("projects/json/project.yaml", y)
            found = [f for f in t.lint() if f.rule == "schema"]
            self.assertEqual([(f.where, f.msg) for f in found], [
                ("projects/json/project.yaml", "build.builder is not one of release.yaml's images.builder")])

    def test_counts_that_disagree_with_the_tree(self):
        with tree() as t:
            y = t.yaml("release.yaml")
            y["counts"]["binaries"] += 1
            t.put_yaml("release.yaml", y)
            self.assertIn("schema", rules_of(t.lint()))

    def test_a_witness_names_one_of_the_statements_builds(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["statements"]["ubsan_halts_may_fail"]["witness"]["build"] = "plain"
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertTrue(any("does not name" in f.msg for f in t.lint()))


class Namespace(unittest.TestCase):
    """release.yaml's `namespace` and `opam_stem` (OSSV-162): their forms, and the theory each harness.yaml states."""

    def test_rocq_must_be_the_name_the_namespace_gives(self):
        rel = "projects/zlib/checksum_fuzzer/harness.yaml"
        with tree(render=False) as t:
            rename_namespace(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            edit(t, rel, lambda y: y.update(rocq="OssFuzzTheorems.zlib.checksum_fuzzer"))
            self.assertIn("%s: rocq must be OSSVerify.zlib.checksum_fuzzer" % rel, errors(t))
            self.assertTrue(any(f.where == rel and f.msg == "rocq must be OSSVerify.zlib.checksum_fuzzer"
                                for f in t.lint()))

    def test_the_namespace_and_stem_patterns(self):
        """A namespace is a capital letter, then letters and digits; an opam stem is lower-case words of letters and
        digits joined by single dashes."""
        with tree(render=False) as t:
            rename_namespace(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(errors(t), [])
            saved = t.read("release.yaml")
            for key, value in (("namespace", "ossverify"), ("namespace", "OSS.Verify"), ("namespace", "OSS_Verify"),
                               ("opam_stem", "Oss"), ("opam_stem", "a--b"), ("opam_stem", "oss-verify-")):
                with self.subTest(key=key, value=value):
                    edit(t, "release.yaml", lambda r: r.update({key: value}))
                    self.assertTrue(any(e.startswith("release.yaml: release.%s: %r does not match" % (key, value))
                                        for e in errors(t)), errors(t))
                    t.write("release.yaml", saved)


class FactsPool(unittest.TestCase):
    def test_a_pool_loads_the_tree_a_serial_load_does_errors_in_the_same_order(self):
        with tree() as t:
            t.write("projects/zlib/checksum_fuzzer/harness.yaml", "statements: {a: 1}\nstatements: {}\n", "a")
            t.write("projects/zlib/project.yaml", "status: [unclosed\n", "a")
            os.makedirs(t.path("projects/nofacts"))
            serial = facts.load(t.root, jobs=1)
            with mock.patch.object(facts, "POOL_MIN_FILES", 0):
                pooled = facts.load(t.root, jobs=4)
            self.assertEqual(len(serial.errors), 2)
            self.assertEqual(pooled.errors, serial.errors)
            self.assertEqual(sorted(pooled.projects), sorted(serial.projects))


class PerFileScope(unittest.TestCase):
    """--changed-only BASE: the per-file text rules read only the files that differ from commit BASE, or every file
    when a file that every file's verdict reads differs from it; the rules over the whole tree run as they always do."""
    MAIL = "mail someone" + "@" + "example.com"
    HOST = "see /" + "data/someone/x"
    PER_FILE_RULES = ("private-data", "links", "proofs", "licence", "contract-literals")

    def commit(self, t):
        """Make t a git checkout of one commit, HEAD: the base that --changed-only compares with."""
        git = ["git", "-C", t.root, "-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false"]
        subprocess.run(git[:3] + ["init", "-q"], check=True)
        subprocess.run(git + ["add", "-A"], check=True)
        subprocess.run(git + ["commit", "-q", "-m", "base"], check=True)

    def changed_only(self, t, **kw):
        """t.lint(changed_only="HEAD", ...) as strings, and what it wrote on stderr."""
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            found = [str(f) for f in t.lint(changed_only="HEAD", **kw)]
        return found, err.getvalue()

    def test_a_pool_reports_what_one_process_reports_in_the_same_order(self):
        with tree() as t:
            t.write("notes/zlib.md", self.MAIL + "\n", "a")
            t.write("docs/x.md", self.HOST + "\n")
            t.write("proofs/zlib/checksum_fuzzer/lib/Table.v", "(* " + self.MAIL + " *)\nDefinition t := 0.\n")
            serial = [str(f) for f in t.lint(jobs=1)]
            pooled = [str(f) for f in t.lint(jobs=4)]
            self.assertEqual(len([f for f in serial if f.startswith("private-data")]), 3)
            self.assertEqual(pooled, serial)

    def test_findings_in_many_files_keep_their_order_across_the_pool(self):
        with tree() as t:
            t.write("notes/zlib.md", "mail someone" + "@" + "example.com; see https://example.org/x\n", "a")
            t.write("proofs/zlib/checksum_fuzzer/lib/Cheat.v", "Axiom cheat : False.\n")
            # findings in many files, so that they span many of the pool's workers
            for i in range(48):
                t.write("docs/mail-%02d.md" % i, "mail person%d" % i + "@" + "example.com\n")
            one = [str(f) for f in t.lint(jobs=1)]
            self.assertEqual(sorted({f.split()[0] for f in one}), ["links", "private-data", "proofs"])
            self.assertEqual(sum("docs/mail-" in f for f in one), 48)
            self.assertEqual([str(f) for f in t.lint(jobs=4)], one)

    def test_changed_only_scans_only_the_files_changed_since_base(self):
        with tree() as t:
            t.write("notes/zlib.md", self.MAIL + "\n", "a")   # in the base, unchanged since: a per-file finding
            t.write("docs/y.md", "nothing private\n")         # in the base, changed since
            self.commit(t)
            t.write("docs/x.md", self.HOST + "\n")            # added since the base
            t.write("docs/y.md", self.MAIL + "\n", "a")
            mail_line = t.read("notes/zlib.md").split("\n").index(self.MAIL) + 1
            private = lambda found: sorted(f.split()[1].rstrip(":") for f in found if f.startswith("private-data "))
            self.assertEqual(private(map(str, t.lint())),
                             ["docs/x.md:1", "docs/y.md:2", "notes/zlib.md:%d" % mail_line])
            only, err = self.changed_only(t)
            self.assertEqual(private(only), ["docs/x.md:1", "docs/y.md:2"])
            self.assertEqual(err, "")

    def test_a_deleted_file_is_not_read_and_its_exception_is_checked(self):
        """A file the change deletes has no text left to read; an exception for it is now unused, as a full lint
        reports."""
        with tree() as t:
            t.write("docs/old.md", self.HOST + "\n")
            t.put_yaml("tools/oft/lint-exceptions.yaml", {
                "schema": "oss-fuzz-theorems/lint-exceptions/1",
                "exceptions": [{"path": "docs/old.md", "rule": "private-data", "key": "0" * 16, "count": 1,
                                "reason": "a test"}]})
            self.commit(t)
            os.remove(t.path("docs/old.md"))
            whole = [str(f) for f in t.lint()]
            self.assertEqual(whole, ["paths tools/oft/lint-exceptions.yaml: an exception for private-data docs/old.md "
                                     "that is not used 1 time(s)"])
            self.assertEqual(self.changed_only(t), (whole, ""))

    def test_an_exception_for_an_unchanged_file_is_not_reported_unused(self):
        with tree() as t:
            t.write("docs/x.md", self.HOST + "\n")
            t.put_yaml("tools/oft/lint-exceptions.yaml", {
                "schema": "oss-fuzz-theorems/lint-exceptions/1",
                "exceptions": [{"path": "docs/x.md", "rule": "private-data", "key": "0" * 16, "count": 1,
                                "reason": "a test"}]})
            self.commit(t)
            t.write("docs/y.md", "nothing private\n")
            self.assertEqual(self.changed_only(t), ([], ""))
            t.write("docs/x.md", "nothing private either\n")     # the entry's file changed: it is read, and the
            only, _ = self.changed_only(t)                         # entry is reported as a full lint reports it
            self.assertEqual([f for f in only if "not used" in f], [f for f in map(str, t.lint()) if "not used" in f])
            self.assertEqual(len(only), 1)

    def test_an_entry_in_either_layout_is_checked_when_its_file_changes(self):
        """An entry names its file in either layout (layout.canonical), and the changed paths name it in theirs: once
        the file an entry in the per-project form clears changes in an old-layout tree, the entry is read again, and an
        unused one is reported as a full lint reports it."""
        rel = "proofs/zlib/checksum_fuzzer/provenance/port/projects/zlib/Dockerfile"
        with tree() as t:
            port_built(t, "zlib")
            self.assertEqual(t.generate(), 0, t.last_output)
            t.write(rel, "# Copyright " + self.MAIL + "\n")
            key = next(f.key for f in t.lint() if f.rule == "private-data")
            t.put_yaml("tools/oft/lint-exceptions.yaml", {
                "schema": "oss-fuzz-theorems/lint-exceptions/1",
                "exceptions": [{"path": layout.moved(rel), "rule": "private-data", "key": key, "count": 1,
                                "reason": "a test"}]})
            self.assertEqual([str(f) for f in t.lint()], [])
            self.commit(t)
            t.write(rel, "# Copyright the authors\n")
            whole = [str(f) for f in t.lint()]
            self.assertEqual(whole, ["paths tools/oft/lint-exceptions.yaml: an exception for private-data %s that is "
                                     "not used 1 time(s)" % layout.moved(rel)])
            self.assertEqual(self.changed_only(t), (whole, ""))

    def test_changed_only_reads_every_file_when_the_exceptions_change(self):
        """An entry removed from lint-exceptions.yaml leaves its finding in a file that did not change, and an entry
        added for a path that does not exist is unused: --changed-only reports what a full lint reports, and says
        why it read every file."""
        with tree() as t:
            rel = "projects/zlib/checksum_fuzzer/source/checksum_fuzzer.c"
            t.write(rel, "/* built in /" + "home/someone/zlib */\n", "a")
            key = [f for f in t.lint() if f.rule == "private-data"][0].key
            entry = {"path": rel, "rule": "private-data", "key": key, "count": 1, "reason": "a test"}
            t.put_yaml("tools/oft/lint-exceptions.yaml",
                       {"schema": "oss-fuzz-theorems/lint-exceptions/1", "exceptions": [entry]})
            self.commit(t)
            self.assertEqual(self.changed_only(t), ([], ""))
            t.put_yaml("tools/oft/lint-exceptions.yaml", {
                "schema": "oss-fuzz-theorems/lint-exceptions/1",
                "exceptions": [dict(entry, path="docs/gone.md")]})
            whole = [str(f) for f in t.lint()]
            self.assertEqual([f.split()[0] for f in whole], ["private-data", "paths"])
            only, err = self.changed_only(t)
            self.assertEqual(only, whole)
            self.assertEqual(err, "oft lint --changed-only: tools/oft/lint-exceptions.yaml changed, and the verdict on "
                                  "a file that did not change can depend on it: the per-file rules read every file\n")

    def test_changed_only_reads_every_file_when_a_fact_changes(self):
        """A link the facts record may be linked from any file: once zlib's homepage changes, an unchanged page
        that links to the old one has an unknown link."""
        with tree() as t:
            t.write("docs/x.md", "see https://www.zlib.net/\n")
            self.commit(t)
            y = t.yaml("projects/zlib/project.yaml")
            y["homepage"] = "https://zlib.example.org/"
            t.put_yaml("projects/zlib/project.yaml", y)
            whole = [str(f) for f in t.lint()]
            self.assertIn("docs/x.md:1:", [f.split()[1] for f in whole if f.startswith("links ")])
            only, err = self.changed_only(t)
            self.assertEqual(only, whole)
            self.assertIn("projects/zlib/project.yaml changed", err)

    def held_internal_port(self, t):
        """The fixture with its finding, which holds zlib back, and zlib built from the port's internal copy: its
        project.yaml may name that copy."""
        add_findings(t)
        p = t.yaml("projects/zlib/project.yaml")
        p["build"]["oss_verify"] = {"repository": INTERNAL, "commit": "d" * 40, "path": "projects/zlib"}
        p["assets"]["port"] = {"release": "v2026.11.0", "file": "zlib-port.tar.zst", "bytes": 1000,
                               "sha256": "9" * 64}
        t.put_yaml("projects/zlib/project.yaml", p)

    def test_changed_only_reads_every_file_again_when_a_finding_changes(self):
        """Which project.yaml may name the port's internal copy follows from the findings: once zlib's finding is public,
        zlib is not held back, and --changed-only reads its unchanged project.yaml again and finds what a full lint
        finds."""
        rel = "findings/zlib/checksum_fuzzer/stand-in-abort/finding.yaml"
        with tree() as t:
            self.held_internal_port(t)
            self.commit(t)
            y = t.yaml(rel)
            y.update(state="public", upstream="https://bugs.example.org/1")
            t.put_yaml(rel, y)
            private = lambda found: sorted(f.split()[1].split(":")[0] for f in found if f.startswith("private-data "))
            whole = [str(f) for f in t.lint()]
            self.assertEqual(private(whole), ["projects/zlib/project.yaml"])
            only, err = self.changed_only(t)
            self.assertEqual(private(only), private(whole))
            self.assertIn(rel + " changed", err)

    def test_a_pool_lets_a_held_project_name_the_internal_port(self):
        with tree() as t:
            self.held_internal_port(t)
            serial = [str(f) for f in t.lint(jobs=1)]
            pooled = [str(f) for f in t.lint(jobs=4)]
            self.assertEqual([f for f in serial if f.startswith("private-data")], [])
            self.assertEqual(pooled, serial)

    def test_the_rules_over_the_whole_tree_still_run(self):
        """A stray path, a schema error and a contributor's change outside its paths, none of them in a file the
        change touches, are found as a full lint finds them."""
        with tree() as t:
            t.write("stray.txt", "x\n")
            t.write("projects/abseil-py/project.yaml", "colour: {shade: blue}\n", "a")
            t.write("notes/zlib.md", self.MAIL + "\n", "a")
            self.commit(t)
            t.write("docs/x.md", "nothing private\n")
            kw = dict(changed=["tools/oft/lint.py", "docs/x.md"], pr_kind="contributor")
            whole = [str(f) for f in t.lint(**kw)]
            only, err = self.changed_only(t, **kw)
            self.assertLessEqual({"paths", "private-data", "schema"}, {f.split()[0] for f in whole}, whole)
            self.assertEqual(only, [f for f in whole if f.split()[0] not in self.PER_FILE_RULES])
            self.assertTrue(any("stray.txt" in f for f in only), only)
            self.assertEqual(err, "")

    def test_changed_only_needs_a_base_git_can_read(self):
        from oft import __main__ as cli
        with tree() as t:
            err = io.StringIO()
            with contextlib.redirect_stderr(err), self.assertRaises(SystemExit) as e:
                cli.main(["--root", t.root, "lint", "--changed-only"])
            self.assertEqual(e.exception.code, 2)
            self.assertIn("argument --changed-only: expected one argument", err.getvalue())
            t.write("notes/zlib.md", self.MAIL + "\n", "a")
            self.commit(t)
            git = ["git", "-C", t.root, "-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false"]
            subprocess.run(git + ["commit", "-q", "--allow-empty", "-m", "change"], check=True)
            # a commit the checkout does not have, a word that names a directory of the tree (git would read it as
            # a path and compare the index with the work tree: an empty change), a tree rather than a commit, and
            # an option: each an error, never an empty change
            for bad in ("no-such-commit", "notes", "HEAD^{tree}", "--output=x"):
                with self.subTest(base=bad):
                    self.assertRaisesRegex(lint.ChangedOnlyError, "names no commit", t.lint, changed_only=bad)
            self.assertFalse(os.path.exists(t.path("x")))
            with contextlib.redirect_stdout(io.StringIO()) as out:
                self.assertEqual(cli.main(["--root", t.root, "lint", "--changed-only", "notes"]), 1)
            self.assertEqual(out.getvalue(), "FAIL oft lint --changed-only: 'notes' names no commit of %s\n" % t.root)
            # a revision that names a commit, by any spelling, works
            sha = subprocess.run(git[:3] + ["rev-parse", "HEAD~1"], capture_output=True, text=True).stdout.strip()
            for good in ("HEAD", "HEAD~1", sha):
                with self.subTest(base=good), contextlib.redirect_stderr(io.StringIO()) as err:
                    self.assertEqual([str(f) for f in t.lint(changed_only=good)], [])
                    self.assertEqual(err.getvalue(), "")

    def test_changed_only_refuses_a_root_below_the_checkout_top(self):
        """git names the changed paths from the checkout's top, walk names them from root: below the top no tracked
        change would match, so lint stops rather than read nothing."""
        from oft import __main__ as cli
        with tree() as t:
            parent = os.path.dirname(t.root)
            git = ["git", "-C", parent, "-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false"]
            subprocess.run(git[:3] + ["init", "-q"], check=True)
            subprocess.run(git + ["add", "-A"], check=True)
            subprocess.run(git + ["commit", "-q", "-m", "base"], check=True)
            t.write("notes/zlib.md", self.MAIL + "\n", "a")
            self.assertIn("private-data", [f.rule for f in t.lint()])
            self.assertRaisesRegex(lint.ChangedOnlyError, "is not the top of a git checkout", t.lint,
                                   changed_only="HEAD")
            with contextlib.redirect_stdout(io.StringIO()) as out:
                self.assertEqual(cli.main(["--root", t.root, "lint", "--changed-only", "HEAD"]), 1)
            self.assertIn("FAIL oft lint --changed-only: %s is not the top of a git checkout" % t.root, out.getvalue())
        with tree() as t:   # no checkout at all
            self.assertRaisesRegex(lint.ChangedOnlyError, "is not the top of a git checkout", t.lint,
                                   changed_only="HEAD")

    def test_changed_only_reads_every_file_when_the_running_tools_change(self):
        """A local ./oft lint runs the tree's own tools: a change to them (a stricter rule, a new phrase) can change
        the verdict on a file that did not change, so every file is read.  CI runs the base's tools, outside the tree,
        and a change under tools/ is then just a changed file."""
        with tree() as t:
            t.write("notes/zlib.md", self.MAIL + "\n", "a")   # in the base, unchanged since: a per-file finding
            self.commit(t)
            t.write("tools/oft/rules_extra.py", "RULE = 1\n")
            private = lambda found: [f for f in found if f.startswith("private-data notes/zlib.md:")]
            only, err = self.changed_only(t)                    # the running tools are outside the tree
            self.assertEqual((private(only), err), ([], ""))
            self.assertIsNone(lint.running_tools(t.root))
            with mock.patch.object(lint, "HERE", t.path("tools", "oft")):
                self.assertEqual(lint.running_tools(t.root), "tools/oft")
                only, err = self.changed_only(t)
                self.assertEqual(private(only), private(map(str, t.lint())))
                self.assertEqual(len(private(only)), 1)
                self.assertIn("tools/oft/rules_extra.py changed", err)
            with mock.patch.object(lint, "HERE", t.root):         # tools at the top: any change is a change to them
                self.assertEqual(lint.running_tools(t.root), ".")
                only, err = self.changed_only(t)
                self.assertEqual(len(private(only)), 1)

    def test_changed_only_reads_every_file_when_gitattributes_changes(self):
        """A .gitattributes (at the top or in a directory) changes the bytes git checks out for a file whose blob did
        not change (line ends, encoding), so a change to one reads every file."""
        for rel in (".gitattributes", "docs/.gitattributes"):
            with self.subTest(rel=rel), tree() as t:
                t.write("notes/zlib.md", self.MAIL + "\n", "a")
                self.commit(t)
                t.write(rel, "*.md text\n")
                only, err = self.changed_only(t)
                self.assertTrue(any(f.startswith("private-data notes/zlib.md:") for f in only), only)
                self.assertIn(rel + " changed", err)

    def test_changed_only_reads_every_contract_when_a_symbol_fact_changes(self):
        """A contract file's verdict reads its fuzz target's symbol facts (contract-literals): a change to one that
        drops a name the contract uses makes the unchanged contract a finding."""
        with tree() as t:
            put_contract_fact(t)
            t.write(CONTRACT, CONTRACT_HEAD + "Definition A : Z := Symbols.Plain.s_pcap_source_next.\n")
            t.generate()
            self.commit(t)
            put_contract_fact(t, [r for r in CONTRACT_FACT if r[0] != "pcap_source_next"])
            only, err = self.changed_only(t)
            self.assertIn("contract-literals %s:3: plain has no symbol s_pcap_source_next" % CONTRACT, only)
            self.assertIn(layout.symbol_fact("zlib", "checksum_fuzzer", "plain") + " changed", err)

    def test_changed_only_reads_changelog_md_alone_when_it_alone_changes(self):
        """CHANGELOG.md is a fact no other file's verdict reads (the inventory below says why): a change to it alone
        has the per-file rules read it and no other file, and a finding in it is still found."""
        with tree() as t:
            t.write("notes/zlib.md", self.MAIL + "\n", "a")   # unchanged since the base: a per-file finding
            t.write("CHANGELOG.md", "# Changelog\n")
            self.commit(t)
            t.write("CHANGELOG.md", "# Changelog\n\nA line.\n")
            self.assertEqual(self.changed_only(t), ([], ""))
            t.write("CHANGELOG.md", "# Changelog\n\n%s\n" % self.HOST)
            only, err = self.changed_only(t)
            self.assertEqual([(f.split()[0], f.split()[1].rstrip(":")) for f in only],
                             [("private-data", "CHANGELOG.md:3")], only)
            self.assertEqual(err, "")

    # The fact files outside the margin (read_by_every_verdict), each with the reason no per-file verdict on another
    # file reads it: files facts.load parses, by paths.py's pattern, beyond the ones paths.py classes "facts", and
    # CHANGELOG.md, the one file paths.py classes "facts" that the margin leaves out.  A file a per-file rule reads
    # for another file's verdict must be inside the margin instead.
    # This is a reviewed inventory, not a detector: it is written by hand against the rules as they read today, so
    # it holds a new rule's author to naming the file it reads here.  It cannot see a new rule read one by itself.
    FACTS_OUTSIDE_THE_MARGIN = {
        "approvals.yaml": "which proofs a release publishes: no per-file rule reads it",
        "findings/{project}/unpatched.yaml": "the findings ledger: check_paths reads it over the whole tree, so a "
                                             "change to it is judged there, every run",
        "findings/{project}/{harness}/series": "the ledger's series: the same whole-tree rule",
        "proofs/{project}/{harness}/{statement}/proof.yaml": "a proof's own pins: rules.check reads them over the "
                                                             "whole tree",
        "counterexamples/{project}/{harness}/{statement}/expect.yaml": "a counterexample's own outcome: the same",
        "CHANGELOG.md": "the release notes: no rule reads them for a verdict on another file (fact_urls reads "
                        "projects, harnesses and findings; facts.load does not parse it; release_tree reads it only "
                        "as a file the cut keeps), so a change to it is judged in itself",
    }
    FACT_FILES = (["findings/{project}/{harness}/*/finding.yaml",
                   "proofs/{project}/{harness}/provenance/PROVENANCE.yaml",
                   "projects/{project}/{harness}/proofs/provenance/PROVENANCE.yaml"] + list(FACTS_OUTSIDE_THE_MARGIN))

    def test_the_margin_matches_the_reviewed_inventory_of_facts(self):
        """read_by_every_verdict is a margin over the files a per-file verdict reads.  Nothing derives it from the
        facts, so this test pins it to the inventory above: every file facts.load parses is inside the margin or
        carries its reason there.  It fails when the margin and the inventory disagree, not when a rule starts to read
        a new file; that stays the reviewer's question for any change to scan_file, fact_urls or apply_exceptions."""
        facts_classed = [p for cls, p in paths.TABLE if cls == "facts"]
        patterns = facts_classed + [p for p in self.FACT_FILES if p not in facts_classed]
        self.assertIn("projects/{project}/{harness}/harness.yaml", patterns)
        for pattern in patterns:
            rel = (pattern.replace("{project}", "zlib").replace("{harness}", "api-driver")
                   .replace("{statement}", "s1").replace("**", "x").replace("*", "x"))
            with self.subTest(pattern=pattern):
                inside = lint.read_by_every_verdict(rel)
                if pattern in self.FACTS_OUTSIDE_THE_MARGIN:
                    self.assertFalse(inside, "%s is inside the margin now: drop its row" % pattern)
                else:
                    self.assertTrue(inside, "%s is a fact a verdict could read and the margin misses: cover it in "
                                            "read_by_every_verdict, or give it a row with its reason" % pattern)

    def lint_step(self, into="refs/heads/main", routed="true", event="pull_request",
                  kind="maintainer", changed=(), planned="base", rc=(0, 0), main=None):
        """pr.yml's lint step, run as the workflow runs it for a change into the branch whose full ref is `into`, with
        the base step's `routed`, the plan job's answer `planned`, and a python that exits as `rc` says for the base's
        run and the change's own: (the step's exit status, its lint runs, each as [PYTHONPATH, ...the arguments]).
        main: the text of the base's tools/oft/__main__.py (default: this one's)."""
        jobs = pr_yml_jobs(self)
        step = next(s for s in jobs["lint"]["steps"] if s.get("name") == "lint, by the base's rules")
        with tempfile.TemporaryDirectory() as d:
            os.makedirs(os.path.join(d, "base", "tools", "oft"))
            shutil.copy(os.path.join(REPO, "tools", "oft", "__main__.py"), os.path.join(d, "base", "tools", "oft"))
            if main is not None:
                with open(os.path.join(d, "base", "tools", "oft", "__main__.py"), "w") as f:
                    f.write(main)
            os.makedirs(os.path.join(d, "head"))
            open(os.path.join(d, "head", "release.yaml"), "w").close()
            with open(os.path.join(d, "changed.txt"), "w") as f:
                f.write("".join(p + "\n" for p in changed))
            os.mkdir(os.path.join(d, "bin"))
            with open(os.path.join(d, "bin", "python"), "w") as f:
                f.write("#!/bin/sh\ncase \"$PYTHONPATH\" in base/tools) rc=%d ;; *) rc=%d ;; esac\n"
                        'printf "%%s\\n" "$PYTHONPATH" "$@" >> "%s"\nprintf "\\0" >> "%s"\nexit "$rc"\n'
                        % (rc[0], rc[1], os.path.join(d, "args"), os.path.join(d, "args")))
            os.chmod(os.path.join(d, "bin", "python"), 0o755)
            env = dict(os.environ, PATH=os.path.join(d, "bin") + os.pathsep + os.environ["PATH"], RUNNER_TEMP=d,
                       GITHUB_WORKSPACE=d, GITHUB_STEP_SUMMARY=os.path.join(d, "summary.md"), ROUTED=routed,
                       GITHUB_EVENT_NAME=event, BASE="b" * 40, INTO=into, KIND=kind, PLANNED_TOOLS=planned,
                       SINCE="")   # no record of a last passing lint (test_workflow_verdicts.LintRecordTest)
            done = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", step["run"]], cwd=d,
                                  env=env, capture_output=True, text=True)
            runs = []
            if os.path.exists(os.path.join(d, "args")):
                with open(os.path.join(d, "args")) as f:
                    runs = [r.split("\n")[:-1] for r in f.read().split("\0")[:-1]]
            return done.returncode, runs

    def test_pr_yml_lints_changed_files_only_for_a_routed_change(self):
        """A routed change, into main or into any other branch (a pull request stacked on another, or into a lane's
        branch), a pull request, a merge queue group or a push alike, lints its changed files only: each is judged on
        its own change, and an unchanged file keeps its verdict at the base.  The gate into main is unchanged: a branch
        reaches main only through a pull request into main, whose own lint reads every file that differs from main.
        A push the base step could not route (no base to compare with) has no base to take verdicts from: it lints
        every file."""
        for event in ("pull_request", "merge_group", "push"):
            with self.subTest(event=event):
                self.assertEqual(self.lint_step("refs/heads/main", event=event)[1][0][-2:],
                                 ["--changed-only", "b" * 40])
        for into in ("refs/heads/mcsl/s1", "refs/heads/main-old", "refs/heads/refs/heads/main", "main"):
            with self.subTest(into=into):
                self.assertEqual(self.lint_step(into, "true", "pull_request")[1][0][-2:],
                                 ["--changed-only", "b" * 40])
        for routed in ("false", ""):
            with self.subTest(routed=routed):
                self.assertNotIn("--changed-only", self.lint_step("refs/heads/main", routed, "push")[1][0])

    def test_pr_yml_names_the_branch_each_event_goes_into(self):
        """INTO, which the lint record steps compare with a record and write into one, is spelled as a full ref for
        every event: a pull request's base branch name with refs/heads/ before it, a merge queue's base_ref, and the
        ref pushed.  This pins the expression's text; GitHub's own evaluation of it is seen only in a run (the pull
        request's proof)."""
        step = next(s for s in pr_yml_jobs(self)["lint"]["steps"] if s.get("id") == "lint_record")
        into = " ".join(step["env"]["INTO"].split())
        self.assertEqual(into, "${{ github.event_name == 'pull_request' && format('refs/heads/{0}', "
                               "github.event.pull_request.base.ref) || github.event_name == 'merge_group' && "
                               "github.event.merge_group.base_ref || github.ref }}")

    def test_pr_yml_hands_the_base_step_s_routing_to_every_step_that_reads_it(self):
        """ROUTED reaches each step that reads it from its own job's base step."""
        jobs = pr_yml_jobs(self)
        for job, step_key in (("plan", "plan"), ("plan", "reach"),
                              ("lint", "the findings ledger over the change's history, by the base's rules"),
                              ("lint", "lint, by the base's rules")):
            step = next(s for s in jobs[job]["steps"] if step_key in (s.get("id"), s.get("name")))
            with self.subTest(job=job, step=step_key):
                self.assertEqual(step["env"]["ROUTED"], "${{ steps.base.outputs.routed }}")
                self.assertIn("$ROUTED", step["run"])

    # the change the plan job answered `head` for: its facts are unreadable to the base's tools and readable to its
    # own, the one change the base's rules cannot give a verdict on
    JOIN = dict(kind="release", changed=["tools/oft/lint.py", "projects/zlib/project.yaml"], planned="head")

    def test_the_change_the_plan_job_named_is_judged_by_its_own_tools(self):
        """Both runs happen, in that order, and the change's own tools lint every file (no --changed-only)."""
        rc, runs = self.lint_step(**self.JOIN)
        self.assertEqual(rc, 0)
        self.assertEqual([r[0] for r in runs], ["base/tools", "head/tools"])
        self.assertEqual([r[1:5] for r in runs], [["-m", "oft", "--root", "head"]] * 2)
        self.assertNotIn("--changed-only", runs[1])
        self.assertIn("--pr-kind", runs[1])

    def test_the_base_s_status_is_reported_and_the_change_s_own_decides(self):
        """Each run's status on its own: the base's does not fail the step, and the change's own does."""
        self.assertEqual(self.lint_step(rc=(1, 0), **self.JOIN)[0], 0)
        self.assertEqual(self.lint_step(rc=(0, 1), **self.JOIN)[0], 1)
        self.assertEqual(self.lint_step(rc=(1, 1), **self.JOIN)[0], 1)
        rc, runs = self.lint_step(event="merge_group", **self.JOIN)
        self.assertEqual(([r[0] for r in runs], rc), (["base/tools", "head/tools"], 0))

    def test_every_other_change_is_judged_by_the_base_s_rules_alone(self):
        """One run, the base's, and its status is the step's, wherever the plan job did not answer `head`: a release
        change of the tools whose facts the base's tools read, and anything the plan job leaves alone."""
        for why, kw in (("the plan job answered base", dict(self.JOIN, planned="base")),
                        ("no answer at all", dict(self.JOIN, planned="")),
                        ("a maintainer's", dict(self.JOIN, kind="maintainer", planned="base")),
                        ("a contributor's", dict(self.JOIN, kind="contributor", planned="base"))):
            with self.subTest(why=why):
                rc, runs = self.lint_step(**kw)
                self.assertEqual(([r[0] for r in runs], rc), (["base/tools"], 0))
                self.assertEqual(self.lint_step(rc=(1, 0), **kw)[0], 1)

    def test_pr_yml_always_passes_the_base_checkout_as_the_pending_base(self):
        """The licence-pending entries a pull request may keep are the base commit's, which lint reads through git
        from the sparse checkout of the base (--pending-base), whatever the event; tools older than the flag get
        none.  The change's own tools, when the plan names them, read the tree's own entries, as the tests job's
        whole-tree lint does: their run takes no --pending-base."""
        for event, into in (("pull_request", "refs/heads/main"), ("pull_request", "refs/heads/ossv/candidates"),
                            ("push", "refs/heads/main"), ("merge_group", "refs/heads/main")):
            with self.subTest(event=event, into=into):
                args = self.lint_step(into, event=event)[1][0]
                self.assertIn("--pending-base", args)
                self.assertEqual(os.path.basename(args[args.index("--pending-base") + 1]), "base")
        old = 'li.add_argument("--changed-only")\n'
        self.assertNotIn("--pending-base", self.lint_step("refs/heads/ossv/candidates", main=old)[1][0])
        rc, runs = self.lint_step(**self.JOIN)
        self.assertEqual(([r[0] for r in runs], rc), (["base/tools", "head/tools"], 0))
        self.assertIn("--pending-base", runs[0])
        self.assertNotIn("--pending-base", runs[1])

    def test_the_command_reads_changed_only(self):
        from oft import __main__ as cli
        with tree() as t:
            t.write("notes/zlib.md", self.MAIL + "\n", "a")   # unchanged since the base
            self.commit(t)
            with contextlib.redirect_stdout(io.StringIO()) as out:
                self.assertEqual(cli.main(["--root", t.root, "lint"]), 1, out.getvalue())
            with contextlib.redirect_stdout(io.StringIO()) as out:
                self.assertEqual(cli.main(["--root", t.root, "lint", "--changed-only", "HEAD"]), 0, out.getvalue())

    def test_jobs_takes_one_or_more(self):
        from oft import __main__ as cli
        with tree() as t:
            for jobs in ("0", "-1", "x"):
                with self.subTest(jobs=jobs):
                    err = io.StringIO()
                    with contextlib.redirect_stderr(err), self.assertRaises(SystemExit) as e:
                        cli.main(["--root", t.root, "lint", "--jobs", jobs])
                    self.assertEqual(e.exception.code, 2)
                    self.assertIn("argument --jobs: %r is not a number of processes (1 or more)" % jobs, err.getvalue())
            with contextlib.redirect_stdout(io.StringIO()) as out:
                self.assertEqual(cli.main(["--root", t.root, "lint", "--jobs", "1"]), 0, out.getvalue())

class PrivateData(unittest.TestCase):
    def check(self, text, path="notes/zlib.md"):
        with tree() as t:
            t.write(path, text, "a")
            return [f for f in t.lint() if f.rule == "private-data"]

    def test_a_host_path(self):
        self.assertEqual(len(self.check("see /" + "data/someone/x\n")), 1)

    def test_a_path_on_a_data_disk_of_our_machines(self):
        """/mnt/disks/ and /mnt/nvme/ name a machine's disk, in a module the release ships too."""
        for path in ("/" + "mnt/nvme/someone/compute-inventory.csv", "/" + "mnt/disks/someone/x"):
            with self.subTest(path=path):
                self.assertEqual([f.msg for f in self.check("see %s\n" % path, "tools/oft/notes.py")],
                                 ["a host path"])
        self.assertEqual(self.check("see /" + "mnt/cdrom/x\n"), [])

    def test_a_change_ledger_names_the_host_paths_of_its_inputs(self):
        """A change ledger records where its logs and inputs are on the machine that summed it, and the release
        removes changes/; a token there is still a finding."""
        path = "changes/c/checks.tsv"
        self.assertEqual(self.check("implement\t/" + "mnt/nvme/someone/run.log\n", path), [])
        self.assertEqual(self.check("implement\t/" + "home/someone/run.log\n", path), [])
        self.assertEqual([f.msg for f in self.check("ghp_" + "a" * 36 + "\n", path)], ["an access token"])

    def test_the_caller_says_when_a_change_ledger_keeps_host_paths(self):
        """scan_file gives scan_shapes host_paths=False for changes/, rather than scan_shapes deciding from where."""
        text = "see /" + "mnt/nvme/someone/run.log\n"
        self.assertEqual(lint.scan_shapes(text, "changes/c/checks.tsv", host_paths=False), [])
        self.assertEqual([f.msg for f in lint.scan_shapes(text, "changes/c/checks.tsv")], ["a host path"])

    def test_a_private_address(self):
        self.assertEqual(len(self.check("host " + ".".join(["10", "1", "2", "3"]) + "\n")), 1)

    def test_a_shared_address_space_address(self):
        address = ".".join(("100", "88", "1", "2"))
        self.assertEqual(len(self.check("host " + address + "\n")), 1)
        self.assertEqual(self.check("version 100.1.2\n"), [])

    def test_an_email_address(self):
        self.assertEqual(len(self.check("mail someone" + "@" + "example.com\n")), 1)

    def test_a_numeric_reference_too_long_for_any_code_point_is_read_as_text(self):
        """html.unescape reads a decimal reference with
        int(), which refuses more than 4,300 digits, so one such line stopped `oft lint`; and
        leading zeros count too.  urls.unescape, which the private-data and link rules read references
        with, leaves a reference too long for any code point as it is, reads one padded with zeros without them, and
        reads every other one as html.unescape does."""
        huge, padded = "&#" + "9" * 4400 + ";", "&#" + "0" * 5000 + "65;"
        for text in (huge + "\n", "[a](https://example.org/%s)\n" % huge, '<a href="%s">a</a>\n' % huge,
                     "&#38;#" + "9" * 4400 + ";\n", padded + "\n", "&#x" + "0" * 5000 + "41;\n",
                     "[a](https://example.org/%s)\n" % padded):
            with self.subTest(text=text[:20]):
                self.assertEqual(self.check(text), [])
        self.assertEqual(urls.unescape(huge), huge)
        self.assertEqual(urls.unescape(padded), "A")
        same = "&amp; &#65; &#x42; &ampx &#128; &#0; &#x110000; &notit; &#0000000000067; &#65 &#x42"
        self.assertEqual(urls.unescape(same), html.unescape(same))

    def test_an_address_shape_inside_a_proof_string_is_payload(self):
        at = "x" + "@" + "y.zz"
        lib = "proofs/zlib/checksum_fuzzer/lib/Table.v"
        self.assertEqual(self.check('Definition t : PrimString.string := "#$%s#$".\n' % at, lib), [])
        self.assertEqual(len(self.check("(* mail %s *)\nDefinition t := 0.\n" % at, lib)), 1)
        self.assertEqual(len(self.check('Definition t := "/' + 'data/someone/x".\n', lib)), 1)

    def test_a_private_key(self):
        self.assertEqual(len(self.check("-----BEGIN RSA " + "PRIVATE KEY-----\n")), 1)

    def test_an_access_token(self):
        self.assertEqual(len(self.check("ghp" + "_" + "A" * 36 + "\n")), 1)

    def test_a_pinned_copy_is_verbatim_only_while_its_bytes_are_the_pinned_ones(self):
        path = "LICENSES/anthropic-proofs-NOTICE"
        text = "Contact someone" + "@" + "example.com; see https://example.org/x\n"
        pin = {path: hashlib.sha256(text.encode()).hexdigest()}
        with mock.patch.dict(lint.PINNED_VERBATIM, pin), tree() as t:
            t.write(path, text)
            self.assertEqual([str(f) for f in t.lint() if f.rule in ("private-data", "links")], [])
            t.write(path, text.replace("x\n", "y\n"))
            self.assertEqual(sorted(f.rule for f in t.lint() if f.rule in ("private-data", "links")),
                             ["links", "private-data"])

    def test_container_home_is_not_a_host(self):
        self.assertEqual(self.check("WORKDIR /home/opam\n"), [])

    def test_upstream_copies_keep_their_authors_addresses(self):
        mail = "/* by someone" + "@" + "example.com */\n"
        self.assertEqual(self.check(mail, "projects/zlib/checksum_fuzzer/source/checksum_fuzzer.c"), [])
        self.assertTrue(lint.verbatim("projects/zlib/checksum_fuzzer/source/x.c"))
        self.assertFalse(lint.verbatim("projects/zlib/api-driver/source/driver.c"))

    def test_an_exception_clears_one_finding_in_an_upstream_copy(self):
        with tree() as t:
            rel = "projects/zlib/checksum_fuzzer/source/checksum_fuzzer.c"
            t.write(rel, "/* built in /" + "home/someone/zlib */\n", "a")
            found = [f for f in t.lint() if f.rule == "private-data"]
            self.assertEqual(len(found), 1)
            t.put_yaml("tools/oft/lint-exceptions.yaml", {
                "schema": "oss-fuzz-theorems/lint-exceptions/1",
                "exceptions": [{"path": rel, "rule": "private-data", "key": found[0].key, "count": 1,
                                "reason": "a test"}]})
            self.assertEqual(t.lint(), [])

    def test_a_text_file_that_is_not_utf8_is_read(self):
        rel = "docs/x.md"
        text = b"\xa9 notes\n\nhttps:" + b"//buildbox-7/x\n\nsee /theorem-labs/" + b"agent-infra\n"
        with tree() as t:
            t.write(rel, "", "a")
            with open(t.path(rel), "wb") as out:
                out.write(text)
            found = {(f.rule, f.where) for f in t.lint() if f.where.startswith(rel + ":")}
        self.assertEqual(found, {("links", rel + ":3"), ("private-data", rel + ":5")})

    def test_the_internal_port_name_is_allowed_only_in_a_held_project_field(self):
        with tree() as t:
            t.write("notes/zlib.md", INTERNAL + "\n", "a")
            self.assertTrue(any(f.rule == "private-data" for f in t.lint()))
        with tree() as t:
            add_findings(t)
            p = t.yaml("projects/zlib/project.yaml")
            p["build"]["oss_verify"] = {"repository": INTERNAL, "commit": "d" * 40, "path": "projects/zlib"}
            p["assets"]["port"] = {"release": "v2026.11.0", "file": "zlib-port.tar.zst", "bytes": 1000,
                                   "sha256": "9" * 64}
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertEqual([f for f in t.lint() if f.rule == "private-data"], [])
        with tree() as t:
            p = t.yaml("projects/zlib/project.yaml")
            p["build"]["oss_verify"] = {"repository": INTERNAL, "commit": "d" * 40, "path": "projects/zlib"}
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertTrue(any(f.rule == "private-data" and f.where.startswith("projects/zlib/project.yaml:")
                                for f in t.lint()))

    def test_another_repository_field_of_a_held_project_may_not_name_the_internal_port(self):
        """Only build.oss_verify.repository: another repository key of the same file is not that field."""
        with tree() as t:
            add_findings(t)
            p = t.yaml("projects/zlib/project.yaml")
            p["build"]["oss_verify"] = {"repository": INTERNAL, "commit": "d" * 40, "path": "projects/zlib"}
            p["assets"]["port"] = {"release": "v2026.11.0", "file": "zlib-port.tar.zst", "bytes": 1000,
                                   "sha256": "9" * 64}
            p["library"]["repository"] = "https://github.com/" + INTERNAL
            t.put_yaml("projects/zlib/project.yaml", p)
            found = [f for f in t.lint() if f.rule == "private-data"]
            self.assertTrue(found and all(f.where.startswith("projects/zlib/project.yaml:") for f in found), found)

    def test_an_unused_exception(self):
        with tree() as t:
            t.put_yaml("tools/oft/lint-exceptions.yaml", {
                "schema": "oss-fuzz-theorems/lint-exceptions/1",
                "exceptions": [{"path": "notes/zlib.md", "rule": "private-data", "key": "0" * 16, "count": 1,
                                "reason": "stale"}]})
            self.assertTrue(any("not used" in f.msg for f in t.lint()))

    def test_an_entry_of_a_kind_this_lint_does_not_read_is_skipped(self):
        """A later lint's entries (one with a path, one with none, as `licence` and `licence-pending` were for the lint
        before them) clear nothing and are not reported unused, so its pull request passes this lint; the kinds it reads
        still are."""
        rel = "projects/zlib/checksum_fuzzer/source/checksum_fuzzer.c"
        later = [{"path": "proofs/zlib/checksum_fuzzer/lib/A.v", "rule": "a-later-kind", "message": "72% of its lines",
                  "key": "proofs/zlib/checksum_fuzzer/lib/B.v", "count": 1, "reason": "written here"},
                 {"unit": "zlib/checksum_fuzzer", "rule": "a-later-kind-pending", "due": "2026-10-31",
                  "series": "pending", "reason": "applied in its own series"}]
        with tree() as t:
            t.write(rel, "/* built in /" + "home/someone/zlib */\n", "a")
            found = [f for f in t.lint() if f.rule == "private-data"]
            self.assertEqual(len(found), 1)
            clear = {"path": rel, "rule": "private-data", "key": found[0].key, "count": 1, "reason": "a test"}
            stale = {"path": "notes/zlib.md", "rule": "private-data", "key": "0" * 16, "count": 1, "reason": "stale"}
            t.put_yaml("tools/oft/lint-exceptions.yaml", {"schema": "oss-fuzz-theorems/lint-exceptions/1",
                                                          "exceptions": [clear] + later})
            self.assertEqual(t.lint(), [])
            t.put_yaml("tools/oft/lint-exceptions.yaml", {"schema": "oss-fuzz-theorems/lint-exceptions/1",
                                                          "exceptions": later + [stale]})
            self.assertEqual([f.msg for f in t.lint() if "not used" in f.msg],
                             ["an exception for private-data notes/zlib.md that is not used 1 time(s)"])


class InternalOnly(unittest.TestCase):
    """dev/stream/, the OSS Verify stream's operational tools: `oft release-tree` cuts the directory whole, so the
    shapes that name a place and the link rule, which keep such a name out of a release, do not read it
    (lint.internal_only).  A credential is not a name, and still does."""

    # What these tools say while they do their work: the tree they run from, the box they run on and its address,
    # the repository they are in, the address they write to, and a lock file's line pinning a package by its URL.
    # Each shape is written in parts, since this test file is not under dev/stream/ and every rule reads it.
    TREE = "/" + "home/someone/src/oss-verifier"
    BOX = "box-7.tailnet." + "ts.net"
    ADDRESS = ".".join(("10", "1", "2", "3"))
    MAIL = "ops" + "@" + "example.com"
    TOOL = ("#!/bin/sh\n"
            "# the agent's tree is %s, on %s (%s), from %s\n"
            "curl -fsS https://%s/ready || mail %s\n" % (TREE, BOX, ADDRESS, INTERNAL, BOX, MAIL))
    LOCK = ('[[package]]\nname = "ossv"\n'
            'url = "https://files.pythonhosted.org/packages/ab/cd/ossv-1.0-py3-none-any.whl"\n')
    SHAPES = ("a host path", "a private host name", "a private address", "a private repository's name",
              "an e-mail address")

    def test_the_stream_s_tools_may_name_their_machines_and_pin_their_packages(self):
        with tree() as t:
            t.write("dev/stream/bin/ossv-agent", self.TOOL)
            t.write("dev/stream/uv.lock", self.LOCK)
            self.assertEqual([str(f) for f in t.lint()], [])

    def test_the_same_text_outside_the_stream_is_still_a_finding(self):
        """The exemption is the directory's, not the shapes': every one of them is reported in a file a release
        carries."""
        with tree() as t:
            t.write("notes/zlib.md", self.TOOL + self.LOCK, "a")
            found = [str(f) for f in t.lint()]
            self.assertEqual(sorted({f.split()[0] for f in found}), ["links", "private-data"], found)
            for what in self.SHAPES:
                self.assertTrue(any(f.startswith("private-data notes/zlib.md:") and what in f for f in found),
                                (what, found))
            for link in ("https://%s/ready" % self.BOX, "https://files.pythonhosted.org/"):
                self.assertTrue(any(f.startswith("links notes/zlib.md:") and link in f for f in found),
                                (link, found))

    def test_a_private_key_or_an_access_token_in_the_stream_is_still_a_finding(self):
        """A committed credential is a live credential whether or not it ships, so the cut does not clear it."""
        with tree() as t:
            t.write("dev/stream/bin/ossv-agent",
                    "#!/bin/sh\ntoken=" + "ghp" + "_" + "A" * 36 + "\n-----BEGIN RSA " + "PRIVATE KEY-----\n")
            found = [f for f in t.lint() if f.rule == "private-data"]
            self.assertEqual(sorted(f.msg for f in found), ["a private key", "an access token"],
                             [str(f) for f in found])

    def test_a_url_s_user_information_in_the_stream_is_still_a_finding(self):
        """A password written into a git remote or a curl line is a live credential of a shape no token pattern
        knows.  It names no place, so the cut that clears the places does not clear it; the plain address on the
        next line still names a place, and is still not read here."""
        with tree() as t:
            # written in parts: this file is not under dev/stream/, and every rule reads it, the link rule among them
            t.write("dev/stream/bin/ossv-agent",
                    "#!/bin/sh\n"
                    "curl -fsS http" + "s://" + "ossv-bot:" + "S3cretPassw0rd" + "@" + "gateway.example.org/x\n"
                    "mail " + self.MAIL + "\n")
            found = [f for f in t.lint() if f.rule == "private-data"]
            self.assertEqual([f.msg for f in found], ["a URL's user information"], [str(f) for f in found])
            self.assertTrue(found[0].where.endswith(":2"), str(found[0]))

    def test_github_s_own_ssh_user_is_not_user_information_and_every_other_user_still_is(self):
        """GitHub's SSH clone URL, user `git` at `github.com`, is the only way to clone over SSH from GitHub, so that user
        is a fixed part of a URL and not a credential: an imported tool that clones writes it, and three of the five
        findings pull request 496's review left open were that one docstring shape (R5-1).  The boundary is that the
        user half is read for anything else: a person's account, a token, and the password form the rule exists for.
        """
        with tree() as t:
            t.write("dev/stream/bin/ossv-agent",
                    "#!/bin/sh\n"
                    "git clone ssh" + "://" + "git" + "@github.com/google/oss-fuzz\n")
            self.assertEqual([str(f) for f in t.lint()], [])
        with tree() as t:
            # written in parts for the same reason as the test above: every rule reads this file
            t.write("dev/stream/bin/ossv-agent",
                    "#!/bin/sh\n"
                    "git clone ssh" + "://" + "deploy" + "-bot@" + "github.com/google/oss-fuzz\n"
                    "git clone http" + "s://" + "x-access-token:" + "ghp" + "_" + "A" * 36 + "@"
                    + "github.com/google/oss-fuzz\n")
            found = [f for f in t.lint() if f.rule == "private-data"]
            self.assertEqual(sorted(f.msg for f in found),
                             ["a URL's user information", "a URL's user information", "an access token"],
                             [str(f) for f in found])

    def test_an_exception_clears_a_stand_in_credential_in_the_stream(self):
        """The stream's own secret scanner has tests, and a test of a scanner holds the shapes it scans for: a
        reviewed entry, read by a person, is how such a stand-in is recorded."""
        with tree() as t:
            rel = "dev/stream/bin/test_ossv_binscan.py"
            t.write(rel, "STAND_IN = " + '"' + "ghp" + "_" + "A" * 36 + '"\n')
            found = [f for f in t.lint() if f.rule == "private-data"]
            self.assertEqual([f.msg for f in found], ["an access token"], [str(f) for f in found])
            t.put_yaml("tools/oft/lint-exceptions.yaml", {
                "schema": "oss-fuzz-theorems/lint-exceptions/1",
                "exceptions": [{"path": rel, "rule": "private-data", "key": found[0].key, "count": 1,
                                "reason": "a test"}]})
            self.assertEqual(t.lint(), [])

    def test_the_exemption_stands_on_the_cut_that_justifies_it(self):
        """Each exempt directory is one `oft release-tree` removes whole (release_tree.INTERNAL, where a directory is
        written with its trailing /): were it ever kept, the text these rules stop reading would be published."""
        from oft import release_tree
        for prefix in lint.INTERNAL_ONLY:
            self.assertTrue(prefix.endswith("/"), prefix)
            self.assertIn(prefix, release_tree.INTERNAL, prefix)
            self.assertTrue(lint.internal_only(prefix + "bin/x"), prefix)
        for rel in ("streaming/x.md", "notes/zlib.md", "tools/oft/lint.py", "projects/zlib/project.yaml"):
            self.assertFalse(lint.internal_only(rel), rel)


class Links(unittest.TestCase):
    def test_a_link_to_a_private_repository(self):
        # the link rule refuses the link, and the private-data rule the private repository's name in the text
        with tree() as t:
            t.write("notes/zlib.md", "See https://github.com/theorem-labs/" + "some-private-repository.\n", "a")
            self.assertEqual(rules_of(t.lint()), ["links", "private-data"])

    def test_a_link_to_a_public_repository(self):
        with tree() as t:
            t.write("notes/zlib.md", "Enroll at https://github.com/" + "theorem-labs/oss-verify.\n", "a")
            self.assertEqual(rules_of(t.lint()), [])

    def test_a_link_to_asan_static_by_its_name_and_by_its_former_name(self):
        """asan-static is public, and GitHub redirects its former name, static-asan, to it."""
        for name in ("asan-static", "static-asan"):
            with self.subTest(name=name), tree() as t:
                url = "https://github.com/" + "theorem-labs/%s/commit/b05061352064" % name
                t.write("notes/zlib.md", "Built from %s.\n" % url, "a")
                self.assertEqual(rules_of(t.lint()), [])

    def test_a_private_repository_name_split_where_github_shows_it_whole(self):
        """GitHub shows `\\-` as `-` and drops an HTML comment, so a public name with a private one's suffix after
        either reads as the private name: the private-data rule refuses it in a URL and in a path, and the link rule
        the URL too."""
        public = "theorem-labs/" + "oss-verify"
        for split in ("\\-prelaunch", "<!-- -->-prelaunch"):
            for text, rules in (("https://github.com/" + public + split, ["links", "private-data"]),
                                ("see /" + public + split, ["private-data"]),
                                (public + split, ["private-data"])):
                with self.subTest(text=text), tree() as t:
                    t.write("notes/zlib.md", text + "\n", "a")
                    self.assertEqual(rules_of(t.lint()), rules)

    def test_an_unknown_link_in_rendered_text(self):
        with tree() as t:
            t.write("notes/zlib.md", "See https://example.org/x and http://www.zlib.net/.\n", "a")
            self.assertEqual(len([f for f in t.lint() if f.rule == "links"]), 2)

    def test_a_link_shape_inside_a_proof_string_is_payload(self):
        lib = "proofs/zlib/checksum_fuzzer/lib/Replay.v"
        def links(text):
            with tree() as t:
                t.write(lib, text, "a")
                return [f for f in t.lint() if f.rule == "links"]
        self.assertEqual(links('Definition t : PrimString.string := "#x://%Q~z#".\n'), [])
        self.assertEqual(len(links("(* see https://example.org/x *)\nDefinition t := 0.\n")), 1)

    def test_a_long_payload_line_is_read_in_linear_time(self):
        line = "0a" * 50000
        start = time.process_time()
        self.assertIsNone(lint.URL.search(line))
        self.assertLess(time.process_time() - start, 1.0)

    def test_a_markdown_destination_has_githubs_parenthesis_limit(self):
        def link(depth):
            return "[x](x%s%s)" % ("(" * depth, ")" * depth)
        self.assertEqual([item.ref for item in urls.links(link(32), True)], ["x" + "(" * 32 + ")" * 32])
        self.assertEqual(list(urls.links(link(33), True)), [])
        start = time.process_time()
        list(urls.links("](" * 10000, True))
        self.assertLess(time.process_time() - start, 1.0)

    def test_links_the_facts_record_are_allowed(self):
        with tree() as t:
            t.write("notes/zlib.md", "See https://github.com/madler/zlib/blob/master/README.\n", "a")
            self.assertEqual(t.lint(), [])

    def test_only_the_debian_snapshot_archive_may_be_read_over_http(self):
        with tree() as t:
            t.write("notes/zlib.md", "From http://snapshot.debian.org/archive/debian/20261001T000000Z and "
                    "https://snapshot.debian.org/file/0123, not http://deb.debian.org/debian.\n", "a")
            found = [f for f in t.lint() if f.rule == "links"]
            self.assertEqual([f.msg.rsplit(" ", 1)[-1] for f in found], ["http://deb.debian.org/debian."])

    # The two pages AddressSanitizer's runtime names in a report, which the comparison kit copies verbatim into a
    # build record's evidence.
    WIKI = "https://github.com/google/sanitizers/wiki/AddressSanitizerContainerOverflow"
    ISSUE = "https://github.com/google/sanitizers/issues/189"
    EVIDENCE = "proofs/zlib/checksum_fuzzer/provenance/evidence/asan-report.txt"

    def links_of(self, rel, text):
        """What the links rule says of text written at rel: the target of each finding."""
        with tree() as t:
            t.write(rel, text, "a")
            return [f.msg.rsplit(" ", 1)[-1] for f in t.lint() if f.rule == "links"]

    def test_the_two_sanitizer_urls_asan_prints_are_allowed_anywhere(self):
        for rel in (self.EVIDENCE, "notes/zlib.md"):
            for url in (self.WIKI, self.ISSUE):
                with self.subTest(rel=rel, url=url):
                    self.assertEqual(self.links_of(rel, "==1==HINT: see %s\n" % url), [])

    def test_a_sanitizer_url_is_allowed_as_a_report_and_a_page_write_it(self):
        """How the kit's output and a page that quotes it put the URL: a report ends the sentence after it, and a
        page may make it a Markdown or an HTML link.  A link ends before the full stop or the bracket."""
        for text in ("If you suspect a false positive see also: %s.\n" % self.WIKI,
                     "(%s)\n" % self.ISSUE,
                     "[the page](%s)\n" % self.WIKI,
                     '<a href="%s">issue 189</a>\n' % self.ISSUE):
            with self.subTest(text=text):
                self.assertEqual(self.links_of(self.EVIDENCE, text), [])
                self.assertEqual(self.links_of("notes/zlib.md", text), [])

    def test_a_markdown_destination_is_read_as_github_builds_the_link(self):
        """A destination carries its escapes and character references into the link GitHub builds, and the rule
        reads it the same way, so an escaped spelling of an allowed URL is that URL and nothing else is."""
        for text, found in (("[x](https&#58;//github.com/google/sanitizers/issues/189)\n", []),
                            ('<a href="https&#58;//github.com/google/sanitizers/issues/189">x</a>\n', []),
                            ("[x](https\\://github.com/google/sanitizers/issues/189)\n", []),
                            ("[x](https&#58;//github.com/google/sanitizers/issues/190)\n",
                             ["https&#58;//github.com/google/sanitizers/issues/190"])):
            with self.subTest(text=text):
                self.assertEqual(self.links_of("notes/zlib.md", text), found)

    def test_only_those_two_urls_written_as_they_are_are_allowed(self):
        """Each stands as it is written and nothing else: another page of the same wiki or repository, a deeper
        path, a trailing character, a query, a fragment, another spelling of the same page, and http."""
        others = ("https://github.com/google/sanitizers/wiki/AddressSanitizerLeakSanitizer",
                  "https://github.com/google/sanitizers/issues/1890",
                  self.ISSUE + "/events",
                  self.WIKI + "X",
                  self.WIKI + "?x=1",
                  self.WIKI + "#overflow",
                  self.ISSUE + "?x=1",
                  self.ISSUE + "#issue-1",
                  "https://GITHUB.COM/google/sanitizers/issues/189",
                  "https://github.com:443/google/sanitizers/issues/189",
                  "https://github.com/google%2Fsanitizers%2Fissues%2F189",
                  "https://github.com/google/sanitizers/x/../issues/189",
                  "http://github.com/google/sanitizers/issues/189")
        for url in others:
            with self.subTest(url=url):
                self.assertEqual(self.links_of(self.EVIDENCE, "see %s\n" % url), [url])

    def test_an_unrelated_bad_link_in_evidence_is_still_reported(self):
        self.assertEqual(self.links_of(self.EVIDENCE, "see %s and https://example.org/x\n" % self.ISSUE),
                         ["https://example.org/x"])

    # Every backslash below is one character: the kit quotes the runtime's output, so the end of the printed line
    # follows the URL as text.
    def test_the_escaped_tail_the_kit_leaves_after_a_sanitizer_url(self):
        """One run of literal C escapes at the very end, and the full stop a report puts before it, is not part of
        the page the line names; the three forms the fuzz_uci evidence holds."""
        for tail, url in ((r"\n\x00", self.ISSUE), (r"\x00", self.WIKI), (r".\n\x00", self.WIKI)):
            for rel in (self.EVIDENCE, "notes/zlib.md", "proofs/zlib/checksum_fuzzer/lib/Replay.v"):
                with self.subTest(tail=tail, rel=rel):
                    self.assertEqual(self.links_of(rel, "see %s%s\n" % (url, tail)), [])

    def test_a_backslash_that_is_not_that_tail_opens_another_page(self):
        """A backslash is a slash to a browser and to urls.parse, so a link written with one opens whatever the
        whole of it names.  Only the escaped tail comes off, and only at the end: anything else is the finding it
        always was, in rendered text, in a target's source copy and in evidence."""
        others = (r"https://github.com/google/oss-fuzz\..\..\evil-page",
                  self.ISSUE + r"\n\..\evil",
                  self.ISSUE + r"\x00extra",
                  "https://github.com/google/sanitizers/issues/190" + r"\n\x00",
                  "http://github.com/google/sanitizers/issues/189" + r"\n\x00")
        for url in others:
            for rel in (self.EVIDENCE, "notes/zlib.md", "proofs/zlib/checksum_fuzzer/lib/Replay.v"):
                with self.subTest(url=url, rel=rel):
                    self.assertEqual(self.links_of(rel, "see %s\n" % url), [url])


class FreeText(unittest.TestCase):
    def test_text_with_no_place_in_the_rendering(self):
        with tree() as t:
            y = t.yaml("projects/imagemagick/project.yaml")
            y["reason_args"]["text"] = "a note that no sentence uses"
            t.put_yaml("projects/imagemagick/project.yaml", y)
            self.assertIn("free-text", rules_of(t.lint()))


class ProofsException(unittest.TestCase):
    """A notation token the proofs rule refuses can be cleared by one reviewed entry that names it exactly: its path,
    line, message and string literal, count 1.  Anything less exact, or an entry no finding matches, is a finding."""
    REL = "proofs/zlib/checksum_fuzzer/plain_halts/Proof.v"
    TOKEN = "Notation \"'LF2CBN(' t ')'\" := t (at level 0, only parsing).\n"
    MSG = ("a notation token with a '\"', or a '(' after anything but '.', '`' or ':', is not allowed in a proof")

    def found(self, where, token="LF2CBN"):
        return "proofs %s: %s (key \"'%s(' t ')'\")" % (where, self.MSG, token)

    def entry(self, **change):
        return dict({"path": self.REL, "rule": "proofs", "line": 2, "message": self.MSG,
                     "key": "\"'LF2CBN(' t ')'\"", "count": 1, "reason": "a test"}, **change)

    def lint(self, files, entries):
        with tree() as t:
            t.put_yaml("proofs/zlib/checksum_fuzzer/plain_halts/proof.yaml", {
                "schema": "oss-fuzz-theorems/proof/1", "proves": "zlib/checksum_fuzzer/plain_halts",
                "fingerprint": next(s for s in facts.load(t.root).statements()
                                    if s.id == "zlib/checksum_fuzzer/plain_halts").fingerprint})
            for rel, body in files.items():
                t.write(rel, body)
            t.put_yaml("tools/oft/lint-exceptions.yaml",
                       {"schema": "oss-fuzz-theorems/lint-exceptions/1", "exceptions": entries})
            t.generate()
            return [str(f) for f in t.lint() if f.rule == "proofs" or "lint-exceptions" in f.where]

    def test_the_exact_entry_clears_its_one_finding(self):
        self.assertEqual(self.lint({self.REL: "(* a *)\n" + self.TOKEN}, [self.entry()]), [])

    def test_the_same_token_elsewhere_still_fails(self):
        other = "proofs/zlib/checksum_fuzzer/plain_halts/Other.v"
        found = self.lint({self.REL: "(* a *)\n" + self.TOKEN, other: "(* a *)\n" + self.TOKEN}, [self.entry()])
        self.assertEqual(found, [self.found(other + ":2")])
        found = self.lint({self.REL: "(* a *)\n" + self.TOKEN + self.TOKEN.replace("LF2CBN", "LF3CBN")},
                          [self.entry()])
        self.assertEqual(found, [self.found(self.REL + ":3", "LF3CBN")])

    def test_a_stale_entry_fails(self):
        found = self.lint({self.REL: "(* a *)\n(* b *)\n" + self.TOKEN}, [self.entry()])
        self.assertEqual(found, [self.found(self.REL + ":3"),
                                 "paths tools/oft/lint-exceptions.yaml: an exception for proofs %s:2 that is not "
                                 "used 1 time(s)" % self.REL])

    def test_an_entry_that_is_not_exact_fails(self):
        for change in ({"count": 2}, {"count": True}, {"count": 1.0}, {"line": None}, {"line": "2"},
                       {"message": ""}, {"line": True}, {"extra": 1}):
            with self.subTest(change=change):
                entry = {k: v for k, v in self.entry(**change).items() if v is not None}
                found = self.lint({self.REL: "(* a *)\n" + self.TOKEN}, [entry])
                self.assertEqual(found, [self.found(self.REL + ":2"),
                                         "paths tools/oft/lint-exceptions.yaml: an exception for proofs %s must name "
                                         "exactly its path, line, message and key, with count 1 and a reason, once"
                                         % self.REL])

    def test_a_second_entry_for_the_same_finding_fails(self):
        found = self.lint({self.REL: "(* a *)\n" + self.TOKEN}, [self.entry(), self.entry(reason="again")])
        self.assertEqual(found, ["paths tools/oft/lint-exceptions.yaml: an exception for proofs %s must name exactly "
                                 "its path, line, message and key, with count 1 and a reason, once" % self.REL])


class Proofs(unittest.TestCase):
    def proof(self, body, **extra):
        with tree() as t:
            t.put_yaml("proofs/zlib/checksum_fuzzer/plain_halts/proof.yaml", dict({
                "schema": "oss-fuzz-theorems/proof/1", "proves": "zlib/checksum_fuzzer/plain_halts",
                "fingerprint": next(s for s in facts.load(t.root).statements()
                                    if s.id == "zlib/checksum_fuzzer/plain_halts").fingerprint}, **extra))
            t.write("proofs/zlib/checksum_fuzzer/plain_halts/Proof.v", body)
            t.generate()
            return [f for f in t.lint() if f.rule == "proofs" or "proof.yaml" in str(f)]

    def test_a_proof_names_no_author(self):
        found = self.proof("Theorem plain_halts_holds : True. Proof. exact I. Qed.\n", authors=["A. Person"])
        self.assertTrue(any("unknown key 'authors'" in str(f) for f in found), found)

    def test_admitted(self):
        self.assertEqual(len(self.proof("Theorem plain_halts_holds : True.\nProof. Admitted.\n")), 1)

    def test_an_axiom(self):
        self.assertEqual(len(self.proof("Axiom cheat : False.\n")), 1)

    def test_what_hides_an_axiom_from_check_s_audit_is_refused(self):
        """An attribute that prints a note of the proof's choosing where its theorem is used (deprecated, warn), and
        what declares an axiom outside a Section's assumptions (Declare Instance, Declare Module; Variable, Hypothesis
        and Context outside a Section), are refused: together they let a proof rest on an axiom that oft check's audit
        read past (the Verified Linux team's report, 2026-10-29)."""
        theorem = "Theorem plain_halts_holds : True.\nProof. exact I. Qed.\n"
        refused = {
            '#[deprecated(since="x", note="\nClosed under the global context\n")]\n' + theorem:
                "the attribute 'deprecated'",
            '#[warn(note="Closed under the global context", cats="x")]\n' + theorem: "the attribute 'warn'",
            "Declare Instance cheat : True.\n": "'Declare Instance' is not allowed",
            "Declare Module M : T.\n": "'Declare Module' is not allowed",
            "Hypothesis cheat : False.\n": "'Hypothesis' outside a Section",
            "#[local] Variable v : nat.\n": "'Variable' outside a Section",
            "Local Hypotheses a b : False.\n": "'Hypotheses' outside a Section",
            "Variables a b : nat.\n": "'Variables' outside a Section",
            "Context {A : Type}.\n": "'Context' outside a Section",
            "Module M.\nHypothesis cheat : False.\nEnd M.\n": "'Hypothesis' outside a Section",
            "Section S.\nVariable x : nat.\nEnd S.\nHypothesis cheat : False.\n": "'Hypothesis' outside a Section",
            # Rocq runs a sentence under Succeed or Fail and then undoes it: no Section is open after either
            'Set Warnings "-declaration-outside-section".\nSucceed Section S.\nHypothesis cheat : False.\n':
                "'Hypothesis' outside a Section",
            "Time Succeed Module M.\nHypothesis cheat : False.\n": "'Hypothesis' outside a Section",
            # inside a proof Section is an error, so Fail succeeds, and still no Section is open after it
            "Lemma t : True.\nProof. Fail Section S. exact I. Qed.\nHypothesis cheat : False.\n":
                "'Hypothesis' outside a Section",
            "Lemma t : True.\nProof.\n- Fail Section S. exact I.\nQed.\nHypothesis cheat : False.\n":
                "'Hypothesis' outside a Section",
            # Reset goes back past the Section it names: rocq compile accepts it, and what follows is outside
            "Section S.\nReset S.\nHypothesis cheat : False.\nEnd S.\n": "'Reset' goes back in the file",
            "Reset Initial.\n": "'Reset' goes back in the file",
            # the command form of the note attributes, for the whole file
            'Attributes deprecated(since="x", note="\nClosed under the global context\n").\n': "'Attributes' sets",
            'Attributes warn(note="Closed under the global context", cats="x").\n': "'Attributes' sets",
            # an admitted obligation is an axiom (cheat_obligation_1)
            "Program Definition cheat : False := _.\nAdmit Obligations.\n": "'Admit Obligations' is not allowed",
            # Fail as an attribute is no control flag: with its warning off, Rocq ignores it and the End closes S
            'Set Warnings "-unsupported-attributes".\nSection S.\n#[Fail] End S.\nHypothesis cheat : False.\n':
                "'Hypothesis' outside a Section",
            # a declared token that ends in '.' would end a sentence for these rules: `1 +. Section 2` opens nothing
            "Notation \"x '+.' 'Section' y\" := (x + y) (at level 50).\nCheck (1 +. Section 2).\n"
            "Hypothesis cheat : False.\n": "a notation token that ends in '.'",
            'Infix "+." := Nat.add (at level 50).\n': "a notation token that ends in '.'",
            # the `..` of a recursive notation's body ends no sentence, so `.. Section (` opens no Section
            "Notation \"'Section' x\" := x (at level 0, x at level 0).\n"
            "Notation \"[[ x ; .. ; y ]]\" := (cons x .. Section (cons y nil) ..).\n"
            'Set Warnings "-declaration-outside-section".\nHypothesis cheat : False.\n': "'Hypothesis' outside a Section",
        }
        for body, why in refused.items():
            with self.subTest(body=body):
                found = [str(f) for f in self.proof(body)]
                self.assertEqual(len(found), 1, found)
                self.assertIn(why, found[0])
        # what silences warnings is not a note, a Section's assumptions are arguments once it ends, a Section stays
        # open past an End that Succeed undoes, Reset Ltac Profile only clears a profile, and `..` is Rocq's own token
        fine = ('#[warnings="-deprecated"] Notation n := 0.\nSet Warnings "-notation-overridden".\n'
                "Local Set Warnings \"-deprecated\".\nModule A := B.\nModule M.\nSection S.\nHypothesis h : False.\n"
                "Variables a b : nat.\nContext {T : Type}.\nSucceed End S.\nHypothesis g : False.\nEnd S.\nEnd M.\n"
                "Time Section T.\nVariable v : nat.\nEnd T.\nReset Ltac Profile.\n"
                'Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).\n' + theorem)
        self.assertEqual(self.proof(fine), [])

    def test_primitive_projections_are_fine(self):
        self.assertEqual(self.proof("Set Primitive Projections.\n"), [])
        self.assertEqual(len(self.proof("Primitive cheat : False := #int63_add.\n")), 1)

    def test_comments_and_strings_do_not_count(self):
        self.assertEqual(self.proof('(* not (* Admitted *) here *)\nDefinition s := "Axiom".\n'), [])

    def test_a_pin_is_the_statements_fingerprint_under_this_version(self):
        with tree() as t, mock.patch.object(facts, "FINGERPRINT_TAG", "oss-fuzz-theorems/statement/1"):
            other = next(s for s in facts.load(t.root).statements() if s.id == "zlib/checksum_fuzzer/plain_halts")
        found = self.proof("Theorem plain_halts_holds : True. Proof. exact I. Qed.\n", fingerprint=other.fingerprint)
        self.assertEqual([f.msg.split(" (")[0] for f in found], ["fingerprint differs from the statement's current one"])

    def test_load_and_cd_are_commands_only_where_a_sentence_starts(self):
        names = ("Lemma l : forall i, i = Load 2 \\/ i <> Load 2.\n"
                 "Proof.\n  intros [ | x ]; destruct (Some (Load 2)) as [C2 Cd];\n  | Load _ => auto\n"
                 "  end.\nQed.\n")
        self.assertEqual(self.proof(names), [])
        refused = self.proof('Load "cheat".\nLemma l : True.\nProof. Cd "/tmp".\n  exact I.\nQed.\n')
        self.assertEqual(sorted((str(f).split(": ")[0].rsplit(":", 1)[-1], "'Load'" in str(f)) for f in refused),
                         [("1", True), ("3", False)])

    @staticmethod
    def lines(found):
        return sorted(int(str(f).split(": ")[0].rsplit(":", 1)[-1]) for f in found)

    def test_wall_clock_timeouts(self):
        refused = self.proof("Set Default Timeout 60.\nLemma l : True.\nProof. timeout 5 exact I.\nQed.\n"
                             "Timeout 10 Check I.\nLemma m : True.\nProof. idtac; timeout 5 exact I.\nQed.\n"
                             "Lemma k : True.\nProof. first [ exact I | timeout 5 exact I ].\nQed.\n"
                             "Lemma j : True.\nProof. try idtac; timeout 5 exact I.\nQed.\n")
        self.assertEqual(self.lines(refused), [1, 3, 5, 7, 10, 13])

    def test_a_timeout_whose_expiry_something_catches_is_refused_too(self):
        # under load the expiry still changes what the proof does: `try` leaves the goal open, a later arm runs
        body = ("Lemma l : True.\nProof. first [ timeout 5 exact I | exact I ].\nQed.\n"
                "Lemma m : True.\nProof. try (timeout 5 fail). exact I.\nQed.\n"
                "Lemma k : True.\nProof. solve [ timeout 5 exact I | exact I ].\nQed.\n"
                "Lemma j : True.\nProof. repeat (timeout 5 fail). exact I.\nQed.\n"
                "Ltac hot2_mid := timeout 8 lia.\n")
        self.assertEqual(self.lines(lint.scan_proof(body, "proofs/varnish/esi_parse_fuzzer/lib/D_Dir.v")),
                         [2, 5, 8, 11, 13])

    def test_a_justified_timeout_and_a_commented_one_are_fine(self):
        self.assertEqual(self.proof("(* Set Default Timeout 60. timeout 5 *)\n"
                                    "Lemma l : True.\n"
                                    "Proof. first [ timeout 5 exact I | exact I ]. (* timeout-ok: the next arm *)\nQed.\n"
                                    "Ltac t := first [ timeout 5 lia (* [a note] *)   (*timeout-ok:fast tier*)\n"
                                    "  | nia ].\n"), [])

    def test_the_justification_ends_the_line_of_the_timeout_and_gives_a_reason(self):
        body = ("Ltac a := first [ timeout 5 lia | nia ]. (* timeout-ok: *)\n"
                "Ltac b := (* timeout-ok: fast tier *) first [ timeout 5 lia | nia ].\n"
                "(* timeout-ok: fast tier *)\nLtac c := first [ timeout 5 lia | nia ].\n"
                "Ltac d := first [ timeout 5 lia | nia ]. Definition s := \"(* timeout-ok: fast tier *)\".\n"
                "Ltac e := first [ timeout 5 lia | nia ]. (* timeout-ok: fast *) idtac.\n"
                "Ltac f := first [ timeout 5 lia | nia ]. (* timeout-ok: fast *) (* other *)\n"
                "Ltac g := first [ timeout 5 lia\n  | nia ]. (* timeout-ok: fast tier *)\n")
        self.assertEqual(self.lines(lint.scan_proof(body, "proofs/zlib/checksum_fuzzer/lib/T.v")),
                         [1, 2, 4, 5, 6, 7, 8])

    def test_a_timeout_of_a_variable_and_the_ltac2_timeouts_are_refused(self):
        body = ("Ltac t n := timeout n lia.\n"
                "Ltac2 a () := Control.timeout 5 (fun () => ()).\n"
                "Ltac2 b () := Control.timeoutf 0.5 (fun () => ()).\n"
                "Ltac2 c () := Ltac2.Control.timeout 5 (fun () => ()).\n"
                "Import Ltac2.Control.\nLtac2 d () := timeoutf 0.5 (fun () => ()).\n"
                "Ltac2 e () := let f := Control.timeout in f 5 (fun () => ()).\n"
                "Ltac2 g () := Control.timeout 5 (fun () => ()). (* timeout-ok: fast tier *)\n"
                "Definition timeout_ms := 5. Definition my_timeout := timeout_ms. Definition MyControl := 1.\n")
        self.assertEqual(self.lines(lint.scan_proof(body, "proofs/zlib/checksum_fuzzer/lib/T.v")),
                         [1, 2, 3, 4, 6, 7])

    def test_an_ltac2_external_bound_to_the_timeout_primitive_is_refused(self):
        body = ('Ltac2 @external tmo : int -> (unit -> unit) -> unit := "rocq-runtime.plugins.ltac2" "timeout".\n'
                'Ltac2 @external\n  tmf : float -> (unit -> unit) -> unit :=\n'
                '  "rocq-runtime.plugins.ltac2" "timeoutf".\n'
                'Ltac2 @external sgo : string -> int -> int := "rocq-runtime.plugins.ltac2" "string_get".\n'
                '(* Ltac2 @external c : int := "rocq-runtime.plugins.ltac2" "timeout". *)\n'
                'Definition s := "Ltac2 @external c : int := ""rocq-runtime.plugins.ltac2"" ""timeout"".".\n')
        self.assertEqual(self.lines(lint.scan_proof(body, "proofs/zlib/checksum_fuzzer/lib/T.v")), [1, 2])

    def test_a_comment_does_not_hide_an_ltac2_external(self):
        body = ('Ltac2 @external a : int := "rocq-runtime.plugins.ltac2" (* x *) "timeout".\n'
                'Ltac2 @external b : int := (* x *) "rocq-runtime.plugins.ltac2" "timeout".\n'
                'Ltac2 @ (* x *) external c : int := "rocq-runtime.plugins.ltac2" "timeout".\n'
                'Ltac2 @external d (* "string_get" *) : int := "rocq-runtime.plugins.ltac2" "timeoutf".\n'
                'Ltac2 @external e : int := "rocq-runtime.plugins.ltac2" (* "timeout" *) "string_get".\n')
        self.assertEqual(self.lines(lint.scan_proof(body, "proofs/zlib/checksum_fuzzer/lib/T.v")), [1, 2, 3, 4])

    def test_an_ltac2_external_may_bind_only_an_allowed_primitive(self):
        body = ('Ltac2 @external a : string -> int -> int := "rocq-runtime.plugins.ltac2" "string_set".\n'
                'Ltac2 @external b : string -> int -> int := "other-plugin" "string_get".\n'
                'Ltac2 @external c : string -> int -> int := "rocq-runtime.plugins.ltac2" "string_get".\n'
                'Ltac2 @external d : int := "rocq-runtime.plugins.ltac2" "string_set". (* timeout-ok: no *)\n')
        found = lint.scan_proof(body, "proofs/zlib/checksum_fuzzer/lib/T.v")
        self.assertEqual(self.lines(found), [1, 2, 4])
        self.assertIn('binds "rocq-runtime.plugins.ltac2" "string_set"', str(found[0]))
        with tempfile.TemporaryDirectory() as root:
            rel = "theories/T.v"
            os.makedirs(os.path.join(root, "theories"))
            with open(os.path.join(root, rel), "w") as f:
                f.write(body)
            found = [f.where for f in lint.scan_file(root, rel, facts.Tree(root), frozenset(), frozenset())[0]
                     if f.rule == "proofs"]
        self.assertEqual(found, ["theories/T.v:1", "theories/T.v:2", "theories/T.v:4"])

    def test_a_parenthesised_or_qualified_timeout_is_refused(self):
        body = ("Import Ltac2.Control.\n"
                "Ltac2 a () := timeout (5) (fun () => ()).\n"
                "Ltac2 b n := timeout(n) (fun () => ()).\n"
                "Module C := Ltac2.Control.\n"
                "Ltac2 d () := C.timeoutf 0.5 (fun () => ()).\n"
                "Ltac2 e () := C.timeout\n  5 (fun () => ()).\n")
        self.assertEqual(self.lines(lint.scan_proof(body, "proofs/zlib/checksum_fuzzer/lib/T.v")), [2, 3, 5, 6])

    def test_a_timeout_in_tests_is_refused(self):
        files = ("tests/proofs/toy/exit0/plain_halts/Proof.v", "tests/toy/README.md")
        with tempfile.TemporaryDirectory() as root:
            for rel in files:
                os.makedirs(os.path.dirname(os.path.join(root, rel)), exist_ok=True)
                with open(os.path.join(root, rel), "w") as f:
                    f.write("Lemma l : True.\nProof. timeout 5 exact I.\nQed.\n")
            found = [[f.where for f in lint.scan_file(root, rel, facts.Tree(root), frozenset(), frozenset())[0]
                      if f.rule == "proofs"] for rel in files]
        self.assertEqual(found, [["tests/proofs/toy/exit0/plain_halts/Proof.v:2"], []])

    def test_a_timeout_in_theories_projects_or_a_rocq_template_is_refused(self):
        with tree() as t:
            t.generate()
            t.write("theories/Tmo.v", "Set Default Timeout 5.\nLemma l : True. Proof. timeout 5 exact I. Qed.\n"
                                      "Lemma m : True. Proof. first [ timeout 5 exact I | exact I ]. "
                                      "(* timeout-ok: the next arm *)\nQed.\n")
            with open(t.path("projects/zlib/checksum_fuzzer/Statements.v"), "a") as f:
                f.write("Timeout 5 Check I.\n")
            with open(t.path("projects/zlib/checksum_fuzzer/Statements.v")) as f:
                last = f.read().count("\n")
            found = sorted(f.where for f in t.lint() if f.rule == "proofs")
        self.assertEqual(found, ["projects/zlib/checksum_fuzzer/Statements.v:%d" % last,
                                 "theories/Tmo.v:1", "theories/Tmo.v:2"])
        templates = ("tools/oft/templates/X.v.tmpl", "tools/oft/templates/X.md.tmpl")
        with tempfile.TemporaryDirectory() as root:
            os.makedirs(os.path.join(root, "tools/oft/templates"))
            for rel in templates:
                with open(os.path.join(root, rel), "w") as f:
                    f.write("Ltac t n := timeout n lia.\n")
            found = [len([f for f in lint.scan_file(root, rel, facts.Tree(root), frozenset(), frozenset())[0]
                          if f.rule == "proofs"]) for rel in templates]
        self.assertEqual(found, [1, 0])

    def test_a_command_that_reads_a_file_is_refused_in_every_form(self):
        """A proof's compile reads no file: Load, Cd and Extra Dependency are refused when a comment, a line break, an
        attribute or a control prefix separates their words or comes first, and so are the ReadFile commands."""
        forms = {
            "Load on the next line": ('Lemma l : True.\nProof. exact I. Qed.\nLoad\n  "cheat".\n', 3, "Load"),
            "a comment first": ('(* c *) Load "cheat".\n', 1, "Load"),
            "an attribute": ('Lemma l : True.\nProof. exact I. Qed.\n#[local] Load "cheat".\n', 3, "Load"),
            "a control prefix": ('Lemma l : True.\nProof. exact I. Qed.\nTimeout 5 Time Load "cheat".\n', 3, "Load"),
            "Fail": ('Lemma l : True.\nProof. exact I. Qed.\nFail Cd "/tmp".\n', 3, "Cd"),
            "Extra Dependency split": ('Extra (* c *)\n  Dependency "CHANGELOG.md" as log.\n', 1, "Extra Dependency"),
            "From ... Extra Dependency": ('From Foo Extra Dependency "a" as a.\n', 1, "Extra Dependency"),
            "ReadFileBytes": ("Definition b := ReadFileBytes.\n", 1, "ReadFileBytes"),
            "a control flag before an attribute": (
                'Lemma l : True.\nProof. exact I. Qed.\nTime #[warnings="-deprecated"] Load "cheat".\n', 3, "Load"),
            "a legacy attribute": ('Lemma l : True.\nProof. exact I. Qed.\nProgram Load "cheat".\n', 3, "Load"),
            "Timeout in hexadecimal": ('Lemma l : True.\nProof. exact I. Qed.\nTimeout 0x5 Load "cheat".\n', 3, "Load"),
            "a bullet": ('Lemma l : True.\nProof.\n- Load "cheat".\n', 3, "Load"),
            "a byte-order mark": ('\ufeffLoad "cheat".\n', 1, "Load"),
            "Locate File": ('Locate File "cheat.v".\n', 1, "Locate File"),
            "a goal selector and a brace": ('Lemma l : True.\nProof.\n1:{ Load "cheat".\n', 3, "Load"),
        }
        for name, (body, line, word) in forms.items():
            with self.subTest(form=name):
                # a Timeout prefix is also a wall-clock limit, refused on its own (test_wall_clock_timeouts)
                found = [str(f) for f in self.proof(body) if "wall-clock" not in str(f)]
                self.assertEqual([(f.split(": ")[0].rsplit(":", 1)[-1], "%r is" % word in f) for f in found],
                                 [(str(line), True)], found)

    def test_a_forbidden_command_split_across_lines_is_refused(self):
        found = self.proof("Declare\n  ML (* c *) Module \"x\".\nAdd\nLoadPath \"y\" as Y.\n")
        self.assertEqual(sorted(str(f).split(": ")[0].rsplit(":", 1)[-1] for f in found), ["1", "3"], found)

    def test_a_token_that_rocq_lexes_otherwise_is_refused(self):
        """A notation token holding a '(' or a '"' can make Rocq read as code what these rules take for a comment or
        a string; such a token, and a comment right after '.', '`' or ':', are refused."""
        for body in ('Notation "<(*" := 0 (at level 0).\nDefinition a := <(*.\nLoad "cheat".\n',
                     'Notation "<""" := 0 (at level 0).\nDefinition a := <".\nLoad "cheat".\n',
                     'Notation "*" := tt (at level 0).\nDefinition a := `(*).\nLoad "cheat".\n'):
            with self.subTest(body=body):
                found = [str(f) for f in self.proof(body)]
                self.assertEqual([f.split(": ")[0].rsplit(":", 1)[-1] for f in found],
                                 ["2" if "`" in body else "1"], found)
        self.assertEqual(self.proof('Local Notation "\'HBF.(\' f \')\'" := (f) (at level 0).\n'), [])

    def test_a_rocq_file_with_a_nul_byte_is_refused(self):
        found = self.proof('(* \0 *)\nLoad "cheat".\n')
        self.assertEqual([f.msg.split(" (")[0] for f in found], ["a Rocq file that is not read as text"], found)

    def test_a_generated_rocq_file_that_would_read_a_file_is_refused(self):
        with tree() as t:
            path = "projects/zlib/checksum_fuzzer/Statements.v"
            t.write(path, t.read(path) + 'Load "x".\nDefinition y := Load.\n')
            found = [str(f) for f in t.lint() if f.rule == "proofs" and path in str(f)]
        self.assertEqual(len(found), 1, found)
        self.assertIn("'Load' is not allowed in a file of projects/", found[0])


# a contract file of zlib/checksum_fuzzer (old layout), and the build plain's symbol fact the ContractLiterals tests
# give it, in place of the fixture's: (name, kind, address, size)
CONTRACT = "proofs/zlib/checksum_fuzzer/lib/Prog/pcap_source_next_c.v"
CONTRACT_FACT = [("_start", "func", 0x11260, 0), ("pcap_source_next", "func", 0x132a0, 896),
                 ("dummy", "func", 0x13620, 4), ("dummy", "func", 0x13624, 4), (".text", "section", 0x11260, 0xb000),
                 ("stderr", "object", 0x1d800, 224), (".data", "section", 0x1d800, 0xe0),
                 (".got", "section", 0x1d8e0, 152), (".got", "section", 0x1d978, 8), (".bss", "section", 0x1e000, 64)]
# the harness theory of the contract's fuzz target, in the fixture's namespace (its release.yaml names none)
HARNESS_THEORY = names.rocq_harness(names.NAMESPACE_DEFAULT, "zlib", "checksum_fuzzer")
# the imports a contract writes before its first definition, so a definition below is on line 3
CONTRACT_HEAD = ("From Stdlib Require Import ZArith.\n"
                 "From %s Require Import Symbols.\n" % HARNESS_THEORY)


def put_contract_fact(t, rows=CONTRACT_FACT, build="plain"):
    """Write zlib/checksum_fuzzer's symbol fact of build, of the binary harness.yaml pins, with rows (name, kind,
    address, size) and stand-in hashes."""
    pin = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")["builds"][build]["sha256"]
    symbols.write(t.path(layout.symbol_fact("zlib", "checksum_fuzzer", build)),
                  [symbols.Sym(n, k, a, s, "1f" * 32 if s else "-", "2e" * 32 if k == "func" and s else "-", "-")
                   for n, k, a, s in rows], pin)


class ContractLiterals(unittest.TestCase):
    """contract-literals: a contract file (lib/Prog/**/<fn>_c.v, or under lib/U/, lib/A/ or lib/B/) of a fuzz target
    with a symbol fact names each address from Symbols.v, never as a numeral (hexadecimal or decimal) inside an
    allocated section of one of its builds, and names only what the build's Symbols.v defines (spec R3, A2)."""

    def lint(self, files, fact=True, more=(), **kw):
        """The contract-literals findings of the fixture with files ({path: text}, or the text of CONTRACT) written,
        and the plain symbol fact CONTRACT_FACT, or none at all, and more [(build, rows)] facts."""
        if isinstance(files, str):
            files = {CONTRACT: files}
        with tree() as t:
            if fact:
                put_contract_fact(t)
            else:
                os.remove(t.path(layout.symbol_fact("zlib", "checksum_fuzzer", "plain")))
            for build, rows in more:
                put_contract_fact(t, rows, build)
            for rel, text in files.items():
                t.write(rel, text)
            t.generate()
            return [str(f) for f in t.lint(**kw) if f.rule == "contract-literals"]

    @staticmethod
    def found(line, msg, rel=CONTRACT):
        return "contract-literals %s:%d: %s" % (rel, line, msg)

    def test_an_entry_address_in_a_contract_is_refused(self):
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition PCAP_SOURCE_NEXT : Z := 0x132a0.\n"),
                         [self.found(3, "0x132a0 is inside .text of plain: name it from Symbols")])
        for literal in ("0X132A0", "0x1_32a0", "0x11260", "0x1c25f"):   # .text is [0x11260, 0x1c260)
            with self.subTest(literal=literal):
                self.assertEqual(self.lint(CONTRACT_HEAD + "Definition A : Z := (%s + 4)%%Z.\n" % literal),
                                 [self.found(3, "%s is inside .text of plain: name it from Symbols" % literal)])

    def test_a_decimal_address_is_refused_too(self):
        """Spec A2: no literal address, in any base.  78496 is 0x132a0, inside .text; a decimal numeral is read whole,
        fraction and exponent (rocq 9.2: 784.96e2 is 78496 in Q), with the hexadecimal rule's exclusions: an integer
        no allocated section holds, a value with a fraction left, a numeral inside a name, a comment or a string."""
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition E : Z := 78496.\nDefinition F : Z := (78_496 + 4)%Z.\n"
                                   "Definition G : Q := 784.96e2.\nDefinition H : Q := 7849600e-2.\n"),
                         [self.found(3, "78496 is inside .text of plain: name it from Symbols"),
                          self.found(4, "78_496 is inside .text of plain: name it from Symbols"),
                          self.found(5, "784.96e2 is inside .text of plain: name it from Symbols"),
                          self.found(6, "7849600e-2 is inside .text of plain: name it from Symbols")])
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition A : Z := 65536.\nDefinition B : Z := 115296.\n"
                                   "Definition C : Q := 78496.5.\nDefinition D : Q := 7849.6.\n"
                                   "Definition A_78496 : Z := 8.\n(* 78496 *)\nDefinition S := \"78496\".\n"
                                   "Definition T : Q := 1e99999999999999999999.\nDefinition U : Z := %s.\n"
                                   % ("7" * 5000)), [])

    def test_a_literal_inside_data_is_refused(self):
        """A data object, and a GOT slot, which no symbol names: each is inside an allocated section."""
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition A_STDERR : Z := 0x1d800.\n"
                                   "Definition A_GOT_STDERR : Z := 0x1d920.\n"),
                         [self.found(3, "0x1d800 is inside .data of plain: name it from Symbols"),
                          self.found(4, "0x1d920 is inside .got of plain: name it from Symbols")])

    def test_a_constant_no_section_holds_passes(self):
        """A division's magic multiplier, a float's bits, a stack bound and the first byte past .text are inside no
        allocated section of any build: they are no address Symbols.v could name."""
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition D : Z := 0xcccccccd.\n"
                                   "Definition E : Z := 0xe38e38e38e38e38f.\nDefinition F : Z := 0x40b7700000000000.\n"
                                   "Definition G : Z := 0x7fffa000.\nDefinition H : Z := 0x1c260.\n"), [])

    def test_the_image_base_passes_when_no_section_holds_it(self):
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition IMG_LO : Z := 0x10000.\n"), [])

    def test_a_section_of_any_build_with_a_symbol_fact_counts(self):
        """A literal inside a section of the ubsan build is refused in a plain contract too; the message names the
        first build, in the fixed order plain, ubsan, asan, asan-ubsan, whose section holds it."""
        ubsan = [("main", "func", 0x20000, 16), (".text", "section", 0x20000, 0x1000)]
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition A : Z := 0x20010.\nDefinition B : Z := 0x132a0.\n",
                                   more=[("ubsan", ubsan)]),
                         [self.found(3, "0x20010 is inside .text of ubsan: name it from Symbols"),
                          self.found(4, "0x132a0 is inside .text of plain: name it from Symbols")])

    def test_a_tls_section_yields_to_the_section_its_addresses_overlap(self):
        """A .tbss's addresses are a template's and overlap the sections after it: a literal in both is named by the
        section that starts last."""
        rows = CONTRACT_FACT + [(".tbss", "section", 0x1c260, 0x100), (".init_array", "section", 0x1c270, 8)]
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition A : Z := 0x1c270.\nDefinition B : Z := 0x1c260.\n",
                                   more=[("plain", rows)]),
                         [self.found(3, "0x1c270 is inside .init_array of plain: name it from Symbols"),
                          self.found(4, "0x1c260 is inside .tbss of plain: name it from Symbols")])

    def test_a_symbols_reference_is_clean(self):
        self.assertEqual(self.lint(CONTRACT_HEAD
                                   + "Definition PCAP_SOURCE_NEXT : Z := Symbols.Plain.s_pcap_source_next.\n"), [])

    def test_every_namespace_of_symbols_v_is_read(self):
        """Symbols.v defines the address and the size of each function, of size 0 too, and of each data object, and
        in Sec those of each allocated section: a reference to any of them is clean."""
        self.assertEqual(self.lint(CONTRACT_HEAD
                                   + "Definition NEXT_SIZE : Z := Symbols.Plain.Size.s_pcap_source_next.\n"
                                   "Definition START : Z := Symbols.Plain.s__start.\n"
                                   "Definition A_STDERR : Z := Symbols.Plain.s_stderr + 8.\n"
                                   "Definition BSS : Z := Symbols.Plain.Sec.s_bss + 0x40.\n"
                                   "Definition BSS_SIZE : Z := Symbols.Plain.Sec.Size.s_bss.\n"), [])

    def test_an_address_in_a_comment_is_clean(self):
        self.assertEqual(self.lint(CONTRACT_HEAD + "(* pcap_source_next was at 0x132a0 in 1.8.0 *)\n"
                                   'Definition note := "0x132a0".\n'), [])

    def test_a_small_constant_is_clean(self):
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition NEXT_K : Z := 5744.\nDefinition M : Z := 0xffff.\n"
                                   "Definition A_0x132a0 : Z := 0.\n"), [])

    def test_a_harness_without_a_symbol_fact_is_not_judged(self):
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition PCAP_SOURCE_NEXT : Z := 0x132a0.\n"
                                   "Definition GONE : Z := Symbols.Plain.s_gone.\n", fact=False), [])

    def test_a_symbol_the_map_lacks_is_refused(self):
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition GONE : Z := Symbols.Plain.s_gone.\n"),
                         [self.found(3, "plain has no symbol s_gone")])

    def test_a_size_or_a_section_the_map_lacks_is_refused(self):
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition A : Z := Symbols.Plain.Size.s_gone.\n"
                                   "Definition B : Z := Symbols.Plain.Sec.s_rodata.\n"
                                   "Definition C : Z := Symbols.Plain.Sec.Size.s_pcap_source_next.\n"),
                         [self.found(3, "plain has no symbol Size.s_gone"),
                          self.found(4, "plain has no symbol Sec.s_rodata"),
                          self.found(5, "plain has no symbol Sec.Size.s_pcap_source_next")])

    def test_a_name_two_symbols_share_has_no_identifier(self):
        """musl's static dummy is two functions of the build, so Symbols.v gives it no identifier (names.rocq_idents);
        the same for two sections of one name."""
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition DUMMY : Z := Symbols.Plain.s_dummy.\n"
                                   "Definition GOT : Z := Symbols.Plain.Sec.s_got.\n"),
                         [self.found(3, "plain has no symbol s_dummy: dummy names two or more functions or objects "
                                        "of plain, so Symbols.v gives it no identifier"),
                          self.found(4, "plain has no symbol Sec.s_got: .got names two or more sections of plain, so "
                                        "Symbols.v gives it no identifier")])

    def test_a_build_without_a_symbol_fact_has_no_module(self):
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition A : Z := Symbols.Asan.s_pcap_source_next.\n"),
                         [self.found(3, "asan has no symbol fact: Symbols.v has no module Asan")])

    def test_the_forms_a_reference_is_written_in(self):
        """A reference is read qualified (Symbols.Plain.s_x, also under its library's path) and, after Require Import
        Symbols, as Plain.s_x; Plain.<name> of any other module (the image's Plain.M) is no reference."""
        self.assertEqual(self.lint(CONTRACT_HEAD
                                   + "Definition A : Z := %s.Symbols.Plain.s_gone.\n" % HARNESS_THEORY
                                   + "Definition B : Z := Plain.s_gone + Plain.s_pcap_source_next.\n"
                                   "Definition C : Z := Plain.Sec.Size.s_gone.\n"
                                   "Definition D := Plain.M.loaded_segments.\n"),
                         [self.found(3, "plain has no symbol s_gone"), self.found(4, "plain has no symbol s_gone"),
                          self.found(5, "plain has no symbol Sec.Size.s_gone")])

    def test_a_name_split_by_blanks_or_comments_is_read_whole(self):
        """Rocq reads `Symbols.Plain\n  .s_x`, `Symbols.Plain (* c *).s_x` and `Symbols .Plain .Sec .s_x` as the one
        name Symbols.Plain.s_x (rocq 9.2 compiles each): blanks and comments may stand before each `.field`."""
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition A : Z := Symbols.Plain\n  .s_gone.\n"
                                   "Definition B : Z := Symbols.Plain (* c *).s_gone.\n"
                                   "Definition C : Z := Symbols .Plain .Sec .s_gone.\n"
                                   "Definition D : Z := Symbols.Plain\n  .s_pcap_source_next.\n"
                                   "Definition E : Z := Plain (* c *)\n  .s_gone.\n"),
                         [self.found(3, "plain has no symbol s_gone"), self.found(5, "plain has no symbol s_gone"),
                          self.found(6, "plain has no symbol Sec.s_gone"), self.found(9, "plain has no symbol s_gone")])

    def test_a_longer_path_under_a_defined_name_is_refused(self):
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition A : Z := Symbols.Plain.s_pcap_source_next.s_gone.\n"
                                   "Definition B : Z := Plain.s_pcap_source_next.s_gone.\n"
                                   "Definition C : Z := Symbols.Plain.Sec.s_bss.Size.\n"),
                         [self.found(3, "plain has no symbol s_pcap_source_next.s_gone"),
                          self.found(4, "plain has no symbol s_pcap_source_next.s_gone"),
                          self.found(5, "plain has no symbol Sec.s_bss.Size")])

    def test_a_hexadecimal_numeral_is_read_whole(self):
        """A hexadecimal numeral has a fraction and a binary exponent too (rocq 9.2: 0x1.32ap16 is 78496 in Q):
        its value decides, and one that is not an integer is no address.  An exponent far past any address is read
        without computing its power of two, which would not fit in memory (1 << 10**17 is a MemoryError), and one of
        5000 digits without int(), which refuses more than 4300 decimal digits."""
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition A : Q := 0x1.32ap16.\nDefinition B : Q := 0x2654p3.\n"
                                   "Definition C : Q := 0x132a0.0p-16.\nDefinition D : Q := 0x132a0.8p0.\n"
                                   "Definition E : Q := 0x1p99999999999999999.\n"
                                   "Definition F : Q := 0x1p-99999999999999999.\n"
                                   "Definition G : Z := 0x132a0.\nDefinition H : Q := 0x1p%s.\n" % ("1" * 5000)),
                         [self.found(3, "0x1.32ap16 is inside .text of plain: name it from Symbols"),
                          self.found(4, "0x2654p3 is inside .text of plain: name it from Symbols"),
                          self.found(9, "0x132a0 is inside .text of plain: name it from Symbols")])

    def test_a_padded_exponent_is_read_by_its_value(self):
        """Zeros before an exponent's digits change nothing (rocq 9.2: each numeral below is 78496 in Q), so they do
        not count toward the exponent-length guard, with either sign."""
        self.assertEqual(self.lint(CONTRACT_HEAD + "Definition A : Q := 0x132a0p0000000000000000000.\n"
                                   "Definition B : Q := 0x1.32ap0000000000000000016.\n"
                                   "Definition C : Q := 0x132a00p-0000000000000000000004.\n"),
                         [self.found(3, "0x132a0p0000000000000000000 is inside .text of plain: name it from Symbols"),
                          self.found(4, "0x1.32ap0000000000000000016 is inside .text of plain: name it from Symbols"),
                          self.found(5, "0x132a00p-0000000000000000000004 is inside .text of plain: name it from "
                                        "Symbols")])

    def test_only_contract_files_are_judged(self):
        body = CONTRACT_HEAD + "Definition A : Z := 0x132a0.\n"
        lib = "proofs/zlib/checksum_fuzzer/lib/"
        judged = [lib + p for p in ("A/Prog/memcmp_c.v", "B/Prog/memcmp_c.v", "Prog/CF/cf_next_c.v",
                                    "Prog/pcap_source_next_c.v", "U/Prog/pcap_source_next_c.v")]
        files = dict.fromkeys(judged + [lib + p for p in ("Prog/StdioModel.v", "Lib/Mem_c.v", "X/Prog/memcmp_c.v",
                                                          "Prog/c.v")], body)
        serial = self.lint(files, jobs=1)
        self.assertEqual(sorted(serial), [self.found(3, "0x132a0 is inside .text of plain: name it from Symbols", rel)
                                          for rel in judged])
        self.assertEqual(self.lint(files, jobs=4), serial)

    def test_a_contract_file_in_the_per_project_layout_is_judged(self):
        rel = "projects/zlib/checksum_fuzzer/proofs/lib/Prog/pcap_source_next_c.v"
        self.assertEqual(self.lint({rel: CONTRACT_HEAD + "Definition A : Z := 0x132a0.\n"}),
                         [self.found(3, "0x132a0 is inside .text of plain: name it from Symbols", rel)])


class Licence(unittest.TestCase):
    """A proof file's licence lines agree with NOTICE: Anthropic's copyright and Apache-2.0 OR MIT together, in a fuzz
    target whose build record lists the three texts of that licence, or MIT for a file written here.  In the old layout
    (proofs/<p>/<h>/); LicencePerProject runs every test in the per-project one (projects/<p>/<h>/proofs/)."""
    LAYOUT = layout.OLD
    ANTHROPIC = "(* Copyright 2026 Anthropic PBC *)\n(* SPDX-License-Identifier: %s *)\n"

    def lib(self, harness="checksum_fuzzer", project="zlib"):
        """A fuzz target's proof library folder, with a slash, in the layout of the test."""
        return layout.proof_lib_dir(project, harness, self.LAYOUT) + "/"

    def proofs(self, harness="checksum_fuzzer", project="zlib"):
        """A fuzz target's proofs folder, with a slash, in the layout of the test."""
        return layout.proofs_dir(project, harness, self.LAYOUT) + "/"

    @property
    def LIB(self):
        return self.lib()

    @property
    def RECORD(self):
        return layout.record_path("zlib", "checksum_fuzzer", self.LAYOUT)

    def at(self, name):
        """The path of name: as it is when it is one (under proofs/ or projects/), else under zlib/checksum_fuzzer's
        proof library."""
        return name if name.startswith(("proofs/", "projects/")) else self.LIB + name

    @contextlib.contextmanager
    def tree(self):
        """A fixture tree in the layout of the test: ported, as `oft port-layout` ports it, for the per-project one."""
        with tree() as t:
            if self.LAYOUT == layout.NEW:
                self.assertEqual(port.port_worktree(t.root, out=io.StringIO()), 0)
            yield t

    def licence(self, files, texts=lint.ANTHROPIC_TEXTS, **kw):
        """The licence findings, as (where, message), of lint with kw on a tree with files (name under lib/ -> text)
        and a build record that lists texts."""
        with self.tree() as t:
            t.write(self.RECORD, build_record(proofs={"licence": "Apache-2.0 OR MIT", "texts": list(texts)}))
            for name, text in files.items():
                t.write(self.at(name), text + "Definition x := 0.\n")
            return sorted((f.where.replace(self.LIB, ""), f.msg) for f in t.lint(**kw) if f.rule == "licence")

    def test_the_tree_is_in_the_layout_of_the_test(self):
        with self.tree() as t:
            t.write(self.LIB + "A.v", "Definition x := 0.\n")
            self.assertEqual((layout.of_tree(t.root), layout.of_path(self.LIB + "A.v")), (self.LAYOUT, self.LAYOUT))

    def test_anthropic_lines_with_the_record_and_a_file_written_here_pass(self):
        self.assertEqual(self.licence({
            "Kept.v": self.ANTHROPIC % "Apache-2.0 OR MIT",
            "Changed.v": self.ANTHROPIC % "Apache-2.0 OR MIT" + "(* Modified by Theorem Labs, 2026-10: ported *)\n",
            "Low.v": "(* a *)\n" * 8 + self.ANTHROPIC % "Apache-2.0 OR MIT",   # lines 9 and 10: still the head
            "Ours.v": "(* SPDX-License-Identifier: MIT *)\n",
            "NoLines.v": "",
            "Data.v": "(* Machine-generated data computed from the task's compiled program image. *)\n"}), [])

    def test_a_licence_line_in_any_comment_style_is_read(self):
        found = self.licence({"Block.v": "(*\n * SPDX-License-Identifier: GPL-2.0-only\n *)\n",
                              "Bare.v": "(*\n   SPDX-License-Identifier: GPL-2.0-only\n*)\n",
                              "After.v": "(* x *) (* SPDX-License-Identifier: GPL-2.0-only *)\n"})
        self.assertEqual([w for w, _ in found], ["After.v:1", "Bare.v:2", "Block.v:2"])
        self.assertTrue(all("is neither licence" in m for _, m in found), found)

    def test_apache_alone_under_anthropic_copyright_is_refused(self):
        found = self.licence({"Old.v": self.ANTHROPIC % "Apache-2.0", "Rev.v": self.ANTHROPIC % "MIT OR Apache-2.0"})
        self.assertEqual([w for w, _ in found], ["Old.v:2", "Rev.v:2"])
        self.assertTrue(all("is neither licence" in m for _, m in found), found)

    def test_licence_lines_below_the_head_are_refused(self):
        found = self.licence({"Late.v": "(* a *)\n" * 9 + self.ANTHROPIC % "Apache-2.0",
                              "LateCopy.v": "(* a *)\n" * 10 + "(* Copyright 2026 Anthropic PBC *)\n",
                              "Indented.v": "(* a *)\n" * 10 + "  (* SPDX-License-Identifier: GPL-3.0-only *)\n",
                              "InComment.v": "(* a *)\n" * 10
                                             + "(* about\n   SPDX-License-Identifier: GPL-3.0-only *)\n",
                              "LateBlock.v": "(* a *)\n" * 10 + "(*\n * SPDX-License-Identifier: GPL-3.0-only\n *)\n",
                              "LateCopyBlock.v": "(* a *)\n" * 10 + "(*\n * Copyright 2026 Anthropic PBC\n *)\n"})
        self.assertEqual([w for w, _ in found], ["InComment.v:12", "Indented.v:11", "Late.v:11", "LateBlock.v:12",
                                                 "LateCopy.v:11", "LateCopyBlock.v:12"])
        self.assertTrue(all("opens the file" in m for _, m in found), found)

    def test_one_licence_line(self):
        found = self.licence({"Two.v": self.ANTHROPIC % "Apache-2.0 OR MIT" + "(* SPDX-License-Identifier: MIT *)\n",
                              "MitThenBlock.v": "(* SPDX-License-Identifier: MIT *)\n"
                                                "(*\n * SPDX-License-Identifier: GPL-2.0-only\n *)\n"})
        self.assertEqual(found, [("MitThenBlock.v:3", "a proof file has one licence: this tag says 'GPL-2.0-only', "
                                                      "the first one 'MIT'"),
                                 ("Two.v:3", "a proof file has one licence: this tag says 'MIT', the first one "
                                             "'Apache-2.0 OR MIT'")])

    def test_a_second_tag_that_restates_the_licence_is_allowed(self):
        restated = (self.ANTHROPIC % "Apache-2.0 OR MIT"
                    + "(* Modified by Theorem Labs, 2026-10: a doc comment that restates the notice. *)\n"
                    "(** The initial memory of the image.\n"
                    "    Copyright 2026 Anthropic PBC; SPDX-License-Identifier: Apache-2.0 OR MIT.\n"
                    "    Its generic lemmas keep their notices. *)\n")
        found = self.licence({"Restated.v": restated,
                              "Again.v": self.ANTHROPIC % "Apache-2.0 OR MIT"
                                         + "(* SPDX-License-Identifier:  Apache-2.0 OR MIT *)\n",
                              "MitTwice.v": "(* SPDX-License-Identifier: MIT *)\n"
                                            "(** SPDX-License-Identifier: MIT. *)\n",
                              "Other.v": self.ANTHROPIC % "Apache-2.0 OR MIT"
                                         + "(** SPDX-License-Identifier: Apache-2.0. *)\n"})
        self.assertEqual([w for w, _ in found], ["Other.v:3"])
        self.assertIn("this tag says 'Apache-2.0.'", found[0][1])

    def test_a_file_with_crlf_line_ends_is_read_as_one_with_line_feeds(self):
        crlf = lambda text: text.replace("\n", "\r\n")
        self.assertEqual(self.licence({"Kept.v": crlf(self.ANTHROPIC % "Apache-2.0 OR MIT"),
                                       "Block.v": crlf("(*\n   SPDX-License-Identifier: MIT\n*)\n")}), [])

    def test_a_changed_anthropic_copyright_line_below_the_head_is_refused(self):
        found = self.licence({"LateChanged.v": "(* a *)\n" * 39 + "(* Copyright (c) 2026 Anthropic PBC *)\n",
                              "LateLower.v": "(* a *)\n" * 10 + "(* copyright 2026 anthropic *)\n"})
        self.assertEqual([w for w, _ in found], ["LateChanged.v:40", "LateLower.v:11"])
        self.assertTrue(all("opens the file" in m for _, m in found), found)

    def test_a_changed_anthropic_copyright_line_beside_the_kept_one_is_refused(self):
        found = self.licence({"Both.v": "(* Copyright 2026 Anthropic PBC *)\n(* Copyright (c) 2026 Anthropic PBC *)\n"
                                        "(* SPDX-License-Identifier: Apache-2.0 OR MIT *)\n",
                              "BothLow.v": self.ANTHROPIC % "Apache-2.0 OR MIT" + "(* a *)\n" * 5
                                           + "(* (c) copyright 2026 anthropic, Theorem Labs *)\n",
                              "Words.v": self.ANTHROPIC % "Apache-2.0 OR MIT"
                                         + "(** Copyright 2026 Anthropic PBC and Theorem Labs. *)\n",
                              "Pair.v": self.ANTHROPIC % "Apache-2.0 OR MIT"
                                        + "(** Copyright 2026 Anthropic PBC; Copyright (c) 2026 Anthropic. *)\n"})
        self.assertEqual([w for w, _ in found], ["Both.v:2", "BothLow.v:8", "Pair.v:3", "Words.v:3"])
        self.assertTrue(all("unchanged" in m for _, m in found), found)

    def test_a_file_of_a_programs_words_or_data_has_no_other_licence_lines(self):
        data = "(* Machine-generated data computed from the task's compiled program image. *)\n"
        words = "(* This file states or restates instruction words of the task's compiled program. *)\n"
        found = self.licence({"DataMit.v": data + "(* SPDX-License-Identifier: MIT *)\n",
                              "DataBlock.v": data + "(*\n * SPDX-License-Identifier: MIT\n *)\n",
                              "DataCopy.v": data + "(* Copyright 2026 Anthropic PBC *)\n",
                              "WordsAnthropic.v": words + self.ANTHROPIC % "Apache-2.0 OR MIT"})
        self.assertEqual([w for w, _ in found], ["DataBlock.v:3", "DataCopy.v", "DataMit.v:2", "WordsAnthropic.v:3"])
        self.assertTrue(all("keeps the program's licences" in m for _, m in found), found)

    def test_anthropic_copyright_needs_anthropic_licence(self):
        found = self.licence({"Mit.v": self.ANTHROPIC % "MIT", "Bare.v": "(* Copyright 2026 Anthropic PBC *)\n"})
        self.assertEqual([w for w, _ in found], ["Bare.v", "Mit.v:2"])
        self.assertTrue(all("Apache-2.0 OR MIT" in m for _, m in found), found)

    def test_anthropic_licence_needs_anthropic_copyright(self):
        found = self.licence({"Claim.v": "(* SPDX-License-Identifier: Apache-2.0 OR MIT *)\n",
                              "Cc.v": "(* Copyright (c) 2026 Anthropic PBC *)\n"
                                      "(* SPDX-License-Identifier: Apache-2.0 OR MIT *)\n"})
        self.assertEqual([w for w, _ in found], ["Cc.v:2", "Claim.v:1"])

    def test_a_changed_anthropic_copyright_line_is_refused(self):
        # requirement 7 keeps Anthropic's lines unchanged; a changed one must not read as no Anthropic line at all
        found = self.licence({"Var.v": "(* Copyright (c) 2026 Anthropic PBC *)\n(* SPDX-License-Identifier: MIT *)\n",
                              "Dot.v": "(* Copyright 2026 Anthropic PBC. *)\n(* SPDX-License-Identifier: MIT *)\n",
                              "Range.v": "(* Copyright 2025-2026 Anthropic PBC *)\n",
                              "Lower.v": "(* copyright 2026 Anthropic PBC *)\n(* SPDX-License-Identifier: MIT *)\n",
                              "DataVar.v": "(* Machine-generated data computed from the task's compiled program "
                                           "image. *)\n(* Copyright (c) 2026 Anthropic PBC *)\n"})
        self.assertEqual([w for w, _ in found], ["DataVar.v:2", "Dot.v:1", "Lower.v:1", "Range.v:1", "Var.v:1"])
        self.assertTrue(all("unchanged" in m for _, m in found), found)

    def test_a_shared_library_file_is_no_fuzz_targets_and_the_licence_rule_does_not_read_it(self):
        # proofs/lib/ has no place in either layout: the paths rule refuses every file in it (paths.py admits none)
        with self.tree() as t:
            t.write("proofs/lib/Common.v", self.ANTHROPIC % "Apache-2.0 OR MIT" + "Definition x := 0.\n")
            found = [(f.rule, f.where) for f in t.lint() if "proofs/lib/" in f.where]
        self.assertIn(("paths", "proofs/lib/Common.v"), found)
        self.assertNotIn("licence", [rule for rule, _ in found])

    def test_anthropic_licence_needs_a_record_that_lists_all_three_texts(self):
        found = self.licence({"Kept.v": self.ANTHROPIC % "Apache-2.0 OR MIT"}, texts=lint.ANTHROPIC_TEXTS[:2])
        self.assertEqual([w for w, _ in found], ["Kept.v:2"])
        self.assertIn(self.RECORD, found[0][1])

    def test_a_contributors_pull_request_is_not_held_to_the_record_but_to_the_lines(self):
        # the maintainer writes the build record before it merges (docs/adding-a-proof.md, requirement 7)
        files = {"Kept.v": self.ANTHROPIC % "Apache-2.0 OR MIT", "Old.v": self.ANTHROPIC % "Apache-2.0"}
        found = self.licence(files, texts=(), pr_kind="contributor")
        self.assertEqual([w for w, _ in found], ["Old.v:2"])
        self.assertEqual([w for w, _ in self.licence(files, texts=(), pr_kind="maintainer")], ["Kept.v:2", "Old.v:2"])

    def test_a_changed_build_record_rereads_the_files_it_licenses(self):
        # --changed-only: dropping a text from the record must refuse a proof file that did not change
        with self.tree() as t:
            t.write(self.RECORD, build_record(proofs={"texts": list(lint.ANTHROPIC_TEXTS)}))
            t.write(self.LIB + "Kept.v", self.ANTHROPIC % "Apache-2.0 OR MIT" + "Definition x := 0.\n")
            PerFileScope.commit(self, t)   # the base --changed-only compares with
            t.write(self.RECORD, build_record(proofs={"texts": list(lint.ANTHROPIC_TEXTS[1:])}))
            err = io.StringIO()
            with contextlib.redirect_stderr(err):
                found = [f.where for f in t.lint(changed_only="HEAD") if f.rule == "licence"]
        self.assertEqual(found, [self.LIB + "Kept.v:2"], err.getvalue())

    # A licence-pending entry in lint-exceptions.yaml: the licence findings of its unit are reported as pending and do
    # not fail, until the series that applies the unit's licence lines removes the entry.
    TODAY = datetime.date(2026, 10, 30)
    GPL = "(* SPDX-License-Identifier: GPL-2.0-only *)\nDefinition x := 0.\n"
    NOT_EXACT = ("an exception for licence-pending %s must have exactly unit (<project>/<fuzz target>), rule, due "
                 "(YYYY-MM-DD), series (pending or #<number>) and reason, once per unit")

    @staticmethod
    def pending_entry(unit="zlib/checksum_fuzzer", **changes):
        return dict({"unit": unit, "rule": "licence-pending", "due": "2026-10-31", "series": "pending",
                     "reason": "its licence lines are applied in its own series"}, **changes)

    def write_pending(self, t, files, entries):
        """Write files (a name under lib/, or a path, -> text), a build record that lists the three texts, and
        lint-exceptions.yaml with entries."""
        t.write(self.RECORD, build_record(proofs={"licence": "Apache-2.0 OR MIT",
                                                  "texts": list(lint.ANTHROPIC_TEXTS)}))
        for name, text in files.items():
            t.write(self.at(name), text)
        t.put_yaml(lint.EXCEPTIONS, {"schema": "oss-fuzz-theorems/lint-exceptions/1", "exceptions": entries})

    def pending(self, files, entries, today=TODAY, **kw):
        """(the failing findings of the licence rule and on lint-exceptions.yaml, the pending findings) of lint with kw
        on a tree with files and entries (write_pending), as str with lib/'s path cut."""
        with self.tree() as t:
            self.write_pending(t, files, entries)
            held = []
            found = t.lint(pending=held, today=today, **kw)
        cut = lambda fs: sorted(str(f).replace(self.LIB, "") for f in fs)
        return cut(f for f in found if f.rule == "licence" or f.where == lint.EXCEPTIONS), cut(held)

    def test_a_listed_units_licence_findings_are_pending_and_do_not_fail(self):
        other = self.lib("api-driver") + "Other.v"
        files = {"Gpl.v": self.GPL, "Copy.v": self.GPL, other: self.GPL}
        failing, held = self.pending(files, [])
        self.assertEqual([f.split(":")[0] for f in failing], ["licence Copy.v", "licence Gpl.v", "licence " + other])
        self.assertEqual(held, [])
        failing, held = self.pending(files, [self.pending_entry()])
        self.assertEqual([f.split(":")[0] for f in failing], ["licence " + other])   # another unit's finding fails
        self.assertEqual([f.split(":")[0] for f in held], ["licence Copy.v", "licence Gpl.v"])
        self.assertIn("is neither licence", held[1])

    def test_a_pending_entry_whose_unit_has_no_licence_finding_fails(self):
        """A series named `pending` waits for nothing in particular, so an entry for a unit with no licence finding is
        a finding at once; one named for the pull request that brings the unit's files waits for it (below)."""
        failing, held = self.pending({"Clean.v": "Definition x := 0.\n"}, [self.pending_entry()])
        self.assertEqual((failing, held), (["paths %s: unit zlib/checksum_fuzzer has no licence finding: its licence "
                                            "series pending removes its licence-pending entry" % lint.EXCEPTIONS], []))

    def test_a_pending_entry_past_its_due_date_fails(self):
        expired = "paths %s: unit zlib/checksum_fuzzer: its licence series pending was due 2026-10-31" % lint.EXCEPTIONS
        for today, want in ((datetime.date(2026, 10, 31), []), (datetime.date(2026, 11, 1), [expired])):
            with self.subTest(today=today):
                failing, held = self.pending({"Gpl.v": self.GPL}, [self.pending_entry()], today=today)
                self.assertEqual(failing, want)
                self.assertEqual(len(held), 1)   # its findings stay pending: the one failure is the entry's
        # without a date given, lint takes today's date in UTC: here a clock whose UTC date is a day past its local one
        class Clock(datetime.datetime):
            @classmethod
            def now(cls, tz=None):
                utc = datetime.datetime(2031, 1, 2, 0, 30, tzinfo=datetime.timezone.utc)
                return utc.astimezone(tz) if tz is not None else datetime.datetime(2031, 1, 1, 14, 30)
        with mock.patch.object(lint.datetime, "datetime", Clock):
            self.assertEqual(lint.utc_today(), datetime.date(2031, 1, 2))
        failing, _ = self.pending({"Gpl.v": self.GPL}, [self.pending_entry(due="2000-01-01")], today=None)
        self.assertEqual(failing, [expired.replace("2026-10-31", "2000-01-01")])

    ADDED = ("paths %s: unit %s: a licence-pending entry that the base does not have, in a pull request that changes "
             "proof files: a tools pull request adds an entry, and review judges it")

    def committed(self, base):
        """base's root, made a git checkout of one commit, HEAD: the pending base reads HEAD's entries through git."""
        PerFileScope.commit(self, base)
        return base.root

    def test_a_proof_pull_request_adds_no_pending_entry_for_any_unit(self):
        """A pull request that changes a file of a fuzz target's proofs folder adds no licence-pending entry, for a
        unit with proofs in the base or for one whose first proofs it brings."""
        new = self.lib("api-driver") + "New.v"
        record = layout.record_path("zlib", "api-driver", self.LAYOUT)
        with self.tree() as base, self.tree() as head:
            self.write_pending(base, {"Gpl.v": self.GPL}, [])
            base.write(record, build_record(proofs={"texts": list(lint.ANTHROPIC_TEXTS)}))   # no proofs yet
            self.write_pending(head, {"Gpl.v": self.GPL, new: self.GPL},
                               [self.pending_entry(), self.pending_entry("zlib/api-driver")])
            head.write(record, build_record(proofs={"texts": list(lint.ANTHROPIC_TEXTS)}))
            held = []
            found = head.lint(changed=[lint.EXCEPTIONS, new], pending_base=self.committed(base), pending=held,
                              today=self.TODAY)
            self.assertEqual([str(f) for f in found if f.rule == "licence" or f.where == lint.EXCEPTIONS],
                             [self.ADDED % (lint.EXCEPTIONS, u) for u in ("zlib/api-driver", "zlib/checksum_fuzzer")])
            self.assertEqual(len(held), 2)   # the findings stay pending: what fails is each added entry

    def test_a_tools_pull_request_adds_pending_entries_for_any_unit(self):
        """A pull request that changes no proof file adds entries, for a unit with proofs in the base and for one with
        none yet; its review judges them."""
        with self.tree() as base, self.tree() as head:
            self.write_pending(base, {"Gpl.v": self.GPL}, [])
            self.write_pending(head, {"Gpl.v": self.GPL},
                               [self.pending_entry(), self.pending_entry("zlib/api-driver")])
            head.write("tools/oft/README.md", "the rule\n")
            held = []
            found = head.lint(changed=[lint.EXCEPTIONS, "tools/oft/README.md"], pending_base=self.committed(base),
                              pending=held, today=self.TODAY)
            self.assertEqual([str(f) for f in found if f.rule == "licence" or f.where == lint.EXCEPTIONS], [])
            self.assertEqual(len(held), 1)

    def test_a_new_units_ship_pull_request_adds_no_entry_and_needs_one_from_a_tools_pull_request(self):
        """The first proofs of a fuzz target may carry licence lines that its own series applies later.  Its ship
        pull request may not add the unit's entry; with the entry that a tools pull request added before it, its
        lint (--changed and --pr-kind maintainer, with the base or without it) fails on nothing and reports the
        unit's licence findings pending."""
        ship, record = self.lib("api-driver"), layout.record_path("zlib", "api-driver", self.LAYOUT)
        changed = [ship + "First.v", ship + "Second.v"]
        with self.tree() as base, self.tree() as head:
            for t in (base, head):
                self.write_pending(t, {"Kept.v": "Definition x := 0.\n"}, [])
                t.write(record, build_record(proofs={"texts": list(lint.ANTHROPIC_TEXTS)}))
            head.write(ship + "First.v", self.GPL)
            head.write(ship + "Second.v", self.GPL)
            entries = {"schema": "oss-fuzz-theorems/lint-exceptions/1",
                       "exceptions": [self.pending_entry("zlib/api-driver")]}
            head.put_yaml(lint.EXCEPTIONS, entries)   # the ship pull request adds the entry itself
            found = head.lint(changed=changed + [lint.EXCEPTIONS], pending_base=self.committed(base),
                              pr_kind="maintainer", today=self.TODAY)
            self.assertEqual([str(f) for f in found], [self.ADDED % (lint.EXCEPTIONS, "zlib/api-driver")])
            base.put_yaml(lint.EXCEPTIONS, entries)   # a tools pull request added it first
            for kw in ({"pending_base": self.committed(base)}, {}):
                with self.subTest(base="pending_base" in kw):
                    held = []
                    found = head.lint(changed=changed, pr_kind="maintainer", pending=held, today=self.TODAY, **kw)
                    self.assertEqual([str(f) for f in found], [])
                    self.assertEqual(sorted(f.where.replace(ship, "") for f in held), ["First.v:1", "Second.v:1"])
                    self.assertTrue(all(f.rule == "licence" for f in held), held)

    def test_the_pending_base_is_the_base_commit_read_through_git_in_a_sparse_checkout(self):
        """pr.yml checks the base out with its sparse patterns: no proofs folder is on disk, and the list is read from
        the commit, not from the checkout's files.  A proof pull request's new entry for a unit the base has is
        refused there."""
        sparse = ["/*", "!/*/", "/tools/", "/findings/", "/projects/*/unpatched.yaml", "/projects/*/*/findings/"]
        with self.tree() as base, self.tree() as head, tempfile.TemporaryDirectory() as d:
            self.write_pending(base, {"Gpl.v": self.GPL}, [])
            git = ["git", "-C", self.committed(base)]
            checkout = os.path.join(d, "base")
            subprocess.run(git + ["worktree", "add", "-q", "--no-checkout", "--detach", checkout, "HEAD"], check=True)
            subprocess.run(["git", "-C", checkout, "sparse-checkout", "set", "--no-cone"] + sparse, check=True)
            subprocess.run(["git", "-C", checkout, "checkout", "-q", "--detach"], check=True)
            self.assertFalse(os.path.exists(os.path.join(checkout, self.LIB, "Gpl.v")))
            # an entry on disk that the base commit does not have: not the base's list
            with open(os.path.join(checkout, lint.EXCEPTIONS), "a") as f:
                f.write("  - unit: zlib/checksum_fuzzer\n    rule: licence-pending\n    due: '2026-10-31'\n"
                        "    series: pending\n    reason: not committed\n")
            self.write_pending(head, {"Gpl.v": self.GPL + "(* a change *)\n"}, [self.pending_entry()])
            found = head.lint(changed=[lint.EXCEPTIONS, self.LIB + "Gpl.v"], pending_base=checkout, today=self.TODAY)
            self.assertEqual([str(f) for f in found if f.rule == "licence" or f.where == lint.EXCEPTIONS],
                             [self.ADDED % (lint.EXCEPTIONS, "zlib/checksum_fuzzer")])
            subprocess.run(git + ["worktree", "remove", "--force", checkout], check=True)

    def test_an_entry_that_names_a_file_a_sparse_checkout_leaves_out_is_left_to_a_whole_tree_lint(self):
        """enroll.yml's facts job lints a checkout without the proof libraries (tools/enroll/check.sh): lint reads none
        of the files left out, so a licence-pending entry whose unit has one is not stale there, nor is an exception
        that names one unused.  A whole-tree lint of the same commit still reports both."""
        stale = ("paths %s: unit zlib/checksum_fuzzer has no licence finding: its licence series pending removes its "
                 "licence-pending entry" % lint.EXCEPTIONS)
        token = {"path": self.LIB + "Token.v", "rule": "proofs", "line": 1, "key": "\"'LF2CBN(' t ')'\"", "count": 1,
                 "message": "a notation token with a '\"' is not allowed in a proof", "reason": "a test"}
        unused = "paths %s: an exception for proofs %sToken.v:1 that is not used 1 time(s)" % (lint.EXCEPTIONS, self.LIB)
        with self.tree() as t:
            self.write_pending(t, {"Clean.v": "Definition x := 0.\n", "Token.v": "Definition y := 1.\n"},
                               [self.pending_entry(), token])
            self.committed(t)
            whole = sorted(str(f) for f in t.lint(today=self.TODAY) if f.where == lint.EXCEPTIONS)
            self.assertEqual(whole, sorted([stale, unused]))
            subprocess.run(["git", "-C", t.root, "sparse-checkout", "set", "--no-cone", "/*", "!/" + self.LIB],
                           check=True)
            self.assertFalse(os.path.exists(t.path(self.LIB + "Clean.v")))
            self.assertEqual(lint.left_out(t.root), {self.LIB + "Clean.v", self.LIB + "Token.v"})
            err = io.StringIO()
            with contextlib.redirect_stderr(err):
                found = t.lint(today=self.TODAY)
            self.assertEqual([str(f) for f in found if f.where == lint.EXCEPTIONS], [])
            self.assertIn("oft lint: 2 tracked file(s) are left out of this sparse checkout (%sClean.v first)"
                          % self.LIB, err.getvalue())
            # a file put back on disk is read again, and its unit's entry judged
            subprocess.run(["git", "-C", t.root, "sparse-checkout", "disable"], check=True)
            self.assertEqual(lint.left_out(t.root), set())
            self.assertEqual(sorted(str(f) for f in t.lint(today=self.TODAY) if f.where == lint.EXCEPTIONS), whole)

    def test_a_sparse_checkout_still_judges_the_names_of_the_files_it_leaves_out(self):
        """pr.yml's pull-request lint checks the tree out without the proof libraries: check_paths judges the name
        of each file left out, so a stray path there still fails; and a left-out file that differs from the commit
        --changed-only compares with is a finding, since lint must read its bytes and cannot."""
        stray = "paths %sstray.bin: matches no path pattern" % self.LIB
        with self.tree() as t:
            self.write_pending(t, {"Clean.v": "Definition x := 0.\n", "stray.bin": "x"}, [self.pending_entry()])
            self.committed(t)
            self.assertIn(stray, [str(f) for f in t.lint(today=self.TODAY)])
            t.write(self.at("Clean.v"), "Definition x := 1.\n")
            subprocess.run(["git", "-C", t.root, "-c", "user.name=t", "-c", "user.email=t@invalid", "commit", "-qam",
                            "change Clean.v"], check=True)
            subprocess.run(["git", "-C", t.root, "sparse-checkout", "set", "--no-cone", "/*", "!/" + self.LIB],
                           check=True)
            self.assertIn(self.LIB + "stray.bin", lint.left_out(t.root))
            with contextlib.redirect_stderr(io.StringIO()):
                whole = [str(f) for f in t.lint(today=self.TODAY)]
                since = [str(f) for f in t.lint(today=self.TODAY, changed_only="HEAD~1")]
            self.assertIn(stray, whole)
            self.assertIn(stray, since)
            self.assertIn("paths %sClean.v: this file differs from HEAD~1, and this sparse checkout leaves it out (1 "
                          "such file(s)): check it out, or lint the whole tree" % self.LIB, since)
            self.assertFalse(any("differs from" in f for f in whole))

    def test_a_pending_base_whose_list_git_cannot_read_lists_no_entry(self):
        """A pending base that is no git checkout gives no entry, so a proof pull request's entry is refused."""
        with self.tree() as head, tempfile.TemporaryDirectory() as d:
            self.write_pending(head, {"Gpl.v": self.GPL}, [self.pending_entry()])
            found = head.lint(changed=[self.LIB + "Gpl.v"], pending_base=d, today=self.TODAY)
            self.assertEqual([str(f) for f in found if f.rule == "licence" or f.where == lint.EXCEPTIONS],
                             [self.ADDED % (lint.EXCEPTIONS, "zlib/checksum_fuzzer")])

    def test_the_command_compares_the_entries_with_the_pending_base(self):
        from oft import __main__ as cli
        with self.tree() as base, self.tree() as head, tempfile.TemporaryDirectory() as d:
            self.write_pending(base, {"Gpl.v": self.GPL}, [])
            self.write_pending(head, {"Gpl.v": self.GPL + "(* a change *)\n"}, [self.pending_entry(due="2999-12-31")])
            changed = os.path.join(d, "changed.txt")
            with open(changed, "w") as f:
                f.write(self.LIB + "Gpl.v\n")
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                rc = cli.main(["--root", head.root, "lint", "--changed", changed, "--pending-base",
                               self.committed(base)])
            self.assertEqual(rc, 1, out.getvalue())
            self.assertIn(self.ADDED % (lint.EXCEPTIONS, "zlib/checksum_fuzzer"), out.getvalue().splitlines())

    def test_an_entry_for_a_unit_with_no_rocq_files_is_not_stale_until_they_come(self):
        record = layout.record_path("zlib", "api-driver", self.LAYOUT)
        stale = ("paths %s: unit zlib/api-driver has no licence finding: its licence series pending removes its "
                 "licence-pending entry" % lint.EXCEPTIONS)
        with self.tree() as t:
            self.write_pending(t, {"Gpl.v": self.GPL}, [self.pending_entry(), self.pending_entry("zlib/api-driver")])
            self.assertEqual([str(f) for f in t.lint(today=self.TODAY) if f.where == lint.EXCEPTIONS], [])
            t.write(record, build_record(proofs={"texts": list(lint.ANTHROPIC_TEXTS)}))   # a build record is no proof
            self.assertEqual([str(f) for f in t.lint(today=self.TODAY) if f.where == lint.EXCEPTIONS], [])
            t.write(self.lib("api-driver") + "Clean.v", "Definition x := 0.\n")
            self.assertEqual([str(f) for f in t.lint(today=self.TODAY) if f.where == lint.EXCEPTIONS], [stale])
            # its due date still counts while it is absent
            os.remove(t.path(self.lib("api-driver") + "Clean.v"))
            self.write_pending(t, {"Gpl.v": self.GPL}, [self.pending_entry(),
                                                        self.pending_entry("zlib/api-driver", due="2026-10-01")])
            self.assertEqual([str(f) for f in t.lint(today=self.TODAY) if f.where == lint.EXCEPTIONS],
                             ["paths %s: unit zlib/api-driver: its licence series pending was due 2026-10-01"
                              % lint.EXCEPTIONS])

    def test_a_pull_request_keeps_or_changes_an_entry_its_base_has(self):
        with self.tree() as base, self.tree() as head:
            self.write_pending(base, {"Gpl.v": self.GPL}, [self.pending_entry(due="2026-10-30", series="pending")])
            self.write_pending(head, {"Gpl.v": self.GPL}, [self.pending_entry(series="#441")])
            head.write(self.LIB + "Gpl.v", self.GPL + "(* a change *)\n")
            found = head.lint(changed=[lint.EXCEPTIONS, self.LIB + "Gpl.v"], pending_base=self.committed(base),
                              today=self.TODAY)
            self.assertEqual([str(f) for f in found if f.rule == "licence" or f.where == lint.EXCEPTIONS], [])
            # with no base to compare with (a whole-tree lint), an entry is judged only by its unit and its due date
            self.assertEqual([str(f) for f in base.lint(today=self.TODAY) if f.where == lint.EXCEPTIONS], [])

    def test_an_expired_entry_fails_only_a_change_that_touches_its_unit_or_the_list(self):
        """An expired entry fails a lint with no change to judge, and a pull request that touches its unit (in either
        layout) or lint-exceptions.yaml; any other pull request gets it as an expired finding, which does not fail."""
        other = layout.proof_lib_dir("zlib", "checksum_fuzzer",
                                     layout.NEW if self.LAYOUT == layout.OLD else layout.OLD) + "/Gpl.v"
        expired = "paths %s: unit zlib/checksum_fuzzer: its licence series pending was due 2026-10-01" % lint.EXCEPTIONS
        with self.tree() as t:
            self.write_pending(t, {"Gpl.v": self.GPL}, [self.pending_entry(due="2026-10-01")])
            t.write("docs/x.md", "a page\n")
            for changed, failing in ((["docs/x.md"], False), ([self.LIB + "Gpl.v"], True), ([other], True),
                                     ([lint.EXCEPTIONS], True), (None, True)):
                with self.subTest(changed=changed):
                    held, late = [], []
                    found = t.lint(changed=changed, pending=held, expired=late, today=self.TODAY)
                    self.assertEqual([str(f) for f in found if f.rule == "licence" or f.where == lint.EXCEPTIONS],
                                     [expired] if failing else [])
                    self.assertEqual([str(f) for f in late], [] if failing else [expired])
                    self.assertEqual(len(held), 1)   # its unit's findings stay pending either way
                    self.assertTrue(all(lint.is_expired(f) for f in late))

    def test_a_change_of_the_list_trips_only_the_expired_entries_it_adds_or_edits(self):
        """Compared with the base: a series that deletes its own entry passes beside other expired entries (the
        libreac series after 2026-11-01); an expired entry the change adds or edits fails; with no base to compare
        with, any change of the list trips every expired entry."""
        mine, other = self.pending_entry(due="2026-10-01"), self.pending_entry("zlib/other", due="2026-10-01")
        late_msg = "paths %s: unit %%s: its licence series %%s was due 2026-10-01" % lint.EXCEPTIONS
        cf, zo = "zlib/checksum_fuzzer", "zlib/other"
        with self.tree() as base, self.tree() as before, self.tree() as head:
            self.write_pending(base, {"Gpl.v": self.GPL}, [mine, other])
            self.write_pending(before, {"Gpl.v": self.GPL}, [other])
            both, only_other = self.committed(base), self.committed(before)
            # (name, the head's entries, the pending base, failing (unit, series), warned (unit, series))
            cases = (("another unit's entry deleted", [mine], both, [], [(cf, "pending")]),
                     ("this entry edited", [dict(mine, series="#441")], both, [(cf, "#441")], []),
                     ("this entry added", [mine, other], only_other, [(cf, "pending")], [(zo, "pending")]),
                     ("no base to compare with", [mine, other], None, [(cf, "pending"), (zo, "pending")], []))
            for name, entries, pending_base, failing, warned in cases:
                with self.subTest(name):
                    self.write_pending(head, {"Gpl.v": self.GPL}, entries)
                    held, late = [], []
                    found = head.lint(changed=[lint.EXCEPTIONS], pending=held, expired=late, today=self.TODAY,
                                      pending_base=pending_base)
                    self.assertEqual([str(f) for f in found if f.rule == "licence" or f.where == lint.EXCEPTIONS],
                                     [late_msg % u for u in failing])
                    self.assertEqual([str(f) for f in late], [late_msg % u for u in warned])
                    self.assertEqual(len(held), 1)

    def test_the_command_warns_of_an_expired_entry_that_the_change_does_not_touch(self):
        from oft import __main__ as cli
        with self.tree() as t, tempfile.TemporaryDirectory() as d:
            self.write_pending(t, {"Gpl.v": self.GPL}, [self.pending_entry(due="2000-01-01")])
            t.write("docs/x.md", "a page\n")
            changed = os.path.join(d, "changed.txt")
            with open(changed, "w") as f:
                f.write("docs/x.md\n")
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                rc = cli.main(["--root", t.root, "lint", "--changed", changed])
            lines = out.getvalue().splitlines()
            self.assertEqual(rc, 0, out.getvalue())
            msg = "unit zlib/checksum_fuzzer: its licence series pending was due 2000-01-01"
            self.assertIn("expired paths %s: %s" % (lint.EXCEPTIONS, msg), lines)
            self.assertIn("::warning file=%s::%s" % (lint.EXCEPTIONS, msg), lines)
            self.assertTrue(lines[-1].startswith("oft lint: 0 finding(s); 1 pending licence finding(s) in 1 unit(s)"))
            self.assertTrue(lines[-1].endswith("; 1 expired licence-pending entr(ies) that this change does not touch, "
                                               "which do not fail"), lines[-1])

    def test_is_expired_names_only_the_finding_of_an_expired_entry(self):
        """test_this_repository_is_clean fails on every finding but these: a stale or inexact entry is no expiry."""
        late = self.pending_entry(due="2000-01-01")
        found = lint.apply_pending([], [late, self.pending_entry("zlib/other", series="soon")], today=self.TODAY)
        self.assertEqual([(lint.is_expired(f), f.msg) for f in found], [
            (True, "unit zlib/checksum_fuzzer: its licence series pending was due 2000-01-01"),
            (False, "unit zlib/checksum_fuzzer has no licence finding: its licence series pending removes its "
                    "licence-pending entry"),
            (False, self.NOT_EXACT % "zlib/other")])

    def test_a_pending_entry_that_is_not_exact_fails(self):
        exact = self.pending_entry()
        cases = {"a key more": dict(exact, count=1), "no series": {k: v for k, v in exact.items() if k != "series"},
                 "series a word": dict(exact, series="soon"), "series a link": dict(exact, series="#441 x"),
                 "series #0": dict(exact, series="#0"), "due no date": dict(exact, due="2026-13-01"),
                 "due another form": dict(exact, due="31 October 2026"), "due not text": dict(exact, due=20261031),
                 "due the basic form": dict(exact, due="20261031"),
                 "unit a path": dict(exact, unit="proofs/zlib/checksum_fuzzer"),
                 "unit a project": dict(exact, unit="zlib"),
                 "empty reason": dict(exact, reason="")}
        for name, e in cases.items():
            with self.subTest(case=name):
                failing, held = self.pending({"Gpl.v": self.GPL}, [e])
                self.assertEqual([f.split(":")[0] for f in failing], ["licence Gpl.v", "paths " + lint.EXCEPTIONS])
                self.assertEqual(failing[1], "paths %s: %s" % (lint.EXCEPTIONS, self.NOT_EXACT % e.get("unit")))
                self.assertEqual(held, [])
        failing, held = self.pending({"Gpl.v": self.GPL}, [exact, dict(exact, due="2026-11-02")])   # one per unit
        self.assertEqual((failing, len(held)),
                         (["paths %s: %s" % (lint.EXCEPTIONS, self.NOT_EXACT % exact["unit"])], 1))

    def test_changed_only_reports_a_stale_pending_entry_only_when_it_reads_every_file(self):
        stale = ("paths %s: unit zlib/checksum_fuzzer has no licence finding: its licence series pending removes its "
                 "licence-pending entry" % lint.EXCEPTIONS)
        expired = "paths %s: unit zlib/checksum_fuzzer: its licence series pending was due 2000-01-01" % lint.EXCEPTIONS
        with self.tree() as t:
            self.write_pending(t, {"Clean.v": "Definition x := 0.\n"}, [self.pending_entry(due="2000-01-01")])
            self.assertEqual(sorted(str(f) for f in t.lint() if f.where == lint.EXCEPTIONS), sorted([expired, stale]))
            PerFileScope.commit(self, t)
            t.write("docs/x.md", "nothing private\n")   # the per-file rules read only this file
            found, err = PerFileScope.changed_only(self, t)
            self.assertEqual([f for f in found if lint.EXCEPTIONS in f], [expired], err)

    def test_the_command_prints_and_counts_pending_findings_and_does_not_fail_on_them(self):
        """By default one line per fuzz target with its count, and the counts sum to the summary's total; each finding
        only with --list-pending."""
        from oft import __main__ as cli
        with self.tree() as t:
            self.write_pending(t, {"Gpl.v": self.GPL, "Gpl3.v": self.GPL.replace("Definition x", "Definition z")},
                               [self.pending_entry(due="2999-12-31")])
            summary = ("oft lint: 0 finding(s); 2 pending licence finding(s) in 1 unit(s) that %s lists, which do not "
                       "fail" % lint.EXCEPTIONS)
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                rc = cli.main(["--root", t.root, "lint"])
            lines = out.getvalue().splitlines()
            self.assertEqual(rc, 0, out.getvalue())
            self.assertEqual([line for line in lines if line.startswith("pending ")],
                             ["pending zlib/checksum_fuzzer: 2 licence finding(s) (--list-pending prints each)"])
            self.assertEqual(lines[-1], summary)
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                rc = cli.main(["--root", t.root, "lint", "--list-pending"])
            lines = out.getvalue().splitlines()
            self.assertEqual(rc, 0, out.getvalue())
            each = [line for line in lines if line.startswith("pending ")]
            self.assertEqual(sorted(line.split(":")[0] for line in each),
                             ["pending licence %sGpl.v" % self.LIB, "pending licence %sGpl3.v" % self.LIB])
            self.assertEqual(lines[-1], summary)
            # without the entry, both are findings
            t.put_yaml(lint.EXCEPTIONS, {"schema": "oss-fuzz-theorems/lint-exceptions/1", "exceptions": []})
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                rc = cli.main(["--root", t.root, "lint"])
            self.assertEqual((rc, out.getvalue().splitlines()[-1]), (1, "oft lint: 2 finding(s)"))

    def test_an_entry_whose_series_is_a_pull_request_may_wait_for_the_files_it_brings(self):
        """The pull request that brings a unit's files cannot be excepted either way while it is open: a proof pull
        request adds no entry, and a tools pull request's entry names a unit whose files on the base have no licence
        finding.  So an entry whose series is that pull request ('#<number>') waits for it while its due date has not
        passed; after the due date the rule applies as it does to any other entry."""
        clean = {"Clean.v": "Definition x := 0.\n"}
        stale = ("paths %s: unit zlib/checksum_fuzzer has no licence finding: its licence series %s removes its "
                 "licence-pending entry")
        late = "paths %s: unit zlib/checksum_fuzzer: its licence series %s was due 2000-01-01"
        self.assertEqual(self.pending(clean, [self.pending_entry(series="#539", due="2999-12-31")]), ([], []))
        self.assertEqual(self.pending(clean, [self.pending_entry(series="#539", due="2000-01-01")])[0],
                         [stale % (lint.EXCEPTIONS, "#539"), late % (lint.EXCEPTIONS, "#539")])
        self.assertEqual(self.pending(clean, [self.pending_entry(due="2999-12-31")])[0],
                         [stale % (lint.EXCEPTIONS, "pending")])

    def test_the_counts_per_fuzz_target_sum_to_the_pending_total(self):
        old, new = "proofs/zlib/checksum_fuzzer/lib/", "projects/zlib/api_driver/proofs/lib/"
        pending = [lint.Finding("licence", old + "A.v:1", "m"), lint.Finding("licence", new + "B.v:1", "m"),
                   lint.Finding("licence", old + "C.v:3", "m"), lint.Finding("licence", new + "D.v:2", "m"),
                   lint.Finding("licence", old + "E.v:1", "m")]
        counts = lint.pending_by_unit(pending)
        self.assertEqual(counts, [("zlib/api_driver", 2), ("zlib/checksum_fuzzer", 3)])
        self.assertEqual(sum(n for _, n in counts), len(pending))
        self.assertEqual(lint.pending_by_unit([]), [])


class LicencePerProject(Licence):
    """Every test of Licence in the per-project layout, projects/<p>/<h>/proofs/ (tools/oft/layout.py): the build
    records, a project's fuzz targets, the paths a finding names and --changed-only's margin as that layout has them."""
    LAYOUT = layout.NEW


class Memory(unittest.TestCase):
    """lint's bounds on memory: a process of it that holds more than --max-rss-gib stops the run, and the default
    number of processes is what the available memory holds at WORKER_GIB each."""
    GIB = 2 ** 30
    BIG = 256 << 20

    def test_default_jobs_is_what_the_available_memory_holds(self):
        gib, each = self.GIB, int(lint.WORKER_GIB * self.GIB)
        for cpus, avail, want in ((32, 64 * gib, 32), (32, 16 * gib, 16 * gib // each), (32, each - 1, 1),
                                  (32, None, 32), (4, 64 * gib, 4)):
            with self.subTest(cpus=cpus, avail=avail), mock.patch.object(lint.facts, "cpus", return_value=cpus), \
                    mock.patch.object(lint, "memory_available", return_value=avail):
                self.assertEqual(lint.default_jobs(), want)

    def test_the_available_memory_is_meminfos_less_each_cgroup_limit_above(self):
        gib = self.GIB
        with tempfile.TemporaryDirectory() as d:
            proc, cgroup = os.path.join(d, "proc"), os.path.join(d, "cgroup")

            def write(rel, text):
                os.makedirs(os.path.dirname(os.path.join(d, rel)), exist_ok=True)
                with open(os.path.join(d, rel), "w") as f:
                    f.write(text)
            write("proc/meminfo", "MemTotal:       1 kB\nMemAvailable:   %d kB\n" % (40 * gib // 1024))
            self.assertEqual(lint.memory_available(proc, cgroup), 40 * gib)   # no cgroup to read
            write("proc/self/cgroup", "0::/user.slice/lane.scope\n")
            self.assertEqual(lint.memory_available(proc, cgroup), 40 * gib)   # no cgroup files
            write("cgroup/user.slice/memory.max", "%d\n" % (24 * gib))
            write("cgroup/user.slice/memory.current", "%d\n" % (20 * gib))
            write("cgroup/user.slice/lane.scope/memory.max", "max\n")
            write("cgroup/user.slice/lane.scope/memory.current", "%d\n" % (3 * gib))
            self.assertEqual(lint.memory_available(proc, cgroup), 4 * gib)   # the parent's limit less its use
            write("cgroup/user.slice/lane.scope/memory.max", "%d\n" % (5 * gib))
            self.assertEqual(lint.memory_available(proc, cgroup), 2 * gib)   # the scope's own
            write("cgroup/memory.max", "%d\n" % gib)
            write("cgroup/memory.current", "0\n")
            self.assertEqual(lint.memory_available(proc, cgroup), gib)   # the top of the cgroup namespace
            write("proc/meminfo", "MemTotal:       1 kB\n")
            self.assertIsNone(lint.memory_available(proc, cgroup))

    @staticmethod
    def work(item):
        """An item of a pool: "big" takes BIG bytes more and then waits, "slow" waits 30 s, any other comes back."""
        if item == "big":
            held = b"x" * Memory.BIG
            time.sleep(10)
            return len(held)
        time.sleep(30 if item == "slow" else 0)
        return item

    def stopped(self, run):
        """(the ResourceStop of run(), the seconds it took) under a bound of this process's memory and 64 MiB."""
        started = time.monotonic()
        with mock.patch.object(lint, "_MAX_RSS", lint.rss() + (64 << 20)), self.assertRaises(lint.ResourceStop) as e:
            run()
        return str(e.exception), time.monotonic() - started

    @unittest.skipUnless("fork" in multiprocessing.get_all_start_methods(), "no fork: the items run in this process")
    def test_a_pool_worker_past_its_bound_stops_the_others_and_the_run(self):
        why, took = self.stopped(lambda: lint.forked_map(self.work, ["big", "slow", "slow"], 3, chunksize=1))
        self.assertIn("a worker process ended without its result", why)
        self.assertLess(took, 20)   # the slow workers were stopped, not waited for
        self.assertEqual(multiprocessing.active_children(), [])
        with mock.patch.object(lint, "_MAX_RSS", lint.rss() + (1 << 30)):
            self.assertEqual(lint.forked_map(self.work, ["a", "b"], 2), ["a", "b"])

    def test_lint_stops_when_its_own_process_passes_its_bound(self):
        from oft import __main__ as cli
        before = lint._MAX_RSS
        with tree() as t:
            with self.assertRaises(lint.ResourceStop) as e:
                t.lint(max_rss_gib=0.001)
            self.assertIn("process %d holds" % os.getpid(), str(e.exception))
            self.assertIn("over --max-rss-gib 0.001; the run stops", str(e.exception))
            self.assertEqual(lint._MAX_RSS, before)   # the bound is the run's only
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                rc = cli.main(["--root", t.root, "lint", "--max-rss-gib", "0.001"])
            self.assertEqual((rc, out.getvalue().splitlines()[-1][:22]), (lint.MAX_RSS_EXIT, "FAIL oft lint: process"))
            self.assertEqual(t.lint(max_rss_gib=lint.MAX_RSS_GIB), [])



class ProofHarnessDirs(unittest.TestCase):
    """proofs/<p>/<h>/lib/ (the harness's proof library) and proofs/<p>/<h>/provenance/ (its build record)."""

    def tree_with(self, files):
        t = Tree()
        self.addCleanup(t.close)
        for rel, text in files.items():
            t.write(rel, text)
        t.generate()
        return t

    LIB = {"proofs/zlib/checksum_fuzzer/lib/Base.v": "Definition one := 1.\n",
           "proofs/zlib/checksum_fuzzer/lib/Sub/Deep.v": "Definition two := 2.\n"}
    PROVENANCE = {"proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.yaml": build_record(),
                  "proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.md": "# Build record\n",
                  "proofs/zlib/checksum_fuzzer/provenance/recipe/targets/checksum_fuzzer/build.sh": "make\n",
                  "proofs/zlib/checksum_fuzzer/provenance/LICENSES/zlib-LICENSE": "zlib licence\n"}

    def test_a_library_and_a_build_record_are_allowed_and_are_not_proof_directories(self):
        t = self.tree_with(dict(self.LIB, **self.PROVENANCE))
        self.assertEqual([str(f) for f in t.lint()], [])
        loaded = facts.load(t.root)
        self.assertEqual(loaded.errors, [])
        self.assertEqual(loaded.proof_libs, {"zlib/checksum_fuzzer": "proofs/zlib/checksum_fuzzer/lib"})
        self.assertEqual(loaded.records, {("zlib", "checksum_fuzzer"): FIXTURE_RECIPE})
        self.assertEqual(loaded.proofs, {})

    def test_another_file_in_the_build_record(self):
        t = self.tree_with(dict(self.PROVENANCE, **{"proofs/zlib/checksum_fuzzer/provenance/notes.txt": "x\n"}))
        self.assertTrue(any(f.rule == "paths" and "provenance/notes.txt" in str(f) for f in t.lint()))

    def test_a_library_is_held_to_the_proofs_rule(self):
        t = self.tree_with({"proofs/zlib/checksum_fuzzer/lib/Sub/Cheat.v": "Lemma x : False.\nProof. Admitted.\n"})
        found = [f for f in t.lint() if f.rule == "proofs"]
        self.assertEqual(len(found), 1)
        self.assertIn("lib/Sub/Cheat.v", str(found[0]))

    def test_licence_texts_and_recipe_are_verbatim_but_the_record_is_not(self):
        t = self.tree_with(dict(self.PROVENANCE, **{
            "proofs/zlib/checksum_fuzzer/provenance/LICENSES/zlib-LICENSE": "See http://www.apache.org/licenses/\n",
            "proofs/zlib/checksum_fuzzer/provenance/recipe/targets/x/pin": "git https://example.org/x.git\n",
            "proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.md":
                "Built at https://github.com/theorem-labs/" + "internal\n"}))
        links = [str(f) for f in t.lint() if f.rule == "links"]
        self.assertEqual(len(links), 1, links)
        self.assertIn("provenance/PROVENANCE.md", links[0])


class Layout(unittest.TestCase):
    """Both layouts of a fuzz target's proofs, counterexamples and findings (tools/oft/layout.py): lint holds each to
    the same rules, refuses an old-layout path beside a per-project one, and reads an exception, or the findings
    ledger, across the move."""
    MIXED = "an old-layout path in a per-project tree: run ./oft port-layout"
    LIB = "proofs/zlib/checksum_fuzzer/lib/Token.v"
    PORT_FILE = "proofs/zlib/checksum_fuzzer/provenance/port/projects/zlib/Dockerfile"
    TOKEN_KEY = "\"'LF2CBN(' t ')'\""
    FINDING = "zlib/checksum_fuzzer/findings/stand-in-abort/"

    def ported(self, t):
        """Move t to the per-project layout, as `oft port-layout` does."""
        self.assertEqual(port.port_worktree(t.root, out=io.StringIO()), 0)

    def test_an_old_layout_path_in_a_per_project_tree_is_refused(self):
        """An unported pull request lays old-layout files over a per-project base: each is refused, and told to run
        ./oft port-layout.  A tree in either layout alone has no such finding."""
        old = (["findings/zlib/unpatched.yaml", "findings/zlib/checksum_fuzzer/series"]
               + ["findings/zlib/checksum_fuzzer/stand-in-abort/" + name
                  for name in ("0001-stand-in.patch", "control.bin", "finding.yaml", "input.bin")]
               + ["patches/zlib/0001-x.patch", "proofs/zlib/checksum_fuzzer/plain_halts/Proof.v",
                  "proofs/zlib/checksum_fuzzer/plain_halts/proof.yaml"])

        def mixed(t):
            return sorted(str(f) for f in t.lint() if f.msg == self.MIXED)
        with tree() as t:
            self.assertEqual(mixed(t), [])
            self.ported(t)
            self.assertEqual(mixed(t), [])
            add_findings(t)
            add_proof(t, "zlib/checksum_fuzzer/plain_halts")
            t.write("patches/zlib/0001-x.patch", "a patch\n")
            self.assertEqual(mixed(t), sorted("paths %s: %s" % (rel, self.MIXED) for rel in old))

    def findings_to_clear(self, t):
        """Give t, in the old layout, a notation token in a proof library and an e-mail address in a build record's
        copy of the port's project files (zlib built by the port): one finding each, which an entry may clear.  The
        e-mail address's key."""
        port_built(t, "zlib")
        t.write(self.LIB, "(* a *)\n" + ProofsException.TOKEN)
        t.write(self.PORT_FILE, "# Copyright someone" + "@" + "example.com\n")
        self.assertEqual(t.generate(), 0, t.last_output)
        found = t.lint()
        self.assertEqual(sorted((f.rule, f.where) for f in found),
                         [("private-data", self.PORT_FILE + ":1"), ("proofs", self.LIB + ":2")])
        return next(f.key for f in found if f.rule == "private-data")

    def clear(self, t, path, key):
        """Write the two entries that clear findings_to_clear's findings, each naming its file as path(the old-layout
        path) names it."""
        t.put_yaml("tools/oft/lint-exceptions.yaml", {"schema": "oss-fuzz-theorems/lint-exceptions/1", "exceptions": [
            {"path": path(self.LIB), "rule": "proofs", "line": 2, "message": ProofsException.MSG,
             "key": self.TOKEN_KEY, "count": 1, "reason": "a test"},
            {"path": path(self.PORT_FILE), "rule": "private-data", "key": key, "count": 1, "reason": "a test"}]})

    def test_an_old_form_exception_clears_the_finding_on_the_moved_file(self):
        """lint-exceptions.yaml keeps its entries in the old form, since the base's lint matches them by path: once
        the tree is ported, each still clears its finding, now on the moved file, and none is reported unused."""
        with tree() as t:
            self.clear(t, lambda rel: rel, self.findings_to_clear(t))
            self.assertEqual([str(f) for f in t.lint()], [])
            self.ported(t)
            self.assertEqual([str(f) for f in t.lint()], [])

    def test_a_new_form_exception_clears_the_old_layout_finding(self):
        with tree() as t:
            self.clear(t, layout.moved, self.findings_to_clear(t))
            self.assertEqual([str(f) for f in t.lint()], [])
            self.ported(t)
            self.assertEqual([str(f) for f in t.lint()], [])

    def test_a_contributor_may_change_new_layout_proofs_and_not_statements(self):
        """A contributor's pull request changes proofs and counterexamples, now in a fuzz target's own folder, and
        never what states a statement there."""
        with tree() as t:
            old_layout_tree(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.ported(t)
            change = ["projects/zlib/checksum_fuzzer/proofs/plain_halts/Proof.v",
                      "projects/zlib/checksum_fuzzer/proofs/plain_halts/proof.yaml",
                      "projects/zlib/checksum_fuzzer/proofs/plain_halts/dune",
                      "projects/zlib/checksum_fuzzer/proofs/dune",
                      "projects/zlib/checksum_fuzzer/proofs/lib/A.v",
                      "projects/zlib/checksum_fuzzer/proofs/provenance/PROVENANCE.yaml",
                      "projects/json/fuzzer-parse_bjdata/counterexamples/plain_halts/input.bin",
                      "projects/json/fuzzer-parse_bjdata/counterexamples/plain_halts/expect.yaml"]
            self.assertEqual([str(f) for f in t.lint(changed=change, pr_kind="contributor")], [])
            for rel in ("projects/zlib/checksum_fuzzer/harness.yaml", "projects/zlib/checksum_fuzzer/Distribution.v"):
                self.assertEqual([str(f) for f in t.lint(changed=[rel], pr_kind="contributor")],
                                 ["paths %s: an exported fact: only a release pull request changes it" % rel,
                                  "paths %s: outside the proofs and counterexamples folders, docs/ and generated "
                                  "files" % rel])

    def test_size_caps_hold_in_both_layouts(self):
        caps = {"counterexamples/zlib/checksum_fuzzer/plain_halts/input.bin": 64 << 10,
                "counterexamples/zlib/checksum_fuzzer/plain_halts/expect.yaml": 64 << 10,
                "findings/zlib/checksum_fuzzer/stand-in-abort/input.bin": facts.FINDING_INPUT_CAP,
                "findings/zlib/checksum_fuzzer/stand-in-abort/control.bin": facts.FINDING_INPUT_CAP,
                "findings/zlib/checksum_fuzzer/stand-in-abort/finding.yaml": facts.FINDING_FILE_CAP,
                "findings/zlib/checksum_fuzzer/stand-in-abort/0001-stand-in.patch": facts.FINDING_FILE_CAP,
                "findings/zlib/checksum_fuzzer/series": facts.FINDING_FILE_CAP,
                "findings/zlib/unpatched.yaml": facts.FINDING_FILE_CAP,
                "proofs/zlib/checksum_fuzzer/plain_halts/classifier/model.bin": 1 << 20,
                "proofs/zlib/checksum_fuzzer/plain_halts/Proof.v": facts.MAX_BYTES}
        for old, cap in caps.items():
            self.assertEqual((facts.file_cap(old), facts.file_cap(layout.moved(old))), (cap, cap), old)
        with tree() as t:
            self.ported(t)
            rel = "projects/json/fuzzer-parse_bjdata/counterexamples/plain_halts/input.bin"
            t.write(rel, "\0" * ((64 << 10) + 1))
            self.assertIn("paths %s: %d bytes, over the %d-byte cap" % (rel, (64 << 10) + 1, 64 << 10),
                          [str(f) for f in t.lint()])

    def test_a_proof_in_the_per_project_layout_is_held_to_the_proofs_rule(self):
        """A Rocq file of a fuzz target's proofs folder is read as a proof in either layout: refused for an admit,
        its wall-clock limit reported once, and a qualified name in it not read as a host name."""
        with tree() as t:
            self.ported(t)
            rel = "projects/zlib/checksum_fuzzer/proofs/lib/Sub/Cheat.v"
            t.write(rel, "Require Import Parser." + "Internal.\nLemma x : False.\nProof. Admitted.\n"
                         "Lemma y : True.\nProof. timeout 5 exact I.\nQed.\n")
            self.assertEqual([(f.rule, f.where) for f in t.lint()], [("proofs", rel + ":3"), ("proofs", rel + ":5")])

    def test_the_build_record_rules_read_both_layouts(self):
        record = "proofs/zlib/checksum_fuzzer/provenance/"
        for old in (record + "LICENSES/zlib-LICENSE", record + "recipe/targets/checksum_fuzzer/build.sh"):
            self.assertEqual((lint.verbatim(old), lint.verbatim(layout.moved(old))), (True, True), old)
        for old in (record + "port/manifest.yaml", record + "port/projects/zlib/build.sh"):
            self.assertEqual((lint.port_record(old), lint.port_record(layout.moved(old))), (True, True), old)
        new = layout.moved(record)
        self.assertTrue(lint.PORT_MANIFEST.match(new + "port/manifest.yaml"))
        self.assertTrue(lint.PORT_PROJECT_YAML.match(new + "port/projects/zlib/project.yaml"))
        self.assertTrue(lint.PORT_PROJECT_FILE.match(new + "port/projects/zlib/Dockerfile"))
        # the port's files of another project are not the record's own
        self.assertFalse(lint.PORT_PROJECT_YAML.match(new + "port/projects/json/project.yaml"))
        self.assertFalse(lint.PORT_PROJECT_FILE.match(new + "port/projects/json/Dockerfile"))
        self.assertFalse(lint.verbatim(new + "PROVENANCE.md"))

    def test_a_finding_the_port_moved_is_not_deleted(self):
        """The diff of a port lists every finding file twice, deleted where it was and added where it went; the
        base's ledger is in the other layout.  Either way round, nothing is deleted."""
        for moved in ("head", "base"):
            with self.subTest(moved=moved), tree() as base, tree() as t:
                add_findings(base)
                add_findings(t)
                self.ported(t if moved == "head" else base)
                old = [rel for rel in base.files() + t.files() if rel.startswith("findings/")]
                changed = sorted(set(old + [layout.moved(rel) for rel in old]))
                self.assertEqual([str(f) for f in t.lint(changed=changed, pr_kind="maintainer", base=base.root)], [])

    def test_a_per_project_ledger_is_never_deleted(self):
        with tree() as base, tree() as t:
            add_findings(base)
            self.ported(base)
            self.ported(t)
            base.write("projects/zlib/unpatched-bin/checksum_fuzzer/checksum_fuzzer.plain", "fetched, not tracked")
            found = [str(f) for f in t.lint(changed=[], pr_kind="release", base=base.root)]
            deleted = sorted(f.split(": ", 1)[0] for f in found if "never deleted" in f)
            self.assertEqual(deleted, ["paths projects/" + self.FINDING + name for name in
                                       ("0001-stand-in.patch", "control.bin", "finding.yaml", "input.bin")]
                             + ["paths projects/zlib/unpatched.yaml"])

    def test_a_moved_finding_keeps_what_its_runs_are_of(self):
        """A finding the base has keeps its control, its state and its pins wherever the pull request moves it; each
        change is reported where the proposed tree has the file."""
        record, unpatched = "projects/" + self.FINDING + "finding.yaml", "projects/zlib/unpatched.yaml"
        control = "projects/" + self.FINDING + "control.bin"
        with tree() as base, tree() as t:
            add_findings(base)
            add_findings(t)
            self.ported(t)
            t.write(control, "\0\0\0\0\0\0\nanother control\n")
            y = t.yaml(record)
            y["state"] = "open"
            t.put_yaml(record, y)
            t.write("projects/zlib/checksum_fuzzer/findings/series", "")
            y = t.yaml(unpatched)
            y["harnesses"]["checksum_fuzzer"]["asan"]["sha256"] = "8" * 64
            t.put_yaml(unpatched, y)
            old = [rel for rel in base.files() if rel.startswith("findings/")]
            changed = old + [layout.moved(rel) for rel in old]
            self.assertEqual([str(f) for f in t.lint(changed=changed, pr_kind="maintainer", base=base.root)],
                             ["paths %s: a finding's control.bin is never changed: %s" % (control, control),
                              "paths %s: a finding's state never returns to open: %s was patched" % (record, record),
                              "paths %s: a finding's unpatched pins are never changed: %s "
                              "harnesses.checksum_fuzzer.asan" % (unpatched, unpatched)])


class Withheld(unittest.TestCase):
    def test_a_patch_has_no_disclosure_field(self):
        with tree() as t:
            y = t.yaml("projects/zlib/project.yaml")
            y["patches"].append({"id": "some-fix", "upstream": "reported", "disclosure": "withheld"})
            t.put_yaml("projects/zlib/project.yaml", y)
            self.assertIn("schema", rules_of(t.lint()))

    def test_withheld_items_without_the_project_saying_so(self):
        with tree() as t:
            y = t.yaml("projects/zlib/project.yaml")
            del y["withheld"]
            t.put_yaml("projects/zlib/project.yaml", y)
            self.assertIn("withheld", rules_of(t.lint()))

    def test_a_withheld_reason_with_nothing_withheld(self):
        with tree() as t:
            y = t.yaml("projects/json/project.yaml")
            y["withheld"] = {"unpublished": True}
            t.put_yaml("projects/json/project.yaml", y)
            self.assertTrue(any("nothing is withheld for that reason" in f.msg for f in t.lint()))

    def test_evidence_for_a_withheld_statement(self):
        with tree() as t:
            y = t.yaml("projects/json/fuzzer-parse_bjdata/harness.yaml")
            y["statements"]["plain_halts"]["status"] = "withheld"
            y["statements"]["plain_halts"]["withheld"] = "not-yet-published"
            t.put_yaml("projects/json/fuzzer-parse_bjdata/harness.yaml", y)
            self.assertTrue(any("cannot carry" in f.msg for f in t.lint()))

    def test_a_withheld_build_shows_no_detail(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["builds"]["asan"]["withheld"] = "not-yet-published"
            for s in ("asan_halts", "asan_agrees", "asan_disagrees_at_most", "asan_agreement_decidable"):
                y["statements"][s] = dict(y["statements"][s], status="withheld", withheld="not-yet-published")
                y["statements"][s].pop("binds_checks", None)
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertTrue(any("is withheld but shows bytes, sha256, segments" in f.msg for f in t.lint()))
            for k in ("bytes", "sha256", "segments"):
                del y["builds"]["asan"][k]
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            r = t.yaml("release.yaml")
            r["counts"]["binaries"] -= 1
            t.put_yaml("release.yaml", r)
            self.assertEqual(t.generate(), 1)         # Characterise.v, for the asan pair only, is now stale
            for line in t.last_output.splitlines():
                if line.endswith("no longer produce; remove it"):
                    os.unlink(t.path(line.split(":")[0]))
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            page = t.read("projects/zlib/checksum_fuzzer/README.md")
            self.assertIn("| asan | `checksum_fuzzer.asan` | withheld: not in this release yet | |", page)
            self.assertNotIn(facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"].data["builds"]["plain"]
                             ["file"] + "` | withheld", page)

    def test_a_withheld_statement_has_no_fingerprint(self):
        with tree() as t:
            st = {s.id: s for s in facts.load(t.root).statements()}
            self.assertIsNone(st["zlib/api-driver/asan_ubsan_agrees"].fingerprint)
            self.assertIsNotNone(st["zlib/api-driver/asan_agrees"].fingerprint)
            self.assertIn("zlib/api-driver/asan_ubsan_agrees\tagreement\tplain,asan-ubsan\tmay-fail\t-\twithheld\t"
                          "not-yet-published\t1\t-\t-", t.read("index/statements.tsv"))

    def test_a_gpl_binary_without_its_source(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["licence"] = "GPL-2.0-only AND MIT"
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            p = t.yaml("projects/zlib/project.yaml")
            del p["assets"]["src"], p["assets"]["src_manifest"]
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertTrue(any("source bundle" in f.msg for f in t.lint()))

    def test_the_source_is_three_files(self):
        """assets.src goes with assets.src_manifest, each named for what it is, and the archive's recipe is one that
        release.yaml lists; the fixture has all three (the control: it lints clean)."""
        with tree() as t:
            self.assertEqual([str(f) for f in t.lint()], [])
            p = t.yaml("projects/zlib/project.yaml")
            man = p["assets"].pop("src_manifest")
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertTrue(any("assets.src and assets.src_manifest go together" in f.msg for f in t.lint()))
            p["assets"]["src_manifest"] = dict(man, file="other-src.MANIFEST.tsv")
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertTrue(any("assets.src_manifest.file must be zlib-src.MANIFEST.tsv" in f.msg for f in t.lint()))
            p["assets"]["src_manifest"] = dict(man, release="v2026.12.0")
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertTrue(any("different releases" in f.msg for f in t.lint()))
            p["assets"]["src_manifest"] = man
            t.put_yaml("projects/zlib/project.yaml", p)
            r = t.yaml("release.yaml")
            del r["recipes"]
            t.put_yaml("release.yaml", r)
            self.assertTrue(any("assets.bin.recipe, recipe.tar.zst in v2026.11.0, is not one of release.yaml's recipes"
                                in f.msg for f in t.lint()))

    def test_each_binary_archive_is_named_for_its_project(self):
        """The release workflows read an archive's project from its name, so zlib's must be zlib-bin.tar.zst; two
        projects that swap their archives' names are refused (the control: the fixture lints clean)."""
        with tree() as t:
            self.assertEqual([str(f) for f in t.lint()], [])
            for name, other in (("zlib", "json"), ("json", "zlib")):
                p = t.yaml("projects/%s/project.yaml" % name)
                p["assets"]["bin"]["file"] = other + "-bin.tar.zst"
                t.put_yaml("projects/%s/project.yaml" % name, p)
            found = [str(f) for f in t.lint()]
            for name in ("zlib", "json"):
                self.assertTrue(any("projects/%s/project.yaml" % name in f and "assets.bin.file must be %s-bin.tar.zst"
                                    % name in f for f in found), found)

    def test_the_source_assets_and_the_recipe_in_a_second_release(self):
        """A GitHub release holds at most 1,000 files, so the source assets and the recipe may be attached to
        v<release>-src, and a binary archive is never in a source release (the control: the fixture, everything in
        v2026.11.0, lints clean)."""
        with tree() as t:
            self.assertEqual([str(f) for f in t.lint()], [])
            p = t.yaml("projects/zlib/project.yaml")
            for k in ("src", "src_manifest"):
                p["assets"][k]["release"] = "v2026.11.0-src"
            p["assets"]["bin"]["recipe"]["release"] = "v2026.11.0-src"
            t.put_yaml("projects/zlib/project.yaml", p)
            j = t.yaml("projects/json/project.yaml")
            j["assets"]["bin"]["recipe"]["release"] = "v2026.11.0-src"
            t.put_yaml("projects/json/project.yaml", j)
            r = t.yaml("release.yaml")
            r["recipes"][0]["release"] = "v2026.11.0-src"
            t.put_yaml("release.yaml", r)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            page = t.read("projects/zlib/README.md")
            self.assertIn("Corresponding source, in release [v2026.11.0-src](", page)
            self.assertIn("`recipe.tar.zst`, this release's build recipe", page)
            p["assets"]["bin"]["release"] = "v2026.11.0-src"
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertTrue(any("assets.bin is attached to v2026.11.0-src, a release of source assets" in f.msg
                                for f in t.lint()))
            p["assets"]["bin"]["release"] = "v2026.11.0-sources"
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertIn("schema", rules_of(t.lint()))

    def test_a_copyleft_library_withholds_every_binary(self):
        """A GPL or LGPL library makes every binary copyleft, whatever the
        binary's own expression says; with no source bundle every build and
        statement is withheld, and the project says why."""
        with tree() as t:
            p = t.yaml("projects/zlib/project.yaml")
            p["library"]["licence"] = "LGPL-2.1-or-later"
            del p["assets"]["src"], p["assets"]["src_manifest"]
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertTrue(any("source bundle" in f.msg for f in t.lint()))
            del p["assets"]
            p["withheld"] = {"source_bundle": True}
            t.put_yaml("projects/zlib/project.yaml", p)
            n = 0
            for h in ("checksum_fuzzer", "api-driver"):
                y = t.yaml("projects/zlib/%s/harness.yaml" % h)
                for b in y["builds"].values():
                    b["withheld"] = "source-bundle"
                    for k in ("bytes", "sha256", "segments"):
                        del b[k]
                    n += 1
                for s in y["statements"].values():
                    for k in ("witness", "binds_checks"):
                        s.pop(k, None)
                    s["status"], s["withheld"] = "withheld", "source-bundle"
                t.put_yaml("projects/zlib/%s/harness.yaml" % h, y)
                # a withheld build shows no SHA-256, so it has no symbol fact either (lint, paths)
                shutil.rmtree(t.path("projects/zlib/%s/symbols" % h), ignore_errors=True)
            r = t.yaml("release.yaml")
            r["counts"]["binaries"] -= n
            t.put_yaml("release.yaml", r)
            self.assertEqual(t.generate(), 1)         # the statement files it rendered before are now stale
            for line in t.last_output.splitlines():
                if line.endswith("no longer produce; remove it"):
                    os.unlink(t.path(line.split(":")[0]))
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            self.assertIn("under a copyleft licence", t.read("projects/zlib/README.md"))
            self.assertIn("No binaries are attached", t.read("projects/zlib/README.md"))
            self.assertIn("withheld: waits for its source bundle", t.read("projects/zlib/checksum_fuzzer/README.md"))

    def test_withheld_must_say_why(self):
        with tree() as t:
            p = t.yaml("projects/zlib/project.yaml")
            p["withheld"] = {}
            t.put_yaml("projects/zlib/project.yaml", p)
            self.assertTrue(any("names no reason" in f.msg for f in t.lint()))


class Recipes(unittest.TestCase):
    """release.yaml lists the recipes, at most one in each GitHub release. Each project's binary archive pins the one
    it was built with (assets.bin.recipe), in any release, and every build record of the project cites it too."""
    JSON = "projects/json/project.yaml"
    JSON_RECORD = "proofs/json/fuzzer-parse_bjdata/provenance/PROVENANCE.yaml"
    APART = ("Corresponding source, in release [v2026.11.0](", "the build recipe these binaries were built with "
             "(the build scripts, pins and patches), `%s` in release [v2026.12.0-src](" % NEXT_RECIPE["file"])

    def test_a_later_release_adds_source_assets_with_a_recipe_of_its_own(self):
        with tree() as t:
            later_release(t)
            self.assertEqual([str(f) for f in t.lint()], [])
            self.assertIn("`json-src.MANIFEST.tsv`, which says where the build lays each one down; and "
                          "`%s`, this release's build recipe" % NEXT_RECIPE["file"], t.read("projects/json/README.md"))
            self.assertIn("Corresponding source, in release [v2026.12.0-src](", t.read("projects/json/README.md"))
            zlib = t.read("projects/zlib/README.md")
            self.assertIn("Corresponding source, in release [v2026.11.0](", zlib)
            self.assertIn("`recipe.tar.zst`, that release's build recipe", zlib)

    def test_a_recipe_only_rebuild_leaves_the_source_asset_where_it_is(self):
        with tree() as t:
            recipe_only_rebuild(t)
            self.assertEqual([str(f) for f in t.lint()], [])
            zlib = t.read("projects/zlib/README.md")
            for text in self.APART:
                self.assertIn(text, zlib)

    def test_a_project_without_a_build_record_pins_a_later_recipe(self):
        with tree() as t:
            recipe_only_rebuild(t, record=False)
            self.assertEqual(facts.load(t.root).records, {})
            self.assertEqual([str(f) for f in t.lint()], [])
            zlib = t.read("projects/zlib/README.md")
            for text in self.APART:
                self.assertIn(text, zlib)

    def test_an_archive_and_its_build_records_cite_one_listed_recipe(self):
        with tree() as t:
            later_release(t)
            t.write(self.JSON_RECORD, build_record(FIXTURE_RECIPE))
            self.assertTrue(any(self.JSON_RECORD in f and "recipe.asset, recipe.tar.zst in v2026.11.0, is not the "
                                "recipe of projects/json's binary archive (assets.bin.recipe: %s in "
                                "v2026.12.0-src)" % NEXT_RECIPE["file"] in f for f in map(str, t.lint())))
            unlisted = dict(NEXT_RECIPE, sha256="9b" * 32)
            p = t.yaml(self.JSON)
            p["assets"]["bin"]["recipe"] = unlisted
            t.put_yaml(self.JSON, p)
            t.write(self.JSON_RECORD, build_record(unlisted))
            found = [str(f) for f in t.lint()]
            self.assertTrue(any(self.JSON in f and "assets.bin.recipe, %s in v2026.12.0-src, is not one "
                                "of release.yaml's recipes" % NEXT_RECIPE["file"] in f for f in found), found)
            self.assertFalse(any(self.JSON_RECORD in f for f in found), found)
            t.write(self.JSON_RECORD, "schema: oss-verify-proofs build record v1\n")
            self.assertTrue(any(self.JSON_RECORD in f and "recipe.asset: expected a mapping" in f
                                for f in map(str, t.lint())))

    def test_a_fallback_record_may_cite_no_recipe(self):
        """A fallback record's binaries were built by the unpublished internal recipe, so it cites none; any other
        record without recipe.asset is refused (above)."""
        with tree() as t:
            t.write(self.JSON_RECORD, "schema: oss-verify-proofs build record v1\n"
                                      "fallback: {reason: built before the recipe was published}\n")
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            self.assertEqual(facts.load(t.root).records, {})

    ZLIB = "projects/zlib/project.yaml"
    ZLIB_RECORD = "proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.yaml"

    def test_a_private_project_may_pin_a_recipe_of_its_own(self):
        """A `release: private` project, which no public release carries, may pin a recipe release.yaml does not list
        (one kept in this repository's drafts), by its sha256; any other project may not. Its build records cite that
        pin, sha256 and all, and a private pin that names a listed recipe's file is refused unless it is that recipe."""
        with tree() as t:
            own_recipe(t, "json", OWN_RECIPE, self.JSON_RECORD)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            p = t.yaml(self.JSON)
            del p["release"]
            t.put_yaml(self.JSON, p)
            found = [str(f) for f in t.lint()]
            self.assertTrue(any(self.JSON in f and "assets.bin.recipe, %s in v2026.11.7-src, is not one "
                                "of release.yaml's recipes" % OWN_RECIPE["file"] in f for f in found), found)
            own_recipe(t, "json", OWN_RECIPE)
            # a build record that cites the pin with another sha256
            t.write(self.JSON_RECORD, build_record(dict(OWN_RECIPE, sha256="7b" * 32)))
            found = [str(f) for f in t.lint()]
            own = OWN_RECIPE["file"]
            self.assertTrue(any(self.JSON_RECORD in f and "recipe.asset, %s in v2026.11.7-src, is not the recipe of "
                                "projects/json's binary archive (assets.bin.recipe: %s in v2026.11.7-src)" % (own, own)
                                in f for f in found), found)
            # a private pin with the file name of the listed recipe, and another sha256
            own_recipe(t, "json", dict(FIXTURE_RECIPE, sha256="7b" * 32), self.JSON_RECORD)
            found = [str(f) for f in t.lint()]
            self.assertTrue(any(self.JSON in f and "assets.bin.recipe, recipe.tar.zst in v2026.11.0, names the file of "
                                "release.yaml's recipe in v2026.11.0, but is not that recipe" in f for f in found), found)
            self.assertFalse(any(self.JSON_RECORD in f for f in found), found)

    def test_two_private_projects_pin_recipes_of_their_own(self):
        """Two private projects, each with a recipe and a build record of its own, lint clean; so do two that pin one
        and the same recipe."""
        with tree() as t:
            own_recipe(t, "zlib", OWN_RECIPE, self.ZLIB_RECORD)
            own_recipe(t, "json", OTHER_OWN_RECIPE, self.JSON_RECORD)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            own_recipe(t, "json", OWN_RECIPE, self.JSON_RECORD)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])

    def test_two_private_recipes_with_one_file_name_are_one_recipe(self):
        """fetch checks one recipe per (release, file), and a download keeps the assets of every release in one
        directory by file name: two private pins with one file name and another release, bytes or sha256 are refused,
        against each project."""
        for change in ({"sha256": "7b" * 32}, {"bytes": 4000001}, {"release": "v2026.12.0-src"}):
            with self.subTest(change=change), tree() as t:
                own_recipe(t, "zlib", OWN_RECIPE, self.ZLIB_RECORD)
                own_recipe(t, "json", dict(OWN_RECIPE, **change), self.JSON_RECORD)
                found = [str(f) for f in t.lint()]
                for path, other in ((self.JSON, "zlib"), (self.ZLIB, "json")):
                    self.assertTrue(any(path in f and "has the file name of projects/%s's own recipe" % other in f
                                        for f in found), found)
                self.assertFalse(any("PROVENANCE.yaml" in f for f in found), found)

    def test_a_private_project_names_its_recipe(self):
        """A private project's binary archive names its recipe as every other's does: none is refused."""
        with tree() as t:
            own_recipe(t, "json", OWN_RECIPE, self.JSON_RECORD)
            p = t.yaml(self.JSON)
            del p["assets"]["bin"]["recipe"]
            t.put_yaml(self.JSON, p)
            found = [str(f) for f in t.lint()]
            self.assertTrue(any(self.JSON in f and "assets.bin.recipe is missing" in f for f in found), found)

    def test_a_release_carries_one_recipe_and_each_file_name_once(self):
        with tree() as t:
            later_release(t)
            r = t.yaml("release.yaml")
            r["recipes"].append(dict(NEXT_RECIPE, file=recipe_file(3), sha256="9b" * 32))
            t.put_yaml("release.yaml", r)
            self.assertTrue(any("recipes lists more than one recipe in v2026.12.0-src" in f.msg for f in t.lint()))
            r["recipes"][-1] = dict(FIXTURE_RECIPE, release="v2026.13.0-src", sha256="9b" * 32)
            t.put_yaml("release.yaml", r)
            found = [f.msg for f in t.lint()]
            self.assertTrue(any("recipes names the file recipe.tar.zst more than once" in m for m in found), found)
            self.assertFalse(any("more than one recipe in" in m for m in found), found)


class RecipeShapes(unittest.TestCase):
    """oft reads both shapes of release.yaml: `recipes` with a recipe on each binary archive, and the shape before it,
    which a published tree still has: one `recipe`, which every archive was built with and none names another."""
    PAGES = ("projects/zlib/README.md", "projects/json/README.md")
    ZLIB = "projects/zlib/project.yaml"

    def test_the_shape_before_recipes_reads_as_its_one_recipe(self):
        with tree() as t:
            newer = {p: t.read(p) for p in self.PAGES}
            older_shape(t)
            t.write("proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.yaml", build_record())
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            self.assertEqual({p: t.read(p) for p in self.PAGES}, newer)
            t.write("proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.yaml", build_record(NEXT_RECIPE))
            self.assertTrue(any("recipe.asset, %s in v2026.12.0-src, is not the recipe of projects/zlib's binary archive "
                                "(release.yaml's recipe: recipe.tar.zst in v2026.11.0)" % NEXT_RECIPE["file"] in f.msg
                                for f in t.lint()))

    def test_a_malformed_file_of_either_shape_fails(self):
        for shape, path, change in (("older", "recipe.sha256", lambda r: r["recipe"].update(sha256="x")),
                                    ("newer", "recipes[0].file", lambda r: r["recipes"][0].update(file="r.tar.gz"))):
            with self.subTest(shape=shape), tree() as t:
                if shape == "older":
                    older_shape(t)
                r = t.yaml("release.yaml")
                change(r)
                t.put_yaml("release.yaml", r)
                found = [f for f in t.lint() if f.rule == "schema"]
                self.assertTrue(any("release.yaml" in str(f) and path in f.msg for f in found), [str(f) for f in found])

    def test_an_older_release_yaml_that_does_not_load_adds_no_finding_to_the_records(self):
        with tree() as t:
            older_shape(t)
            t.write("proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.yaml", build_record())
            r = t.yaml("release.yaml")
            r["recipe"]["sha256"] = "x"
            t.put_yaml("release.yaml", r)
            found = [str(f) for f in t.lint() if "PROVENANCE.yaml" in str(f)]
            self.assertEqual(found, [])

    def test_release_yaml_names_recipe_or_recipes_not_both(self):
        with tree() as t:
            r = t.yaml("release.yaml")
            r["recipe"] = dict(FIXTURE_RECIPE)
            t.put_yaml("release.yaml", r)
            self.assertTrue(any("names both recipe and recipes" in f.msg for f in t.lint()))

    def test_a_newer_archive_names_its_recipe(self):
        with tree() as t:
            p = t.yaml(self.ZLIB)
            del p["assets"]["bin"]["recipe"]
            t.put_yaml(self.ZLIB, p)
            self.assertTrue(any(self.ZLIB in str(f) and "assets.bin.recipe is missing" in f.msg for f in t.lint()))

    def test_an_older_archive_names_no_other_recipe(self):
        with tree() as t:
            older_shape(t)
            p = t.yaml(self.ZLIB)
            p["assets"]["bin"]["recipe"] = dict(NEXT_RECIPE)
            t.put_yaml(self.ZLIB, p)
            self.assertTrue(any(self.ZLIB in str(f) and "assets.bin.recipe, %s in v2026.12.0-src, is not "
                                "one of release.yaml's recipes" % NEXT_RECIPE["file"] in f.msg for f in t.lint()))


class ExitChecks(unittest.TestCase):
    """A stops_with: exit check carries the source's argument and whether that exit() reaches the driver's
    guard (docs/facts.md, "A check")."""

    def exit_check(self, t, **kw):
        fields = dict({"stops_with": "exit", "exit_status": 1}, **kw)
        y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
        for c in y["checks"]:
            c.update(fields)
        t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
        return y

    def test_an_exit_check_says_whether_its_exit_reaches_the_guard(self):
        with tree() as t:
            self.exit_check(t)
            self.assertTrue(any("exit_reaches_guard goes with stops_with: exit" in f.msg for f in t.lint()))

    def test_exit_reaches_guard_belongs_to_an_exit_check_only(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["checks"][0]["exit_reaches_guard"] = True
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertTrue(any("exit_reaches_guard goes with stops_with: exit" in f.msg for f in t.lint()))

    def test_the_source_argument_loads_as_written(self):
        """exit(-1) and exit(258) are what the source passes, and facts.load keeps them as such; the schema's
        range is tested in Schemas.test_the_exit_guard_fields."""
        for arg in (-1, 258):
            with tree() as t:
                self.exit_check(t, exit_status=arg, exit_reaches_guard=True)
                h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
                self.assertEqual(h.data["checks"][0]["exit_status"], arg)

    def test_a_check_whose_exit_may_not_reach_the_guard_binds_no_statement(self):
        with tree() as t:
            self.exit_check(t, exit_reaches_guard="unknown")
            self.assertTrue(any("binds_checks is True, but the checks give False" in f.msg for f in t.lint()))


class FailureHandlers(unittest.TestCase):
    """Only a harness whose linked code installs no handler that can take over a failed check binds a halts
    statement (docs/facts.md, "Failure handlers")."""

    H = "projects/zlib/checksum_fuzzer/harness.yaml"

    def test_a_harness_not_read_or_with_a_handler_binds_no_statement(self):
        for value in ("present", "unknown", None):
            with tree() as t:
                y = t.yaml(self.H)
                if value is None:
                    del y["failure_handlers"]
                else:
                    y["failure_handlers"] = value
                t.put_yaml(self.H, y)
                self.assertTrue(any("binds_checks is True, but the checks give False" in f.msg for f in t.lint()),
                                value)

    def test_the_page_names_only_the_checks_a_statement_proves(self):
        with tree() as t:
            y = t.yaml(self.H)
            y["checks"][0]["live"] = "unknown"
            t.put_yaml(self.H, y)
            t.generate()
            page = t.read("projects/zlib/checksum_fuzzer/README.md")
            self.assertIn("so the checks at line 18 and line 19 above hold", page)
            self.assertIn("A failure of any of the checks at line 18 and line 19 ends the process", page)
            self.assertIn("No statement here proves the other check.", page)

    def test_the_page_names_no_other_check_when_every_check_is_bound(self):
        """A may-fail halts statement (exits: any) binds no exit check, so not every statement binds it, but no
        other check is left to name."""
        with tree() as t:
            y = t.yaml(self.H)
            y["checks"] = [dict(y["checks"][0], stops_with="exit", exit_status=1, exit_reaches_guard=True)]
            y["statements"]["plain_halts_may_fail"] = {"kind": "halts", "builds": ["plain"], "reading": "may-fail",
                                                      "exits": "any", "status": "open"}
            t.put_yaml(self.H, y)
            self.assertEqual(t.generate(), 0, t.last_output)
            page = t.read("projects/zlib/checksum_fuzzer/README.md")
            self.assertIn("A failure of the check at line", page)
            self.assertIn("so a proof of one of those statements implies it on every input it covers.\n", page)
            self.assertNotIn("No statement here proves the other", page)
            self.assertNotIn("so the checks above hold", page)

    def test_a_page_with_one_binding_check_of_three_counts_in_the_singular(self):
        with tree() as t:
            y = t.yaml(self.H)
            for c in y["checks"][1:]:
                c["live"] = "unknown"
            t.put_yaml(self.H, y)
            t.generate()
            page = t.read("projects/zlib/checksum_fuzzer/README.md")
            self.assertIn("so the check at line 17 above holds", page)
            self.assertIn("A failure of the check at line 17 ends the process", page)
            self.assertIn("No statement here proves the other checks.", page)


class Pending(unittest.TestCase):
    def test_a_pending_source_lists_no_files_and_anchors_no_checks(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["source"]["pending"] = True
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            msgs = [f.msg for f in t.lint()]
            self.assertTrue(any("lists no files" in m for m in msgs))
            y["source"]["files"] = []
            y["checks"] = []
            for s in y["statements"].values():
                s.pop("binds_checks", None)
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            os.unlink(t.path("projects/zlib/checksum_fuzzer/source/checksum_fuzzer.c"))
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            self.assertIn("source not in this release yet", t.read("projects/zlib/checksum_fuzzer/README.md"))


class Placeholders(unittest.TestCase):
    def test_a_placeholder_digest_blocks_only_a_release(self):
        with tree() as t:
            r = t.yaml("release.yaml")
            r["images"]["checker"] = r["images"]["checker"].split("@")[0] + "@sha256:" + "0" * 64
            t.put_yaml("release.yaml", r)
            self.assertEqual([str(f) for f in t.lint()], [])
            found = t.lint(release=True)
            self.assertEqual([(f.rule, f.where.split(":")[0]) for f in found], [("schema", "release.yaml")])
            self.assertTrue(found[0].msg.startswith("checker is a placeholder"), found[0].msg)

    def test_each_placeholder_is_its_own_finding(self):
        """Replacing one placeholder clears its finding and no other: a file is
        not reported once for however many placeholders it holds."""
        with tree() as t:
            r = t.yaml("release.yaml")
            r["images"]["runner"] = r["images"]["runner"].split("@")[0] + "@sha256:" + "0" * 64
            r["semantics"]["commit"] = "0" * 40
            t.put_yaml("release.yaml", r)
            found = t.lint(release=True)
            self.assertEqual(sorted(f.msg.split(" ")[0] for f in found), ["commit", "runner"])
            self.assertEqual({f.where.split(":")[0] for f in found}, {"release.yaml"})
            r["images"]["runner"] = t.yaml("release.yaml")["images"]["checker"]
            t.put_yaml("release.yaml", r)
            self.assertEqual([f.msg.split(" ")[0] for f in t.lint(release=True)], ["commit"])


class DistributionBodies(unittest.TestCase):
    """The two definition forms the rendered distributions use besides a plain
    byte list: an alphabet under List.nodup, and a long header in chunks."""

    def test_an_alphabet_under_nodup(self):
        from oft import rules
        body = ("Definition alpha : list byte :=\n  List.nodup (fun x y => decide (x = y))\n"
                "    [ Z_to_bv 8 48; Z_to_bv 8 49 ].\n")
        self.assertEqual(rules._bytes_def(body, "alpha"), b"01")

    def test_a_header_in_chunks(self):
        from oft import rules
        body = ("Definition hdr_000 : list byte :=\n  [ Z_to_bv 8 1; Z_to_bv 8 2 ].\n"
                "Definition hdr_001 : list byte :=\n  [ Z_to_bv 8 3 ].\n"
                "Definition hdr : list byte :=\n  ((hdr_000 ++ hdr_001))%list.\n")
        self.assertEqual(rules._bytes_def(body, "hdr"), b"\x01\x02\x03")
        self.assertIsNone(rules._bytes_def(body.replace("hdr_001 :", "other :"), "hdr"))



class Uninstrumented(unittest.TestCase):
    """builds.<b>.uninstrumented: what a build links that no sanitizer instruments."""
    H = "projects/zlib/checksum_fuzzer/harness.yaml"
    LIST = [{"name": "libc.a", "kind": "libc", "sha256": "a" * 64},
            {"name": "crc32_x86.S.o", "kind": "assembly", "source": "contrib/crc32_x86.S"}]

    def _with(self, t, build, items):
        y = t.yaml(self.H)
        y["builds"][build]["uninstrumented"] = items
        t.put_yaml(self.H, y)

    def test_a_list_on_a_published_build_is_clean(self):
        with tree() as t:
            self._with(t, "asan", self.LIST)
            self.assertEqual(t.generate(), 0)
            self.assertEqual([str(f) for f in t.lint()], [])

    def test_an_unknown_kind_or_an_empty_list(self):
        with tree() as t:
            self._with(t, "asan", [{"name": "x.a", "kind": "mystery"}])
            self.assertIn("schema", rules_of(t.lint()))
        with tree() as t:
            self._with(t, "asan", [])
            self.assertIn("schema", rules_of(t.lint()))

    def test_a_member_without_its_source(self):
        with tree() as t:
            self._with(t, "asan", [{"name": "crc32_x86.S.o", "kind": "assembly"}])
            self.assertTrue(any("names its source file" in f.msg for f in t.lint()))

    def test_twice(self):
        with tree() as t:
            self._with(t, "asan", [self.LIST[0], self.LIST[0]])
            self.assertTrue(any("listed twice" in f.msg for f in t.lint()))

    def test_a_withheld_build_shows_no_list(self):
        with tree() as t:
            self._with(t, "asan", self.LIST)
            y = t.yaml(self.H)
            rec = y["builds"]["asan"]
            rec["withheld"] = "not-yet-published"
            for k in ("bytes", "sha256", "segments"):
                rec.pop(k, None)
            t.put_yaml(self.H, y)
            self.assertTrue(any("no uninstrumented list" in f.msg for f in t.lint()))


class CopyleftSources(unittest.TestCase):
    """A binary bound by a GPL-family licence takes the release-wide toolchain source, and the source of every
    library it links from the build image (release.yaml sources and image_libraries)."""
    H = "projects/zlib/checksum_fuzzer/harness.yaml"

    def test_an_or_choice_does_not_bind(self):
        cases = {"GPL-2.0-only": True, "LGPL-2.1-or-later AND MIT": True, "BSD-3-Clause OR GPL-2.0-only": False,
                 "(BSD-3-Clause OR GPL-2.0-only) AND MIT": False, "GPL-2.0-only WITH Linux-syscall-note": True,
                 "(GPL-2.0-or-later OR LGPL-3.0-or-later) AND BSD-3-Clause": True, "Zlib": False, "NOASSERTION": False}
        for expr, binds in cases.items():
            self.assertEqual(facts.gpl_binds(expr), binds, expr)

    def _link(self, t, copyleft, in_sysroot_src=True, listed=True):
        y = t.yaml(self.H)
        for b in y["builds"].values():
            b["uninstrumented"] = [{"name": "libgmp.a", "kind": "image-library"}]
        t.put_yaml(self.H, y)
        r = t.yaml("release.yaml")
        r["sources"] = {"release": "sources-v1",
                        "toolchain": {"file": "toolchain-src.tar.zst", "bytes": 1, "sha256": "0" * 64},
                        "sysroot": {"file": "sysroot-src.tar.zst", "bytes": 1, "sha256": "0" * 64}}
        if listed:
            r["image_libraries"] = {"libgmp.a": {"library": "GMP", "licence": "LGPL-3.0-or-later OR GPL-2.0-or-later",
                                                 "copyleft": copyleft, "in_sysroot_src": in_sysroot_src}}
        t.put_yaml("release.yaml", r)

    def test_a_copyleft_library_from_the_image_names_both_archives(self):
        with tree() as t:
            self._link(t, copyleft=True)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            page = t.read("projects/zlib/README.md")
            self.assertIn("The binaries of `checksum_fuzzer` are under a GPL-family licence", page)
            self.assertIn("`toolchain-src.tar.zst`", page)
            self.assertIn("`sysroot-src.tar.zst`", page)
            self.assertIn("/releases/tag/sources-v1", page)

    def test_a_permissive_library_from_the_image_names_neither(self):
        with tree() as t:
            self._link(t, copyleft=False)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertNotIn("toolchain-src.tar.zst", t.read("projects/zlib/README.md"))

    def test_a_copyleft_binary_waits_for_its_libraries_source(self):
        with tree() as t:
            self._link(t, copyleft=True, in_sysroot_src=False)
            self.assertTrue(any("whose source sources.sysroot does not hold" in f.msg for f in t.lint()))

    def test_every_library_from_the_image_is_listed(self):
        with tree() as t:
            self._link(t, copyleft=True, listed=False)
            self.assertTrue(any("image_libraries does not list" in f.msg for f in t.lint()))


class SharedFiles(unittest.TestCase):
    """paths: no pull request changes a shared generated file (paths.SHARED); the line's render after the merge
    writes them, so a project page is asked for only in a release."""

    def test_a_pull_request_that_changes_a_shared_file_is_refused(self):
        for kind in ("contributor", "maintainer", "release"):
            for rel in ("index/statements.tsv", "README.md", "projects/zlib/README.md"):
                with tree() as t:
                    t.write(rel, t.read(rel) + "x\n")
                    found = [str(f) for f in t.lint(changed=[rel], pr_kind=kind)]
                    self.assertIn("paths %s: %s" % (rel, lint.SHARED_FILE), found)

    def test_one_that_deletes_a_shared_file_passes(self):
        for rel in ("index/statements.tsv", "projects/zlib/README.md"):
            with tree() as t:
                os.remove(t.path(rel))
                found = [f for f in t.lint(changed=[rel], pr_kind="maintainer")
                         if f.where in (rel, "projects/zlib")]
                self.assertEqual([str(f) for f in found], [])

    def test_a_project_page_is_required_only_in_a_release(self):
        with tree() as t:
            os.remove(t.path("projects/zlib/README.md"))
            want = "paths projects/zlib: no README.md (run ./oft generate)"
            self.assertNotIn(want, [str(f) for f in t.lint()])
            self.assertIn(want, [str(f) for f in t.lint(release=True)])

    def test_a_target_page_and_its_dune_files_still_pass(self):
        with tree() as t:
            changed = ["projects/zlib/checksum_fuzzer/README.md", "proofs/zlib/checksum_fuzzer/plain_halts/dune"]
            found = [f for f in t.lint(changed=changed, pr_kind="contributor") if f.rule == "paths"]
            self.assertEqual([str(f) for f in found], [])


class LintOnlyHand(unittest.TestCase):
    """paths: the moved skills' files are hand-written to lint alone (lint.LINT_ONLY_HAND), and paths.TABLE, part of
    the checker, does not name them."""

    MOVED = {".claude/skills/porting-released-proofs/": (
                 "SKILL.md", "references/asan-kit.md", "references/porting-pitfalls.md",
                 "references/search-tools.md", "references/second-corpus.md", "references/two-image-targets.md"),
             ".claude/skills/clean-room-restatement/": (
                 "SKILL.md", "references/sizing-a-programme.md", "references/writer-reviewer-checklists.md")}

    def test_each_moved_file_is_hand_to_lint_and_unknown_to_the_checker(self):
        for base, files in self.MOVED.items():
            for rel in files:
                self.assertEqual([c for c, _, _ in lint.classify_path(base + rel)], ["hand"], base + rel)
                self.assertEqual(paths.classify(base + rel), [], base + rel)

    def test_nothing_else_beside_them_is_admitted(self):
        for base in self.MOVED:
            for rel in ("references/notes.txt", "references/deeper/x.md", "scripts/x.sh"):
                self.assertEqual(lint.classify_path(base + rel), [], base + rel)

    def test_a_table_path_keeps_its_own_class(self):
        self.assertEqual(lint.classify_path(".claude/skills/adding-a-proof/SKILL.md"),
                         paths.classify(".claude/skills/adding-a-proof/SKILL.md"))

    def test_the_checker_image_s_pyyaml_pin_is_hand_to_lint_and_unknown_to_the_checker(self):
        """toolchain/requirements.txt, the PyYAML pin toolchain/checker.Dockerfile installs (OSSV-276): hand-written to
        lint alone, until the release that moves tools/oft/ gives it a paths.TABLE row."""
        self.assertEqual([c for c, _, _ in lint.classify_path("toolchain/requirements.txt")], ["hand"])
        self.assertEqual(paths.classify("toolchain/requirements.txt"), [])
        self.assertEqual(lint.classify_path("toolchain/other.txt"), paths.classify("toolchain/other.txt"))


class OldNamespace(unittest.TestCase):
    """paths: in a tree whose release.yaml renames the Rocq namespace, a file that still names the old one is a finding
    that names the command that fixes it (OSSV-162, Review Focus 5)."""

    NOTE = "notes/zlib.md"

    def note(self, t):
        t.write(self.NOTE, t.read(self.NOTE) + "From OssFuzzTheorems.Core Require Import Shapes.\n")

    def old_names(self, t):
        return [str(f) for f in t.lint() if f.msg.startswith("names the Rocq namespace OssFuzzTheorems")]

    def test_a_file_naming_the_old_namespace_in_a_renamed_tree_is_a_finding(self):
        with tree() as t:
            t.write("tools/oft/names.py", 'NAMESPACE_DEFAULT = "OssFuzzTheorems"\n')
            git_repo(t.root)
            out = io.StringIO()
            self.assertEqual(nsrename.rename_tree(t.root, "OSSVerify", "oss-verify", out=out, jobs=1), 0,
                             out.getvalue())
            # the shared generated files still name it until the line's render, and the tools always do: no finding
            self.assertEqual(self.old_names(t), [])
            self.note(t)
            self.assertEqual(self.old_names(t), ["paths %s: %s" % (self.NOTE, lint.OLD_NAMESPACE % "OSSVerify")])
            self.assertIn("run ./oft rename-namespace, or ./oft port-branch for a branch", lint.OLD_NAMESPACE)

    def test_the_old_namespace_in_a_tree_that_was_not_renamed_is_no_finding(self):
        with tree() as t:
            self.note(t)
            self.assertEqual(self.old_names(t), [])


if __name__ == "__main__":
    unittest.main()
