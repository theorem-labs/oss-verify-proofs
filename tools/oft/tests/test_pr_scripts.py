"""The scripts of pr.yml's steps under .github/scripts/pr/ (Dispatch issue OSSV-841).  GitHub starts no run of a
workflow file over 500 KB, so the long run texts of some steps live in files there, and each such step's whole `run:`
is one call, helpers.SCRIPT_CALL, which runs the file as `shell: bash` runs a step's text: `bash --noprofile --norc
-eo pipefail`.  A script runs from the same commit as the workflow only when the job checked that commit out into
head/, with .github/ in the checkout, before the step: this holds each call to that, and holds the rest of the shape
that keeps a script the step's text (no ${{ }} in it, which GitHub would not fill in; no other shell)."""
import os
import re
import unittest

from oft import paths, yamlio
from oft.tests import helpers
from oft.tests.helpers import REPO

WORKFLOWS = os.path.join(REPO, ".github", "workflows")
SCRIPTS = os.path.join(REPO, ".github", "scripts", "pr")
CHECKOUT = "actions/checkout@"
# tools/publish/ is the internal repository's alone (INTERNAL list): a release's cut removes it with every other
# internal path, so a tree without it is a release's
INTERNAL_TREE = os.path.isdir(os.path.join(REPO, "tools", "publish"))


def includes_github(checkout):
    """Whether the checkout step CHECKOUT puts .github/ in head/: no sparse checkout, a cone that names .github, or
    non-cone patterns that take every top-level entry and leave out nothing under .github/."""
    with_ = checkout.get("with") or {}
    patterns = [p.strip() for p in str(with_.get("sparse-checkout") or "").splitlines() if p.strip()]
    if not patterns:
        return True
    if str(with_.get("sparse-checkout-cone-mode", True)).lower() != "false":
        return any(p.rstrip("/") in (".github", ".github/scripts", ".github/scripts/pr") for p in patterns)
    return "/*" in patterns and not any(p.startswith("!/.github") for p in patterns)


def reads_the_calls(workflow, job, step):
    """Whether the step is the plan job's reach step of pr.yml, which names .github/scripts/pr/ in its text to read
    the scripts the made_from job calls, and calls none."""
    return (workflow, job, step.get("id")) == ("pr.yml", "plan", "reach")


class ScriptCalls(unittest.TestCase):
    def setUp(self):
        if not os.path.isdir(WORKFLOWS):
            self.skipTest("no .github/workflows/ beside tools/oft")
        self.calls = []        # (workflow, job, index, step, script)
        for name in sorted(os.listdir(WORKFLOWS)):
            if not name.endswith((".yml", ".yaml")):
                continue
            doc = yamlio.load_file(os.path.join(WORKFLOWS, name))
            for job_name, job in (doc.get("jobs") or {}).items():
                for i, step in enumerate(job.get("steps") or []):
                    run = step.get("run")
                    if reads_the_calls(name, job_name, step):
                        continue
                    if isinstance(run, str) and ".github/scripts/" in run:
                        m = helpers.SCRIPT_CALL.fullmatch(run)
                        self.assertIsNotNone(m, "%s %s step %d: a run that names .github/scripts/ is the one call "
                                                "helpers.SCRIPT_CALL, and nothing else: %r" % (name, job_name, i, run))
                        self.calls.append((name, doc, job_name, i, step, m.group(1)))

    def test_each_call_runs_a_script_that_is_there_and_each_script_is_called(self):
        called = {script for *_, script in self.calls}
        on_disk = {os.path.join(".github", "scripts", "pr", n) for n in os.listdir(SCRIPTS)} if os.path.isdir(SCRIPTS) \
            else set()
        self.assertEqual(sorted(called - on_disk), [], "calls of scripts that are not there")
        self.assertEqual(sorted(on_disk - called), [], "scripts no step calls")

    def test_each_script_is_read_from_the_commit_the_workflow_runs_from(self):
        """The job checks out the event's commit (no ref, no repository) into head/, with .github/ in it, before the
        step, and every checkout into head/ before the step does so: a script is never read from the base's tree or
        from another commit."""
        for name, _doc, job_name, i, step, script in self.calls:
            with self.subTest(workflow=name, job=job_name, step=step.get("name") or step.get("id")):
                steps = _doc["jobs"][job_name]["steps"]
                heads = [s for s in steps[:i] if str(s.get("uses", "")).startswith(CHECKOUT)
                         and (s.get("with") or {}).get("path") == "head"]
                self.assertTrue(heads, "no checkout into head/ before the step")
                for s in heads:
                    self.assertNotIn("ref", s.get("with") or {})
                    self.assertNotIn("repository", s.get("with") or {})
                    self.assertTrue(includes_github(s), "a checkout into head/ without .github/: %r" % s.get("with"))

    def test_each_script_runs_as_the_step_ran_its_text(self):
        """No shell of its own (the workflow's `bash`, which is `bash --noprofile --norc -eo pipefail`, as the call
        runs the file), and no ${{ }} in the file, which GitHub fills in only in a step's own text."""
        for name, doc, job_name, i, step, script in self.calls:
            with self.subTest(workflow=name, job=job_name, step=step.get("name") or step.get("id")):
                self.assertNotIn("shell", step)
                job = doc["jobs"][job_name]
                shell = ((job.get("defaults") or {}).get("run") or {}).get("shell") \
                    or ((doc.get("defaults") or {}).get("run") or {}).get("shell")
                self.assertEqual(shell, "bash")
                with open(os.path.join(REPO, script), encoding="utf-8") as f:
                    self.assertNotIn("${{", f.read())

    def test_the_jobs_whose_text_the_reach_step_compares_read_their_scripts_or_call_none(self):
        """The plan job's reach step compares two jobs' parsed text with the base's: the made_from job's, whose
        comparison reads each script a step calls in its place (MadeFromReachTest), and the farm_tests job's, whose
        comparison does not.  So no step of the farm_tests job calls a script: a change to one would reach no farm
        leg, where the same change in the job's own text runs every leg.  Moving one there needs that comparison to
        read scripts first, as the made_from one does."""
        doc = yamlio.load_file(os.path.join(WORKFLOWS, "pr.yml"))
        calls = [s.get("name") or s.get("id") for s in doc["jobs"]["farm_tests"].get("steps") or []
                 if helpers.SCRIPT_CALL.fullmatch(str(s.get("run", "")))]
        self.assertEqual(calls, [])
        reach = next(s for s in doc["jobs"]["plan"]["steps"] if s.get("id") == "reach")["run"]
        made_from = re.search(r"\n *# made-from records\n(.*?\n) *# end of made-from records\n", reach, re.S).group(1)
        self.assertIn(r"(\.github/scripts/pr/[a-z0-9-]+\.sh)", made_from)
        self.assertIn(r"'^\.github/(workflows/pr\.yml|scripts/pr/.*)$'", made_from)

    # The call's pattern is written again where helpers cannot be imported: the rehearsal script, the tests of
    # dev/licence/, dev/stream/, tools/publish/ and tools/enroll/, and the reach step of pr.yml itself.  A change to the
    # call changes each of these, and helpers.SCRIPT_CALL.  A release has no internal copy (paths.is_internal): the
    # cut removes it, so a release's tree skips each of those, and the internal tree reads every copy.
    COPIES = ("tools/oft/ci/pr-steps.sh", "dev/licence/test_made_from.py", "dev/stream/tests/test_repo_checks.py",
              "tools/publish/tests/test_workflows.py", "tools/enroll/tests/test_ci.py", ".github/workflows/pr.yml")

    def test_each_copy_of_the_call_s_pattern_reads_the_same_call(self):
        pieces = ("exec bash --noprofile --norc -eo pipefail ", r"GITHUB_WORKSPACE/head/(\.github/scripts/pr/[a-z0-9-]+\.sh)")
        for piece in pieces:
            self.assertIn(piece, helpers.SCRIPT_CALL.pattern)
        for rel in self.COPIES:
            with self.subTest(copy=rel):
                if not INTERNAL_TREE and paths.is_internal(rel):
                    self.skipTest("no tools/publish/ beside tools/oft: a release's tree, whose cut removes %s" % rel)
                with open(os.path.join(REPO, rel), encoding="utf-8") as f:
                    text = f.read()
                for piece in pieces:
                    self.assertIn(piece, text)
        for name, _doc, _job, _i, step, script in self.calls:
            self.assertEqual(step["run"], 'exec bash --noprofile --norc -eo pipefail "$GITHUB_WORKSPACE/head/%s"' % script)

    def test_inline_scripts_gives_the_workflow_its_steps_texts(self):
        """helpers.inline_scripts, for a test of a workflow's whole text: the text it gives parses to the jobs that
        with_scripts gives, and names no script."""
        with open(os.path.join(WORKFLOWS, "pr.yml"), encoding="utf-8") as f:
            text = f.read()
        inlined = helpers.inline_scripts(text)
        self.assertNotIn("$GITHUB_WORKSPACE/head/.github/scripts/", inlined)
        self.assertEqual(yamlio.load(inlined), helpers.with_scripts(yamlio.load(text)))

    def test_with_scripts_gives_each_step_its_script_s_text(self):
        doc = helpers.with_scripts(yamlio.load_file(os.path.join(WORKFLOWS, "pr.yml")))
        for job_name, job in doc["jobs"].items():
            for step in job.get("steps") or []:
                if not reads_the_calls("pr.yml", job_name, step):
                    self.assertNotRegex(str(step.get("run", "")), re.compile(r"\.github/scripts/pr/"))


if __name__ == "__main__":
    unittest.main()
