"""pr.yml's prove job: `theorem prove` for each unit the plan names, and its check on the pull request's head.  Its
shape (what it waits for, what it may do, that it blocks nothing), its step that takes the base branch's tools (and
posts nothing when they have no tools/oft/ci/prove-pr, as in the public repository, whose release has none), and its
step that runs the driver, run as GitHub runs them with a stand-in driver.  The real driver's run in that step is in
test_prove_pr, which the release removes with the driver."""
import os
import shutil
import subprocess
import unittest

from oft.tests.helpers import tree
from oft.tests.test_keys import GIT, GIT_ENV
from oft.tests.test_workflow_verdicts import HAVE_WORKFLOWS, NO_WORKFLOWS, load, step

CHECKOUT = "actions/checkout@11bd71901bbe5b1630ceea73d27597364c9af683"
TOOLS_STEP = "the base branch's tools, which report on this change"
UNITS_STEP = "the units theorem prove reports on"
RUN_STEP = "theorem prove, and the check on the pull request's head"
SHA = "e" * 40   # the pull request's head, where the check goes


def job():
    return load("pr.yml")["jobs"]["prove"]


def run_script(text, cwd, env):
    """Runs a step's script as GitHub does, in cwd, its standard output and error as one log."""
    script = os.path.join(os.path.dirname(cwd), "step-%d.sh" % len(os.listdir(os.path.dirname(cwd))))
    with open(script, "w") as f:
        f.write(text)
    return subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", script], cwd=cwd,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=env)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class Shape(unittest.TestCase):
    def test_it_computes_its_own_units_and_blocks_nothing(self):
        """It waits for the plan alone, but plans its report's units itself; neither required nor main-gate waits for
        the report or the release-kind planning that serves it."""
        jobs = load("pr.yml")["jobs"]
        j = job()
        self.assertEqual(j["needs"], "plan")
        self.assertEqual(" ".join(j["if"].split()),
                         "${{ !cancelled() && needs.plan.result == 'success' && github.event_name == 'pull_request' "
                         "&& github.event.pull_request.head.repo.full_name == github.repository }}")
        self.assertNotIn("prove", jobs["required"]["needs"])
        self.assertNotIn("prove", jobs["main-gate"]["needs"])
        self.assertNotIn("unit_list", jobs["plan"]["outputs"])
        units = step(j, UNITS_STEP)
        self.assertEqual((units["id"], units["if"], units["env"]),
                         ("units", "steps.tools.outputs.run == 'true'",
                          {"BASE": "${{ needs.plan.outputs.base }}"}))
        self.assertEqual(step(j, RUN_STEP)["env"]["UNITS"], "${{ steps.units.outputs.unit_list }}")

    def test_it_may_write_checks_and_nothing_else(self):
        self.assertEqual(job()["permissions"], {"contents": "read", "checks": "write"})

    def test_it_runs_the_base_branch_s_tools_and_no_file_of_the_change(self):
        j = job()
        checkout = j["steps"][0]
        self.assertEqual((checkout["uses"], checkout["with"]),
                         (CHECKOUT, {"path": "head", "filter": "blob:none", "sparse-checkout": ".github"}))
        self.assertEqual(step(j, TOOLS_STEP)["env"], {"BASE": "${{ needs.plan.outputs.base }}"})
        run = step(j, RUN_STEP)
        self.assertEqual((run["working-directory"], run["if"]), ("base", "steps.tools.outputs.run == 'true'"))
        self.assertEqual({k: run["env"][k] for k in ("GH_TOKEN", "REPO", "BASE", "HEAD", "SHA")},
                         {"GH_TOKEN": "${{ github.token }}", "REPO": "${{ github.repository }}",
                          "BASE": "${{ needs.plan.outputs.base }}", "HEAD": "${{ github.sha }}",
                          "SHA": "${{ github.event.pull_request.head.sha }}"})
        for s in j["steps"]:
            with self.subTest(step=s.get("name", s.get("uses"))):
                self.assertNotIn("${{", s.get("run", ""))


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
@unittest.skipUnless(shutil.which("git"), "git is not installed")
class ToolsStep(unittest.TestCase):
    """The step that adds a worktree of the plan's base, its tools alone, beside the change's checkout: the job goes
    on only when those tools have tools/oft/ci/prove-pr."""

    def git(self, cwd, *args):
        done = subprocess.run(GIT + ["-C", cwd, *args], env=GIT_ENV, capture_output=True, text=True)
        self.assertEqual(done.returncode, 0, done.stderr)
        return done.stdout.strip()

    def tools_step(self, with_driver):
        with tree() as t:
            work = os.path.dirname(t.root)
            origin = os.path.join(work, "origin")
            os.mkdir(origin)
            self.git(origin, "init", "-q", "-b", "main")
            for key in ("uploadpack.allowFilter", "uploadpack.allowAnySHA1InWant"):
                self.git(origin, "config", key, "true")
            os.makedirs(os.path.join(origin, "tools", "oft", "ci"))
            name = "prove-pr" if with_driver else "check-units.sh"
            with open(os.path.join(origin, "tools", "oft", "ci", name), "w") as f:
                f.write("#!/bin/sh\n")
            os.chmod(os.path.join(origin, "tools", "oft", "ci", name), 0o755)
            self.git(origin, "add", "-A")
            self.git(origin, "commit", "-q", "-m", "base")
            base = self.git(origin, "rev-parse", "HEAD")
            with open(os.path.join(origin, "change.txt"), "w") as f:
                f.write("change\n")
            self.git(origin, "add", "-A")
            self.git(origin, "commit", "-q", "-m", "change")
            ws = os.path.join(work, "ws")
            os.mkdir(ws)
            self.git(ws, "clone", "-q", "--depth=1", "--filter=blob:none", "file://" + origin, "head")
            output = os.path.join(work, "output")
            done = run_script(step(job(), TOOLS_STEP)["run"], ws,
                              dict(GIT_ENV, BASE=base, GITHUB_WORKSPACE=ws, GITHUB_OUTPUT=output))
            with open(output) as f:
                outputs = dict(line.split("=", 1) for line in f.read().splitlines())
            return done, outputs, os.path.exists(os.path.join(ws, "base", "tools", "oft", "ci", "prove-pr"))

    def test_the_base_s_tools_run(self):
        done, outputs, there = self.tools_step(True)
        self.assertEqual((done.returncode, outputs, there), (0, {"run": "true"}, True), done.stdout)

    def test_base_tools_with_no_prove_pr_post_nothing(self):
        done, outputs, there = self.tools_step(False)
        self.assertEqual((done.returncode, outputs, there), (0, {"run": "false"}, False), done.stdout)
        self.assertIn("the base branch's tools have no tools/oft/ci/prove-pr: no report and no check", done.stdout)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class RunStep(unittest.TestCase):
    """The step that runs the driver in the base's tools, inside stop-commands, since the report is the head's data."""

    def test_its_exit_status_is_the_driver_s(self):
        with tree() as t:
            t.write("tools/oft/ci/prove-pr", "#!/bin/sh\necho '::warning::not a command here'\nexit 3\n")
            os.chmod(t.path("tools/oft/ci/prove-pr"), 0o755)
            done = run_script(step(job(), RUN_STEP)["run"], t.root, dict(os.environ, UNITS=""))
        self.assertEqual(done.returncode, 3)
        lines = done.stdout.splitlines()
        self.assertEqual(lines[1:], ["::warning::not a command here", "::%s::" % lines[0][len("::stop-commands::"):]])


if __name__ == "__main__":
    unittest.main()
