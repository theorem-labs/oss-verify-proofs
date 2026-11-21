"""The guard on the size of the workflow files: the step `no workflow file is over 490,000 bytes, so GitHub still starts
its runs`, in pr.yml's plan job and in workflow-size.yml, run as GitHub runs it.  GitHub starts no run of a workflow file
over 500 KB and shows one failed run with no job, so no check of the change runs and no step can say why (Dispatch issue
OSSV-841: #2907's pr.yml of 515,273 bytes got no run).  The step fails a change while each file still has room, and it
reads only the sizes of the change's own .github/workflows/ files: no tool of the base or of the change runs before it.
workflow-size.yml runs the same text in a workflow of its own, which starts whatever pr.yml's size."""
import os
import subprocess
import tempfile
import unittest

from oft import yamlio
from oft.tests.helpers import REPO

PR_YML = os.path.join(REPO, ".github", "workflows", "pr.yml")
SIZE_YML = os.path.join(REPO, ".github", "workflows", "workflow-size.yml")
WORKFLOWS = os.path.dirname(PR_YML)
GUARD = "no workflow file is over 490,000 bytes, so GitHub still starts its runs"
LIMIT = 490000
CHECKOUT = "actions/checkout"


def workflow(test, path):
    """The workflow file at PATH, loaded.  Only a tree with no .github/workflows/ at all skips the test (the runner
    image, which runs these tests, holds only tools/oft); a tree that has the folder and not the file fails it, so a
    deleted workflow-size.yml is a failure and not a skip."""
    if not os.path.isdir(WORKFLOWS):
        test.skipTest("no .github/workflows/ beside tools/oft")
    test.assertTrue(os.path.isfile(path), "no %s" % os.path.relpath(path, REPO))
    return yamlio.load_file(path)


def run_guard(step, files, folder=True, links=()):
    """STEP's run text, run as `shell: bash` runs it, in a workspace whose head/.github/workflows/ holds FILES ({name:
    size in bytes, or the bytes themselves}) and LINKS ((name, target) symbolic links); with FOLDER false there is no
    head/ at all.  (exit status, output)."""
    with tempfile.TemporaryDirectory() as work:
        where = os.path.join(work, "head", ".github", "workflows")
        if folder:
            os.makedirs(where)
        for name, body in files.items():
            with open(os.path.join(where, name), "wb") as f:
                f.write(b"#" * body if isinstance(body, int) else body)
        for name, target in links:
            os.symlink(target, os.path.join(where, name))
        script = os.path.join(work, "guard.sh")
        with open(script, "w") as f:
            f.write(step["run"])
        done = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", script], cwd=work,
                              capture_output=True, text=True, env={"PATH": os.environ["PATH"]})
        return done.returncode, done.stdout + done.stderr


def guard_of(test, steps, where):
    found = [i for i, s in enumerate(steps) if s.get("name") == GUARD]
    test.assertEqual(len(found), 1, "%s has one step %r" % (where, GUARD))
    return found[0]


class Boundary:
    """The guard's verdicts, for the step self.step."""

    def test_a_file_of_exactly_the_limit_passes(self):
        rc, out = run_guard(self.step, {"pr.yml": LIMIT, "other.yml": 10, "third.yaml": LIMIT})
        self.assertEqual(rc, 0, out)
        self.assertIn("each of the 3 workflow files is 490000 bytes or less", out)

    def test_one_byte_over_the_limit_fails_and_names_the_file(self):
        for name in ("pr.yml", "big.yaml"):
            with self.subTest(file=name):
                rc, out = run_guard(self.step, {"pr.yml": 5, name: LIMIT + 1, "small.yml": 100})
                self.assertEqual(rc, 1, out)
                self.assertIn("::error file=.github/workflows/%s::.github/workflows/%s is 490001 bytes, over 490000"
                              % (name, name), out)
                self.assertNotIn("small.yml", out)

    def test_bytes_are_counted_not_characters(self):
        """245,000 'é' are 490,000 bytes in UTF-8: they pass, and one byte more fails."""
        rc, out = run_guard(self.step, {"pr.yml": "é".encode() * 245000})
        self.assertEqual(rc, 0, out)
        rc, out = run_guard(self.step, {"pr.yml": "é".encode() * 245000 + b"#"})
        self.assertEqual(rc, 1, out)
        self.assertIn(".github/workflows/pr.yml is 490001 bytes", out)

    def test_every_file_over_the_limit_is_named_before_it_fails(self):
        rc, out = run_guard(self.step, {"pr.yml": 5, "a.yml": LIMIT + 1, "b.yml": LIMIT + 2})
        self.assertEqual(rc, 1, out)
        self.assertIn(".github/workflows/a.yml is 490001 bytes", out)
        self.assertIn(".github/workflows/b.yml is 490002 bytes", out)

    def test_an_upper_case_suffix_and_a_dotfile_are_measured_too(self):
        for name in ("UPPER.YML", "UPPER.YAML", "Mixed.Yml", ".hidden.yml"):
            with self.subTest(file=name):
                rc, out = run_guard(self.step, {"pr.yml": 5, name: LIMIT + 1})
                self.assertEqual(rc, 1, out)
                self.assertIn(".github/workflows/%s is 490001 bytes" % name, out)

    def test_a_file_that_is_no_workflow_is_not_measured(self):
        rc, out = run_guard(self.step, {"pr.yml": 5, "notes.md": LIMIT + 1, "x.yml.bak": LIMIT + 1})
        self.assertEqual(rc, 0, out)
        self.assertIn("each of the 1 workflow files", out)

    def test_a_workflow_that_is_a_symbolic_link_fails_rather_than_going_unmeasured(self):
        """A link (pr.yml itself, or any other workflow name) is neither measured as a file nor skipped: the step fails
        and names it."""
        for name in ("pr.yml", "other.YML"):
            with self.subTest(file=name):
                files = {"real.txt": 5} if name == "pr.yml" else {"pr.yml": 5, "real.txt": 5}
                rc, out = run_guard(self.step, files, links=[(name, "real.txt")])
                self.assertEqual(rc, 1, out)
                self.assertIn("::error file=.github/workflows/%s::.github/workflows/%s is a symbolic link" % (name, name),
                              out)

    def test_a_checkout_with_no_pr_yml_fails_rather_than_measuring_nothing(self):
        """No head/ at all, an empty workflows folder, or one without pr.yml: the checkout is not the tree it should be,
        and a pass would say nothing."""
        for case, files, folder in (("no head/", {}, False), ("an empty folder", {}, True),
                                    ("no pr.yml", {"other.yml": 5}, True)):
            with self.subTest(case=case):
                rc, out = run_guard(self.step, files, folder)
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::head/.github/workflows/pr.yml is not there", out)

    def test_the_step_takes_no_input_but_the_files(self):
        """Nothing can skip it, and GitHub fills nothing into its text."""
        self.assertEqual(set(self.step), {"name", "run"})
        self.assertNotIn("${{", self.step["run"])


class PlanJobGuard(Boundary, unittest.TestCase):
    def setUp(self):
        self.steps = workflow(self, PR_YML)["jobs"]["plan"]["steps"]
        self.index = guard_of(self, self.steps, "pr.yml's plan job")
        self.step = self.steps[self.index]

    def test_it_runs_right_after_the_checkout_and_before_the_base_and_its_tools(self):
        """It reads the checkout above it, and nothing the base step or a later step makes."""
        before = self.steps[self.index - 1]
        self.assertEqual(before.get("uses", "").split("@")[0], CHECKOUT)
        self.assertEqual(before["with"]["path"], "head")
        self.assertNotIn("ref", before["with"])
        self.assertEqual(self.steps[self.index + 1].get("id"), "base")

    def test_this_tree_s_workflow_files_are_within_the_limit(self):
        for name in sorted(os.listdir(WORKFLOWS)):
            if name.lower().endswith((".yml", ".yaml")):
                with self.subTest(file=name):
                    self.assertLessEqual(os.path.getsize(os.path.join(WORKFLOWS, name)), LIMIT)


class OwnWorkflowGuard(Boundary, unittest.TestCase):
    """workflow-size.yml: the guard that still runs once pr.yml is past the limit, so main's required checks name it."""

    def setUp(self):
        self.doc = workflow(self, SIZE_YML)
        self.assertEqual(list(self.doc["jobs"]), ["workflow-size"])
        self.job = self.doc["jobs"]["workflow-size"]
        self.steps = self.job["steps"]
        self.index = guard_of(self, self.steps, "workflow-size.yml")
        self.step = self.steps[self.index]

    def test_it_runs_the_same_text_as_pr_yml_s_guard(self):
        plan = workflow(self, PR_YML)["jobs"]["plan"]["steps"]
        self.assertEqual(self.step["run"], plan[guard_of(self, plan, "pr.yml's plan job")]["run"])

    def test_it_starts_on_every_pull_request_and_merge_queue_group_and_runs_as_pr_yml_s_steps_run(self):
        on = self.doc.get("on", self.doc.get(True))
        self.assertEqual(set(on), {"pull_request", "merge_group"})
        self.assertEqual(on["pull_request"]["types"], ["opened", "synchronize", "reopened", "ready_for_review"])
        self.assertEqual(self.doc["permissions"], {"contents": "read"})
        self.assertEqual(self.doc["defaults"], {"run": {"shell": "bash"}})
        self.assertNotIn("if", self.job)

    def test_it_checks_out_only_the_candidate_tree_s_workflows_and_nothing_else_runs(self):
        """The commit GitHub checks out for the event (no ref), only .github/workflows/, with no credentials left in
        it; and the one other step is the guard."""
        self.assertEqual(len(self.steps), 2)
        checkout = self.steps[0]
        self.assertEqual(checkout["uses"].split("@")[0], CHECKOUT)
        self.assertEqual(checkout["uses"].split("@")[1].split()[0], self.pinned_checkout())
        self.assertEqual(checkout["with"], {"path": "head", "persist-credentials": False, "filter": "blob:none",
                                            "sparse-checkout-cone-mode": False,
                                            "sparse-checkout": "/.github/workflows/\n"})
        self.assertEqual(self.index, 1)

    def pinned_checkout(self):
        """The commit pr.yml pins actions/checkout to."""
        pins = {s["uses"].split("@")[1] for j in workflow(self, PR_YML)["jobs"].values() for s in j.get("steps", [])
                if s.get("uses", "").startswith(CHECKOUT + "@")}
        self.assertEqual(len(pins), 1, pins)
        return pins.pop()


if __name__ == "__main__":
    unittest.main()
