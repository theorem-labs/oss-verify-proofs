"""statement-freeze.yml and pin-coherence.yml, run as GitHub runs them on a pull request (test_held_content.Job),
against a scratch origin that holds main and refs/pull/<n>/head and the stand-in gh of test_held_content.  The scratch
tree holds the base's copy of the two guards, a CODEOWNERS file of made-up logins, and a made-up project.  Each class
skips, with a reason, when a file of .github/ that it reads is absent."""
import os
import shutil
import tempfile
import unittest

from oft import yamlio
from oft.tests.test_held_content import (FREEZE_WORKFLOW as FREEZE, PINS_WORKFLOW as PINS, PIN_COHERENCE,
                                         STATEMENT_FREEZE, Job, Origin, absent, gh_calls, pull_request)

FREEZE_ABSENT = absent(FREEZE, STATEMENT_FREEZE)
PINS_ABSENT = absent(PINS, PIN_COHERENCE)
# the steps the tests read, by name
REVIEWS = "the reviews of this pull request"
ASSERTS = "a change to what this repository asserts is named, and needs a code owner"
MOVED = "a moved binary pin moves the statements about that binary"

OWNER, READER = "made-up-owner", "made-up-reader"
STATEMENTS_V = "projects/demo/unit/Statements.v"
HARNESS = "projects/demo/unit/harness.yaml"
ROW = "demo/unit/plain_halts"


def statements(fingerprint):
    return ("id\tkind\tbuilds\treading\texits\tstatus\tdetail\trevision\tfingerprint\tproof\n"
            "%s\thalts\tplain\tbudget\t0,2\topen\t-\t1\t%s\t-\n" % (ROW, fingerprint))


def harness(sha256):
    return ("schema: oss-fuzz-theorems/harness/1\nbuilds:\n  plain:\n    file: f.plain\n    bytes: 10\n"
            "    sha256: %s\nlicence: NOASSERTION\n" % sha256)


def binaries(sha256):
    return ("project\tharness\tbuild\tfile\tstatus\twithheld_reason\tbytes\tsha256\tlicence\n"
            "demo\tunit\tplain\tf.plain\tpublished\t-\t10\t%s\tNOASSERTION\n" % sha256)


class Guards(unittest.TestCase):
    """A scratch origin whose main holds the two guards, a CODEOWNERS file, and the made-up project demo with one
    fuzz target, its statement file, its build pin and its statement row."""
    SHA, OTHER_SHA, FINGERPRINT = "ab" * 32, "cd" * 32, "ef" * 32

    def setUp(self):
        root = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, root)
        files = {}
        for path in (STATEMENT_FREEZE, PIN_COHERENCE):
            with open(path, "rb") as f:
                files[".github/guards/" + os.path.basename(path)] = f.read()
        files.update({
            ".github/CODEOWNERS": "# made-up code owners\n/.github/ @%s\n**/Statements.v @%s\nindex/*.tsv @%s\n"
                                  % (OWNER, OWNER, OWNER),
            "README.md": "A scratch repository of the public guards' tests.\n",
            STATEMENTS_V: "Theorem demo_holds : 1 = 1.\n",
            HARNESS: harness(self.SHA),
            "index/statements.tsv": statements(self.FINGERPRINT),
            "index/binaries.tsv": binaries(self.SHA)})
        self.origin = Origin(os.path.join(root, "repository"), files)

    def job(self, workflow, name, head, event="pull_request", reviews=(), page_size=100):
        """The job `name` of workflow on event for pull request 7 at head; the stand-in gh serves reviews (each
        (login, state), of that head) at most page_size a page."""
        self.origin.publish(head)
        state = {"reviews": {"7": [{"login": login, "state": state, "at": "refs/pull/7/head"}
                                   for login, state in reviews]},
                 "page_size": page_size}
        return Job(self, workflow, name, pull_request(self.origin, head, event=event), self.origin, gh_state=state)


@unittest.skipIf(FREEZE_ABSENT, FREEZE_ABSENT)
class StatementFreeze(Guards):
    def freeze(self, head, **kw):
        return self.job(FREEZE, "statement-freeze", head, **kw)

    def test_it_starts_on_pull_request_and_on_its_reviews_and_runs_in_the_public_repository_alone(self):
        on = yamlio.load_file(FREEZE)["on"]
        self.assertNotIn("pull_request_target", on)
        self.assertEqual(on["pull_request"], {"types": ["opened", "synchronize", "reopened"]})
        self.assertEqual(on["pull_request_review"], {"types": ["submitted", "dismissed"]})
        head = self.origin.commit("a change", {"README.md": "Another line.\n"})
        self.assertTrue(self.freeze(head).runs())
        self.assertFalse(Job(self, FREEZE, "statement-freeze",
                             pull_request(self.origin, head, repository="acme/proofs"), self.origin).runs())

    def test_a_statement_change_with_no_approval_fails(self):
        head = self.origin.commit("a statement change", {STATEMENTS_V: "Theorem demo_holds : 1 = 2.\n"})
        job = self.freeze(head, reviews=[(READER, "APPROVED")]).run()
        self.assertEqual(job.step(REVIEWS)["outcome"], "success", job.output())
        step = job.step(ASSERTS)
        self.assertEqual(step["status"], 1, job.output())
        self.assertIn(STATEMENTS_V, step["stdout"])
        self.assertIn("no code owner has an APPROVED review of this exact head", step["stderr"])

    def test_a_change_that_touches_no_statement_and_no_pin_passes(self):
        head = self.origin.commit("a change", {"README.md": "Another line.\n"})
        job = self.freeze(head).run()
        self.assertEqual([o for _, o in job.outcomes()], ["success"] * 4, job.output())
        self.assertIn("this change alters no theorem statement", job.step(ASSERTS)["stdout"])

    def test_a_code_owner_s_approval_of_the_head_on_the_second_page_of_reviews_passes(self):
        head = self.origin.commit("a statement change", {STATEMENTS_V: "Theorem demo_holds : 1 = 2.\n"})
        job = self.freeze(head, event="pull_request_review", reviews=[(READER, "COMMENTED"), (OWNER, "APPROVED")],
                          page_size=1).run()
        step = job.step(ASSERTS)
        self.assertEqual(step["status"], 0, job.output())
        self.assertIn("approved at this head by %s" % OWNER, step["stdout"])
        calls = gh_calls(job.gh)
        self.assertEqual([(c["method"], c["endpoint"], c["pages"]) for c in calls],
                         [("GET", "repos/theorem-labs/oss-verify-proofs/pulls/7/reviews?per_page=100", 2)])
        self.assertIn("--paginate", calls[0]["argv"])

    def test_a_dismissed_approval_does_not_pass(self):
        head = self.origin.commit("a statement change", {STATEMENTS_V: "Theorem demo_holds : 1 = 2.\n"})
        job = self.freeze(head, event="pull_request_review", reviews=[(READER, "COMMENTED"), (OWNER, "DISMISSED")],
                          page_size=1).run()
        self.assertEqual(job.step(REVIEWS)["outcome"], "success", job.output())
        self.assertEqual(job.step(ASSERTS)["status"], 1, job.output())


@unittest.skipIf(PINS_ABSENT, PINS_ABSENT)
class PinCoherence(Guards):
    def pins(self, head):
        return self.job(PINS, "pin-coherence", head)

    def test_it_starts_on_pull_request_and_runs_in_the_public_repository_alone(self):
        on = yamlio.load_file(PINS)["on"]
        self.assertNotIn("pull_request_target", on)
        self.assertEqual(on["pull_request"], {"types": ["opened", "synchronize", "reopened"]})
        head = self.origin.commit("a change", {"README.md": "Another line.\n"})
        self.assertTrue(self.pins(head).runs())
        self.assertFalse(Job(self, PINS, "pin-coherence",
                             pull_request(self.origin, head, repository="acme/proofs"), self.origin).runs())

    def test_a_moved_build_sha256_with_no_change_to_its_statements_fails(self):
        head = self.origin.commit("a new binary", {HARNESS: harness(self.OTHER_SHA),
                                                   "index/binaries.tsv": binaries(self.OTHER_SHA)})
        job = self.pins(head).run()
        step = job.step(MOVED)
        self.assertEqual(step["status"], 1, job.output())
        self.assertIn("%s: the plain binary moved" % ROW, step["stdout"])

    def test_a_change_that_moves_no_pin_passes(self):
        head = self.origin.commit("a change", {"README.md": "Another line.\n"})
        job = self.pins(head).run()
        self.assertEqual([o for _, o in job.outcomes()], ["success"] * 3, job.output())


if __name__ == "__main__":
    unittest.main()
