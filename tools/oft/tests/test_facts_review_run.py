"""tools/oft/ci/facts-review-run and facts-review-gather, and the review job's failure path in facts-review.yml: a
review that does not finish says why, in the job's log and in the comment, and gather fetches only what it gathers.

On internal #86 (run 40224321468) the review agent exited 1 twice and the log showed nothing of why, and gather's
`git archive` fetched the whole head commit (8.5 GB) until the fetch broke. The workflow is in the internal
repository only (`oft release-tree` removes it), so the tests that read it skip where it is not; the scripts and
these tests ship."""
import json
import os
import re
import shutil
import subprocess
import tempfile
import unittest

from oft import yamlio
from oft.tests.helpers import REPO
from oft.tests.test_facts_review_gate import API, FAKE_GH, GATHER, HAVE_WORKFLOW, NO_WORKFLOW, WORKFLOW

RUN = os.path.join(REPO, "tools", "oft", "ci", "facts-review-run")
COMMENT = os.path.join(REPO, "tools", "oft", "ci", "facts-review-comment")
# A stand-in for the review agent's tool, which facts-review-run runs in an environment of its own, through
# facts-review-served: on its call N it prints the file `result.N` beside it and exits with the status in `status.N`,
# if there is a `status.N`, and else prints `result`, if there is one, and exits with the status in `status`. It
# prints as `--output-format stream-json` does: a result that is a JSON object comes after a turn of the model it was
# asked for, as a `result` event whose modelUsage names Anthropic's API; any other text is printed as it is. It counts
# its calls in `calls`, and writes the identity token it was given, if any, to `tokens`.
FAKE_CLAUDE = """#!/usr/bin/env bash
here=$(dirname "$0")
n=$(( $(cat "$here/calls" 2> /dev/null || echo 0) + 1 ))
echo "$n" > "$here/calls"
[ -n "${ANTHROPIC_IDENTITY_TOKEN_FILE:-}" ] && cat "$ANTHROPIC_IDENTITY_TOKEN_FILE" >> "$here/tokens"
model=none prev=""
for a in "$@"; do [ "$prev" = --model ] && model=$a; prev=$a; done
result=$here/result status=$here/status
[ -f "$here/status.$n" ] && result=$here/result.$n status=$here/status.$n
if [ -f "$result" ] && jq -se 'length == 1 and (.[0] | type) == "object"' "$result" > /dev/null 2>&1; then
  printf '{"type": "assistant", "message": {"id": "msg_%s", "model": "%s", "content": []}}\\n' "$n" "$model"
  jq -c --arg m "$model" '{type: "result"} + . + (if has("modelUsage") then {} else
    {modelUsage: {($m): {provider: "firstParty", canonicalModel: $m}}} end)' "$result"
elif [ -f "$result" ]; then
  cat "$result"
fi
exit "$(cat "$status")"
"""
# A stand-in for the GitHub identity token endpoint: a new token on each call, none at all once `curl-fails` is there
# beside it, and an answer with no token (`{}`) once `curl-empty` is. It writes down its arguments in `curl.argv` and
# the headers it read on standard input (`-H @-`) in `curl.headers`.
FAKE_CURL = """#!/usr/bin/env bash
here=$(dirname "$0")
printf '%s\\0' "$@" >> "$here/curl.argv"
for a in "$@"; do [ "$a" = @- ] && cat >> "$here/curl.headers"; done
n=$(( $(cat "$here/curls" 2> /dev/null || echo 0) + 1 ))
echo "$n" > "$here/curls"
[ -f "$here/curl-fails" ] && exit 22
[ -f "$here/curl-empty" ] && { echo '{}'; exit 0; }
echo "{\\"value\\": \\"jwt-$n\\"}"
"""
MAX_TURNS = {"type": "result", "subtype": "error_max_turns", "is_error": True, "num_turns": 201,
             "duration_ms": 845123}
MAX_TURNS_WHY = ("the review agent ended with exit status 1, error_max_turns after 201 turns and 845 seconds, "
                 "and wrote no review (an error result)")
# A record of what answered, as facts-review-served writes it, that its check passes, and the line the check prints.
SERVED_OK = ("asked anthropic/claude-opus-5-5\nendpoint api.anthropic.com\nusage firstParty/claude-opus-5-5\n"
             "firstParty/claude-opus-5-5 3\n")
ANSWERED_OK = "firstParty/claude-opus-5-5 (3 turns)"


def write(path, text, mode=None):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        f.write(text)
    if mode:
        os.chmod(path, mode)


def failure_line(workflow_step):
    """The review step's pattern for the line of failure.txt it shows, from the workflow's own text."""
    m = re.search(r"grep -m1 -xE '([^']+)' \.review/failure\.txt", workflow_step)
    assert m, "the review step no longer reads .review/failure.txt with grep -m1 -xE"
    return re.compile(m.group(1))


@unittest.skipUnless(shutil.which("jq"), "jq is not installed")
class RunTest(unittest.TestCase):
    """facts-review-run against a stand-in claude: how each way the agent can end reaches the log and failure.txt."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="oft-review-run-")
        self.dir = os.path.realpath(self._tmp.name)
        write(os.path.join(self.dir, "bin", "claude"), FAKE_CLAUDE, 0o755)
        write(os.path.join(self.dir, "bin", "curl"), FAKE_CURL, 0o755)
        write(os.path.join(self.dir, ".review", "changed.txt"), "M\tprojects/zlib/project.yaml\n")
        # The review step's own environment: the token file it wrote, and what a new token is fetched with.
        self.token_file = os.path.join(self.dir, "oidc", "jwt")
        write(self.token_file, "jwt-0\n")
        self.env = dict(os.environ, PATH=os.path.join(self.dir, "bin") + os.pathsep + os.environ["PATH"], PR="7",
                        ANTHROPIC_IDENTITY_TOKEN_FILE=self.token_file, ACTIONS_ID_TOKEN_REQUEST_TOKEN="t",
                        ACTIONS_ID_TOKEN_REQUEST_URL="https://token.example/?x=1")

    def tearDown(self):
        self._tmp.cleanup()

    def run_review(self, result, status, *later):
        """facts-review-run, over a claude that ends with `result` and `status` on each call, or, given `later`
        (result, status) pairs, with the first pair on its first call and the pairs of `later` on the calls after."""
        bin_dir = os.path.join(self.dir, "bin")
        for name in os.listdir(bin_dir):
            if name not in ("claude", "curl", "curl-fails", "curl-empty"):
                os.remove(os.path.join(bin_dir, name))
        calls = [(result, status), *later] if later else [(result, status)]
        for n, (r, s) in enumerate(calls, 1):
            suffix = f".{n}" if later else ""
            write(os.path.join(bin_dir, "status" + suffix), str(s))
            if r is not None:
                write(os.path.join(bin_dir, "result" + suffix), r if isinstance(r, str) else json.dumps(r))
        for name in ("failure.txt", "comment.md"):
            if os.path.exists(os.path.join(self.dir, ".review", name)):
                os.remove(os.path.join(self.dir, ".review", name))
        r = subprocess.run(["bash", RUN, ".review"], cwd=self.dir, env=self.env, capture_output=True, text=True)
        failure = os.path.join(self.dir, ".review", "failure.txt")
        why = None
        if os.path.exists(failure):
            with open(failure) as f:
                why = f.read()
        with open(os.path.join(bin_dir, "calls")) as f:
            self.calls = int(f.read())
        tokens = os.path.join(bin_dir, "tokens")
        self.tokens = []
        if os.path.exists(tokens):
            with open(tokens) as f:
                self.tokens = f.read().split()
        return r.returncode, r.stdout, r.stderr, why

    def test_a_turn_limit_says_so(self):
        rc, _, err, why = self.run_review(MAX_TURNS, 1)
        self.assertEqual(rc, 1, err)
        self.assertEqual(why, MAX_TURNS_WHY + ", on try 3 of 3\n")
        for n in (1, 2, 3):
            self.assertIn("facts-review-run: " + MAX_TURNS_WHY + " (try %d)" % n, err)
        self.assertEqual(self.calls, 3)
        self.assertEqual(self.tries(), ["try %d of 3, %s" % (n, MAX_TURNS_WHY) for n in (1, 2, 3)])

    def tries(self):
        with open(os.path.join(self.dir, ".review", "tries.txt")) as f:
            return f.read().splitlines()

    def test_the_cap_is_three_tries(self):
        """The measured rate (8 of about 28 tries died with nothing written, whatever the input) sets 3 tries: a review
        that fails twice and passes on its third is posted, and there is no fourth."""
        review = {"type": "result", "subtype": "success", "is_error": False, "num_turns": 103, "duration_ms": 592000,
                  "result": "No findings."}
        rc, out, err, why = self.run_review(None, 1, (None, 1), (review, 0))
        self.assertEqual(rc, 0, err)
        self.assertIsNone(why)
        self.assertEqual(self.calls, 3)
        self.assertIn("success after 103 turns and 592 seconds (try 3)", out)
        died = r"try [12] of 3, the review agent ended with exit status 1 after \d+ seconds, and wrote no review"
        self.assertRegex(self.tries()[0], died)
        self.assertRegex(self.tries()[1], died)
        self.assertEqual(self.tries()[2], "try 3 of 3, a review, success after 103 turns and 592 seconds")
        self.run_review(None, 1, (None, 1), (None, 1), (review, 0))
        self.assertEqual(self.calls, 3, "a fourth try")

    def test_a_review_that_fails_once_is_tried_again(self):
        """#138's head failed on run 40232827271 and passed on run 40238097164: one more try gets the review."""
        failed = dict(MAX_TURNS, subtype="error_during_execution", errors=["the stream ended"])
        review = {"type": "result", "subtype": "success", "is_error": False, "num_turns": 56, "duration_ms": 276000,
                  "result": "No findings."}
        rc, out, err, why = self.run_review(failed, 1, (review, 0))
        self.assertEqual(rc, 0, err)
        self.assertIsNone(why)
        self.assertEqual(self.calls, 2)
        self.assertIn("error_during_execution after 201 turns and 845 seconds, and wrote no review (an error result) "
                      "(try 1): the stream ended", err)
        with open(os.path.join(self.dir, ".review", "comment.md")) as f:
            self.assertEqual(f.read(), "No findings.\n")
        self.assertIn("success after 56 turns and 276 seconds (try 2)", out)

    def test_a_review_at_the_time_limit_is_not_tried_again(self):
        rc, _, err, why = self.run_review(None, 124)
        self.assertEqual(rc, 1, err)
        self.assertEqual(self.calls, 1)
        self.assertEqual(why, "the review agent ended with exit status 124, stopped at its 45-minute limit, "
                              "and wrote no review (output that is not one JSON object), on try 1 of 3\n")

    def test_each_try_gets_an_identity_token_of_its_own(self):
        """A GitHub identity token is single-use, so a second try with the first try's token is refused: the script
        writes a new one into the file the agent reads (the token endpoint here is a stand-in curl)."""
        self.run_review(MAX_TURNS, 1)
        self.assertEqual(self.tokens, ["jwt-0", "jwt-1", "jwt-2"])

    def test_the_request_token_for_a_new_identity_token_is_not_an_argument(self):
        """R104-07, in the request this script makes for each new identity token: the request token goes to curl on
        standard input, not in -H's argument, where any process on the machine can read it."""
        secret = "request-" + "token-" + "x" * 16
        self.env["ACTIONS_ID_TOKEN_REQUEST_TOKEN"] = secret
        self.run_review(MAX_TURNS, 1)
        self.assertEqual(self.tokens, ["jwt-0", "jwt-1", "jwt-2"])
        bin_dir = os.path.join(self.dir, "bin")
        with open(os.path.join(bin_dir, "curl.argv")) as f:
            self.assertNotIn(secret, f.read())
        with open(os.path.join(bin_dir, "curl.headers")) as f:
            self.assertEqual(f.read().splitlines()[0], f"Authorization: Bearer {secret}")

    def test_without_a_new_identity_token_there_is_no_second_try(self):
        write(os.path.join(self.dir, "bin", "curl-fails"), "")
        rc, _, err, why = self.run_review(MAX_TURNS, 1)
        self.assertEqual(rc, 1, err)
        self.assertEqual(self.calls, 1)
        self.assertEqual(self.tokens, ["jwt-0"])
        self.assertEqual(why, MAX_TURNS_WHY + ", on try 1 of 3, no more tries (no new identity token)\n")

    def test_an_answer_with_no_identity_token_is_no_new_token(self):
        # jq -r .value wrote the text null for `{}`, and the file held null as a token
        write(os.path.join(self.dir, "bin", "curl-empty"), "")
        rc, _, err, why = self.run_review(MAX_TURNS, 1)
        self.assertEqual(rc, 1, err)
        self.assertEqual(self.calls, 1)
        self.assertEqual(self.tokens, ["jwt-0"])
        self.assertEqual(why, MAX_TURNS_WHY + ", on try 1 of 3, no more tries (no new identity token)\n")

    def test_a_failed_model_call_puts_its_message_in_the_log_only(self):
        api_error = dict(MAX_TURNS, subtype="success", result="API Error: 529 Overloaded\n::error::not a command")
        rc, _, err, why = self.run_review(api_error, 1)
        self.assertEqual(rc, 1, err)
        self.assertIn("API Error: 529 Overloaded ::error::not a command", err)
        self.assertEqual(why, "the review agent ended with exit status 1, success after 201 turns and 845 seconds, "
                              "and wrote no review (an error result), on try 3 of 3\n")

    def test_an_agent_that_wrote_nothing_says_so(self):
        for result in (None, json.dumps({"subtype": "Bad Kind!", "num_turns": "x"})):
            with self.subTest(result=result):
                rc, _, err, why = self.run_review(result, 1)
                self.assertEqual(rc, 1, err)
                self.assertRegex(why, r"^the review agent ended with exit status 1 after \d+ seconds, "
                                      r"and wrote no review \((output that is not (one )?JSON( object)?|an error "
                                      r"result)\), on try 3 of 3\n$")
                self.assertIn("bytes in .review/review.json", err)

    def test_a_stream_line_that_is_no_event_is_not_published_or_tried_again(self):
        """The tool writes only JSON objects, one a line: a line that is not one could hide a turn, so
        facts-review-served stops the agent there and the review is not published."""
        for result in ("not json", "[1, 2]"):
            with self.subTest(result=result):
                rc, _, err, why = self.run_review(result, 1)
                self.assertEqual(rc, 4, err)
                self.assertEqual(self.calls, 1)
                self.assertEqual(why, "the review is not published, as the provider or model that answered it is not "
                                      "the one asked for or is not shown\n")
                self.assertIn("facts-review-run: the review is not published: ", err)
                self.assertIn("of its stream is not", err)
                self.assertEqual(self.tries()[-1], "try 1 of 3, not published, as the provider or model that answered "
                                                   "it is not the one asked for or is not shown")

    def test_another_provider_for_a_try_that_also_failed_is_not_published_or_tried_again(self):
        """The agent failed by itself (exit 1), and its record names another provider: not published, not tried
        again, whatever the agent's own status."""
        bedrock = dict(MAX_TURNS, modelUsage={"claude-opus-5-5": {"provider": "bedrock",
                                                                   "canonicalModel": "claude-opus-5-5"}})
        rc, _, err, why = self.run_review(bedrock, 1)
        self.assertEqual(rc, 4, err)
        self.assertEqual(self.calls, 1)
        self.assertIn("but bedrock/claude-opus-5-5 (1 turn) answered", err)
        self.assertEqual(why, "the review is not published, as the provider or model that answered it is not the one "
                              "asked for or is not shown\n")

    def test_an_error_result_fails_whatever_the_exit_status(self):
        rc, _, err, why = self.run_review(dict(MAX_TURNS, subtype="error_during_execution",
                                               errors=["the stream ended"]), 0)
        self.assertEqual(rc, 1, err)
        self.assertIn("the stream ended", err)
        self.assertIn("exit status 0, error_during_execution after 201 turns", why)

    def test_a_try_that_exits_0_without_a_review_says_why(self):
        """A start that failed exits 0 with a success result (#146's turn_setup_failed shape), and a result can be
        blank: the line names the terminal reason and which check refused it, in this script's words."""
        setup = {"type": "result", "subtype": "success", "is_error": False, "terminal_reason": "turn_setup_failed",
                 "num_turns": 1, "duration_ms": 2000, "result": "API Error: no turn ::error::x"}
        rc, _, err, why = self.run_review(setup, 0)
        self.assertEqual(rc, 1, err)
        self.assertEqual(why, "the review agent ended with exit status 0, success after 1 turns and 2 seconds, "
                              "terminal reason turn_setup_failed, and wrote no review (a run that did not reach its "
                              "end), on try 3 of 3\n")
        blank = {"type": "result", "subtype": "success", "is_error": False, "num_turns": 9, "duration_ms": 9000,
                 "result": " 1 2 "}
        rc, _, err, why = self.run_review(blank, 0)
        self.assertEqual(rc, 1, err)
        self.assertEqual(why, "the review agent ended with exit status 0, success after 9 turns and 9 seconds, "
                              "and wrote no review (a result with no words in it), on try 3 of 3\n")

    def test_no_half_written_identity_token_is_left(self):
        """Each new token is written to a file of its own and moved into place; none of those files is left."""
        self.run_review(MAX_TURNS, 1)
        oidc = os.path.dirname(self.token_file)
        self.assertEqual(sorted(os.listdir(oidc)), ["jwt"])

    def test_a_review_writes_the_comment(self):
        rc, out, err, why = self.run_review({"type": "result", "subtype": "success", "is_error": False,
                                             "num_turns": 56, "duration_ms": 276000, "result": "No findings."}, 0)
        self.assertEqual(rc, 0, err)
        self.assertIsNone(why)
        with open(os.path.join(self.dir, ".review", "comment.md")) as f:
            self.assertEqual(f.read(), "No findings.\n")
        self.assertIn("success after 56 turns and 276 seconds", out)

    @unittest.skipUnless(HAVE_WORKFLOW, NO_WORKFLOW)
    def test_the_review_step_shows_each_line_this_script_writes(self):
        """Every failure.txt line above matches the pattern the review step lets through to the comment."""
        step = next(s for s in yamlio.load_file(WORKFLOW)["jobs"]["review"]["steps"] if s.get("id") == "review")
        pattern = failure_line(step["run"])
        long_kind = dict(MAX_TURNS, subtype="e" * 220, num_turns=10 ** 12, duration_ms=10 ** 15)
        for result, status in ((MAX_TURNS, 1), (None, 1), (dict(MAX_TURNS, subtype="success"), 0), (long_kind, 1)):
            with self.subTest(result=result):
                _, _, err, why = self.run_review(result, status)
                self.assertTrue(pattern.fullmatch(why.rstrip("\n")), why + err)


@unittest.skipUnless(HAVE_WORKFLOW, NO_WORKFLOW)
class FailureStepTest(unittest.TestCase):
    """The review job's review step and the comment job's step, run as GitHub runs them, when the review fails."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="oft-review-step-")
        self.dir = self._tmp.name
        self.jobs = yamlio.load_file(WORKFLOW)["jobs"]
        self.output = os.path.join(self.dir, "output")

    def tearDown(self):
        self._tmp.cleanup()

    def run_step(self, job, step_id, env, name=None):
        steps = self.jobs[job]["steps"]
        step = next(s for s in steps if (s.get("id") == step_id if step_id else s.get("name") == name))
        script = os.path.join(self.dir, "step.sh")
        write(script, step["run"])
        if os.path.exists(self.output):
            os.remove(self.output)
        open(self.output, "w").close()
        env = dict(os.environ, GITHUB_OUTPUT=self.output, RUNNER_TEMP=self.dir, PR="7", **env)
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", script], cwd=self.dir, env=env,
                           capture_output=True, text=True)
        with open(self.output) as f:
            return r.returncode, r.stdout, f.read()

    def review_step(self, failure_text):
        """The review step, over a stand-in facts-review-run that exits 1 with failure_text in failure.txt."""
        write(os.path.join(self.dir, "tools", "oft", "ci", "facts-review-run"), "#!/usr/bin/env bash\nexit 1\n", 0o755)
        failure = os.path.join(self.dir, ".review", "failure.txt")
        if failure_text is None:
            if os.path.exists(failure):
                os.remove(failure)
        else:
            write(failure, failure_text + "\n")
        token = os.path.join(self.dir, "jwt")
        open(token, "w").close()
        return self.run_step("review", "review", {"ANTHROPIC_IDENTITY_TOKEN_FILE": token})

    @unittest.skipUnless(shutil.which("openssl"), "openssl is not installed")
    def test_the_review_step_shows_the_cause_and_passes_it_on(self):
        rc, out, output = self.review_step(MAX_TURNS_WHY)
        self.assertEqual(rc, 1, out)
        self.assertIn("::error::the facts review did not finish: " + MAX_TURNS_WHY + "\n", out)
        self.assertEqual(output, "failure=" + MAX_TURNS_WHY + "\n")
        self.assertFalse(os.path.exists(os.path.join(self.dir, "jwt")), "the identity token file is removed")

    def session_step(self, script):
        """The review step over a stand-in facts-review-run `script`, with REVIEW_SESSION set."""
        session = os.path.join(self.dir, "review-session")
        shutil.rmtree(session, ignore_errors=True)
        write(os.path.join(self.dir, "tools", "oft", "ci", "facts-review-run"),
              f"#!/usr/bin/env bash\nmkdir -p {session} .review\n{script}\n", 0o755)
        token = os.path.join(self.dir, "jwt")
        open(token, "w").close()
        return self.run_step("review", "review", {"ANTHROPIC_IDENTITY_TOKEN_FILE": token, "REVIEW_SESSION": session})

    @unittest.skipUnless(shutil.which("openssl"), "openssl is not installed")
    def test_the_review_step_says_whether_the_conversation_is_kept(self):
        """A review that kept its conversation says `kept`, which is what lets the next push resume at all; a failed
        run that left the restored conversation in place says nothing, so nothing is saved."""
        session = os.path.join(self.dir, "review-session")
        rc, out, output = self.session_step(f"echo id=x > {session}/session\necho review > .review/comment.md")
        self.assertEqual(rc, 0, out)
        self.assertTrue(output.startswith("session=kept\ncomment<<review-"), output)
        rc, out, output = self.session_step(f"echo id=x > {session}/session\nexit 2")
        self.assertEqual(rc, 2, out)
        self.assertEqual(output, "failure=facts-review-run ended with exit status 2\n")

    def test_only_the_keep_job_writes_the_cache(self):
        """A pull_request_target run has read-only cache access unless a job declares a mode that writes. The job that
        reads the pull request must not: only a job with no permissions, no checkout and no script, whose steps are
        the artifact download and the cache save, writes, and only after a review that kept its conversation."""
        self.assertEqual(self.jobs["review"]["cache-mode"], "read")
        upload = next(s for s in self.jobs["review"]["steps"] if s.get("uses", "").startswith("actions/upload-"))
        self.assertEqual(upload["if"], "${{ !cancelled() && steps.review.outputs.session == 'kept' }}")
        self.assertEqual(self.jobs["review"]["outputs"]["session"], "${{ steps.review.outputs.session }}")
        keep = self.jobs["keep"]
        self.assertEqual((keep["needs"], keep["permissions"], keep["cache-mode"]), ("review", {}, "write-only"))
        self.assertEqual(keep["if"], "${{ !cancelled() && needs.review.outputs.session == 'kept' }}")
        self.assertEqual([s["uses"].split("@")[0] for s in keep["steps"]],
                         ["actions/download-artifact", "actions/cache/save"])
        self.assertTrue(all("run" not in s for s in keep["steps"]))
        # The name the review job's own attempt gave it, which a re-run of the keep job alone still reads.
        self.assertEqual(keep["steps"][0]["with"]["name"], "${{ needs.review.outputs.artifact }}")
        self.assertEqual(self.jobs["review"]["outputs"]["artifact"], upload["with"]["name"])
        # A failed upload does not fail the review.
        self.assertIs(upload["continue-on-error"], True)
        restore = next(s for s in self.jobs["review"]["steps"]
                       if s.get("uses", "").startswith("actions/cache/restore@"))
        self.assertEqual(keep["steps"][1]["with"]["path"], restore["with"]["path"])
        self.assertEqual(keep["steps"][1]["with"]["key"], restore["with"]["key"])
        # The next push finds what this run saved by the prefix, not by the key, which is this run's own.
        self.assertTrue(keep["steps"][1]["with"]["key"].startswith(restore["with"]["restore-keys"]))
        self.assertTrue(restore["with"]["restore-keys"].endswith("/"))
        # On a run by hand (a trusted trigger) a job that says nothing could write: the workflow says `none`.
        default = yamlio.load_file(WORKFLOW)["cache-mode"]
        self.assertEqual(default, "none")
        writers = [name for name, job in self.jobs.items() if job.get("cache-mode", default) not in ("read", "none")]
        self.assertEqual(writers, ["keep"])

    @unittest.skipUnless(shutil.which("openssl"), "openssl is not installed")
    def test_the_review_step_shows_no_other_text(self):
        """A failure.txt that is missing, or holds anything but plain words, is not shown: a workflow command or a
        second output line could come through it. Only its first line of plain words is."""
        for text, shown in ((None, None), ("::warning::x", None), ("x" * 301, None), ("a: b", None),
                            ("a\nfailure=b", "a"), ("failure=b\nplain words", "plain words")):
            with self.subTest(text=text):
                rc, out, output = self.review_step(text)
                self.assertEqual(rc, 1, out)
                self.assertEqual(output, "failure=" + (shown or "facts-review-run ended with exit status 1") + "\n")

    def test_the_job_passes_the_cause_to_the_comment(self):
        self.assertEqual(self.jobs["review"]["outputs"]["failure"],
                         "${{ steps.review.outputs.failure || steps.gather.outputs.failure "
                         "|| steps.why.outputs.failure }}")
        step = next(s for s in self.jobs["comment"]["steps"] if "run" in s)
        self.assertEqual(step["env"]["FAILURE"], "${{ needs.review.outputs.failure }}")

    def plain_words(self, line):
        """The review step's filter for a line it lets through to the comment, over a line another step writes: the
        comment shows all three the same way, so none of them may carry anything but plain words."""
        step = next(s for s in self.jobs["review"]["steps"] if s.get("id") == "review")
        self.assertTrue(failure_line(step["run"]).fullmatch(line), line)

    def test_a_step_that_writes_no_cause_still_leaves_one(self):
        """A failure in the checkout, the dependencies, the agent's tool or the identity token: neither gather nor
        the review step writes a line, so the last step of the job writes one that sends the reader to the log."""
        why = next(s for s in self.jobs["review"]["steps"] if s.get("id") == "why")
        self.assertEqual(why["if"], "${{ failure() && steps.gather.outputs.failure == '' "
                                    "&& steps.review.outputs.failure == '' }}")
        rc, out, output = self.run_step("review", "why", {})
        self.assertEqual(why["env"]["REVIEW_OUTCOME"], "${{ steps.review.outcome }}")
        self.assertEqual(rc, 0, out)
        line = output.split("=", 1)[1].rstrip("\n")
        self.assertEqual(output, "failure=" + line + "\n")
        self.plain_words(line)
        # No review ran, so no record: the comment says that nothing shows what answered.
        self.assertIn(f"against `main`: {line}. What answered it, as the review agent's tool reported it: nothing "
                      "recorded which provider answered the review: it is not attributable. The maintainers review "
                      "the facts.", self.comment_body(line, served=""))
        # A review step that failed and wrote no line was stopped from outside facts-review-run.
        rc, out, output = self.run_step("review", "why", {"REVIEW_OUTCOME": "failure"})
        self.assertEqual(rc, 0, out)
        line = output.split("=", 1)[1].rstrip("\n")
        self.assertIn("the review step was stopped before it could say why", line)
        self.plain_words(line)

    def test_the_gather_step_says_it_failed(self):
        write(os.path.join(self.dir, "tools", "oft", "ci", "facts-review-gather"),
              "#!/usr/bin/env bash\nmkdir -p .review\necho M > .review/changed.txt\nexit 2\n", 0o755)
        rc, out, output = self.run_step("review", "gather", {})
        self.assertEqual(rc, 2, out)
        self.assertEqual(output, "has_facts=true\nfailure=gathering what the review reads ended with exit status 2 "
                                 "(the log of this job says why)\n")
        self.plain_words(output.split("failure=", 1)[1].rstrip("\n"))

    def comment_body(self, failure, result="failure", tries="", review="", served=SERVED_OK):
        """The comment the comment job's step writes over the comment already there, through a stand-in gh, with the
        record of what answered that facts-review-served wrote (SERVED_OK: the provider and model asked for)."""
        for name in ("facts-review-comment", "facts-review-served"):
            script = os.path.join(self.dir, "tools", "oft", "ci", name)
            os.makedirs(os.path.dirname(script), exist_ok=True)
            shutil.copy(os.path.join(os.path.dirname(COMMENT), name), script)
        bin_dir = os.path.join(self.dir, "bin")
        write(os.path.join(bin_dir, "gh"),
              '#!/usr/bin/env bash\ncase " $* " in *" --method PATCH "*) cat > "$FAKE_OUT" ;; *) echo 5 ;; esac\n',
              0o755)
        body = os.path.join(self.dir, "body.json")
        env = {"PATH": bin_dir + os.pathsep + os.environ["PATH"], "FAKE_OUT": body, "REPO": "acme/proofs",
               "REVIEW": review, "REVIEW_RESULT": result, "NO_FACTS": "", "HAS_FACTS": "true", "HEAD_SHA": "a" * 40,
               "BASE_REF": "main", "FAILURE": failure, "GH_TOKEN": "x", "TRIES": tries, "SERVED": served}
        rc, out, _ = self.run_step("comment", None, env, name="post the comment, or update the one already there")
        self.assertEqual(rc, 0, out)
        with open(body) as f:
            return json.load(f)["body"]

    def test_the_comment_says_why_there_is_no_review(self):
        self.assertIn(f"against `main`: {MAX_TURNS_WHY}. What answered it, as the review agent's tool reported it: "
                      f"{ANSWERED_OK}. The maintainers review the facts.", self.comment_body(MAX_TURNS_WHY))
        self.assertIn("against `main`: the review job ended with the result failure.", self.comment_body(""))

    def test_the_comment_says_how_each_try_ended(self):
        """A dead try says so on the pull request too, not only in the job summary: with no review, the comment lists
        each try's ending; with a review that came on a later try, a line before the review says how the earlier ones
        ended. A review on its first try adds nothing, and a line that is not plain words is not shown."""
        self.assertEqual(self.jobs["review"]["outputs"]["tries"], "${{ steps.summary.outputs.tries }}")
        step = next(s for s in self.jobs["comment"]["steps"] if "run" in s)
        self.assertEqual(step["env"]["TRIES"], "${{ needs.review.outputs.tries }}")
        died = "the review agent ended with exit status 1 after 498 seconds, and wrote no review"
        tries = ["try %d of 3, %s" % (n, died) for n in (1, 2, 3)]
        body = self.comment_body(died + ", on try 3 of 3", tries="\n".join(tries + ["::error::not shown"]))
        self.assertTrue(body.endswith("The maintainers review the facts.\n\nHow each try of the review agent ended:\n\n"
                                      + "".join("- %s\n" % t for t in tries)), body)
        self.assertNotIn("::error::", body)
        posted = "try 2 of 3, a review, success after 103 turns and 592 seconds"
        body = self.comment_body("", result="success", tries=tries[0] + "\n" + posted, review="No findings.")
        self.assertIn("<sub>How each try of the review agent ended: %s; %s.</sub>\n\nNo findings.\n" % (tries[0], posted),
                      body)
        body = self.comment_body("", result="success", tries="try 1 of 3, a review, success after 56 turns and 276 "
                                 "seconds", review="No findings.")
        self.assertNotIn("How each try", body)
        # A review that resumed an earlier one says so, and from which commit, even when it came on its first try.
        resumed = ("try 1 of 3 (resumed from the review of 0123456789ab), a review, success after 9 turns and 80 "
                   "seconds")
        body = self.comment_body("", result="success", tries=resumed, review="No findings.")
        self.assertIn("<sub>How each try of the review agent ended: %s.</sub>\n\nNo findings.\n" % resumed, body)

    def summary(self, failure, status, tries):
        """The job summary the review job's last step writes, given the job's failure line, its status and tries.txt."""
        path = os.path.join(self.dir, "summary.md")
        if os.path.exists(path):
            os.remove(path)
        write(os.path.join(self.dir, ".review", "tries.txt"), tries)
        rc, out, output = self.run_step("review", "summary", {"FAILURE": failure, "JOB_STATUS": status,
                                                              "GITHUB_STEP_SUMMARY": path})
        self.assertEqual(rc, 0, out)
        self.last_output = output
        with open(path) as f:
            return f.read()

    def test_the_job_summary_says_how_the_review_ended(self):
        """#165's first attempt (run 40274755332) showed only a failed step whose log ended at its stop-commands line.
        The check's own page now says that no review was written, why, and how each try ended."""
        step = next(s for s in self.jobs["review"]["steps"] if s.get("id") == "summary")
        self.assertEqual(step["env"]["FAILURE"], self.jobs["review"]["outputs"]["failure"])
        self.assertIn("always()", step["if"])
        died = "the review agent ended with exit status 1 after 498 seconds, and wrote no review"
        tries = ["try %d of 3, %s" % (n, died) for n in (1, 2, 3)]
        text = self.summary(died + ", on try 3 of 3", "failure", "\n".join(tries + ["::error::not shown"]) + "\n")
        self.assertEqual(text, "### Facts review\nNo review: %s, on try 3 of 3.\n\n" % died
                         + "".join("- %s\n" % t for t in tries))
        posted = "try 1 of 3, a review, success after 103 turns and 592 seconds"
        self.assertEqual(self.summary("", "success", posted + "\n"),
                         "### Facts review\nA review was written; the comment job posts it on the pull request.\n\n"
                         "- %s\n" % posted)
        self.assertEqual(self.summary("", "cancelled", ""),
                         "### Facts review\nNo review: the review job ended with the result cancelled.\n")

    def test_the_job_summary_step_passes_the_tries_on(self):
        """The same plain lines the summary shows go to the comment job, between a delimiter of the step's own."""
        posted = "try 2 of 3, a review, success after 103 turns and 592 seconds"
        died = "try 1 of 3, the review agent ended with exit status 1 after 498 seconds, and wrote no review"
        self.summary("", "success", died + "\n::error::not shown\n" + posted + "\n")
        m = re.fullmatch(r"tries<<(tries-[0-9a-f]{32})\n(.*)\n\1\n", self.last_output, re.S)
        self.assertIsNotNone(m, self.last_output)
        self.assertEqual(m.group(2), died + "\n" + posted)
        self.summary("", "cancelled", "")
        self.assertEqual(self.last_output, "")


@unittest.skipUnless(shutil.which("jq") and shutil.which("git"), "jq or git is not installed")
class GatherFetchTest(unittest.TestCase):
    """facts-review-gather against a stand-in gh and a local git server: it fetches the files it gathers, and not
    the rest of the head commit."""

    def git(self, *args, cwd=None):
        return subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=t@t", "-c", "init.defaultBranch=main",
                               *args], cwd=cwd, check=True, capture_output=True, text=True).stdout.strip()

    def test_gather_fetches_only_what_it_gathers(self):
        with tempfile.TemporaryDirectory(prefix="oft-gather-") as tmp:
            server = os.path.join(tmp, "server")
            files = {"docs/facts.md": "facts\n", "release.yaml": "release: 1\n",
                     ".claude/skills/a/SKILL.md": "outside: a skill\n", "other/big.txt": "outside: other\n",
                     "projects/zlib/project.yaml": "name: zlib\n",
                     "projects/zlib/checksum_fuzzer/harness.yaml": "checks: []\n",
                     "projects/zlib/checksum_fuzzer/Images.v": "images\n",
                     "projects/png/project.yaml": "name: png\n", "projects/png/t/harness.yaml": "outside: png\n",
                     # Attributes that would keep the facts from the review, if gather read any.
                     ".gitattributes": "projects/** export-ignore\n",
                     "projects/zlib/.gitattributes": "* export-ignore\n"}
            for path, text in files.items():
                write(os.path.join(server, path), text)
            self.git("init", "-q", server)
            self.git("add", "-A", cwd=server)
            self.git("commit", "-qm", "base", cwd=server)
            base = self.git("rev-parse", "HEAD", cwd=server)
            write(os.path.join(server, "projects/zlib/checksum_fuzzer/harness.yaml"), "checks: [one]\n")
            self.git("commit", "-qam", "head", cwd=server)
            head = self.git("rev-parse", "HEAD", cwd=server)
            self.git("config", "uploadpack.allowFilter", "true", cwd=server)
            self.git("config", "uploadpack.allowAnySHA1InWant", "true", cwd=server)
            outside = {self.git("rev-parse", f"{head}:{p}", cwd=server): p
                       for p in (".claude/skills/a/SKILL.md", "other/big.txt", "projects/png/t/harness.yaml")}

            bin_dir, api = os.path.join(tmp, "bin"), os.path.join(tmp, "api")
            write(os.path.join(bin_dir, "gh"), FAKE_GH, 0o755)
            write(os.path.join(api, API + "pulls_7.json"), json.dumps(
                {"number": 7, "title": "t", "body": "b", "draft": False, "base": {"sha": base, "ref": "main"},
                 "head": {"sha": head}}))
            write(os.path.join(api, API + f"compare_{base}...{head}.json"),
                  json.dumps({"merge_base_commit": {"sha": base}}))
            checkout = os.path.join(tmp, "checkout")
            write(os.path.join(checkout, "docs", "facts.md"), "facts\n")
            trace, runner = os.path.join(tmp, "packets"), os.path.join(tmp, "runner")
            os.mkdir(runner)
            env = {k: v for k, v in os.environ.items() if not k.startswith(("GH_", "GITHUB_", "GIT_"))}
            # The script's https://github.com/acme/proofs is the local server; its git commands log what they ask for.
            env.update(PATH=bin_dir + os.pathsep + os.environ["PATH"], FAKE_GH=api, PR="7", REPO="acme/proofs",
                       RUNNER_TEMP=runner, GIT_TRACE_PACKET=trace, GIT_CONFIG_COUNT="1",
                       GIT_CONFIG_KEY_0=f"url.file://{server}.insteadOf",
                       GIT_CONFIG_VALUE_0="https://github.com/acme/proofs")
            r = subprocess.run(["bash", GATHER, ".review"], cwd=checkout, env=env, capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)

            got = os.path.join(checkout, ".review", "head")
            with open(os.path.join(got, "projects/zlib/checksum_fuzzer/harness.yaml")) as f:
                self.assertEqual(f.read(), "checks: [one]\n")
            self.assertTrue(os.path.exists(os.path.join(got, "docs/facts.md")))
            self.assertFalse(os.path.exists(os.path.join(got, "other")))
            with open(trace) as f:
                wanted = set(re.findall(r"\bwant ([0-9a-f]{40})", f.read()))
            self.assertIn(self.git("rev-parse", f"{head}:projects/zlib/checksum_fuzzer/harness.yaml", cwd=server),
                          wanted, "the trace shows the blobs gather fetched")
            self.assertEqual(sorted(p for oid, p in outside.items() if oid in wanted), [],
                             "gather fetched files of the head commit that it does not gather")


if __name__ == "__main__":
    unittest.main()
