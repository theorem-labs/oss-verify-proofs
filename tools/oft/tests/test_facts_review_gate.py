"""tools/oft/ci/facts-review-gate, which lets facts-review.yml skip its review job, against a stand-in gh.

The workflow is in the internal repository only (`oft release-tree` removes it), so the tests that read it skip where
it is not; the script and its own tests ship."""
import json
import os
import re
import shutil
import subprocess
import tempfile
import unittest

from oft import yamlio
from oft.tests.helpers import REPO

GATE = os.path.join(REPO, "tools", "oft", "ci", "facts-review-gate")
GATHER = os.path.join(REPO, "tools", "oft", "ci", "facts-review-gather")
WORKFLOW = os.path.join(REPO, ".github", "workflows", "facts-review.yml")
HAVE_WORKFLOW = os.path.exists(WORKFLOW)
NO_WORKFLOW = "no .github/workflows/facts-review.yml: the internal repository alone has it"
MARKER = "<!-- facts-review -->"
API = "repos_acme_proofs_"   # the stand-in API's file names for the repository acme/proofs
PAGE = 100                   # the gate asks for 100 items a page
# A gh that answers `gh api <endpoint> [--paginate] [-H <accept>] [--jq <filter>]` from <FAKE_GH>/<endpoint>.json,
# with the endpoint's slashes as underscores and its query string dropped: through --jq the way gh applies it (to each
# page), or as the file's bytes when the accept header asks for the raw contents. <endpoint>.json is the first page;
# <endpoint>.2.json, <endpoint>.3.json and on are the pages that only --paginate reads, as GitHub's next links are.
FAKE_GH = r"""#!/usr/bin/env bash
[ "$1" = api ] || exit 9; shift
filter=. endpoint= raw= paginate=
while [ $# -gt 0 ]; do
  case $1 in
    -H) [[ $2 == *raw* ]] && raw=1; shift 2 ;;
    --paginate) paginate=1; shift ;;
    --jq) filter=$2; shift 2 ;;
    *) endpoint=$1; shift ;;
  esac
done
endpoint=${endpoint%%\?*}
file="$FAKE_GH/${endpoint//\//_}.json"
[ -f "$file" ] || { echo "gh: HTTP 404: $endpoint" >&2; exit 1; }
if [ -n "$raw" ]; then cat "$file"; exit; fi
jq -r "$filter" "$file"
n=2
while [ -n "$paginate" ] && [ -f "${file%.json}.$n.json" ]; do
  jq -r "$filter" "${file%.json}.$n.json"; n=$((n + 1))
done
"""

# Paths of each kind gather counts, and of kinds it does not.
FACTS_PATHS = ["projects/zlib/project.yaml", "projects/zlib/checksum_fuzzer/harness.yaml",
               "projects/zlib/checksum_fuzzer/source/fuzz.c", "projects/zlib/checksum_fuzzer/source/sub/x.h",
               "projects/zlib/checksum_fuzzer/Distribution.v"]
OTHER_PATHS = ["README.md", "tools/oft/ci/facts-review-gate", "projects/zlib/README.md",
               "projects/zlib/checksum_fuzzer/Images.v", "projects/zlib/checksum_fuzzer/sub/harness.yaml",
               "proofs/zlib/checksum_fuzzer/provenance/source/fuzz.c", "projects/project.yaml",
               "projects/zlib/checksum_fuzzer/source", "docs/projects/zlib/project.yaml"]


class StandIn(unittest.TestCase):
    """A stand-in gh on PATH, and the API answers it serves for pull request 7 of acme/proofs."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="oft-gate-")
        self.dir = self._tmp.name
        bin_dir = os.path.join(self.dir, "bin")
        os.mkdir(bin_dir)
        with open(os.path.join(bin_dir, "gh"), "w") as f:
            f.write(FAKE_GH)
        os.chmod(os.path.join(bin_dir, "gh"), 0o755)
        self.api = os.path.join(self.dir, "api")
        os.mkdir(self.api)
        self.env = dict(os.environ, PATH=bin_dir + os.pathsep + os.environ["PATH"], FAKE_GH=self.api,
                        PR="7", REPO="acme/proofs")

    def tearDown(self):
        self._tmp.cleanup()

    def pr(self, files, comments=(), changed_files=None):
        """The stand-in API's answers for pull request 7: `files` as (path, old path or None, status), `comments` as
        (login, body); a list is served in pages of 100, as GitHub serves it to the gate."""
        listed = [dict({"filename": p, "status": s}, **({"previous_filename": old} if old else {}))
                  for p, old, s in files]
        with open(os.path.join(self.api, API + "pulls_7.json"), "w") as f:
            json.dump({"number": 7, "changed_files": len(files) if changed_files is None else changed_files}, f)
        for name, items in (("pulls_7_files", listed),
                            ("issues_7_comments", [{"id": i + 1, "user": {"login": u}, "body": b}
                                                   for i, (u, b) in enumerate(comments)])):
            for n in range(max(1, -(-len(items) // PAGE))):
                with open(os.path.join(self.api, API + name + ("" if n == 0 else f".{n + 1}") + ".json"), "w") as f:
                    json.dump(items[n * PAGE:(n + 1) * PAGE], f)

    def gate(self):
        r = subprocess.run(["bash", GATE], env=self.env, capture_output=True, text=True)
        return r.returncode, r.stdout.strip(), r.stderr

    def break_grep(self, when):
        """Put a grep on PATH that answers 2, an error it could not read past, for one of the gate's two searches:
        `when` is "count" for the count of listed files, "facts" for the search for facts files. Every other call
        goes to the real grep. grep answers 1 for "no match", which is an answer, not an error."""
        real = shutil.which("grep", path=os.environ["PATH"])
        self.assertIsNotNone(real, "no grep on PATH")
        with open(os.path.join(self.dir, "bin", "grep"), "w") as f:
            f.write("#!/usr/bin/env bash\n"
                    "kind=count\n"
                    'for a in "$@"; do case $a in *projects*) kind=facts ;; esac; done\n'
                    f'[ "$kind" = {when} ] && {{ echo "grep: input read error" >&2; exit 2; }}\n'
                    f'exec {real} "$@"\n')
        os.chmod(os.path.join(self.dir, "bin", "grep"), 0o755)

    def assertGate(self, want):
        rc, out, err = self.gate()
        self.assertEqual((rc, out), (0, "review=" + want), err)


@unittest.skipUnless(shutil.which("jq"), "jq is not installed")
class GateTest(StandIn):
    def test_each_kind_of_facts_file_goes_to_the_review(self):
        for path in FACTS_PATHS:
            for status in ("modified", "added", "removed"):
                with self.subTest(path=path, status=status):
                    self.pr([("README.md", None, "modified"), (path, None, status)])
                    self.assertGate("true")

    def test_a_facts_file_renamed_away_goes_to_the_review(self):
        self.pr([("projects/zlib/old_project.yaml.bak", "projects/zlib/project.yaml", "renamed")])
        self.assertGate("true")

    def test_a_facts_file_past_the_first_page_of_files_goes_to_the_review(self):
        self.pr([(f"docs/{i}.md", None, "added") for i in range(PAGE)]
                + [("projects/zlib/project.yaml", None, "added")])
        self.assertGate("true")

    def test_no_facts_file_and_no_comment_skips_the_review(self):
        self.pr([(p, None, "modified") for p in OTHER_PATHS])
        self.assertGate("false")

    def test_an_empty_pull_request_skips_the_review(self):
        self.pr([])
        self.assertGate("false")

    def test_the_review_comment_already_there_goes_to_the_review(self):
        """A push that took away the last facts change must still replace the old review comment."""
        self.pr([("README.md", None, "modified")],
                comments=[("a-maintainer", "looks fine"), ("github-actions[bot]", MARKER + "\n## Facts review\n\nold")])
        self.assertGate("true")

    def test_the_review_comment_past_the_first_page_of_comments_goes_to_the_review(self):
        """The comment is found wherever it is in a long discussion: the gate reads every page of comments."""
        self.pr([("README.md", None, "modified")],
                comments=[("a-maintainer", f"comment {i}") for i in range(PAGE)]
                + [("github-actions[bot]", MARKER + "\nold")])
        self.assertGate("true")

    def test_a_comment_that_only_looks_like_it_skips_the_review(self):
        self.pr([("README.md", None, "modified")],
                comments=[("a-maintainer", MARKER + " quoted by a person"),
                          ("github-actions[bot]", "another workflow's comment, " + MARKER)])
        self.assertGate("false")

    def test_a_file_list_github_cut_short_goes_to_the_review(self):
        self.pr([("README.md", None, "modified")], changed_files=3001)
        self.assertGate("true")

    def test_it_fails_when_it_cannot_read_the_pull_request(self):
        self.pr([("README.md", None, "modified")])
        os.remove(os.path.join(self.api, API + "pulls_7_files.json"))
        rc, out, _ = self.gate()
        self.assertNotEqual(rc, 0)
        self.assertNotEqual(out, "review=false")

    def test_a_search_that_failed_never_says_there_is_nothing_to_review(self):
        """A grep that answers 2 is an error, not "no facts file": it must not become review=false, which would
        take the facts review off a pull request that changes the facts and say nothing."""
        for when in ("facts", "count"):
            with self.subTest(when=when):
                self.pr([("projects/zlib/project.yaml", None, "modified")])
                self.break_grep(when)
                rc, out, err = self.gate()
                self.assertNotEqual(rc, 0, err)
                self.assertNotEqual(out, "review=false", err)
        os.remove(os.path.join(self.dir, "bin", "grep"))

    def test_a_search_that_found_nothing_still_answers(self):
        """The fix above must keep grep's answer 1, "no match", an answer: with the real grep a pull request that
        changes no facts file still reaches review=false."""
        self.pr([("README.md", None, "modified")])
        self.assertGate("false")

    def test_it_counts_the_files_gather_counts(self):
        """The gate's facts files are gather's FACTS pathspecs: git, given gather's own pathspecs, picks out the same
        paths of the lists above as the gate does."""
        with open(GATHER) as f:
            src = f.read()
        m = re.search(r"^FACTS=\((.*?)\)$", src, re.M | re.S)
        self.assertIsNotNone(m, "facts-review-gather has no FACTS=(...) line")
        pathspecs = re.findall(r"'([^']+)'", m.group(1))
        # A new kind of facts file in gather must reach the gate's FACTS too; then this list and FACTS_PATHS change.
        self.assertEqual(pathspecs, [":(glob)projects/*/project.yaml", ":(glob)projects/*/*/harness.yaml",
                                     ":(glob)projects/*/*/source/**", ":(glob)projects/*/*/Distribution.v"],
                         "gather's FACTS changed: change the gate's FACTS to match")
        repo = os.path.join(self.dir, "repo")
        paths = FACTS_PATHS + [p for p in OTHER_PATHS if p != "projects/zlib/checksum_fuzzer/source"]
        subprocess.run(["git", "init", "-q", repo], check=True)
        for p in paths:
            os.makedirs(os.path.dirname(os.path.join(repo, p)), exist_ok=True)
            open(os.path.join(repo, p), "w").close()
        subprocess.run(["git", "-C", repo, "add", "--", *paths], check=True)
        by_git = set(subprocess.run(["git", "-C", repo, "-c", "core.quotePath=false", "ls-files", "--", *pathspecs],
                                    check=True, capture_output=True, text=True).stdout.split())
        self.assertEqual(by_git, set(FACTS_PATHS))
        for p in paths:
            with self.subTest(path=p):
                self.pr([(p, None, "modified")])
                self.assertGate("true" if p in by_git else "false")


@unittest.skipUnless(shutil.which("jq"), "jq is not installed")
@unittest.skipUnless(HAVE_WORKFLOW, NO_WORKFLOW)
class StepTest(StandIn):
    """The gate job's step, run as GitHub runs it."""

    def step(self, serve_gate=True, gate_text=None):
        """Runs the step, and gives back what it wrote to GITHUB_OUTPUT."""
        jobs = yamlio.load_file(WORKFLOW)["jobs"]
        script = os.path.join(self.dir, "step.sh")
        with open(script, "w") as f:
            f.write(jobs["gate"]["steps"][-1]["run"])
        served = os.path.join(self.api, API + "contents_tools_oft_ci_facts-review-gate.json")
        if gate_text is not None:
            with open(served, "w") as f:
                f.write(gate_text)
        elif serve_gate:
            shutil.copy(GATE, served)
        runner, output = os.path.join(self.dir, "runner"), os.path.join(self.dir, "output")
        os.mkdir(runner)
        env = dict(self.env, RUNNER_TEMP=runner, GITHUB_OUTPUT=output, SHA="0" * 40)
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", script], env=env, capture_output=True,
                           text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        with open(output) as f:
            return f.read().strip()

    def test_the_step_sends_a_facts_change_to_the_review(self):
        self.pr([("projects/zlib/project.yaml", None, "modified")])
        self.assertEqual(self.step(), "review=true")

    def test_the_step_sends_a_pull_request_with_the_comment_to_the_review(self):
        self.pr([("README.md", None, "modified")], comments=[("github-actions[bot]", MARKER + "\nold")])
        self.assertEqual(self.step(), "review=true")

    def test_the_step_stops_a_pull_request_with_nothing_to_review(self):
        self.pr([("README.md", None, "modified")])
        self.assertEqual(self.step(), "review=false")

    def test_the_step_sends_to_the_review_when_it_cannot_fetch_the_gate(self):
        self.pr([("README.md", None, "modified")])
        self.assertEqual(self.step(serve_gate=False), "review=true")

    def test_the_step_sends_to_the_review_when_the_gate_fails(self):
        self.pr([("README.md", None, "modified")])
        os.remove(os.path.join(self.api, API + "issues_7_comments.json"))
        self.assertEqual(self.step(), "review=true")

    def test_the_step_writes_one_line_whatever_the_gate_prints(self):
        """An answer of more than one line is not an answer: only review=true reaches GITHUB_OUTPUT."""
        self.pr([("README.md", None, "modified")])
        for text in ("echo review=false; echo review=true\n", "echo review=false; echo other=1\n",
                     "echo 'review=false '\n"):
            with self.subTest(gate=text):
                shutil.rmtree(os.path.join(self.dir, "runner"), ignore_errors=True)
                if os.path.exists(os.path.join(self.dir, "output")):
                    os.remove(os.path.join(self.dir, "output"))
                self.assertEqual(self.step(gate_text=text), "review=true")


@unittest.skipUnless(HAVE_WORKFLOW, NO_WORKFLOW)
@unittest.skipUnless(shutil.which("openssl"), "the review step needs openssl")
class ServedTest(unittest.TestCase):
    """The record of what answered the review reaches the comment job whatever the review's ending: the review job's
    `served` output, written also when facts-review-run refuses the review (exit 4), and the comment job's SERVED."""
    RECORD = ("asked anthropic/claude-opus-5-5\nendpoint api.anthropic.com\nusage bedrock/claude-opus-5-5\n"
              "bedrock/claude-opus-5-5 2\n")

    def setUp(self):
        self.jobs = yamlio.load_file(WORKFLOW)["jobs"]

    def test_the_jobs_pass_the_record_on(self):
        self.assertEqual(self.jobs["review"]["outputs"]["served"], "${{ steps.review.outputs.served }}")
        posting = [s for s in self.jobs["comment"]["steps"] if "SERVED" in (s.get("env") or {})]
        self.assertEqual(len(posting), 1)
        self.assertEqual(posting[0]["env"]["SERVED"], "${{ needs.review.outputs.served }}")

    def test_the_review_step_writes_the_record_whatever_the_ending(self):
        step = [s for s in self.jobs["review"]["steps"] if s.get("id") == "review"][0]
        for code in (0, 4, 1):
            with self.subTest(code=code), tempfile.TemporaryDirectory() as directory:
                os.makedirs(os.path.join(directory, "tools", "oft", "ci"))
                os.mkdir(os.path.join(directory, ".review"))
                run = os.path.join(directory, "tools", "oft", "ci", "facts-review-run")
                with open(run, "w") as f:
                    f.write("#!/bin/sh\n"
                            f"printf '%s' '{self.RECORD}' > .review/served\n"
                            "echo 'The facts hold.' > .review/comment.md\n"
                            f"exit {code}\n")
                os.chmod(run, 0o755)
                token, output = os.path.join(directory, "jwt"), os.path.join(directory, "output")
                with open(token, "w") as f:
                    f.write("jwt\n")
                env = dict(os.environ, ANTHROPIC_IDENTITY_TOKEN_FILE=token, GITHUB_OUTPUT=output)
                r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", step["run"]],
                                   cwd=directory, env=env, capture_output=True, text=True)
                self.assertEqual(r.returncode, code, r.stdout + r.stderr)
                with open(output) as f:
                    written = f.read()
                self.assertRegex(written, r"(?m)^served<<(served-[0-9a-f]{32})\n" + re.escape(self.RECORD)
                                 + r"\n\1$")
                self.assertEqual("comment<<" in written, code == 0)
                self.assertFalse(os.path.exists(token), "the identity token file is removed")


def evaluate(expression, needs, cancelled=False):
    """GitHub's value of a job's `if:` (the subset this workflow uses: !, &&, ||, ==, !=, parentheses, '...' strings,
    needs.<job>.result, needs.<job>.outputs.<name>, success(), failure(), cancelled(), always()). As GitHub does, an
    expression that calls no status function is evaluated as `success() && (<expression>)`; strings compare without
    regard to case, and an output a job did not set is ''."""
    text = expression.strip()
    if text.startswith("${{") and text.endswith("}}"):
        text = text[3:-2]
    tokens = re.findall(r"\s*(&&|\|\||==|!=|!|\(|\)|'(?:[^']|'')*'|[A-Za-z_][\w.-]*\(\)|[A-Za-z_][\w.-]*)", text)
    if "".join(tokens).replace(" ", "") != text.replace(" ", ""):
        raise ValueError(f"evaluate() cannot read {expression!r}")
    if not any(t in ("success()", "failure()", "cancelled()", "always()") for t in tokens):
        tokens = ["success()", "&&", "("] + tokens + [")"]
    results = [j["result"] for j in needs.values()]

    def value(t):
        if t.startswith("'"):
            return t[1:-1].replace("''", "'")
        if t.endswith("()"):
            return {"success()": not cancelled and all(r == "success" for r in results),
                    "failure()": not cancelled and any(r == "failure" for r in results),
                    "cancelled()": cancelled, "always()": True}[t]
        parts = t.split(".")
        if parts[0] != "needs" or len(parts) not in (3, 4):
            raise ValueError(f"evaluate() has no value for {t}")
        job = needs[parts[1]]
        return job["result"] if parts[2] == "result" else job.get("outputs", {}).get(parts[3], "")

    def same(a, b):
        return a.lower() == b.lower() if isinstance(a, str) and isinstance(b, str) else a == b

    pos = 0

    def take():
        nonlocal pos
        pos += 1
        return tokens[pos - 1]

    def peek():
        return tokens[pos] if pos < len(tokens) else None

    def unary():
        t = take()
        if t == "!":
            return not unary()
        if t == "(":
            v = either()
            assert take() == ")"
            return v
        return value(t)

    def compare():
        v = unary()
        while peek() in ("==", "!="):
            v = same(v, unary()) if take() == "==" else not same(v, unary())
        return v

    def both():
        v = compare()
        while peek() == "&&":
            take()
            v = compare() and v
        return v

    def either():
        v = both()
        while peek() == "||":
            take()
            v = both() or v
        return v

    v = either()
    assert peek() is None, tokens[pos:]
    return bool(v)


@unittest.skipUnless(HAVE_WORKFLOW, NO_WORKFLOW)
class WorkflowTest(unittest.TestCase):
    def setUp(self):
        self.jobs = yamlio.load_file(WORKFLOW)["jobs"]

    def test_the_review_job_waits_for_the_gate(self):
        jobs = self.jobs
        self.assertEqual(jobs["gate"]["outputs"]["review"], "${{ steps.gate.outputs.review }}")
        steps = jobs["gate"]["steps"]
        self.assertEqual(steps[-1]["id"], "gate")
        self.assertFalse(any("uses" in s for s in steps), "the gate job checks nothing out")
        self.assertIn("tools/oft/ci/facts-review-gate", steps[-1]["run"])
        self.assertEqual(jobs["review"]["needs"], "gate")
        self.assertEqual(jobs["comment"]["needs"], "review")

    def test_the_review_job_runs_unless_the_gate_said_false(self):
        """The review runs when the gate job said review=true, and also when the gate job failed (a lost runner, its
        timeout) and said nothing: an error never skips the review, nor the comment's replacement with it."""
        cases = [({"result": "success", "outputs": {"review": "true"}}, False, True),
                 ({"result": "success", "outputs": {"review": "false"}}, False, False),
                 ({"result": "failure", "outputs": {}}, False, True),
                 ({"result": "failure", "outputs": {"review": "false"}}, False, False),
                 ({"result": "skipped", "outputs": {}}, False, False),     # an edit of the title or body
                 ({"result": "cancelled", "outputs": {}}, True, False)]    # a newer push cancelled the run
        for gate, cancelled, runs in cases:
            with self.subTest(gate=gate, cancelled=cancelled):
                self.assertEqual(evaluate(self.jobs["review"]["if"], {"gate": gate}, cancelled), runs)

    def test_the_comment_job_runs_whenever_the_review_job_ran(self):
        for result, runs in (("success", True), ("failure", True), ("skipped", False)):
            with self.subTest(review=result):
                self.assertEqual(evaluate(self.jobs["comment"]["if"], {"review": {"result": result}}), runs)

    def test_evaluate_adds_success_where_github_does(self):
        """The rule the review job's test rests on: a bare condition on an output skips the job when the gate failed."""
        failed = {"gate": {"result": "failure", "outputs": {}}}
        self.assertFalse(evaluate("needs.gate.outputs.review != 'false'", failed))
        self.assertTrue(evaluate("${{ !cancelled() && needs.gate.outputs.review != 'false' }}", failed))

    def verdict(self, edit, gate, review_ends="success", comment_ends="success", session="", keep_ends="success"):
        """The facts-review job's step over a run: the gate job ended as `gate` (result and outputs); the review job,
        the keep job (after a review whose `session` output is as given) and the comment job run when their `if:`
        says so (skipped otherwise) and end as given.  Its exit status."""
        review = review_ends if evaluate(self.jobs["review"]["if"], {"gate": gate}) else "skipped"
        reviewed = {"review": {"result": review, "outputs": {"session": session} if review != "skipped" else {}}}
        keep = keep_ends if evaluate(self.jobs["keep"]["if"], reviewed) else "skipped"
        comment = comment_ends if evaluate(self.jobs["comment"]["if"], reviewed) else "skipped"
        env = dict(os.environ, EDIT="true" if edit else "false", GATE=gate["result"],
                   ROUTE=gate.get("outputs", {}).get("review", ""), REVIEW=review, COMMENT=comment,
                   SESSION=reviewed["review"]["outputs"].get("session", ""), KEEP=keep)
        with tempfile.NamedTemporaryFile("w", suffix=".sh") as f:
            f.write(self.jobs["facts-review"]["steps"][0]["run"])
            f.flush()
            r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", f.name], env=env,
                               capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr

    def test_the_facts_review_job_is_the_run_s_one_verdict(self):
        """It always runs and needs every other job; it passes when every job the gate sent the run to passed and every
        job it stopped was skipped, and fails on any job that failed or was cancelled, the gate's own included.  An
        edit of the title or body restates the last review's verdict (test_workflow_verdicts.FactsReviewRestateTest);
        here only an edit whose jobs ran fails before it asks.  EDIT and the session case are the gate's and keep's
        own conditions."""
        job = self.jobs["facts-review"]
        self.assertEqual(job["if"], "always()")
        self.assertEqual(sorted(job["needs"]), sorted(n for n in self.jobs if n != "facts-review"))
        self.assertEqual(job["permissions"], {"actions": "write"})
        self.assertEqual(self.jobs["gate"]["if"],
                         "github.event.action != 'edited' || github.event.changes.base != null")
        self.assertEqual(job["steps"][0]["env"]["EDIT"],
                         "${{ github.event.action == 'edited' && github.event.changes.base == null }}")
        self.assertEqual(self.jobs["keep"]["if"], "${{ !cancelled() && needs.review.outputs.session == 'kept' }}")
        self.assertRegex(job["steps"][0]["run"], r"\n *kept\) ")
        review, stop = {"result": "success", "outputs": {"review": "true"}}, {"result": "success",
                                                                             "outputs": {"review": "false"}}
        cases = [
            (False, review, "success", "success", "", "success", 0),     # no session to keep: keep skipped
            (False, review, "success", "success", "kept", "success", 0),
            (False, review, "success", "success", "dropped", "success", 0),     # a value the review never writes: keep skipped
            (False, stop, "success", "success", "", "success", 0),       # review, keep and comment skipped
            (False, review, "failure", "success", "", "success", 1),     # the comment says why; the verdict fails
            (False, review, "failure", "success", "kept", "success", 1),        # the session kept, the review failed
            (False, review, "cancelled", "success", "", "success", 1),
            (False, review, "success", "failure", "", "success", 1),
            (False, review, "success", "success", "kept", "failure", 1),
            (False, review, "success", "success", "kept", "cancelled", 1),
            (False, {"result": "failure"}, "success", "success", "", "success", 1),  # the review ran; the gate failed
            (False, {"result": "cancelled"}, "success", "success", "", "success", 1),
            (False, {"result": "skipped"}, "success", "success", "", "success", 1),  # not an edit, yet no gate
            (True, review, "success", "success", "", "success", 1),     # an edit, yet the gate ran
        ]
        for edit, gate, review_ends, comment_ends, session, keep_ends, want in cases:
            with self.subTest(edit=edit, gate=gate, review=review_ends, comment=comment_ends, session=session,
                              keep=keep_ends):
                rc, out = self.verdict(edit, gate, review_ends, comment_ends, session, keep_ends)
                self.assertEqual(rc, want, out)


if __name__ == "__main__":
    unittest.main()
