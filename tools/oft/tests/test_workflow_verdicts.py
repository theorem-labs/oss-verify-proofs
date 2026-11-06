"""The one verdict of each workflow run: pr.yml's
triggers (no edit starts a run), and the jobs that collect a run's results in images.yml and weekly.yml, each run as
GitHub runs a step, against a stand-in gh; images.yml's verification of the attestation it stores; the base pr.yml
judges a change against, which its router reads the change from, with the files of the base its jobs check out and
lint compares the findings ledger with; the patterns of every sparse checkout, in both layouts; and
tools/oft/ci/pr-steps.sh, which rehearses a pull request's pr.yml run on a full clone.  And what the public
repository's workflows publish and check: the check run release.yml accepts on a tagged commit, the units its sweep
hands weekly.yml, and pr.yml's plan of a push to the public main."""
import fnmatch
import hashlib
import io
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import textwrap
import time
import unittest

from oft import facts, keys, plan, port, yamlio
from oft.tests import helpers
from oft.tests.helpers import REPO, later_release, recipe_only_rebuild, tree

WORKFLOWS = os.path.join(REPO, ".github", "workflows")
# A checkout has .github/workflows; tools/oft alone (the runner image's copy, which runs these tests) has none. A
# missing file in a checkout still fails: only a missing directory skips.
HAVE_WORKFLOWS = os.path.isdir(WORKFLOWS)
NO_WORKFLOWS = "no .github/workflows: tools/oft without the checkout around it"
REPOSITORY = "acme/proofs"
HEAD = "c" * 40
# the check of record a pin names for a deferred check, and the script that prints the two digests a pin names
RECORD = "a VM run of every part of the tree at the merge commit of this change"
PIN_DIGESTS = os.path.join(REPO, "tools", "oft", "ci", "pin-digests.sh")
# A gh that answers `gh api [--method M] [-f/-F K=V ...] <endpoint> [--jq <filter>]` from <FAKE_GH>/<endpoint>.json,
# the endpoint's slashes as underscores and its query string dropped, through --jq as gh applies it (a -f or -F
# field is logged with the call and nothing else, so `gh api graphql` is answered from graphql.json); when
# <endpoint>.1.json,
# <endpoint>.2.json and on are there instead, each call takes the next of them and the last one stays.  A POST is
# answered by <endpoint>.json too, and refused as GitHub refuses a token without the permission when there is none.
# An answer that is the JSON string "error" is a failed call.  Every call is logged, one line each, with its query
# string, to <FAKE_GH>/calls.  With --paginate, an answer's next page, <answer file>.page2, is read through --jq too;
# without it, only the first page is, as GitHub's per_page caps a list.  With --paginate --slurp, as gh does, the
# pages are one array of pages, printed whole: gh refuses --slurp with --jq ("the --slurp option is not supported
# with --jq or --template", gh 2.98.0), and so does this, so a caller pipes them through its own jq.
FAKE_GH = r"""#!/usr/bin/env bash
[ "$1" = api ] || exit 9; shift
filter=. endpoint= method=GET fields=
while [ $# -gt 0 ]; do
  case $1 in
    --jq) filter=$2; shift 2 ;;
    --method|-X) method=$2; shift 2 ;;
    --paginate) paginate=1; shift ;;
    --slurp) slurp=1; shift ;;
    -f|-F) fields="$fields ${2%%=*}"; shift 2 ;;
    *) endpoint=$1; shift ;;
  esac
done
echo "$method $endpoint$fields" >> "$FAKE_GH/calls"
base="$FAKE_GH/$(echo "${endpoint%%\?*}" | tr / _)"
if [ -f "$base.1.json" ]; then
  n=$(cat "$base.count" 2> /dev/null || echo 0); n=$((n + 1))
  [ -f "$base.$n.json" ] || n=$((n - 1))
  echo "$n" > "$base.count"
  file="$base.$n.json"
else
  file="$base.json"
fi
if [ ! -f "$file" ]; then
  [ "$method" = GET ] && echo "gh: Not Found (HTTP 404)" >&2 || echo "gh: Resource not accessible by integration (HTTP 403)" >&2
  exit 1
fi
if [ "$(cat "$file")" = '"error"' ]; then echo "gh: HTTP 502: Server Error" >&2; exit 1; fi
if [ -n "${slurp:-}" ]; then
  [ "$filter" = . ] || { echo "the --slurp option is not supported with --jq or --template" >&2; exit 1; }
  if [ -f "$file.page2" ]; then jq -s . "$file" "$file.page2"; else jq -s . "$file"; fi
  exit $?
fi
jq -r "$filter" "$file" || exit 1
if [ -n "${paginate:-}" ] && [ -f "$file.page2" ]; then jq -r "$filter" "$file.page2"; fi
"""
# sleep takes no time here, and says that it was asked to
FAKE_SLEEP = '#!/usr/bin/env bash\necho "sleep $1" >> "$FAKE_GH/calls"\n'


def load(name):
    return yamlio.load_file(os.path.join(WORKFLOWS, name))


def load_action(name):
    """.github/actions/<name>/action.yml, the composite actions the workflows run."""
    return yamlio.load_file(os.path.join(REPO, ".github", "actions", name, "action.yml"))


def step(job, name):
    found = [s for s in job["steps"] if s.get("name") == name]
    assert len(found) == 1, name
    return found[0]


def pull_request(action, head=HEAD, number=7, title="a change", base_changed=False, run_id=1):
    """The scope of contexts a pull_request event gives a workflow key: an `edited` whose changes hold a base is a
    new base, and one whose changes hold only a title or a body is an edit that reviews nothing.  Each run has an id
    of its own, which facts-review.yml's group for such an edit is keyed by."""
    changes = {"base": {"ref": {"from": "main"}}} if base_changed else {}
    if action == "edited" and not base_changed:
        changes = {"title": {"from": "an older title"}}
    return {"github": {"event_name": "pull_request", "ref": "refs/pull/%d/merge" % number, "sha": "m" * 40,
                       "run_id": run_id,
                       "event": {"action": action, "changes": changes,
                                 "pull_request": {"number": number, "title": title, "head": {"sha": head}}}},
            "inputs": {}}


def pushed(sha, ref="refs/heads/main"):
    return {"github": {"event_name": "push", "ref": ref, "sha": sha, "event": {"before": "0" * 40}}, "inputs": {}}


def merge_group(sha, number=7):
    """A merge_group event: GitHub always sends an action with it (checks_requested or destroyed), unlike a push."""
    ref = "refs/heads/gh-readonly-queue/main/pr-%d-%s" % (number, "e" * 40)
    return {"github": {"event_name": "merge_group", "ref": ref, "sha": sha,
                       "event": {"action": "checks_requested",
                                 "merge_group": {"head_sha": sha, "base_sha": "f" * 40}}},
            "inputs": {}}


def dispatched(pr=7):
    """facts-review.yml's other trigger: a run by hand, which carries inputs and no event action."""
    return {"github": {"event_name": "workflow_dispatch", "ref": "refs/heads/main", "sha": "d" * 40, "event": {}},
            "inputs": {"pr": pr}}


class StandIn(unittest.TestCase):
    """A temporary directory with the stand-in gh and sleep on PATH, and a way to run a workflow's step."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="oft-verdict-")
        self.dir = self._tmp.name
        bin_dir = os.path.join(self.dir, "bin")
        os.mkdir(bin_dir)
        for name, text in (("gh", FAKE_GH), ("sleep", FAKE_SLEEP)):
            with open(os.path.join(bin_dir, name), "w") as f:
                f.write(text)
            os.chmod(os.path.join(bin_dir, name), 0o755)
        self.api = os.path.join(self.dir, "api")
        os.mkdir(self.api)
        self.path = bin_dir + os.pathsep + os.environ["PATH"]
        self.output = os.path.join(self.dir, "output")

    def tearDown(self):
        self._tmp.cleanup()

    def run_step(self, text, env, cwd=None):
        """Runs a step's script as GitHub does (bash --noprofile --norc -eo pipefail), in `cwd` (the checkout): its
        exit status, its output and its job summary.  GITHUB_OUTPUT is set as GitHub sets it, so that a step may write
        its outputs with no guard; `outputs` reads what it wrote.  Each run has a script file of its own, never one a
        shell may still hold: a guard on a developer's machine takes a running script's write bits and gives them back
        only some time after the run ends, so writing the last run's file failed now and then (EACCES)."""
        fd, script = tempfile.mkstemp(prefix="step-", suffix=".sh", dir=self.dir)
        with os.fdopen(fd, "w") as f:
            f.write(text)
        summary = os.path.join(self.dir, "summary")
        full = dict(os.environ, PATH=self.path, FAKE_GH=self.api, GITHUB_STEP_SUMMARY=summary,
                    GITHUB_OUTPUT=self.output, **env)
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", script], env=full, cwd=cwd,
                           capture_output=True, text=True)
        text = ""
        if os.path.exists(summary):
            with open(summary) as f:
                text = f.read()
            os.remove(summary)
        return r.returncode, r.stdout + r.stderr, text

    def outputs(self):
        """{name: value} of what the last step wrote to GITHUB_OUTPUT."""
        if not os.path.exists(self.output):
            return {}
        with open(self.output) as f:
            return dict(line.split("=", 1) for line in f.read().splitlines() if "=" in line)

    def calls(self):
        path = os.path.join(self.api, "calls")
        if not os.path.exists(path):
            return []
        with open(path) as f:
            return f.read().splitlines()


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class PrTriggerTest(unittest.TestCase):
    """pr.yml runs on no edit of a pull request: GitHub sends `edited` for a new title or description and
    for a new base alike, and a run started by a title edit could only restate the head's verdict; when the head's
    run was still checking, the restate ended cancelled and left the newest run with no main-gate, so the merge queue
    refused the pull request until someone re-ran it."""

    def test_no_edit_or_label_starts_a_run(self):
        """No `edited` (above) and no `labeled`: a run for a label would be the head's newest run, with a main-gate
        it did not earn or none; the label `ready` counts from the pull request's next run."""
        wf = load("pr.yml")
        self.assertEqual(wf["on"]["pull_request"]["types"], ["opened", "synchronize", "reopened", "ready_for_review"])
        self.assertNotIn("run-name", wf)

    def test_no_job_or_group_reads_the_edit(self):
        """Nothing is left of the restate: no job is skipped for an edit, the verdict jobs take their verdict from
        this run's own jobs alone, and they need no API scope to read other runs.  queue_run is the one job that reads
        another run, and the one condition that skips plan and lint (tools/oft/tests/test_lint.QueueCheckedPush)."""
        wf = load("pr.yml")
        with open(os.path.join(WORKFLOWS, "pr.yml")) as f:
            text = f.read()
        for word in ("edited", "changes.base", "RESTATE", "force-cancel"):
            self.assertNotIn(word, text.replace("not on `edited`", "").replace("no `edited`", "")
                             .replace("GitHub sends `edited`", ""), word)
        # The verdict jobs ask no other run for their verdict.  What this checks: both jobs hold no job-level env and
        # main-gate no permission; required holds pull-requests: read, for its one read of the API in a script of this
        # file, the pull request's issue comments (merge-pr.sh's VM evidence comment for a check held for the label,
        # PrHoldTest), and contents: read for the stale base steps of a pull request no merge queue checks again (their
        # checkout of this change, and the base's copy of tools/oft/tests/stale_base.py, which reads the base branch's
        # tip and two trees, never a run: PrStaleBaseTest); no step uses an action but that checkout; no step's env but
        # those two steps' names GH_TOKEN; and no step's script names curl or wget as a word, gh but in that one call,
        # or GITHUB_API_URL, api.github.com or a query of /actions/runs ("/actions/runs?": required's step for a push
        # the merge queue checked prints the run queue_run found as a link, /actions/runs/<id>, and calls nothing).
        # What it does not check: a read written another way (python, node, a raw socket) passes it; a reviewer reads
        # these two jobs' steps.  The text is checked as well as the permission because a public repository's runs are
        # readable with no token.
        # required's two reads of the API, both of this pull request and both with pull-requests: read: its issue
        # comments, and the editors of the one evidence comment among them (userContentEdits, which only GraphQL
        # gives, PrHoldTest.test_a_held_check_fails_when_anyone_else_edited_the_evidence_comment).  Each is pinned
        # whole, its whitespace collapsed: which pull request it reads, which node, and which fields.  A second root
        # field in the query, another node id, or a read of anything else fails here.
        comments = ('VM_PR="$PR" VM_HEAD="$HEAD_SHA"',
                    'gh api --paginate --slurp "repos/$GITHUB_REPOSITORY/issues/$VM_PR/comments?per_page=100"')
        editors = ("gh api graphql -f query='query($id: ID!) { node(id: $id) { ... on IssueComment { "
                   "author { __typename login } userContentEdits(first: 100) "
                   "{ totalCount nodes { editor { __typename login } } } } } }'",
                   """-F id="$(sed -n 's/^node //p' <<< "$said" | head -n 1)\"""")
        collect = "every job green, and something checked when the plan named anything"
        self.assertEqual(wf["jobs"]["required"]["permissions"], {"pull-requests": "read", "contents": "read"})
        self.assertEqual(wf["jobs"]["main-gate"]["permissions"], {})
        for job in ("required", "main-gate"):
            self.assertNotIn("env", wf["jobs"][job], job)
            for s in wf["jobs"][job]["steps"]:
                run = " ".join(s.get("run", "").split())
                if job == "required" and s.get("name") == PrStaleBaseTest.CHECKOUT:
                    self.assertTrue(s["uses"].startswith("actions/checkout@"), s["uses"])
                else:
                    self.assertNotIn("uses", s, job)
                if job == "required" and s.get("name") == collect:
                    self.assertEqual(s["env"]["GH_TOKEN"], "${{ github.token }}")
                    self.assertEqual(len(re.findall(r"\bgh\b", run)), 2, run)
                    for text in comments + editors:
                        self.assertIn(text, run)
                        run = run.replace(text, "")
                elif job == "required" and s.get("name") == PrStaleBaseTest.STALE:
                    self.assertEqual(s["env"]["GH_TOKEN"], "${{ github.token }}")
                else:
                    self.assertNotIn("GH_TOKEN", s.get("env", {}), job)
                for pattern in (r"\b(gh|curl|wget)\b", "GITHUB_API_URL", r"api\.github\.com", r"/actions/runs\?"):
                    self.assertNotRegex(run, pattern, job)
        self.assertEqual(" ".join(wf["concurrency"]["group"].split()),
                         "pr-${{ github.event.pull_request.number || format('{0}-{1}', github.ref, github.sha) }}")
        self.assertEqual(wf["jobs"]["required"]["timeout-minutes"], 10)
        queue = "!cancelled() && needs.queue_run.outputs.checked != 'true'"
        # lint also skips a draft (the plan's hold answer): a field of this run's own plan, not the edit
        for job, cond in (("plan", queue), ("lint", queue + " && needs.plan.outputs.hold != 'draft'")):
            self.assertEqual(" ".join(wf["jobs"][job]["if"].split()), "${{ %s }}" % cond, job)

    def test_main_gate_s_base_step_tells_main_by_case(self):
        """A new base starts no run, and that fails closed: on a pull request into another base main-gate is skipped
        under another name (tools/oft/tests/test_lint.QueueCheckedPush), so one retargeted at main has no main-gate
        until a push or a reopen checks it against main.  GitHub's == ignores case, so a pull request into Main runs
        main-gate, and its base step, which does not, fails it."""
        gate = load("pr.yml")["jobs"]["main-gate"]
        base = step(gate, "a pull request's base is main")
        self.assertEqual(base["env"]["BASE"], "${{ github.event.pull_request.base.ref }}")
        for name, code, out in (("Main", 1, "the base is Main, not main"), ("main", 0, "")):
            r = subprocess.run(["bash", "-c", base["run"]], env=dict(os.environ, BASE=name), capture_output=True,
                               text=True)
            self.assertEqual((r.returncode, out in r.stdout), (code, True), name)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class PrStaleBaseTest(unittest.TestCase):
    """required's stale base steps (the release line's #455: the base a pull request run was built on is still the
    tip of the base branch, tools/oft/tests/stale_base.py) run on a pull request that no merge queue checks again: one
    into a base other than main, and one into main on theorem-labs/oss-verify-proofs, whose main merges with no queue
    (QUEUED, in the collecting step).  A pull request into main here skips them: the queue's group run judges it on
    the base as it is then.  A merge queue group and a push skip them too."""
    CHECKOUT = "the change, and the base's copy of the runner that judges it"
    TOOLS = "the base's tools, as the plan job takes them"
    STALE = "the base this run was built on is still the tip of the base branch"

    def test_the_stale_base_steps_run_where_no_merge_queue_checks_again(self):
        from oft.tests.test_facts_review_gate import evaluate
        job = load("pr.yml")["jobs"]["required"]
        collect = step(job, "every job green, and something checked when the plan named anything")
        queued_repo = "example/a-copy-whose-main-merges-through-a-queue"
        for name in (self.CHECKOUT, self.TOOLS, self.STALE):
            cond = " ".join(step(job, name)["if"].split())
            for event, repo, base in (("pull_request", queued_repo, "main"), ("pull_request", queued_repo, "lane"),
                                      ("pull_request", "theorem-labs/oss-verify-proofs", "main"),
                                      ("merge_group", queued_repo, "main"), ("push", queued_repo, "")):
                with self.subTest(step=name, event=event, repo=repo, base=base):
                    github = {"event_name": event, "repository": repo,
                              "event": {"pull_request": {"base": {"ref": base}}} if event == "pull_request" else {}}
                    queued = evaluate(" ".join(collect["env"]["QUEUED"].split()), {}, github=github)
                    self.assertEqual(bool(evaluate(cond, {}, github=github)),
                                     event == "pull_request" and not queued, cond)

    def test_the_stale_base_step_runs_the_base_s_copy_of_the_runner(self):
        job = load("pr.yml")["jobs"]["required"]
        self.assertIn('PYTHONPATH="$GITHUB_WORKSPACE/base/tools" python3 -m oft.tests.stale_base',
                      step(job, self.STALE)["run"])
        self.assertIn("base/tools/oft/tests/stale_base.py", step(job, self.TOOLS)["run"])


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class PrConcurrencyTest(unittest.TestCase):
    """pr.yml's concurrency, as GitHub evaluates it (helpers.Concurrency over helpers.gh_value), event by event: a
    run is cancelled by an event that brings a new commit (a new base starts no run: pr.yml does not run on
    `edited`, PrTriggerTest); a reopen and a mark of ready for review arrive on the very head whose run is going, so
    they cancel nothing and wait.  Measured over 2026-10-24 to 31 on this repository: of the 28 runs
    cancelled on their own head (221 runner-minutes), 17 were those two events, 175 of those minutes, and 8 of them
    were the run the merge needed (one of them 47.9 minutes of check)."""

    def setUp(self):
        self.workflow = load("pr.yml")
        self.runs = helpers.Concurrency(self.workflow)

    def test_a_new_commit_cancels_the_run_of_the_commit_before_it(self):
        """The cost this block saves: of the cancels measured in the window, 341 (9245 runner-minutes) were these."""
        self.runs.start("the old head", pull_request("synchronize", head="a" * 40))
        self.runs.start("the new head", pull_request("synchronize", head="b" * 40))
        self.assertEqual(self.runs.state("the old head"), "cancelled")
        self.assertEqual(self.runs.state("the new head"), "running")

    def test_a_reopen_or_a_mark_of_ready_for_review_cancels_no_run(self):
        """Both arrive on the head whose run is going: the run goes on, and the event's own run waits for it and
        starts when it ends."""
        for action in ("reopened", "ready_for_review"):
            with self.subTest(action=action):
                runs = helpers.Concurrency(self.workflow)
                runs.start("the check", pull_request("synchronize"))
                runs.start("the toggle", pull_request(action))
                self.assertEqual(runs.state("the check"), "running")
                self.assertEqual(runs.state("the toggle"), "pending")
                runs.finish("the check")
                self.assertEqual(runs.state("the toggle"), "running")

    def test_a_new_commit_replaces_the_event_that_waits(self):
        """Nothing waits for a head that is no longer the pull request's: the push cancels the run that checks the
        older head and the run that waits behind it."""
        self.runs.start("the old head", pull_request("synchronize", head="a" * 40))
        self.runs.start("the reopen", pull_request("reopened", head="a" * 40))
        self.runs.start("the new head", pull_request("synchronize", head="b" * 40))
        self.assertEqual([self.runs.state(name) for name in ("the old head", "the reopen", "the new head")],
                         ["cancelled", "cancelled", "running"])

    def test_one_pull_request_s_events_share_one_group_and_two_pull_requests_share_none(self):
        """The group is the pull request's, so a run of another pull request neither cancels this one's run nor
        waits for it."""
        self.assertEqual(self.runs.group(pull_request("synchronize")), self.runs.group(pull_request("reopened")))
        self.runs.start("ours", pull_request("synchronize", number=7))
        self.runs.start("theirs", pull_request("synchronize", number=8))
        self.assertEqual([self.runs.state("ours"), self.runs.state("theirs")], ["running", "running"])

    def test_a_push_to_main_and_a_merge_queue_group_have_a_run_per_commit(self):
        """Each commit of main and each merge queue group is decided on its own: a second push cancels neither."""
        self.runs.start("one commit", pushed("a" * 40))
        self.runs.start("the next commit", pushed("b" * 40))
        self.runs.start("a merge queue group", merge_group("c" * 40))
        self.assertEqual([self.runs.state(name) for name in ("one commit", "the next commit", "a merge queue group")],
                         ["running", "running", "running"])

    def test_a_second_run_of_one_commit_of_main_still_replaces_the_first(self):
        """Unchanged by the rule above, which reads the pull request's actions alone: two runs of the same commit of
        main share a group, and the newer one takes the older one's place."""
        self.runs.start("first", pushed("a" * 40))
        self.runs.start("second", pushed("a" * 40))
        self.assertEqual([self.runs.state("first"), self.runs.state("second")], ["cancelled", "running"])

    def test_the_expressions_are_read_as_github_reads_them(self):
        """The reading the tests above rest on: `&&` and `||` give one of their operands, a group's name is the key's
        text with the values written into it, and neither a push, whose event has no action, nor a merge queue
        group, whose action is `checks_requested`, matches an action name this key lists (unlike types compare as
        numbers: null is 0 and a word is NaN)."""
        self.assertEqual(helpers.gh_value("${{ 'a' && 'b' }}", {}), "b")
        self.assertEqual(helpers.gh_value("${{ '' || 'b' }}", {}), "b")
        self.assertEqual(helpers.gh_value("${{ format('{0}-{1}', 'x', 2) }}", {}), "x-2")
        self.assertEqual(helpers.gh_value("pr-${{ github.event.pull_request.number }}",
                                          pull_request("reopened")), "pr-7")
        self.assertIs(helpers.gh_value("${{ github.event.action != 'reopened' }}", pushed("a" * 40)), True)
        self.assertIs(helpers.gh_value("${{ github.event.action != 'reopened' }}", pull_request("reopened")), False)
        self.assertIs(self.runs.cancels(pushed("a" * 40)), True)
        self.assertIs(self.runs.cancels(merge_group("c" * 40)), True)
        self.assertIs(self.runs.cancels(pull_request("ready_for_review")), False)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class PrHoldTest(unittest.TestCase):
    """check and the fetch-drafts legs that feed it run on a pull request only when it is not a draft and carries the
    label `check` (read live; the label counts from the pull request's next run); with no merge queue after the pull
    request (a base other than main), required fails when the plan named harnesses and they were held."""

    def setUp(self):
        self.wf = load("pr.yml")

    def test_no_label_starts_a_run(self):
        self.assertEqual(self.wf["on"]["pull_request"]["types"],
                         ["opened", "synchronize", "reopened", "ready_for_review"])

    def test_check_and_fetch_drafts_run_only_when_not_held(self):
        jobs = self.wf["jobs"]
        for job in ("check", "fetch-drafts"):
            self.assertIn("&& needs.plan.outputs.hold == 'none'", " ".join(jobs[job]["if"].split()), job)

    def test_controls_run_on_the_4_core_runner_and_a_whole_tree_lint_on_16(self):
        self.assertEqual(self.wf["jobs"]["controls"]["runs-on"], "ubuntu-24.04-4core")
        # The lint job's runner is the plan job's two answers.  A lint whose checkout leaves out the proof
        # libraries (lint_files_left_out) holds about 0.1 GB of files and takes the standard runner; else a
        # per-file lint is minutes of work and takes the 4-core runner, and a whole-tree lint keeps 16 cores,
        # where it is no dearer and 3.4 times faster (the job's comment measures both).
        self.assertEqual(" ".join(self.wf["jobs"]["lint"]["runs-on"].split()),
                         "${{ needs.plan.outputs.lint_files_left_out == 'true' && 'ubuntu-24.04' "
                         "|| needs.plan.outputs.lint_changed_only == 'true' && 'ubuntu-24.04-4core' "
                         "|| 'ubuntu-24.04-16core' }}")
        self.assertEqual(self.wf["jobs"]["plan"]["outputs"]["lint_changed_only"],
                         "${{ steps.lint_gate.outputs.lint_changed_only }}")
        self.assertEqual(self.wf["jobs"]["plan"]["outputs"]["lint_files_left_out"],
                         "${{ steps.lint_gate.outputs.lint_files_left_out }}")

    def test_the_lint_gate_is_stricter_than_the_lint_step_s_own_rule(self):
        """The 4-core runner may carry a per-file lint only.  The lint step keeps its own rule and gives the
        verdict; the gate, which runs before the lint job starts, holds every clause of that rule and two
        more, so `true` chooses the small runner for a whole-tree lint only when the lint job's own reading of
        the record the plan read does not hold, which that job warns of (LintRecordTest).  A clause added to the
        step and not to the gate fails here."""
        gate = next(s for s in self.wf["jobs"]["plan"]["steps"] if s.get("id") == "lint_gate")
        step = next(s for s in self.wf["jobs"]["lint"]["steps"] if s.get("name") == "lint, by the base's rules")
        for clause in ('"$ROUTED" = true', '[ -n "$SINCE" ]',
                       'grep -q -- \'"--changed-only"\' base/tools/oft/__main__.py'):
            self.assertIn(clause, step["run"], clause)
            self.assertIn(clause, gate["run"], clause)
        # neither takes the branch into account: a routed change into any branch is judged on its own change
        for text in (step["run"], gate["run"]):
            self.assertNotIn('"$INTO" = refs/heads/main', text)
        for clause in ('"$PLANNED_TOOLS" != head', "lint.read_by_every_verdict"):
            self.assertIn(clause, gate["run"], clause)
        # the step's SINCE is the gate's (each job's own lint_since step, on the same record), so both read the same
        # tree for the same event; neither reads INTO, since the branch does not change the rule
        for s in (gate, step):
            self.assertNotIn("INTO", s["env"])
        self.assertEqual(gate["env"]["SINCE"], step["env"]["SINCE"])

    def required(self, hold, units, check, drafts_listed="false", fetch="skipped", comments=(), edits=(),
                 lint="success", queued="false"):
        """required's collecting step, with the values GitHub would give its env, for a pull request into a base other
        than main unless `queued` (no merge queue after it: QUEUED false), and a stand-in gh whose list of pull request
        7's issue comments is `comments` ("error": the call fails) and whose editors of the comment it takes are
        `edits`, a login each ("error": that call fails): (exit, output and summary)."""
        s = step(self.wf["jobs"]["required"], "every job green, and something checked when the plan named anything")
        self.assertEqual(s["env"]["HOLD"], "${{ needs.plan.outputs.hold }}")
        values = {"DRAFTS_LISTED": drafts_listed, "FETCH_DRAFTS_RESULT": fetch, "PLAN_RESULT": "success",
                  "TESTS": "false", "CONTROLS": "false", "REPOSITORY_LINT": "false", "UNITS": units, "HOLD": hold,
                  "QUEUED": queued, "PLANNED_TOOLS": "base", "LINT_RESULT": lint, "TESTS_RESULT": "skipped",
                  "CONTROLS_RESULT": "skipped", "CHECK_RESULT": check, "CHECKED_ELSEWHERE": "false",
                  "CHECKED_ELSEWHERE_NOTE": "",
                  # the stream tools' job: no path under dev/stream/ changes in these cases, so it is skipped
                  "STREAM_TOOLS": "false", "STREAM_TOOLS_RESULT": "skipped",
                  # the farm runner's tests: nothing they read changes in these cases, so they are skipped
                  "FARM_TESTS": "false", "FARM_TESTS_RESULT": "skipped",
                  # the evidence comment's inputs: the job's token, this pull request and its head, the poster
                  "GH_TOKEN": "t", "PR": "7", "HEAD_SHA": HEAD, "VM_EVIDENCE_BY": s["env"].get("VM_EVIDENCE_BY", "")}
        env = {k: values[k] for k in s["env"]}   # a variable the step gains and this test does not set fails here
        with tempfile.TemporaryDirectory() as d:
            bin_dir, api = os.path.join(d, "bin"), os.path.join(d, "api")
            os.mkdir(bin_dir)
            os.mkdir(api)
            with open(os.path.join(bin_dir, "gh"), "w") as f:
                f.write(FAKE_GH)
            os.chmod(os.path.join(bin_dir, "gh"), 0o755)
            endpoint = "repos/%s/issues/7/comments" % REPOSITORY
            with open(os.path.join(api, endpoint.replace("/", "_") + ".json"), "w") as f:
                json.dump("error" if comments == "error" else list(comments), f)
            with open(os.path.join(api, "graphql.json"), "w") as f:
                # GraphQL names an App `Bot` and gives its login without the `[bot]` REST appends
                json.dump("error" if edits == "error" else
                          {"data": {"node": {"author": {"__typename": "Bot", "login": "sjawhar-agent"},
                                             "userContentEdits": {
                                                 "totalCount": len(edits),
                                                 "nodes": [{"editor": {"__typename": t, "login": n}}
                                                           for t, n in edits]}}}}, f)
            summary = os.path.join(d, "summary")
            r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", s["run"]], capture_output=True,
                               text=True, env=dict(os.environ, GITHUB_STEP_SUMMARY=summary, FAKE_GH=api,
                                                   PATH=bin_dir + os.pathsep + os.environ["PATH"],
                                                   GITHUB_REPOSITORY=REPOSITORY, **env))
            out = r.stdout + r.stderr
            if os.path.exists(summary):
                with open(summary) as f:
                    out += f.read()
            return r.returncode, out

    @staticmethod
    def evidence(n=1, head=HEAD, mode="checklog", login="sjawhar-agent[bot]", kind="Bot", first_line=None):
        """An issue comment as GitHub lists it: merge-pr.sh's evidence comment, unless the arguments change it."""
        line = first_line if first_line is not None else "<!-- vm-evidence head=%s mode=%s -->" % (head, mode)
        return {"user": {"login": login, "type": kind}, "node_id": "C_%d" % n,
                "html_url": "https://github.com/%s/pull/7#issuecomment-%d"
                % (REPOSITORY, n), "body": line + "\nVM evidence: oft check log covers this head; 5 proofs pass.\n"}

    def test_required_reads_the_pull_request_s_comments_with_the_job_s_pull_requests_read(self):
        """The collecting step lists the pull request's issue comments with the job's token, which holds
        pull-requests: read (GitHub's "List issue comments" accepts Issues or Pull requests read; contents: read is
        the stale base steps'), and trusts only the identity merge-pr.sh posts with."""
        job = self.wf["jobs"]["required"]
        s = step(job, "every job green, and something checked when the plan named anything")
        self.assertEqual(job["permissions"], {"pull-requests": "read", "contents": "read"})
        self.assertEqual((s["env"]["GH_TOKEN"], s["env"]["PR"], s["env"]["HEAD_SHA"], s["env"]["VM_EVIDENCE_BY"]),
                         ("${{ github.token }}", "${{ github.event.pull_request.number }}",
                          "${{ github.event.pull_request.head.sha }}", "sjawhar-agent[bot]"))

    def test_a_check_held_for_the_label_passes_on_merge_pr_s_evidence_comment(self):
        """Of the comments that carry the marker for this head the newest answers, since a later run of merge-pr.sh
        posts a later comment."""
        for mode in ("pvc", "xh", "checklog"):
            with self.subTest(mode=mode):
                rc, out = self.required("label", "3", "skipped",
                                        comments=[self.evidence(1, login="someone", kind="User"),
                                                  self.evidence(2), self.evidence(3, mode=mode)])
                self.assertEqual(rc, 0, out)
                self.assertIn("held check accepted on merge-pr.sh's VM evidence comment (%s): "
                              "https://github.com/%s/pull/7#issuecomment-3" % (mode, REPOSITORY), out)
                self.assertNotIn("harnesses checked", out)

    def test_a_held_check_fails_when_anyone_else_edited_the_evidence_comment(self):
        """GitHub lets an editor rewrite a comment's body, and keeps every editor in userContentEdits, which only
        GraphQL gives: an edit by anyone but the App, and an answer that cannot be read, leave the comment unread.
        The App's own edit (a later run of merge-pr.sh rewriting its comment) counts.  GraphQL names the App a
        `Bot` with the login `sjawhar-agent`, without the `[bot]` REST appends."""
        app = ("Bot", "sjawhar-agent")
        for name, edits, want in (("another editor", [app, ("User", "someone")], 1),
                                  ("a user of the App's name", [("User", "sjawhar-agent")], 1),
                                  ("the read fails", "error", 1),
                                  ("no edit", [], 0),
                                  ("the App's own edit", [app], 0)):
            with self.subTest(case=name):
                rc, out = self.required("label", "3", "skipped", comments=[self.evidence()], edits=edits)
                self.assertEqual(rc, want, out)
                self.assertEqual("held check accepted" in out, want == 0, out)
                # a read that fails says so, with gh's own error, and a read that succeeds says nothing of it
                self.assertEqual("::warning::the editors of pull request 7's evidence comment cannot be read:" in out,
                                 edits == "error", out)

    def test_a_held_check_fails_without_an_evidence_comment_it_can_trust(self):
        """Another author, another bot, a person's account named like the bot, a marker for another commit, a
        marker that is not the first line or not exact, another mode, no comment, or comments that cannot be read:
        today's failure, unchanged.  A draft fails before it asks (test_a_draft_runs_no_lint_...)."""
        other = "d" * 40
        for name, hold, comments in (
                ("another author", "label", [self.evidence(login="someone", kind="User")]),
                ("another bot", "label", [self.evidence(login="other-app[bot]")]),
                ("a person named like the bot", "label", [self.evidence(kind="User")]),
                ("a marker for another commit", "label", [self.evidence(head=other)]),
                ("a short sha", "label", [self.evidence(head=HEAD[:12])]),
                ("another mode", "label", [self.evidence(mode="vm")]),
                ("the marker not first", "label", [self.evidence(first_line="VM evidence")]),
                ("a marker with a trailing space", "label",
                 [self.evidence(first_line="<!-- vm-evidence head=%s mode=checklog --> " % HEAD)]),
                ("no comment", "label", []),
                ("comments that cannot be read", "label", "error")):
            with self.subTest(case=name):
                rc, out = self.required(hold, "3", "skipped", comments=comments)
                self.assertEqual(rc, 1, out)
                self.assertIn("planned checks not run at this head", out)
                self.assertIn("add the label `check` and re-run all jobs", out)
                self.assertNotIn("held check accepted", out)

    def test_the_evidence_comment_does_not_excuse_a_check_that_ran_or_another_failure(self):
        for name, kw in (("check ran while held", dict(hold="label", units="3", check="success")),
                         ("fetch-drafts ran while held", dict(hold="label", units="3", check="skipped",
                                                              drafts_listed="true", fetch="success"))):
            with self.subTest(case=name):
                self.assertEqual(self.required(comments=[self.evidence()], **kw)[0], 1)

    def test_required_fails_when_planned_checks_were_held(self):
        rc, out = self.required("label", "3", "skipped", drafts_listed="true")
        self.assertEqual(rc, 1, out)
        self.assertIn("planned checks not run at this head", out)
        self.assertIn("add the label `check` and re-run all jobs", out)
        for hold, units, check, want in (("none", "3", "success", 0), ("label", "0", "skipped", 0),
                                         ("none", "3", "skipped", 1), ("label", "3", "success", 1),
                                         ("", "0", "skipped", 1), ("false", "0", "skipped", 1)):
            with self.subTest(hold=hold, units=units, check=check):
                self.assertEqual(self.required(hold, units, check)[0], want)

    def test_a_draft_runs_no_lint_and_passes_only_where_the_merge_queue_judges_it(self):
        """On a draft lint and every job after it are skipped.  Into main, whose merge queue lints the change before it
        merges, required passes and says so, whatever the plan named; into any other base it fails until the pull
        request is marked ready for review.  A job that ran on a draft fails it either way, and so does a merge-pr.sh
        evidence comment, which excuses only a check held for the label."""
        for units in ("0", "3"):
            with self.subTest(units=units, queued=True):
                rc, out = self.required("draft", units, "skipped", lint="skipped", queued="true")
                self.assertEqual(rc, 0, out)
                self.assertIn("lint skipped: a draft", out)
            with self.subTest(units=units, queued=False):
                rc, out = self.required("draft", units, "skipped", lint="skipped", comments=[self.evidence()])
                self.assertEqual(rc, 1, out)
                self.assertIn("a draft: lint and the jobs after it did not run at this head; mark it ready for review",
                              out)
                self.assertNotIn("held check accepted", out)
        for name, kw in (("lint ran", dict(lint="success")), ("lint failed", dict(lint="failure")),
                         ("check ran", dict(lint="skipped", check="success")),
                         ("fetch-drafts ran", dict(lint="skipped", drafts_listed="true", fetch="success"))):
            with self.subTest(case=name):
                kw = dict({"check": "skipped"}, **kw)
                rc, out = self.required("draft", "3", queued="true", **kw)
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::a draft, yet ", out)

    def hold_step(self, event, state=None, event_draft="", event_labels="null"):
        """The plan job's hold step with a gh that answers {draft, labels} with `state` (None: the call fails):
        (its exit, its output, what it wrote to GITHUB_OUTPUT)."""
        s = next(s for s in self.wf["jobs"]["plan"]["steps"] if s.get("id") == "hold")
        with tempfile.TemporaryDirectory() as d:
            gh = os.path.join(d, "gh")
            with open(gh, "w") as f:
                f.write("#!/usr/bin/env bash\n" + ("echo 'gh: HTTP 502' >&2; exit 1\n" if state is None else
                                                   "cat <<'EOF'\n%s\nEOF\n" % json.dumps(state)))
            os.chmod(gh, 0o755)
            out = os.path.join(d, "out")
            env = dict(os.environ, PATH=d + os.pathsep + os.environ["PATH"], GITHUB_OUTPUT=out,
                       GITHUB_EVENT_NAME=event, GITHUB_REPOSITORY=REPOSITORY, GH_TOKEN="t", PR="7",
                       EVENT_DRAFT=event_draft, EVENT_LABELS=event_labels)
            r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", s["run"]], env=env,
                               capture_output=True, text=True)
            with open(out) if os.path.exists(out) else open(os.devnull) as f:
                return r.returncode, r.stdout + r.stderr, f.read()

    def test_the_hold_step_reads_the_pull_request_as_it_is_now(self):
        """A re-run keeps its first event, so the step asks for the pull request's draft state and labels; the event's
        own values answer only when that call fails.  It reads the label do-not-merge from the same answer, which
        fails required.  A merge queue group and a push are never held."""
        plan = self.wf["jobs"]["plan"]
        s = next(s for s in plan["steps"] if s.get("id") == "hold")
        self.assertEqual(plan["outputs"]["hold"], "${{ steps.hold.outputs.hold }}")
        self.assertEqual(plan["permissions"], {"contents": "read", "pull-requests": "read"})
        self.assertEqual(s["env"], {"GH_TOKEN": "${{ github.token }}", "PR": "${{ github.event.pull_request.number }}",
                                    "EVENT_DRAFT": "${{ github.event.pull_request.draft }}",
                                    "EVENT_LABELS": "${{ toJSON(github.event.pull_request.labels) }}"})
        check = [{"name": "legion"}, {"name": "Check"}]
        for state, want, dnm in (({"draft": True, "labels": []}, "draft", "false"),
                                 ({"draft": True, "labels": check}, "draft", "false"),
                                 ({"draft": False, "labels": []}, "label", "false"),
                                 ({"draft": False, "labels": [{"name": "ready"}]}, "label", "false"),
                                 ({"draft": False, "labels": check}, "none", "false"),
                                 ({"draft": False, "labels": check + [{"name": "Do-Not-Merge"}]}, "none", "true")):
            with self.subTest(state=state):
                rc, output, wrote = self.hold_step("pull_request", state, event_draft="false", event_labels="[]")
                self.assertEqual((rc, wrote), (0, "hold=%s\ndo_not_merge=%s\n" % (want, dnm)), output)
        for draft, labels, want in (("true", "[]", "draft"), ("false", json.dumps(check), "none"),
                                    ("false", "[]", "label")):
            with self.subTest(draft=draft, labels=labels):
                rc, output, wrote = self.hold_step("pull_request", None, event_draft=draft, event_labels=labels)
                self.assertEqual((rc, wrote), (0, "hold=%s\ndo_not_merge=false\n" % want), output)
                self.assertIn("::warning::could not read pull request 7", output)
        for event in ("push", "merge_group"):
            with self.subTest(event=event):
                self.assertEqual(self.hold_step(event, None)[::2], (0, "hold=none\ndo_not_merge=false\n"))


@unittest.skipUnless(shutil.which("jq") and shutil.which("sha256sum"), "jq or sha256sum is not installed")
class FetchDraftsTagTest(unittest.TestCase):
    """fetch-drafts.yml's fetch step downloads a draft file by the tag its pin names: a release's (v<release>,
    v<release>-src), a sources-v<N> release of release.yaml's source archives, or an enrollment commit's own draft
    (enroll-<project>-<12 hex>, and -src), checked before it reaches `gh release download`."""

    def fetch(self, release):
        """The fetch step for one pin of libreac-bin.tar.zst on `release`, with a gh that downloads the archive:
        (its exit, its output)."""
        s = step(load("fetch-drafts.yml")["jobs"]["fetch"], "this job's draft files, each by the tag its pin "
                 "names, checked against its SHA-256")
        with tempfile.TemporaryDirectory() as d:
            gh = os.path.join(d, "gh")
            with open(gh, "w") as f:
                # gh release download TAG --repo R --pattern FILE --dir DIR
                f.write('#!/usr/bin/env bash\nprintf archive > "$9/$7"\n')
            os.chmod(gh, 0o755)
            pins = json.dumps([{"release": release, "file": "libreac-bin.tar.zst",
                                "sha256": hashlib.sha256(b"archive").hexdigest()}])
            env = dict(os.environ, PATH=d + os.pathsep + os.environ["PATH"], PINS=pins, GH_TOKEN="t",
                       RUNNER_TEMP=d, GITHUB_OUTPUT=os.path.join(d, "out"), GITHUB_REPOSITORY=REPOSITORY,
                       GITHUB_RUN_ID="5", GITHUB_RUN_ATTEMPT="1")
            r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", s["run"]], env=env,
                               capture_output=True, text=True)
            return r.returncode, r.stdout + r.stderr

    def test_the_fetch_drafts_tag_check_accepts_both_forms(self):
        for release in ("v2026.10.3", "v2026.10.3-src", "v2026.10.0-rc.2", "sources-v2", "enroll-libreac-0123456789ab",
                        "enroll-libreac-0123456789ab-src", "enroll-reac-pw-0123456789ab"):
            with self.subTest(release=release):
                rc, out = self.fetch(release)
                self.assertEqual(rc, 0, out)
        for release in ("enroll-libreac-0123", "enroll-Libreac-0123456789ab", "w2026.10.3", "findings-libreac",
                        "enroll-libreac-0123456789ab-bin", "enroll-libreac-0123456789ab*"):
            with self.subTest(release=release):
                rc, out = self.fetch(release)
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::not a release tag: '%s'" % release, out)


FACTS_REVIEW = os.path.join(WORKFLOWS, "facts-review.yml")
# the internal repository alone has these (release_tree.INTERNAL): a release's tests find neither
INDEX = os.path.join(WORKFLOWS, "index.yml")
ENROLL = os.path.join(WORKFLOWS, "enroll.yml")
ENROLL_YML = {"enroll.yml"} if os.path.exists(ENROLL) else set()


@unittest.skipUnless(os.path.exists(FACTS_REVIEW), "no .github/workflows/facts-review.yml: the internal repository "
                                                   "alone has it")
class FactsReviewConcurrencyTest(unittest.TestCase):
    """facts-review.yml follows pr.yml's rule: a new commit cancels the review of the commit before it and so does
    a new base, whose review would otherwise judge the base the pull request has left; a reopen and a mark of ready
    for review reach the head whose review is running, so they cancel nothing and wait."""

    def setUp(self):
        self.runs = helpers.Concurrency(load("facts-review.yml"))

    def test_a_new_commit_cancels_the_review_of_the_commit_before_it(self):
        self.runs.start("the old head", pull_request("synchronize", head="a" * 40))
        self.runs.start("the new head", pull_request("synchronize", head="b" * 40))
        self.assertEqual([self.runs.state("the old head"), self.runs.state("the new head")],
                         ["cancelled", "running"])

    def test_a_reopen_or_a_mark_of_ready_for_review_cancels_no_review(self):
        for action in ("reopened", "ready_for_review"):
            with self.subTest(action=action):
                runs = helpers.Concurrency(load("facts-review.yml"))
                runs.start("the review", pull_request("synchronize"))
                runs.start("the toggle", pull_request(action))
                self.assertEqual([runs.state("the review"), runs.state("the toggle")], ["running", "pending"])

    def test_a_new_base_still_cancels_the_review_of_the_base_the_change_has_left(self):
        self.runs.start("the old base", pull_request("synchronize"))
        self.runs.start("the retarget", pull_request("edited", base_changed=True))
        self.assertEqual([self.runs.state("the old base"), self.runs.state("the retarget")],
                         ["cancelled", "running"])

    def test_each_edit_of_the_title_or_body_holds_a_group_of_its_own(self):
        """Such an edit runs no job (test_facts_review_gate.WorkflowTest), and its run's group is the run's own id,
        not the pull request's number, so it neither cancels a review nor waits for another edit's run."""
        self.runs.start("the review", pull_request("synchronize"))
        self.runs.start("an edit", pull_request("edited", run_id=2))
        self.runs.start("another edit", pull_request("edited", run_id=3))
        self.assertEqual([self.runs.state(name) for name in ("the review", "an edit", "another edit")],
                         ["running", "running", "running"])
        self.assertNotEqual(self.runs.group(pull_request("edited", run_id=2)),
                            self.runs.group(pull_request("edited", run_id=3)))

    def test_a_run_by_hand_keys_on_the_pull_request_it_names(self):
        """workflow_dispatch carries no event action, so it still replaces a review of the same pull request."""
        self.assertEqual(self.runs.group(dispatched(pr=7)), self.runs.group(pull_request("synchronize", number=7)))
        self.runs.start("the review", pull_request("synchronize", number=7))
        self.runs.start("by hand", dispatched(pr=7))
        self.assertEqual([self.runs.state("the review"), self.runs.state("by hand")], ["cancelled", "running"])


def results(names, **given):
    """A needs context: every job of `names` succeeded, except as `given`."""
    return {n: given.get(n.replace("-", "_"), "success") for n in names}


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class CollectTest(StandIn):
    """The job that collects a run's results into its one verdict: it always runs, it needs every other job of the
    workflow (so a job added later cannot pass unseen), and its step passes or fails as the table says."""

    def collector(self, workflow, name):
        jobs = load(workflow)["jobs"]
        job = jobs[name]
        self.assertEqual(job["if"], "always()")
        self.assertEqual(sorted(job["needs"]), sorted(n for n in jobs if n != name))
        self.assertEqual(job["permissions"], {})
        self.assertEqual(len(job["steps"]), 1)
        return job["steps"][0]

    def check(self, step_, cases):
        for env, want in cases:
            with self.subTest(**env):
                rc, out, _ = self.run_step(step_["run"], env)
                self.assertEqual(rc, 0 if want else 1, out)

    def test_images(self):
        s = self.collector("images.yml", "images")
        jobs = load("images.yml")["jobs"]
        self.assertEqual(jobs["image"]["if"], "needs.plan.outputs.images != '[]'")
        # HERE is the plan job's own condition, and VERIFY verify-pins'
        self.assertEqual(s["env"]["HERE"], "${{ %s }}" % jobs["plan"]["if"])
        self.assertEqual(s["env"]["VERIFY"], "${{ %s }}" % jobs["verify-pins"]["if"])

        # a push, or a run by hand that builds an image, by default: verify-pins runs on neither
        def env(here="true", plan="success", images='["checker"]', image="success", verify="false", pins="skipped"):
            return {"HERE": here, "PLAN": plan, "IMAGES": images, "IMAGE": image, "VERIFY": verify, "PINS": pins}
        self.check(s, [
            (env(), True),
            (env(images='["checker","runner"]'), True),
            (env(images="[]", image="skipped"), True),                        # a push that changes no image's input
            (env(image="failure"), False),
            (env(image="cancelled"), False),
            (env(image="skipped"), False),                                    # named, and not built
            (env(images="[]", image="success"), False),                       # built, and not named
            (env(plan="failure", images="", image="skipped"), False),         # e.g. a dispatch off main
            (env(plan="cancelled", images="", image="skipped"), False),
            (env(here="false", plan="skipped", images="", image="skipped"), True),   # the public repository
            (env(here="false"), False),
            # a daily run, or one by hand that builds nothing: the pins are verified
            (env(verify="true", pins="success"), True),
            (env(images="[]", image="skipped", verify="true", pins="success"), True),
            (env(verify="true", pins="failure"), False),                      # a pin refused
            (env(images="[]", image="skipped", verify="true", pins="failure"), False),
            (env(verify="true", pins="cancelled"), False),
            (env(verify="true", pins="skipped"), False),
            (env(image="failure", verify="true", pins="success"), False),
            (env(plan="failure", images="", image="skipped", verify="true", pins="success"), False),
            (env(pins="success"), False),                                     # it ran on a push
            (env(here="false", plan="skipped", images="", image="skipped", pins="success"), False),
        ])

    def test_weekly(self):
        s = self.collector("weekly.yml", "weekly")
        names = ["plan", "sweep", "assets", "determinism", "determinism-compare"]

        def env(here="true", **given):
            r = results(names, **given)
            return {"HERE": here, "PLAN": r["plan"], "SWEEP": r["sweep"], "ASSETS": r["assets"],
                    "DETERMINISM": r["determinism"], "COMPARE": r["determinism-compare"]}
        cases = [(env(), True)]
        for job in ("plan", "sweep", "assets", "determinism", "determinism_compare"):
            for result in ("failure", "cancelled", "skipped"):
                cases.append((env(**{job: result}), False))
        nothing = dict(plan="skipped", sweep="skipped", assets="skipped", determinism="skipped",
                       determinism_compare="skipped")
        cases += [(env(here="false", **nothing), True),               # a scheduled run outside the public repository
                  (env(here="false"), False),
                  (env(here="false", **dict(nothing, assets="success")), False)]
        self.check(s, cases)

    def test_weekly_schedule_runs_in_the_public_repository_only(self):
        """The internal repository's weekly.yml has no schedule (one full sweep there measured about 137 hours of
        16-core runners; the stream lead, 2026-10-28); the public repository's sweeps every Monday. Each job that needs
        no other job, and the collector's HERE, carry the one condition; a run by hand or a release's call runs in
        both."""
        jobs = load("weekly.yml")["jobs"]
        heads = sorted(n for n, j in jobs.items() if "needs" not in j)
        self.assertEqual(heads, ["assets", "plan"])
        condition = jobs["plan"]["if"]
        self.assertEqual(jobs["assets"]["if"], condition)
        self.assertEqual(jobs["weekly"]["steps"][0]["env"]["HERE"], "${{ %s }}" % condition)
        public, internal = "1430054678", "1425069221"
        for repository_id, event, runs in ((public, "schedule", True), (internal, "schedule", False),
                                           (public, "workflow_dispatch", True), (internal, "workflow_dispatch", True),
                                           (internal, "push", True), (internal, "release", True)):
            with self.subTest(repository_id=repository_id, event=event):
                scope = {"github": {"repository_id": repository_id, "event_name": event}}
                self.assertIs(helpers.gh_truthy(helpers.gh_value("${{ %s }}" % condition, scope)), runs)

    # pr.yml's required, for a change whose planned parts a check of record outside this run checked (plan D4: the
    # pinned tree's deferred check, or a merge queue group or a pull request checked on a VM): its collecting step,
    # run with the values GitHub gives its env (a variable the step gains and these tests do not give fails them).
    # Which of the two it is, and the deferral's own rules, are the plan job's elsewhere step's
    # (QueueVmEvidenceTest); required reads the one pair.
    ELSEWHERE_RUN = {"PLAN_RESULT": "success", "TESTS": "true", "CONTROLS": "true", "REPOSITORY_LINT": "true",
                     "UNITS": "2148", "HOLD": "none", "QUEUED": "true", "PLANNED_TOOLS": "head",
                     "LINT_RESULT": "success", "TESTS_RESULT": "success", "CONTROLS_RESULT": "success",
                     "CHECK_RESULT": "skipped", "DRAFTS_LISTED": "false", "FETCH_DRAFTS_RESULT": "skipped",
                     "CHECKED_ELSEWHERE": "true", "CHECKED_ELSEWHERE_NOTE": "the check of record: " + RECORD,
                     # the stream tools' job: these cases change nothing under dev/stream/ that
                     # the job did not pass on, so it ran and passed
                     "STREAM_TOOLS": "true", "STREAM_TOOLS_RESULT": "success",
                     # the farm runner's tests: nothing they read changes in these cases, so they are skipped
                     "FARM_TESTS": "false", "FARM_TESTS_RESULT": "skipped",
                     "GH_TOKEN": "t", "PR": "7", "HEAD_SHA": HEAD, "VM_EVIDENCE_BY": "sjawhar-agent[bot]"}

    def pr_required(self, **given):
        s = step(load("pr.yml")["jobs"]["required"],
                 "every job green, and something checked when the plan named anything")
        values = dict(self.ELSEWHERE_RUN, **given)
        rc, out, summary = self.run_step(s["run"], {k: values[k] for k in s["env"]})
        return rc, out + summary

    def test_required_passes_a_change_checked_elsewhere_whose_check_was_skipped(self):
        """Whatever the label: such a change's check runs nowhere in this workflow, so the hold's "the merge queue
        checks them" would not be true of it.  With the base's tools too: a merge queue group is judged by them.  A
        draft runs no lint and is read as a draft first (PrHoldTest), the merge queue judging it in full."""
        for hold, queued, tools in (("none", "true", "head"), ("none", "false", "head"), ("label", "true", "head"),
                                    ("none", "false", "base")):
            with self.subTest(hold=hold, queued=queued, tools=tools):
                rc, out = self.pr_required(HOLD=hold, QUEUED=queued, PLANNED_TOOLS=tools)
                self.assertEqual(rc, 0, out)
                self.assertIn("checks not run here: 2148 harnesses planned; the check of record: " + RECORD, out)
                self.assertNotIn("checks skipped", out)
                self.assertNotIn("harnesses checked", out)
        rc, out = self.pr_required(HOLD="draft", LINT_RESULT="skipped", TESTS_RESULT="skipped",
                                   CONTROLS_RESULT="skipped", STREAM_TOOLS_RESULT="skipped")
        self.assertEqual(rc, 0, out)
        self.assertIn("lint skipped: a draft", out)

    def test_required_passes_a_group_whose_pull_requests_were_checked_on_a_vm(self):
        evidence = ("merge-pr.sh's VM evidence, each planned part's key equal to its check of record's: "
                    "#563 %s (pvc): https://github.com/%s/pull/563#issuecomment-1, "
                    "#565 %s (checklog): https://github.com/%s/pull/565#issuecomment-2"
                    % (HEAD, REPOSITORY, HEAD, REPOSITORY))
        rc, out = self.pr_required(PLANNED_TOOLS="base", CHECKED_ELSEWHERE_NOTE=evidence)
        self.assertEqual(rc, 0, out)
        self.assertIn("checks not run here: 2148 harnesses planned; " + evidence, out)

    def test_required_passes_a_pull_request_checked_on_a_vm_naming_its_marker_comment(self):
        """A pull request's run defers as a group does (QueueVmEvidenceTest, its pull request cases): required
        says so and names the comment, whatever the label and whether a queue follows."""
        evidence = ("merge-pr.sh's VM evidence, each planned part's key equal to its check of record's: "
                    "#1478 %s (pvc): https://github.com/%s/pull/1478#issuecomment-1" % (HEAD, REPOSITORY))
        for hold, queued in (("none", "true"), ("none", "false"), ("label", "true"), ("label", "false")):
            with self.subTest(hold=hold, queued=queued):
                rc, out = self.pr_required(HOLD=hold, QUEUED=queued, PLANNED_TOOLS="base",
                                           CHECKED_ELSEWHERE_NOTE=evidence)
                self.assertEqual(rc, 0, out)
                self.assertIn("checks not run here: 2148 harnesses planned; " + evidence, out)
                self.assertNotIn("checks skipped", out)

    def test_required_fails_a_change_checked_elsewhere_whose_check_ran(self):
        for name, given in (("check ran", dict(CHECK_RESULT="success")),
                            ("check failed", dict(CHECK_RESULT="failure")),
                            ("fetch-drafts ran", dict(FETCH_DRAFTS_RESULT="success")),
                            ("drafts listed", dict(DRAFTS_LISTED="true", FETCH_DRAFTS_RESULT="success"))):
            with self.subTest(case=name):
                self.assertEqual(self.pr_required(**given)[0], 1)

    def test_required_fails_a_change_checked_elsewhere_that_names_none_or_another_failure(self):
        for name, given in (("no check of record", dict(CHECKED_ELSEWHERE_NOTE="")),
                            ("an answer of another word", dict(CHECKED_ELSEWHERE="yes")),
                            ("no answer", dict(CHECKED_ELSEWHERE="")),
                            ("lint failed", dict(LINT_RESULT="failure")),
                            ("tests failed", dict(TESTS_RESULT="failure")),
                            ("controls failed", dict(CONTROLS_RESULT="failure")),
                            ("the plan failed", dict(PLAN_RESULT="failure"))):
            with self.subTest(case=name):
                self.assertEqual(self.pr_required(**given)[0], 1)

    def test_required_without_that_answer_judges_the_check_as_before(self):
        for check, want in (("success", 0), ("skipped", 1), ("failure", 1)):
            with self.subTest(check=check):
                rc, out = self.pr_required(CHECKED_ELSEWHERE="false", CHECKED_ELSEWHERE_NOTE="", CHECK_RESULT=check)
                self.assertEqual(rc, want, out)
                self.assertNotIn("checks not run here", out)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class ImagesAttestationTest(StandIn):
    """images.yml runs `gh attestation verify` as a digest release.yaml pins is verified, in a run,
    whose token can read this repository's attestations where an agent's cannot: the image job, right after its attest
    step, verifies the name and digest that step attested; the job verify-pins, daily and on a run by hand that builds
    nothing, after no other job, verifies release.yaml's images.checker and images.runner.  Each names every digest
    with its verdict, and fails when the command refuses one or the gh is older than 2.67; the image job tries three
    times.  A run by hand that builds an image is judged by the images it built, not by the pins."""

    NAME = "ghcr.io/theorem-labs/oss-fuzz-theorems-checker"
    DIGEST = "sha256:" + "6" * 64
    SHA = "a" * 40
    PINNED = ("sha256:" + "c" * 64, "sha256:" + "d" * 64)
    PINS = {"checker": "ghcr.io/theorem-labs/oss-fuzz-theorems-checker@" + PINNED[0],
            "runner": "ghcr.io/theorem-labs/oss-fuzz-theorems-runner@" + PINNED[1]}
    # this repository's id, which the jobs' conditions name; an image's name; the digest each build pushes
    HERE = "1425069221"
    IMAGE = "ghcr.io/theorem-labs/oss-fuzz-theorems-%s"
    NEW = {"checker": "sha256:" + "1" * 64, "runner": "sha256:" + "2" * 64}
    VERSION = "2.98.0"
    # the signer the steps require: images.yml at refs/heads/main, as the signing certificate names it
    IDENTITY = "https://github.com/%s/.github/workflows/images.yml@refs/heads/main" % REPOSITORY
    # a gh that names its version (GH_VERSION, or VERSION) and takes `gh attestation verify` alone: it logs the
    # arguments of each verify, one JSON list a line, to <FAKE_GH>/verify.jsonl; it refuses a digest REFUSE names as gh
    # does with the API's 403, and fails the first FLAKY verifies as gh does with a passing error of the API
    GH = ("#!%s\nimport json, os, sys\n"
          "version = os.environ.get('GH_VERSION') or %r\n"
          "if sys.argv[1:] == ['--version']:\n"
          "    print('gh version %%s (2026-08-20)' %% version)\n"
          "    print('https://github.com/cli/cli/releases/tag/v%%s' %% version)\n"
          "    sys.exit(0)\n"
          "log = os.path.join(os.environ['FAKE_GH'], 'verify.jsonl')\n"
          "with open(log, 'a') as f:\n"
          "    f.write(json.dumps(sys.argv[1:]) + '\\n')\n"
          "if sys.argv[1:3] != ['attestation', 'verify']:\n"
          "    sys.exit(9)\n"
          "if sys.argv[3].rsplit('@', 1)[-1] in os.environ.get('REFUSE', '').split():\n"
          "    sys.exit('Error: HTTP 403: Resource not accessible by integration')\n"
          "if sum(1 for _ in open(log)) <= int(os.environ.get('FLAKY') or 0):\n"
          "    sys.exit('Error: HTTP 502: Server Error')\n"
          "print('Verification succeeded!')\n"
          % (sys.executable, VERSION))

    def setUp(self):
        super().setUp()
        with open(os.path.join(self.dir, "bin", "gh"), "w") as f:
            f.write(self.GH)

    def verified(self):
        """The arguments of each `gh attestation verify` the steps ran."""
        path = os.path.join(self.api, "verify.jsonl")
        if not os.path.exists(path):
            return []
        with open(path) as f:
            return [json.loads(line) for line in f]

    def forget(self):
        """Forgets what the stand-ins logged: each verify's arguments and each sleep."""
        for name in ("verify.jsonl", "calls"):
            path = os.path.join(self.api, name)
            if os.path.exists(path):
                os.remove(path)

    @classmethod
    def command(cls, ref, *more):
        """gh's arguments for the command at the top of images.yml, of `ref`."""
        return ["attestation", "verify", "oci://" + ref, "--repo", REPOSITORY, "--cert-identity", cls.IDENTITY,
                "--source-ref", "refs/heads/main"] + list(more)

    def steps(self):
        """The image job, its attest step and the step after it."""
        job = load("images.yml")["jobs"]["image"]
        at = [s.get("id") for s in job["steps"]].index("attest")
        return job, job["steps"][at], job["steps"][at + 1]

    def verify_built(self, name=NAME, digest=DIGEST, refuse=(), version="", flaky=0):
        """The step after the attest step, of the image `name` pushed as `digest`, run with the stand-in gh of
        `version` refusing the digests `refuse` and failing its first `flaky` verifies: (its exit, its output, its
        summary)."""
        verify = self.steps()[2]
        values = {"GH_TOKEN": "t", "NAME": name, "DIGEST": digest}
        env = {k: values[k] for k in verify.get("env", {})}
        env.update(GITHUB_REPOSITORY=REPOSITORY, GITHUB_SHA=self.SHA, REFUSE=" ".join(refuse), GH_VERSION=version,
                   FLAKY=str(flaky))
        return self.run_step(verify["run"], env)

    def test_the_step_after_the_attest_step_verifies_its_subject_with_the_job_s_token(self):
        job, attest, verify = self.steps()
        self.assertEqual(verify.get("env"), {"GH_TOKEN": "${{ github.token }}",
                                             "NAME": attest["with"]["subject-name"],
                                             "DIGEST": attest["with"]["subject-digest"]})
        # its failure is the job's: it runs whenever the attest step passed, and nothing excuses its exit
        self.assertNotIn("if", verify)
        self.assertNotIn("continue-on-error", verify)
        # the attestations API's GET of a digest needs attestations: read, which the attest step's write holds
        self.assertIn(job["permissions"].get("attestations"), ("read", "write"))

    def test_a_verified_attestation_passes_and_names_the_digest(self):
        rc, out, summary = self.verify_built()
        self.assertEqual(rc, 0, out)
        # narrowed to the commit this run built
        self.assertEqual(self.verified(), [self.command("%s@%s" % (self.NAME, self.DIGEST),
                                                        "--source-digest", self.SHA)])
        self.assertEqual(self.calls(), [], out)
        self.assertIn("attestation verified: %s@%s" % (self.NAME, self.DIGEST), out)
        self.assertIn("gh version %s" % self.VERSION, out)
        self.assertIn("attestation verified: %s@%s" % (self.NAME, self.DIGEST), summary)

    def test_a_refused_verification_fails_the_job_after_three_tries_and_names_the_digest(self):
        rc, out, summary = self.verify_built(refuse=[self.DIGEST])
        self.assertEqual(rc, 1, out)
        self.assertIn("Resource not accessible by integration", out)
        self.assertEqual(len(self.verified()), 3, out)
        self.assertEqual(self.calls(), ["sleep 10", "sleep 20"], out)
        self.assertIn("::error::gh attestation verify refused %s@%s" % (self.NAME, self.DIGEST), out)
        self.assertNotIn("attestation verified", out + summary)

    def test_a_failed_try_is_tried_again(self):
        """The attestation was stored seconds before: a passing error of the API or the registry is tried again,
        10 and 20 s later, before the job fails."""
        for flaky, sleeps in ((1, ["sleep 10"]), (2, ["sleep 10", "sleep 20"])):
            with self.subTest(failed_tries=flaky):
                self.forget()
                rc, out, summary = self.verify_built(flaky=flaky)
                self.assertEqual(rc, 0, out)
                self.assertEqual(len(self.verified()), flaky + 1, out)
                self.assertEqual(self.calls(), sleeps, out)
                self.assertIn("attestation verified: %s@%s" % (self.NAME, self.DIGEST), summary)

    def test_a_gh_older_than_2_67_gives_no_verdict(self):
        """gh 2.49 to 2.66 could exit 0 for a digest with no attestation of the predicate type asked for
        (CVE-2025-25204): each step refuses such a gh, or one that names no version, before it verifies anything.  Each
        part of the version is read in base 10: bash reads 09 as a bad octal number and 070 as 56."""
        steps = (("the image job", lambda version: self.verify_built(version=version)),
                 ("verify-pins", lambda version: self.verify_pins(self.release(), version=version)))
        for name, run in steps:
            for version, passes in (("2.66.1", False), ("2.49.0", False), ("1.99.0", False), ("dev", False),
                                    ("2.09.0", False), ("2.67.0", True), ("3.0.0", True), ("2.070.0", True)):
                with self.subTest(step=name, gh=version):
                    self.forget()
                    rc, out, _summary = run(version)
                    self.assertEqual(rc, 0 if passes else 1, out)
                    if passes:
                        self.assertNotEqual(self.verified(), [], out)
                    else:
                        self.assertEqual(self.verified(), [], out)
                        self.assertIn("::error::gh 2.67 or newer", out)
                        self.assertIn("CVE-2025-25204", out)

    def release(self, **pins):
        """A release.yaml with the pins PINS, as `pins` changes them; the builder images are not verified."""
        pins = dict(self.PINS, **pins)
        return ("schema: oss-fuzz-theorems/release/1\nimages:\n  checker: %s\n  runner: %s\n  builder:\n"
                "  - ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:%s\ncounts:\n  projects: 1\n"
                % (pins["checker"], pins["runner"], "e" * 64))

    def verify_pins(self, release, refuse=(), version=""):
        """verify-pins' one step that runs a script, in a checkout whose release.yaml is `release`, with the stand-in
        gh of `version` refusing the digests `refuse`: (its exit, its output, its summary)."""
        scripts = [s for s in load("images.yml")["jobs"]["verify-pins"]["steps"] if "run" in s]
        self.assertEqual(len(scripts), 1)
        checkout = os.path.join(self.dir, "checkout")
        os.makedirs(checkout, exist_ok=True)
        with open(os.path.join(checkout, "release.yaml"), "w") as f:
            f.write(release)
        env = {k: {"GH_TOKEN": "t"}[k] for k in scripts[0].get("env", {})}
        env.update(GITHUB_REPOSITORY=REPOSITORY, REFUSE=" ".join(refuse), GH_VERSION=version)
        return self.run_step(scripts[0]["run"], env, cwd=checkout)

    def test_verify_pins_runs_daily_and_by_hand_building_nothing_after_no_other_job_and_reads_only(self):
        job = load("images.yml")["jobs"]["verify-pins"]
        # it answers for the pins whether or not anything was built
        self.assertNotIn("needs", job)
        self.assertEqual(job["permissions"], {"contents": "read", "attestations": "read"})
        # a refused pin is the job's failure: nothing excuses a step's exit or the job's, and the script always runs
        self.assertNotIn("continue-on-error", job)
        for s in job["steps"]:
            self.assertNotIn("continue-on-error", s)
            self.assertNotIn("if", s)
        here = self.HERE
        for repository_id, event, image, runs in ((here, "schedule", "", True),
                                                  (here, "workflow_dispatch", "none", True),
                                                  (here, "workflow_dispatch", "checker", False),
                                                  (here, "workflow_dispatch", "runner", False),
                                                  (here, "workflow_dispatch", "both", False),
                                                  (here, "push", "", False), ("1", "schedule", "", False),
                                                  ("1", "workflow_dispatch", "none", False)):
            with self.subTest(repository_id=repository_id, event=event, image=image):
                scope = {"github": {"repository_id": repository_id, "event_name": event}, "inputs": {"image": image}}
                self.assertIs(helpers.gh_truthy(helpers.gh_value("${{ %s }}" % job["if"], scope)), runs)

    def test_verify_pins_verifies_and_names_each_pin(self):
        rc, out, summary = self.verify_pins(self.release())
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.verified(), [self.command(self.PINS["checker"]), self.command(self.PINS["runner"])])
        self.assertIn("gh version %s" % self.VERSION, out)
        for key, pin in self.PINS.items():
            self.assertIn("images.%s %s: verified" % (key, pin), out)
            self.assertIn("images.%s %s: verified" % (key, pin), summary)

    def test_verify_pins_fails_on_a_refused_pin_and_still_verifies_the_other(self):
        for key, other in (("checker", "runner"), ("runner", "checker")):
            with self.subTest(refused=key):
                self.forget()
                rc, out, summary = self.verify_pins(self.release(), refuse=[self.PINS[key].split("@")[1]])
                self.assertEqual(rc, 1, out)
                self.assertEqual(len(self.verified()), 2, out)
                self.assertIn("::error::images.%s %s: gh attestation verify refused it" % (key, self.PINS[key]), out)
                self.assertIn("images.%s %s: refused" % (key, self.PINS[key]), summary)
                self.assertIn("images.%s %s: verified" % (other, self.PINS[other]), summary)

    def test_verify_pins_fails_on_a_pin_that_is_not_a_digest_of_its_image(self):
        for name, pins in (("a tag", dict(checker="ghcr.io/theorem-labs/oss-fuzz-theorems-checker:latest")),
                           ("another image", dict(runner=self.PINS["checker"])),
                           ("no pin", dict(runner=""))):
            with self.subTest(case=name):
                rc, out, _summary = self.verify_pins(self.release(**pins))
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::release.yaml's images.", out)

    def test_a_hand_run_may_build_nothing(self):
        """-f image=none plans no image, so a run by hand can verify the pins and build nothing."""
        self.assertIn("none", load("images.yml")["on"]["workflow_dispatch"]["inputs"]["image"]["options"])
        plan = next(s for s in load("images.yml")["jobs"]["plan"]["steps"] if s.get("id") == "plan")
        # checker, whose plan reads nothing either, for contrast
        for choice, images in (("none", "[]"), ("checker", '["checker"]')):
            with self.subTest(image=choice):
                if os.path.exists(self.output):
                    os.remove(self.output)
                env = {"EVENT": "workflow_dispatch", "CHOICE": choice, "BEFORE": "", "GH_TOKEN": "t",
                       "GITHUB_REF": "refs/heads/main", "GITHUB_REPOSITORY_OWNER": "theorem-labs"}
                rc, out, _summary = self.run_step(plan["run"], env)
                self.assertEqual(rc, 0, out)
                self.assertEqual(self.outputs().get("images"), images, out)
                self.assertEqual(self.verified(), [], out)

    def run_images(self, event, images, image="", refuse=()):
        """A run of images.yml in this repository on `event` (with -f image=`image` on a run by hand) whose plan named
        `images`, release.yaml pinning PINS, the stand-in gh refusing the digests `refuse`: each leg of the image job
        pushes NEW[its image] and runs the step after the attest step (its other steps taken to pass), verify-pins
        runs where its condition holds, and the images job's step judges their results, with its env as GitHub
        evaluates it.  (its exit, the output of every step run)."""
        self.forget()
        jobs = load("images.yml")["jobs"]
        scope = {"github": {"repository_id": self.HERE, "event_name": event}, "inputs": {"image": image}}
        outs, image_result, pins_result = [], "skipped", "skipped"
        named = json.loads(images)
        if named:
            image_result = "success"
            for key in named:
                rc, out, _summary = self.verify_built(self.IMAGE % key, self.NEW[key], refuse)
                outs.append(out)
                image_result = "failure" if rc else image_result
        pins = jobs.get("verify-pins")
        if pins and helpers.gh_truthy(helpers.gh_value("${{ %s }}" % pins["if"], scope)):
            rc, out, _summary = self.verify_pins(self.release(), refuse)
            outs.append(out)
            pins_result = "failure" if rc else "success"
        scope["needs"] = {"plan": {"result": "success", "outputs": {"images": images}},
                          "image": {"result": image_result}, "verify-pins": {"result": pins_result}}
        collect = jobs["images"]["steps"][0]
        env = {k: helpers.gh_text(helpers.gh_value(v, scope)) for k, v in collect["env"].items()}
        rc, out, _summary = self.run_step(collect["run"], env)
        outs.append(out)
        return rc, "\n".join(outs)

    def test_a_hand_run_that_builds_is_green_when_its_new_images_verify_whatever_the_pins(self):
        """An image rebuilt by hand for its own verdict while release.yaml's pins have no attestation: the run is
        judged by the images it built, and the pins are not asked for."""
        for image, images in (("checker", '["checker"]'), ("runner", '["runner"]'), ("both", '["checker","runner"]')):
            with self.subTest(image=image):
                rc, out = self.run_images("workflow_dispatch", images, image=image, refuse=self.PINNED)
                self.assertEqual(rc, 0, out)
                self.assertEqual([a[2] for a in self.verified()],
                                 ["oci://%s@%s" % (self.IMAGE % k, self.NEW[k]) for k in json.loads(images)], out)

    def test_a_daily_run_whose_pins_are_refused_is_red(self):
        """Until release.yaml pins digests this workflow attested, every daily run is red, built or not."""
        for images in ("[]", '["runner"]'):
            with self.subTest(images=images):
                rc, out = self.run_images("schedule", images, refuse=self.PINNED)
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::release.yaml's pins were not verified", out)
        rc, out = self.run_images("schedule", "[]")
        self.assertEqual(rc, 0, out)

    def test_a_hand_run_that_builds_nothing_is_red_when_the_pins_are_refused(self):
        rc, out = self.run_images("workflow_dispatch", "[]", image="none", refuse=self.PINNED)
        self.assertEqual(rc, 1, out)
        self.assertIn("::error::release.yaml's pins were not verified", out)
        rc, out = self.run_images("workflow_dispatch", "[]", image="none")
        self.assertEqual(rc, 0, out)

    def test_a_hand_run_whose_new_image_is_refused_is_red(self):
        rc, out = self.run_images("workflow_dispatch", '["checker"]', image="checker", refuse=[self.NEW["checker"]])
        self.assertEqual(rc, 1, out)
        self.assertIn("::error::gh attestation verify refused %s@%s" % (self.IMAGE % "checker", self.NEW["checker"]),
                      out)
        self.assertIn("::error::an image the plan named was not built, pushed and verified", out)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class PlanToolsTest(unittest.TestCase):
    """The check jobs run the tools the plan job named, so that a plan and the checks it schedules are one decision:
    the base's, except for the change the base pins, where the plan step also measured that the base's tools read no
    fuzz target in this tree and the change's own read some (a release line's join, which brings its tools and the
    facts only they can read)."""

    def test_the_plan_job_says_which_tools_it_used(self):
        jobs = load("pr.yml")["jobs"]
        self.assertEqual(jobs["plan"]["outputs"]["tools"], "${{ steps.plan.outputs.tools }}")
        text = step(jobs["plan"], "plan")["run"]
        self.assertIn('echo "tools=${tools%%/*}" >> "$GITHUB_OUTPUT"', text)
        self.assertIn('echo "tools=base" >> "$GITHUB_OUTPUT"', text)      # no facts yet: nothing is planned
        # the verdict's two plan invocations (before content keys and with them) take those tools.  The prove job's
        # release-kind plan is separate, so a failure in it cannot fail this verdict step.
        self.assertNotIn("PYTHONPATH=base/tools python -m oft", text)
        self.assertEqual(text.count("PYTHONPATH=$tools python -m oft --root head plan"), 2)

    def test_the_drafts_step_reads_the_pins_with_the_tools_the_plan_named(self):
        """The plan job's drafts step lists each group's draft binaries by running `oft fetch --list` through the
        base's action: with the base's tools, or, for the change the base pins, that change's own, which alone can
        read its facts.  The action itself stays the base's."""
        drafts = next(s for s in load("pr.yml")["jobs"]["plan"]["steps"] if s.get("id") == "drafts")
        self.assertEqual(drafts["uses"], "./base/.github/actions/plan-drafts")
        self.assertEqual(drafts["with"]["tools"],
                         "${{ github.workspace }}/${{ steps.plan.outputs.tools }}/tools")

    def test_the_check_job_copies_the_tools_the_plan_named(self):
        jobs = load("pr.yml")["jobs"]
        copy = step(jobs["check"], "the tools, copied out of the tree they check")
        self.assertEqual(copy["run"].strip(),
                         'cp -r -- "${{ needs.plan.outputs.tools }}/tools" "$RUNNER_TEMP/tools"')

    def plan_step(self, kind="release", changed=("tools/oft/lint.py", "projects/zlib/project.yaml"),
                  units=("0", "2148"), probe=(0, 0), pin="right", attributes=None, rc=0, check=None, tree=None,
                  record=RECORD, event="pull_request", digests=False, head_pin="digest: ''\n"):
        """pr.yml's plan step, run as the workflow runs it, over a git checkout of a tree with tools/ and theories/,
        and, as a join's head has it, its own tools/oft/migration-pin.yaml (`head_pin`), which both digests leave out.
        `pin` says what the base pins: `right` the digest of that checkout, `wrong` another digest, `none` an empty
        pin, `short` that checkout's digest one character short, `absent` no pin file, `alien` a file of another
        schema.  `check` and `record` are the pin's `check` and
        `check_of_record` (None: no such key), `tree` its `tree`: `right` the tree digest of that checkout, `wrong`
        another, None no such key.  `units`
        is what each set of tools counts, `probe` the status each count exits with.  Gives its outputs, and the
        PYTHONPATH and arguments of each `oft plan` run it made; the step's output is in self.said, the plan file it
        leaves for the drafts step in self.plan_file, and, with `digests`, the runs of tools/oft/ci/pin-digests.sh HEAD
        in that checkout, at its top and in tools/oft, in self.digests."""
        text = step(load("pr.yml")["jobs"]["plan"], "plan")["run"]
        with tempfile.TemporaryDirectory(prefix="oft-plan-tools-") as d:
            head = os.path.join(d, "head")
            for sub in ("tools", "theories"):
                os.makedirs(os.path.join(head, sub))
                with open(os.path.join(head, sub, "x"), "w") as f:
                    f.write(sub)
            open(os.path.join(head, "release.yaml"), "w").close()
            os.makedirs(os.path.join(head, "tools", "oft"))
            with open(os.path.join(head, "tools", "oft", "migration-pin.yaml"), "w") as f:
                f.write(head_pin)
            env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@x", GIT_COMMITTER_NAME="t",
                       GIT_COMMITTER_EMAIL="t@x")
            for args in (["init", "-q"], ["add", "-A"], ["commit", "-qm", "t"]):
                subprocess.run(["git", "-C", head] + args, check=True, env=env, capture_output=True)

            def but_the_pin(listed):
                return "".join(l for l in listed.splitlines(True)
                               if not l.endswith("\ttools/oft/migration-pin.yaml\n"))
            ls_tools = ["git", "-C", head, "ls-tree", "-r", "HEAD", "--", "tools", "theories"]
            listing = but_the_pin(subprocess.run(ls_tools, check=True, env=env, capture_output=True).stdout.decode())
            attrs = subprocess.run(["git", "-C", head, "check-attr", "--stdin", "--source=HEAD"]
                                   + list(keys.CHECKOUT_ATTRIBUTES), check=True, env=env, capture_output=True,
                                   text=True, input="".join(l.split("\t")[1] + "\n" for l in listing.splitlines()))
            digest = hashlib.sha256((listing + attrs.stdout).encode()).hexdigest()
            if attributes is not None:
                # the same blobs, checked out as other bytes: the pin above is of the tree without this file
                with open(os.path.join(head, ".gitattributes"), "w") as f:
                    f.write(attributes)
                for args in (["add", "-A"], ["commit", "-qm", "attributes"]):
                    subprocess.run(["git", "-C", head] + args, check=True, env=env, capture_output=True)
            # the tree a deferred check's pin names: every file of HEAD, the pin file left out
            whole = subprocess.run(["git", "-C", head, "ls-tree", "-r", "HEAD"], check=True, env=env,
                                   capture_output=True).stdout.decode()
            self.assertIn("\ttools/oft/migration-pin.yaml\n", whole)
            tree_digest = hashlib.sha256(but_the_pin(whole).encode()).hexdigest()
            other = "a" * 64
            pinned = {"right": digest, "wrong": other, "none": "", "short": digest[:63]}.get(pin)
            if pinned is not None or pin == "alien":
                os.makedirs(os.path.join(d, "base", "tools", "oft"))
                body = {"schema": "oss-fuzz-theorems/migration-pin/1", "digest": pinned or ""}
                if tree is not None:
                    body["tree"] = {"right": tree_digest, "wrong": "e" * 64}[tree]
                if check is not None:
                    body["check"] = check
                    if record is not None:
                        body["check_of_record"] = record
                if pin == "alien":
                    # everything else as it would be, so that the schema alone refuses the pin
                    body = dict(body, schema="something/else/1", digest=digest)
                with open(os.path.join(d, "base", "tools", "oft", "migration-pin.yaml"), "w") as f:
                    f.write(yamlio.dump(body))
            with open(os.path.join(d, "changed.txt"), "w") as f:
                f.write("".join(p + "\n" for p in changed))
            os.mkdir(os.path.join(d, "bin"))
            with open(os.path.join(d, "bin", "python"), "w") as f:
                # the pin reader runs the real python; a count comes from `units`; `plan --help` says the tools have
                # content keys; a plan run is recorded and gives a plan of one harness and no job
                f.write("#!/bin/sh\ncase \"$PYTHONPATH\" in base/tools) n=%s; p=%d ;; *) n=%s; p=%d ;; esac\n"
                        'case "$1" in -) exec %s "$@" ;; esac\n'
                        'case "$*" in *count-units.py*) echo "$n"; exit "$p" ;; esac\n'
                        'case "$*" in *"plan --help"*) echo "  --store  --tools  --pr-kind"; exit 0 ;; esac\n'
                        'printf "%%s\\n" "$PYTHONPATH $*" >> "%s"\n'
                        'echo \'{"all": false, "units": ["zlib/checksum_fuzzer"], "check_units": [], "parts": [],'
                        ' "jobs": []}\'\n'
                        % (units[0], probe[0], units[1], probe[1], sys.executable, os.path.join(d, "runs")))
            os.chmod(os.path.join(d, "bin", "python"), 0o755)
            env = dict(os.environ, PATH=os.path.join(d, "bin") + os.pathsep + os.environ["PATH"], RUNNER_TEMP=d,
                       GITHUB_WORKSPACE=d, GITHUB_OUTPUT=os.path.join(d, "output"),
                       GITHUB_STEP_SUMMARY=os.path.join(d, "summary.md"), KIND=kind, BASE="b" * 40, ROUTED="true",
                       GITHUB_EVENT_NAME=event)
            done = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", text], cwd=d, env=env,
                                  capture_output=True, text=True)
            self.said = done.stdout + done.stderr
            self.assertEqual(done.returncode, rc, self.said)
            if digests:
                # at the top of the clone and below it
                self.digests = [subprocess.run(["bash", PIN_DIGESTS, "HEAD"], cwd=where, capture_output=True,
                                               text=True, env=dict(env, HOME=d))
                                for where in (head, os.path.join(head, "tools", "oft"))]
            with open(os.path.join(d, "plan.json")) if os.path.exists(os.path.join(d, "plan.json")) else \
                    open(os.devnull) as f:
                self.plan_file = f.read()
            if rc:
                return self.said, []
            with open(os.path.join(d, "output")) as f:
                out = dict(line.rstrip("\n").split("=", 1) for line in f)
            if os.path.exists(os.path.join(d, "summary.md")):
                with open(os.path.join(d, "summary.md")) as f:
                    self.said += f.read()
            runs = []
            if os.path.exists(os.path.join(d, "runs")):
                with open(os.path.join(d, "runs")) as f:
                    runs = f.read().splitlines()
            return out, [r for r in runs if "--max-jobs" in r]

    def test_the_change_the_base_pins_and_whose_facts_the_base_s_tools_cannot_read(self):
        """The base pins this change's tools and theories by their digest, its own tools read no proof in this tree,
        and the
        change's own read some: the change's tools plan it, with no base, so every part is keyed by them and
        checked (test_keys.Plan's test_with_no_base_every_part_without_a_recorded_pass_is_checked says what a plan
        with no base checks).  A base would say only what the old tools read of this tree, which is nothing."""
        out, runs = self.plan_step()
        self.assertEqual(out["tools"], "head")
        self.assertEqual(len(runs), 1)
        self.assertTrue(runs[0].startswith("head/tools "), runs[0])
        self.assertNotIn("--base", runs[0])
        self.assertIn("--pr-kind release", runs[0])

    def test_a_checkout_attribute_moves_the_digest(self):
        """A .gitattributes outside tools/ and theories/ alters the bytes git checks those files out as, without
        changing a blob: the pin covers the attributes too, so such a tree is not the pinned one."""
        out, runs = self.plan_step(attributes="tools/** text eol=crlf\n")
        self.assertEqual(out["tools"], "base")
        self.assertIn("--base", runs[0])

    def test_a_change_the_base_does_not_pin_is_judged_by_the_base_s_tools(self):
        """The pin is the authority, and only the base carries it: without it, or for another tree, or for one of
        the two directories only, the base's tools plan and key the change, however its own tools read the tree.
        A digest that is not 64 hexadecimal characters names no tools either: `pinned` reads it as empty, as
        `pinned_digest` did, since nothing else names a tree of tools/ and theories/."""
        for why, pin in (("no pin file", "absent"), ("an empty pin", "none"), ("another tree", "wrong"),
                         ("another schema", "alien"), ("a digest of 63 characters", "short")):
            with self.subTest(why=why):
                out, runs = self.plan_step(pin=pin)
                self.assertEqual(out["tools"], "base")
                self.assertEqual(len(runs), 1)
                self.assertTrue(runs[0].startswith("base/tools "), runs[0])
                self.assertIn("--base", runs[0])

    def test_the_verdict_plan_keeps_its_kind_and_has_no_report_units(self):
        """The prove job now runs its release-kind plan itself.  This verdict plan keeps the workflow's kind and only
        writes the outputs the verdict consumes."""
        for kind in ("maintainer", "contributor", "release"):
            for pin, tools in (("absent", "base"), ("right", "head")):
                with self.subTest(kind=kind, pin=pin):
                    out, runs = self.plan_step(kind=kind, pin=pin)
                    self.assertEqual(out["tools"], tools)
                    self.assertEqual(len(runs), 1)
                    self.assertTrue(runs[0].startswith("%s/tools " % tools), runs[0])
                    self.assertIn("--pr-kind %s" % kind, runs[0])
                    self.assertNotIn("unit_list", out)

    def test_the_base_s_tools_keep_the_plan_wherever_they_read_the_facts(self):
        """Even for the pinned change: the base's tools read the facts, so they plan it and key it, and the check
        jobs run them."""
        out, runs = self.plan_step(units=("2148", "2148"))
        self.assertEqual(out["tools"], "base")
        self.assertTrue(runs[0].startswith("base/tools "), runs[0])
        self.assertIn("--base", runs[0])

    def test_a_tree_no_tools_read_fails_instead_of_planning_nothing(self):
        """The pinned change, where neither set of tools read a proof or the change's own gave no count: a
        plan from here would be empty and the run would report that it checked everything it planned, so the step
        fails and says so."""
        for why, kw in (("neither reads the facts", dict(units=("0", "0"))),
                        ("a count that is not a number", dict(units=("0", "many"))),
                        ("a number from a probe that failed", dict(units=("0", "2148"), probe=(0, 1)))):
            with self.subTest(why=why):
                out, _ = self.plan_step(rc=1, **kw)
                self.assertIn("no tools read a proof in this tree", out)

    def test_a_count_the_base_s_tools_could_not_give_fails(self):
        """A probe that fails or prints anything but one number read nothing: the step says so, rather than plan
        from a reading that did not happen."""
        for why, kw in (("a word", dict(units=("many", "2148"))),
                        ("a number from a probe that failed", dict(units=("12", "2148"), probe=(1, 0)))):
            with self.subTest(why=why):
                out, _ = self.plan_step(rc=1, **kw)
                self.assertIn("the base's tools could not count the fuzz targets", out)

    # A stand-in for main's tools as the plan step's count meets them, for the four trees below: main's facts.load
    # reads a project only when its project.yaml has main's shape (a recipe-built project's assets.bin.recipe is not in
    # main's schema; a port-built project, as the six enrolled Pau projects are, passes), every fuzz target of such a
    # project from its harness.yaml, and a statement's proof only in the old layout, proofs/<p>/<h>/<s>/proof.yaml.
    # Measured on the joined tree (bf87ea4): main's tools load 29 fuzz targets, all of port-built projects, and 0 with a
    # proof.
    OLD_TOOLS = '''
import os
import yaml


class _Statement:
    def __init__(self, proof):
        self.proof = proof


class _Harness:
    def __init__(self, statements):
        self.statements = statements


class _Tree:
    def __init__(self, harnesses):
        self._harnesses = harnesses

    def harnesses(self):
        return iter(self._harnesses)


def load(root):
    out = []
    projects = os.path.join(root, "projects")
    for p in sorted(os.listdir(projects)):
        with open(os.path.join(projects, p, "project.yaml")) as f:
            project = yaml.safe_load(f)
        if "recipe" in ((project.get("assets") or {}).get("bin") or {}):
            continue
        for h in sorted(os.listdir(os.path.join(projects, p))):
            path = os.path.join(projects, p, h, "harness.yaml")
            if not os.path.isfile(path):
                continue
            with open(path) as f:
                names = (yaml.safe_load(f).get("statements") or {})
            proved = {s: os.path.isfile(os.path.join(root, "proofs", p, h, s, "proof.yaml")) for s in names}
            out.append(_Harness({s: _Statement(True if proved[s] else None) for s in names}))
    return _Tree(out)
'''

    def count_program(self):
        """The plan step's count-units.py, as it writes it."""
        text = step(load("pr.yml")["jobs"]["plan"], "plan")["run"]
        m = re.search(r"cat > \"\$RUNNER_TEMP/count-units\.py\" <<'PY'\n(.*?)\n *PY\n", text, re.S)
        self.assertIsNotNone(m)
        return textwrap.dedent(m.group(1)) + "\n"

    def counts(self, root):
        """Over the tree at root: (the fuzz targets the main stand-in loads, then the step's own count-units.py by the
        main stand-in and by these tools)."""
        program = self.count_program()
        loaded = 'from oft import facts\nprint(sum(1 for _ in facts.load("head").harnesses()))\n'
        got = []
        with tempfile.TemporaryDirectory() as d:
            os.makedirs(os.path.join(d, "old", "oft"))
            open(os.path.join(d, "old", "oft", "__init__.py"), "w").close()
            with open(os.path.join(d, "old", "oft", "facts.py"), "w") as f:
                f.write(self.OLD_TOOLS)
            os.symlink(root, os.path.join(d, "head"))
            for text, tools in ((loaded, "old"), (program, "old"), (program, os.path.join(REPO, "tools"))):
                with open(os.path.join(d, "count.py"), "w") as f:
                    f.write(text)
                r = subprocess.run([sys.executable, "count.py"], cwd=d, capture_output=True, text=True,
                                   env=dict(os.environ, PYTHONPATH=os.path.join(d, tools), PYTHONDONTWRITEBYTECODE="1"))
                self.assertEqual(r.returncode, 0, r.stderr)
                got.append(r.stdout.strip())
        return tuple(got)

    @staticmethod
    def prove(t, sid="zlib/checksum_fuzzer/plain_halts"):
        st = next(s for s in facts.load(t.root).statements() if s.id == sid)
        t.put_yaml("proofs/%s/proof.yaml" % sid, {"schema": "oss-fuzz-theorems/proof/1", "proves": sid,
                                                  "fingerprint": st.fingerprint})
        t.write("proofs/%s/Proof.v" % sid, "Theorem holds : True. Proof. exact I. Qed.\n")

    def test_the_count_is_of_fuzz_targets_with_a_proof(self):
        """What the pin needs the base's tools to read as empty is the proofs, not the fuzz targets (RevJoinB2 delta
        3 F1): after the per-project layout move, main's tools still load the fuzz targets of a project whose
        project.yaml and harness.yaml have their shape, and read none of their proofs.  The step's own count over four
        trees, each fed to the step: an old-layout tree (the base reads its proof: its tools judge it); a per-project
        tree (the base reads nothing: the pin applies); a per-project tree whose fuzz targets the base reads and none of
        whose proofs (the joined tree's case: the pin applies); and a per-project tree with no proof, which the
        change's own tools read as empty too (refused)."""
        cases = []
        with helpers.tree() as t:      # old layout, zlib port-built (read by main's shape), one proof
            helpers.port_built(t, "zlib")
            self.prove(t)
            cases.append(("an old-layout tree", self.counts(t.root), ("2", "1", "1"), "base"))
        with helpers.tree() as t:      # per-project, every project recipe-built (main reads none), one proof
            self.prove(t)
            self.assertEqual(port.port_worktree(t.root, out=io.StringIO()), 0)
            cases.append(("a per-project tree", self.counts(t.root), ("0", "0", "1"), "head"))
        with helpers.tree() as t:      # per-project, zlib port-built: main reads its 2 fuzz targets, not its proof
            helpers.port_built(t, "zlib")
            self.prove(t)
            self.assertEqual(port.port_worktree(t.root, out=io.StringIO()), 0)
            cases.append(("fuzz targets the base reads, and none of their proofs", self.counts(t.root),
                          ("2", "0", "1"), "head"))
        with helpers.tree() as t:      # per-project, no proof at all
            helpers.port_built(t, "zlib")
            self.assertEqual(port.port_worktree(t.root, out=io.StringIO()), 0)
            cases.append(("a change whose own tools read no proof", self.counts(t.root), ("2", "0", "0"), None))
        for why, got, want, tools in cases:
            with self.subTest(case=why):
                self.assertEqual(got, want)
                if tools is None:
                    out, _ = self.plan_step(rc=1, units=got[1:])
                    self.assertIn("no tools read a proof in this tree", out)
                else:
                    out, _ = self.plan_step(units=got[1:])
                    self.assertEqual(out["tools"], tools)

    # The change the base pins with `check: deferred` (plan D4): its parts are planned, and no check job runs here,
    # since the check of record the pin names checks them; only for the tree the pin names.

    def test_the_pinned_tree_with_a_deferred_check_plans_no_check_job(self):
        for event in ("pull_request", "merge_group"):
            with self.subTest(event=event):
                out, runs = self.plan_step(check="deferred", tree="right", event=event)
                self.assertEqual((out["tools"], out["deferred"], out["check_of_record"]), ("head", "true", RECORD))
                self.assertGreater(int(out["units"]), 0)
                self.assertEqual(len(runs), 1)
                self.assertTrue(runs[0].startswith("head/tools "), runs[0])
                self.assertIn("no part is checked here", self.said)
                self.assertIn("The check of record: " + RECORD, self.said)
                self.assertEqual(self.plan_file, "")    # the drafts step makes plan=[] and draft_legs=[] of it

    def test_the_deferred_plan_leaves_the_drafts_step_no_plan(self):
        """The drafts step (the base's action) writes the plan job's `plan` and `draft_legs`: a deferred plan leaves
        it an empty plan file, from which it writes plan=[] and draft_legs=[] (the action's own `if [ ! -s ]`)."""
        text = step(load("pr.yml")["jobs"]["plan"], "plan")["run"]
        self.assertIn(': > "$RUNNER_TEMP/plan.json"', text)
        action = load_action("plan-drafts")
        self.assertIn('if [ ! -s "$PLAN" ]; then\n  { echo \'plan=[]\'; echo \'draft_legs=[]\'; }',
                      action["runs"]["steps"][0]["run"])

    def test_a_deferred_pin_for_another_tree_fails_the_plan(self):
        """Any commit merged into the base after the pin, or any other change with the same tools: the tree differs,
        and the step fails before a check job is planned."""
        for tree in ("wrong", None):
            with self.subTest(tree=tree):
                out, runs = self.plan_step(check="deferred", tree=tree, rc=1)
                self.assertIn("for a deferred check, and this tree is", out)
                self.assertEqual(runs, [])

    def test_a_deferred_pin_that_names_no_check_of_record_fails_the_plan(self):
        for record in (None, ""):
            with self.subTest(record=record):
                out, _ = self.plan_step(check="deferred", tree="right", record=record, rc=1)
                self.assertIn("names no check of record", out)

    def test_a_pin_whose_check_is_another_word_fails_the_plan(self):
        for check in ("Deferred", "deferred ", " deferred", "skip", "true"):
            with self.subTest(check=check):
                out, _ = self.plan_step(check=check, tree="right", rc=1)
                self.assertIn("neither deferred nor empty", out)

    def test_the_pinned_tree_defers_with_the_base_s_tools_too(self):
        """The W2 train: the base's tools read its proofs, so they judge it, and a check of every part
        of it still does not fit in a queue group.  The pin names the tree alone (`digest` empty), and the plan
        defers the check jobs to the check of record while the base's tools plan every part."""
        out, runs = self.plan_step(check="deferred", tree="right", pin="none", units=("89", "89"))
        self.assertEqual((out["tools"], out["deferred"], out["check_of_record"]), ("base", "true", RECORD))
        self.assertGreater(int(out["units"]), 0)
        self.assertIn("--base", runs[0])
        self.assertTrue(runs[0].startswith("base/tools "), runs[0])
        self.assertIn("no part is checked here", self.said)
        self.assertEqual(self.plan_file, "")    # the drafts step makes plan=[] and draft_legs=[] of it

    def test_another_tree_the_base_s_tools_read_is_checked_here(self):
        """The base's tools read the tree and the pin names another one (a pull request into main after the train,
        before the cleanup pull request empties the pin): it is planned and checked as today, and nothing fails."""
        out, runs = self.plan_step(check="deferred", tree="wrong", units=("3", "2148"))
        self.assertEqual((out["tools"], out["deferred"]), ("base", "false"))
        self.assertNotIn("check_of_record", out)
        self.assertIn("the base pins another tree for a deferred check", self.said)
        self.assertIn("--base", runs[0])
        self.assertIn('"units": ["zlib/checksum_fuzzer"]', self.plan_file)

    def test_a_pin_without_a_deferred_check_plans_every_part_as_before(self):
        for kw in (dict(), dict(check="", tree="right")):
            with self.subTest(**kw):
                out, runs = self.plan_step(**kw)
                self.assertEqual((out["tools"], out["deferred"]), ("head", "false"))
                self.assertNotIn("no part is checked here", self.said)
                self.assertIn('"units": ["zlib/checksum_fuzzer"]', self.plan_file)

    def test_the_push_of_the_pinned_tree_defers_too(self):
        """The push of the join's merge commit: main before the push still pins it (the cleanup pull request comes
        after), and the pushed commit's tree is the group's."""
        out, _ = self.plan_step(check="deferred", tree="right", event="push")
        self.assertEqual(out["deferred"], "true")
        self.assertEqual(self.plan_file, "")

    def test_a_tree_the_pin_does_not_name_is_never_deferred(self):
        """The `tree` says which change is deferred, and only that one: a base with no pin file, a pin of another
        schema, and a pin whose tree is another are all checked here."""
        for pin in ("none", "absent", "alien"):
            with self.subTest(pin=pin):
                out, _ = self.plan_step(pin=pin, check="deferred", tree="wrong", units=("3", "2148"))
                self.assertEqual((out["tools"], out["deferred"]), ("base", "false"))
        for pin in ("absent", "alien"):
            with self.subTest(pin=pin, tree="right"):
                out, _ = self.plan_step(pin=pin, check="deferred", tree="right", units=("3", "2148"))
                self.assertEqual((out["tools"], out["deferred"]), ("base", "false"))

    def test_pin_digests_prints_what_the_plan_step_compares(self):
        """tools/oft/ci/pin-digests.sh, run in a clone (at its top or below it), prints the plan step's own two
        digests of that commit, so the re-pin pull request can name them before the join pull request's run computes
        them.  Neither digest reads the pin file the tree itself holds: a head whose pin differs has the same two."""
        seen = []
        for head_pin in ("digest: ''\n", "digest: '%s'\ncheck: deferred\n" % ("a" * 64)):
            with self.subTest(head_pin=head_pin):
                self.plan_step(check="deferred", tree="right", digests=True, head_pin=head_pin)
                digest = re.search(r"this change has ([0-9a-f]{64})$", self.said, re.M).group(1)
                tree = re.search(r"this tree is ([0-9a-f]{64})$", self.said, re.M).group(1)
                for run in self.digests:
                    self.assertEqual((run.returncode, run.stdout), (0, "digest %s\ntree %s\n" % (digest, tree)),
                                     run.stderr)
                seen.append((digest, tree))
        self.assertEqual(seen[0], seen[1])
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(subprocess.run(["bash", PIN_DIGESTS], cwd=d, capture_output=True).returncode, 2)

    def test_the_deferral_reaches_the_jobs_and_required(self):
        """The plan step's two answers are the elsewhere step's to read; that step gives the one pair check,
        fetch-drafts and required read (QueueVmEvidenceTest.test_the_answer_reaches_the_check_job_and_required)."""
        jobs = load("pr.yml")["jobs"]
        elsewhere = step(jobs["plan"], "the parts a check of record outside this run checked")
        self.assertEqual((elsewhere["env"]["DEFERRED"], elsewhere["env"]["CHECK_OF_RECORD"]),
                         ("${{ steps.plan.outputs.deferred }}", "${{ steps.plan.outputs.check_of_record }}"))
        self.assertEqual(jobs["plan"]["outputs"]["checked_elsewhere"],
                         "${{ steps.elsewhere.outputs.checked_elsewhere }}")
        for job in ("check", "fetch-drafts"):
            self.assertIn("&& needs.plan.outputs.checked_elsewhere != 'true'",
                          " ".join(jobs[job]["if"].split()), job)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
@unittest.skipUnless(shutil.which("jq"), "jq is not installed")
class QueueVmEvidenceTest(StandIn):
    """The plan job's elsewhere step: a merge queue group whose change can move no verdict and whose every pull
    request carries merge-pr.sh's VM evidence comment for its own head runs no check job (the OSS Verify lead,
    2026-11-01), and so does a pull request's own run, by the same rules (pr_run).  The step is run as the workflow
    runs it, with the stand-in gh and the repository's own tools as the base's."""

    BASE = "f" * 40
    GROUP = "b" * 40
    # the App as GraphQL names it: a Bot whose login carries no `[bot]`
    APP = ("Bot", "sjawhar-agent")
    PATHS = ["projects/zlib/checksum_fuzzer/proofs/sum/Proof.v", "proofs/curl/fuzz_url/url/Proof.v",
             "CHANGELOG.md", "tools/oft/lint-exceptions.yaml"]
    # the units of the group, each with the pull request that brought it
    UNITS = (("zlib/checksum_fuzzer", 563), ("curl/fuzz_url", 565))
    # ruling 16's pair, the tools' own (plan.ONLY_CHECKER): main's checker at 87c4b944683b and at dd31239f2de
    OLD_CHECKER, NEW_CHECKER = plan.ONLY_CHECKER

    @staticmethod
    def head_of(number):
        """A pull request's head sha, 40 hex characters as GitHub gives it."""
        return ("%d" % number * 20)[:40]

    def comp(self, unit, **moved):
        """A build part's components, as `oft plan` writes them, with `moved` naming what differs: `proofs` for the
        unit's own proofs folder (every proof library its check may read is in it: tools/oft/unitpaths.py), and
        `theories` for theories/."""
        out = {"version": keys.VERSION, "unit": unit, "part": "build", "checker": self.NEW_CHECKER,
               "project": "p0", "image": "i0", "harness": "h0", "proofs": "pf0", "theories": "th0",
               "allowed-axioms": "ax0", "dune-path": "dpath0", "dune-project": "dp0", "rocqchk": "no"}
        out.update(moved)
        return out

    def train(self, unit, **moved):
        """The components the train's own tools write for a unit it does not touch: the checker and theories ids
        ruling 20 pins, over comp's."""
        return self.comp(unit, **dict({"checker": plan.AFTER_THE_TRAIN_CHECKER,
                                       "theories": plan.AFTER_THE_TRAIN_THEORIES}, **moved))

    @staticmethod
    def before_the_train(comp, checker=None):
        """The same components as they stood before the W2 train: keys.VERSION 2, no dune-path component, main's
        checker id (or `checker`, for a check of record that ran under main's older one) and main's theories id
        (ruling 20).  Written out here rather than called from plan, so the test measures the mapping and not the
        code under it."""
        was = {"version": "2", "checker": checker or plan.ONLY_CHECKER[1],
               "theories": plan.BEFORE_THE_TRAIN_THEORIES}
        return {k: was.get(k, v) for k, v in comp.items() if k != "dune-path"}

    @staticmethod
    def key_of(comp):
        """The part's key of those components, as keys.py digests them."""
        return keys.digest("%s=%s" % kv for kv in comp.items())

    def setUp(self):
        super().setUp()
        os.makedirs(os.path.join(self.dir, "base"))
        os.symlink(os.path.join(REPO, "tools"), os.path.join(self.dir, "base", "tools"))
        # the runner's `python`, which the step runs; this box may have none on PATH
        shim = os.path.join(self.dir, "bin", "python")
        with open(shim, "w") as f:
            f.write('#!/bin/sh\nexec %s "$@"\n' % shlex.quote(sys.executable))
        os.chmod(shim, 0o755)
        self.runs = 0
        # head/, as the plan job checks out a pull request: the merge commit GitHub builds, its first parent the
        # base branch and its second the pull request's head, which PR_HEAD is
        head = os.path.join(self.dir, "head")
        git = ["git", "-C", head, "-c", "user.name=t", "-c", "user.email=t@x", "-c", "commit.gpgsign=false"]
        subprocess.run(["git", "init", "-q", "-b", "main", head], check=True)
        for args in (["commit", "-q", "--allow-empty", "-m", "base"], ["checkout", "-q", "-b", "pr"],
                     ["commit", "-q", "--allow-empty", "-m", "the pull request"], ["checkout", "-q", "main"],
                     ["commit", "-q", "--allow-empty", "-m", "main moved"],
                     ["merge", "-q", "--no-ff", "-m", "merge", "pr"]):
            subprocess.run(git + args, check=True, capture_output=True)
        self.PR_HEAD, self.MERGE_BASE = (subprocess.run(git + ["rev-parse", "HEAD^2", "HEAD^1"], check=True,
                                                        capture_output=True, text=True).stdout.split())

    def api_file(self, endpoint, body):
        with open(os.path.join(self.api, endpoint.replace("/", "_") + ".json"), "w") as f:
            json.dump(body, f)

    def comment(self, head, mode="pvc", by="sjawhar-agent[bot]", kind="Bot", first=True, unit_keys=(), node="C_1"):
        """merge-pr.sh's evidence comment: its marker as the first line, and a key line per unit after it."""
        marker = "<!-- vm-evidence head=%s mode=%s -->" % (head, mode)
        body = marker + "\nthe VM run" if first else "a word\n" + marker
        body += "".join("\n<!-- vm-evidence-key unit=%s key=%s -->" % (u, k) for u, k in unit_keys)
        return {"user": {"login": by, "type": kind}, "body": body, "node_id": node,
                "html_url": "https://github.com/%s/pull/1#issuecomment-1" % REPOSITORY}

    @staticmethod
    def edits(*editors, author=("Bot", "sjawhar-agent"), total=None, nodes=None):
        """GitHub's GraphQL answer for the comment's author and its userContentEdits, as it gives them: an App is a
        `Bot` whose login carries no `[bot]`.  Each editor is a (__typename, login) pair, or None for an editor
        GitHub no longer names; `total` is totalCount when it is not the number of editors, and `nodes` replaces the
        node list outright."""
        edits = [{"editor": None if e is None else {"__typename": e[0], "login": e[1]}} for e in editors]
        return {"data": {"node": {
            "author": None if author is None else {"__typename": author[0], "login": author[1]},
            "userContentEdits": {"totalCount": len(edits) if total is None else total,
                                 "nodes": edits if nodes is None else nodes}}}}

    def group(self, paths=None, commits=(("a proof (#563)", 563), ("another proof (#565)", 565)), last=565,
              heads=None, comments=None, pages=None, total=None, event="merge_group", routed="true", ref=None,
              planned=None, recorded=None, parts=None, plan=True, edits=None, deferred="false", record="",
              fails=False, pr="", pr_head="", hold="none"):
        """The step, over a group of `commits` (each a first line and the pull request it names), with `paths` as the
        group's diff from its base.  `heads` gives a pull request's head sha (the default is its own), `comments` its
        comments (the default is merge-pr.sh's marker for that head, with a key line per unit of UNITS), `pages` a
        second page of them; None for either of the first two leaves that call failing.  `planned` and `recorded`
        give a unit's components at this group head and at its check of record (the default of each is comp(unit); a
        recorded None leaves that unit no key line), `parts` the plan's parts outright, `plan=False` leaves the plan
        file empty, and `edits` is GitHub's answer for the comment's editors (the default is none).  `deferred` and
        `record` are the plan step's own answers, for the deferred check this step answers first.  `pr`, `pr_head`
        and `hold` are a pull request's run's number, head and hold.  `fails` says the step is expected to fail,
        which it does for a key that differs from the evidence's."""
        for name in os.listdir(self.api):   # only what this run answers, so one run leaves the next none of it
            os.remove(os.path.join(self.api, name))
        with open(os.path.join(self.dir, "changed.txt"), "w") as f:
            f.write("".join(p + "\n" for p in (self.PATHS if paths is None else paths)))
        self.api_file("graphql", self.edits() if edits is None else edits)
        here = {u: self.comp(u) for u, _n in self.UNITS}
        here.update(planned or {})
        was = dict(here)
        was.update(recorded or {})
        if parts is None:
            parts = [{"unit": u, "part": "build", "key": self.key_of(here[u]), "check": True,
                      "why": "changed: proofs", "components": here[u]} for u, _n in self.UNITS]
        with open(os.path.join(self.dir, "plan.json"), "w") as f:
            if plan:
                json.dump({"all": True, "units": [p["unit"] for p in parts],
                           "check_units": [p["unit"] for p in parts if p["part"] == "build"],
                           "parts": parts, "jobs": []}, f)
        lines = {}
        for unit, number in self.UNITS:
            if was.get(unit) is not None:
                lines.setdefault(number, []).append((unit, self.key_of(was[unit])))
        self.api_file("repos/%s/compare/%s...%s" % (REPOSITORY, self.BASE, self.GROUP),
                      {"total_commits": len(commits) if total is None else total,
                       "commits": [{"commit": {"message": m + "\n\nbody"}} for m, _ in commits]})
        heads = {n: self.head_of(n) for _m, n in commits} if heads is None else heads
        for number, head in heads.items():
            self.api_file("repos/%s/pulls/%d" % (REPOSITORY, number), {"head": {"sha": head}})
            said = self.comment(head, unit_keys=lines.get(number, ())) if comments is None else comments.get(number)
            if said is not None:
                self.api_file("repos/%s/issues/%d/comments" % (REPOSITORY, number), [said])
                if pages is not None and pages.get(number) is not None:
                    # a second page of the same list, as gh's --paginate --slurp hands it to one jq program
                    with open(os.path.join(self.api, ("repos/%s/issues/%d/comments" % (REPOSITORY, number))
                                           .replace("/", "_") + ".json.page2"), "w") as f:
                        json.dump([pages[number]], f)
        text = step(load("pr.yml")["jobs"]["plan"], "the parts a check of record outside this run checked")
        self.runs += 1
        script = os.path.join(self.dir, "step-%d.sh" % self.runs)
        with open(script, "w") as f:
            f.write(text["run"])
        summary = os.path.join(self.dir, "summary")
        env = dict(os.environ, PATH=self.path, FAKE_GH=self.api, GITHUB_OUTPUT=self.output,
                   GITHUB_STEP_SUMMARY=summary, RUNNER_TEMP=self.dir, GITHUB_EVENT_NAME=event,
                   GITHUB_REPOSITORY=REPOSITORY, GH_TOKEN="t", BASE=self.BASE, ROUTED=routed,
                   GROUP_HEAD=self.GROUP, VM_EVIDENCE_BY="sjawhar-agent[bot]", DEFERRED=deferred,
                   CHECK_OF_RECORD=record, PR=pr, PR_HEAD=pr_head, HOLD=hold,
                   REF_NAME="gh-readonly-queue/main/pr-%d-%s" % (last, self.BASE) if ref is None else ref)
        done = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", script], cwd=self.dir, env=env,
                              capture_output=True, text=True)
        self.said = done.stdout + done.stderr
        if os.path.exists(summary):
            with open(summary) as f:
                self.said += f.read()
        self.rc = done.returncode
        if fails:
            # a key that differs from the one its pull request's evidence recorded: the entry leaves the queue
            self.assertEqual(done.returncode, 1, self.said)
        elif deferred != "true" or record:
            # it never fails a group otherwise: it answers true or false (a deferral that names no check of record
            # is the one error, and the plan step refuses that one first)
            self.assertEqual(done.returncode, 0, self.said)
        return self.outputs()

    def test_a_group_of_checked_pull_requests_that_moves_no_verdict_runs_no_check(self):
        out = self.group()
        self.assertEqual(out["checked_elsewhere"], "true")
        for number in (563, 565):
            self.assertIn("#%d %s (pvc)" % (number, self.head_of(number)), out["checked_elsewhere_note"])
        self.assertIn("no check job runs here", self.said)
        # as a deferred check does: no check job and no fetch-drafts leg has a group to start
        with open(os.path.join(self.dir, "plan.json")) as f:
            self.assertEqual(f.read(), "")

    def test_a_path_a_check_reads_leaves_the_group_its_checks(self):
        """plan.paths_a_check_reads says which (tools/oft/tests/test_keys.VmEvidence covers it path by path): a
        statement, the checker, the theories, the toolchain, the workflows, release.yaml, dune-project, and the
        parts no evidence line records -- a counterexample, a finding, a projects/<p>/unpatched.yaml."""
        for path in ("projects/zlib/checksum_fuzzer/harness.yaml", "projects/zlib/project.yaml", "tools/oft/check.py",
                     "tools/oft/keys.py", "theories/Premises.v", "toolchain/rocq.lock", ".github/workflows/pr.yml",
                     "release.yaml", "dune-project", "projects/zlib/unpatched.yaml",
                     "projects/zlib/checksum_fuzzer/findings/f/finding.yaml",
                     "counterexamples/curl/fuzz_url/url/x.bin"):
            with self.subTest(path=path):
                out = self.group(paths=self.PATHS + [path])
                self.assertEqual(out["checked_elsewhere"], "false")
                self.assertIn("changed path(s) a check reads", self.said)

    def test_a_file_no_check_opens_is_no_reason_to_check(self):
        """A file of tools/ that keys.not_the_checker names, by the base's own tools: a check opens none of them,
        so none of them is in a key (tools/oft/keys.py, checker)."""
        out = self.group(paths=["proofs/curl/fuzz_url/url/Proof.v", "tools/oft/tests/test_lint.py",
                                "tools/oft/README.md", "tools/enroll/upload", "tools/publish/release.py"])
        self.assertEqual(out["checked_elsewhere"], "true")

    def test_a_units_generated_readme_is_no_reason_to_check(self):
        """A proof re-renders its fuzz target's page and its project's with the statement's new status, and no key
        holds either (keys.py: the statement folder's component drops its README.md, and a project's component is
        its project.yaml and its harness.yaml files alone).  A change to the statement folder's own facts still
        leaves the group its checks."""
        readmes = ["projects/zlib/checksum_fuzzer/proofs/sum/Proof.v", "projects/zlib/checksum_fuzzer/README.md",
                   "projects/zlib/README.md"]
        self.assertEqual(self.group(paths=readmes)["checked_elsewhere"], "true")
        out = self.group(paths=readmes + ["projects/zlib/checksum_fuzzer/harness.yaml"])
        self.assertEqual(out["checked_elsewhere"], "false")
        self.assertIn("projects/zlib/checksum_fuzzer/harness.yaml", self.said)

    def test_a_pull_request_without_the_marker_for_its_head_leaves_the_group_its_checks(self):
        right = {565: self.comment(self.head_of(565))}
        for why, said in (("no comment at all", None),
                          ("a marker for another head", self.comment("9" * 40)),
                          ("another author", self.comment(self.head_of(563), by="someone")),
                          ("a user, not the App", self.comment(self.head_of(563), kind="User")),
                          ("not the first line", self.comment(self.head_of(563), first=False)),
                          ("another mode", self.comment(self.head_of(563), mode="vm"))):
            with self.subTest(case=why):
                out = self.group(comments={**right, 563: said})
                self.assertEqual(out["checked_elsewhere"], "false")
                self.assertIn("pull request 563", self.said)

    def test_the_marker_of_a_merge_record_or_a_wave_counts(self):
        """merge-pr.sh's merge records post mode=checklog, and a multi-unit wave's comment marks the pull request's
        head: the rule is per pull request, not per unit."""
        for mode in ("pvc", "xh", "checklog"):
            with self.subTest(mode=mode):
                out = self.group(comments={n: self.comment(self.head_of(n), mode=mode,
                                                           unit_keys=[(u, self.key_of(self.comp(u)))])
                                           for u, n in self.UNITS})
                self.assertEqual(out["checked_elsewhere"], "true")

    # Nothing a planned part's check reads may have moved between the tree its check of record ran on and this group
    # head.  The part's content key holds all of it -- the unit's own files, every proof library its check may read
    # (they are in its own proofs folder: tools/oft/unitpaths.py), theories/, toolchain/allowed-axioms.txt, its
    # project's rows, the images and the checker -- so the plan's key for the part, computed here with the base's
    # tools over this group head, must be the key the unit's evidence line recorded.

    def test_equal_keys_skip_the_check(self):
        out = self.group()
        self.assertEqual(out["checked_elsewhere"], "true")
        self.assertIn("2 part(s), each with the key its check of record ran on", self.said)
        self.assertNotIn("leaves the merge queue", self.said)

    def ends_at(self, number):
        """The group's commits in the order that leaves `number` its last entry, which the queue branch names: the
        entry a failing group takes out."""
        commits = [("a proof (#%d)" % n, n) for _u, n in self.UNITS if n != number]
        commits.append(("a proof (#%d)" % number, number))
        return dict(commits=tuple(commits), last=number)

    def assert_dequeued(self, number, unit, was, here):
        """The step failed and named the entry the queue drops: its pull request, its unit, the key the evidence
        recorded and the key this group head has, in the error and in the job summary."""
        self.assertEqual(self.rc, 1, self.said)
        said = ("pull request %d's VM evidence recorded key %s for %s and this group's key for it is %s"
                % (number, self.key_of(was), unit, self.key_of(here)))
        self.assertIn("::error::" + said, self.said)
        self.assertIn("this entry leaves the merge queue", self.said)
        with open(os.path.join(self.dir, "summary")) as f:
            self.assertIn("### this entry leaves the merge queue: " + said, f.read())

    def test_a_proof_library_of_another_unit_on_main_takes_the_entry_out_of_the_queue(self):
        """A wave that changes library files reaches a unit's check only through that unit's own proofs folder, and
        the folder's id is the key's `proofs` component: the key differs from the one the pull request's evidence
        recorded, so the entry leaves the queue and no check job is planned (the OSS Verify lead, 2026-11-01:
        such a check held six approved pull requests behind #613 for three hours)."""
        unit, number = self.UNITS[0]
        here, was = self.comp(unit, proofs="pf1"), self.comp(unit)
        self.group(planned={unit: here}, recorded={unit: was}, fails=True, **self.ends_at(number))
        self.assert_dequeued(number, unit, was, here)
        self.assertEqual(self.outputs().get("checked_elsewhere"), None)
        with open(os.path.join(self.dir, "plan.json")) as f:
            self.assertIn('"parts"', f.read())    # the plan is left as it was: no part is skipped here

    def test_a_theories_change_takes_the_entry_out_of_the_queue(self):
        unit, number = self.UNITS[1]
        here, was = self.comp(unit, theories="th1"), self.comp(unit)
        self.group(planned={unit: here}, recorded={unit: was}, fails=True, **self.ends_at(number))
        self.assert_dequeued(number, unit, was, here)

    def test_a_stale_key_of_an_earlier_entry_leaves_this_group_its_checks(self):
        """A group that fails takes out the entry its own branch names and no other (GitHub, "Managing a merge
        queue"), so an earlier entry's stale key must not fail this group: it would take out an entry whose
        evidence is good.  The checks run here, and the group the stale entry's own branch names takes it out."""
        unit, number = self.UNITS[0]
        last = self.UNITS[1][1]
        here, was = self.comp(unit, proofs="pf1"), self.comp(unit)
        out = self.group(planned={unit: here}, recorded={unit: was}, **self.ends_at(last))
        self.assertEqual(out["checked_elsewhere"], "false")
        self.assertIn("pull request %d is not this group's last entry %d" % (number, last), self.said)
        self.assertNotIn("::error::", self.said)

    def test_a_pull_request_with_no_marker_is_checked_here_whatever_its_keys(self):
        """No marker says nothing about a key, so a key that differs is unknown: today's full check, not a
        dequeue."""
        unit, number = self.UNITS[0]
        out = self.group(planned={unit: self.comp(unit, proofs="pf1")}, recorded={unit: self.comp(unit)},
                         comments={number: None, self.UNITS[1][1]: self.comment(self.head_of(self.UNITS[1][1]))})
        self.assertEqual(out["checked_elsewhere"], "false")
        self.assertIn("pull request %d has no VM evidence comment" % number, self.said)
        self.assertNotIn("leaves the merge queue", self.said)

    def test_a_marker_of_another_author_with_a_key_that_differs_is_no_dequeue(self):
        """A comment the App did not write counts for nothing, keys and all: the group keeps its checks, and no
        entry leaves the queue on a stranger's word."""
        unit, number = self.UNITS[0]
        said = self.comment(self.head_of(number), by="someone", kind="User",
                            unit_keys=[(unit, self.key_of(self.comp(unit)))])
        out = self.group(planned={unit: self.comp(unit, proofs="pf1")}, recorded={unit: self.comp(unit)},
                         comments={number: said, self.UNITS[1][1]: self.comment(self.head_of(self.UNITS[1][1]))})
        self.assertEqual(out["checked_elsewhere"], "false")
        self.assertIn("pull request %d has no VM evidence comment" % number, self.said)
        self.assertNotIn("leaves the merge queue", self.said)

    def test_a_unit_without_a_key_line_forces_the_check(self):
        unit = self.UNITS[0][0]
        out = self.group(recorded={unit: None})
        self.assertEqual(out["checked_elsewhere"], "false")
        self.assertIn("%s has no key line" % unit, self.said)

    def test_the_group_s_commits_must_name_one_pull_request_each_and_end_at_the_branch_s(self):
        """A group is one commit per entry: two commits that name one pull request, or a last commit that is not the
        queue branch's, is a group this step cannot read, and the checks run."""
        for why, kw in (("two commits of one pull request",
                         dict(commits=(("a proof (#563)", 563), ("more of it (#563)", 563)), last=563)),
                        ("the branch's is not the last commit's",
                         dict(commits=(("a proof (#565)", 565), ("another proof (#563)", 563)), last=565))):
            with self.subTest(case=why):
                out = self.group(**kw)
                self.assertEqual(out["checked_elsewhere"], "false")

    def test_a_compare_that_is_no_commit_list_answers_false_and_fails_nothing(self):
        self.group()        # one good run, to write the other answers this one keeps
        with open(os.path.join(self.api, "repos_%s_compare_%s...%s.json"
                               % (REPOSITORY.replace("/", "_"), self.BASE, self.GROUP)), "w") as f:
            f.write("not json at all\n")
        text = step(load("pr.yml")["jobs"]["plan"], "the parts a check of record outside this run checked")
        self.runs += 1
        script = os.path.join(self.dir, "step-%d.sh" % self.runs)
        with open(script, "w") as f:
            f.write(text["run"])
        env = dict(os.environ, PATH=self.path, FAKE_GH=self.api, GITHUB_OUTPUT=self.output,
                   GITHUB_STEP_SUMMARY=os.path.join(self.dir, "summary"), RUNNER_TEMP=self.dir,
                   GITHUB_EVENT_NAME="merge_group", GITHUB_REPOSITORY=REPOSITORY, GH_TOKEN="t", BASE=self.BASE,
                   ROUTED="true", GROUP_HEAD=self.GROUP, VM_EVIDENCE_BY="sjawhar-agent[bot]", DEFERRED="false",
                   CHECK_OF_RECORD="",
                   REF_NAME="gh-readonly-queue/main/pr-565-" + self.BASE)
        done = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", script], cwd=self.dir, env=env,
                              capture_output=True, text=True)
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertEqual(self.outputs()["checked_elsewhere"], "false")

    def test_ruling_20_lets_a_marker_of_the_pre_train_formula_stand(self):
        """Until N6 passes: a check of record that ran before the W2 train recorded the key of the same tree under
        the formula the train changed (keys.VERSION 2, no dune-path), so the group skips and the step names ruling
        20.  A changed proof file or statement is a difference like any other: the entry leaves the queue."""
        (unit, number), _ = self.UNITS
        here = self.train(unit)
        out = self.group(planned={unit: here}, recorded={unit: self.before_the_train(here)})
        self.assertEqual(out["checked_elsewhere"], "true")
        self.assertIn("1 by ruling 20's pre-train tree: " + unit, self.said)
        # with ruling 16's checker pair inside it: the check of record ran before the train and under main's
        # older checker
        out = self.group(planned={unit: here},
                         recorded={unit: self.before_the_train(here, checker=self.OLD_CHECKER)})
        self.assertEqual(out["checked_elsewhere"], "true")
        self.assertIn("1 by ruling 20's pre-train tree: " + unit, self.said)
        for why, moved in (("a changed proof file", {"proofs": "pf1"}),
                          ("a changed statement", {"harness": "h1"}),
                          ("a checker id the ruling does not pin", {"checker": "d" * 64})):
            with self.subTest(case=why):
                self.group(planned={unit: self.train(unit, **moved)},
                           recorded={unit: self.before_the_train(here)},
                           fails=True, **self.ends_at(number))
                self.assertIn("leaves the merge queue", self.said)

    def test_ruling_16_lets_the_checker_differ_between_exactly_those_two_ids(self):
        """Until the VM corpus run N6 passes: a key recorded under main's checker at 87c4b944683b and this group's
        under its checker at dd31239f2de differ in that component alone, and the group still skips.  Any other pair
        of checker ids, in either place, is a difference like any other: the entry leaves the queue."""
        (unit, number), (other, other_number) = self.UNITS
        out = self.group(recorded={unit: self.comp(unit, checker=self.OLD_CHECKER)})
        self.assertEqual(out["checked_elsewhere"], "true")
        self.assertIn("1 by ruling 16's checker pair: " + unit, self.said)
        for why, at, here, was in (
                ("another recorded checker", (number, unit), self.comp(unit),
                 self.comp(unit, checker="c" * 64)),
                ("another checker here", (number, unit), self.comp(unit, checker="d" * 64),
                 self.comp(unit, checker=self.OLD_CHECKER)),
                ("the pair and another component", (number, unit), self.comp(unit, theories="th1"),
                 self.comp(unit, checker=self.OLD_CHECKER)),
                ("the pair the other way round", (other_number, other),
                 self.comp(other, checker=self.OLD_CHECKER), self.comp(other, checker=self.NEW_CHECKER))):
            with self.subTest(case=why):
                self.group(planned={at[1]: here}, recorded={at[1]: was}, fails=True, **self.ends_at(at[0]))
                self.assert_dequeued(at[0], at[1], was, here)

    def test_a_part_that_is_not_a_build_forces_the_check(self):
        """An evidence line records a unit's build key and nothing else, so a planned counterexamples or findings
        part is checked here."""
        unit = self.UNITS[0][0]
        parts = [{"unit": unit, "part": "build", "key": self.key_of(self.comp(unit)), "check": True,
                  "why": "changed: proofs", "components": self.comp(unit)},
                 {"unit": unit, "part": "findings", "key": "e" * 64, "check": True, "why": "changed: findings",
                  "components": {"unit": unit, "part": "findings"}}]
        out = self.group(parts=parts)
        self.assertEqual(out["checked_elsewhere"], "false")
        self.assertIn("the plan marks findings to check", self.said)

    def test_a_plan_with_nothing_to_check_leaves_the_run_as_it_was(self):
        for why, kw in (("no part marked", dict(parts=[])), ("no plan file", dict(plan=False))):
            with self.subTest(case=why):
                out = self.group(**kw)
                self.assertEqual(out["checked_elsewhere"], "false")

    def test_every_pull_request_of_the_group_counts_not_only_the_branch_s(self):
        """The queue branch names the group's last entry; the group is cumulative, and each commit names its own, so
        an earlier entry without the marker leaves the whole group its checks."""
        out = self.group(comments={563: self.comment("9" * 40), 565: self.comment(self.head_of(565))})
        self.assertEqual(out["checked_elsewhere"], "false")
        self.assertIn("pull request 563", self.said)

    def test_a_commit_that_names_no_pull_request_leaves_the_group_its_checks(self):
        out = self.group(commits=(("a proof (#563)", 563), ("a commit of no pull request", 565)))
        self.assertEqual(out["checked_elsewhere"], "false")
        self.assertIn("names no pull request", self.said)

    def test_a_group_longer_than_the_page_read_leaves_the_group_its_checks(self):
        out = self.group(total=40)
        self.assertEqual(out["checked_elsewhere"], "false")
        self.assertIn("one page of the compare read", self.said)

    def test_a_read_that_fails_leaves_the_group_its_checks(self):
        """Fail closed: a compare with no commit of its own, a pull request that cannot be read, comments that
        cannot be read."""
        for why, kw in (("no commit of its own", dict(commits=())),
                        ("a pull request", dict(heads={563: self.head_of(563)})),
                        ("the comments", dict(comments={565: self.comment(self.head_of(565))}))):
            with self.subTest(case=why):
                out = self.group(**kw)
                self.assertEqual(out["checked_elsewhere"], "false")

    def test_another_event_or_no_base_leaves_the_change_its_checks(self):
        for why, kw in (("a pull request that names no number", dict(event="pull_request")),
                        ("a push", dict(event="push")),
                        ("no base to compare with", dict(routed="false")),
                        ("a branch that is not this group's", dict(ref="refs/heads/main")),
                        ("a queue branch of another base", dict(ref="gh-readonly-queue/main/pr-565-" + "9" * 40))):
            with self.subTest(case=why):
                out = self.group(**kw)
                self.assertEqual(out["checked_elsewhere"], "false")

    def test_no_changed_path_leaves_the_group_its_checks(self):
        out = self.group(paths=[])
        self.assertEqual(out["checked_elsewhere"], "false")

    # A pull request's own run: the same rules as a group's, the pull request its one entry, its own comments for
    # the head its merge commit merges, and the plan's keys over that merge commit.  #1478 was proved on the farm
    # (7/7, its marker's keys equal) and re-checked on a GitHub runner for two hours.
    PR = 1478

    def pr_run(self, recorded=None, said=None, head=None, api_head=None, **kw):
        """The step on pull request PR's run, its event's head `head` (the default is PR_HEAD, the merge commit's
        second parent) and the API's head `api_head` (the default is the event's), with `recorded` the components
        the App's marker recorded for a unit (the default is comp(unit), each unit of UNITS in one comment: a wave)
        and `said` that comment outright (the default is the marker for the event's head)."""
        head = self.PR_HEAD if head is None else head
        was = {u: self.comp(u) for u, _n in self.UNITS}
        was.update(recorded or {})
        if said is None:
            said = self.comment(head, unit_keys=[(u, self.key_of(c)) for u, c in was.items()])
        return self.group(event="pull_request", heads={self.PR: head if api_head is None else api_head},
                          comments={self.PR: said}, pr=str(self.PR), pr_head=head, **kw)

    def test_a_pull_request_run_reads_the_event_s_head_not_the_api_s(self):
        """The tree this run keyed merges the event's head; a later push moves the API's head, and a marker for
        that later head says nothing of this tree."""
        keys = [(u, self.key_of(self.comp(u))) for u, _n in self.UNITS]
        later = "8" * 40
        out = self.pr_run(api_head=later)
        self.assertEqual(out["checked_elsewhere"], "true", self.said)
        self.assertIn("#%d %s (pvc)" % (self.PR, self.PR_HEAD), out["checked_elsewhere_note"])
        out = self.pr_run(api_head=later, said=self.comment(later, unit_keys=keys))
        self.assertEqual(out["checked_elsewhere"], "false")
        self.assertIn("pull request %d has no VM evidence comment for its head %s" % (self.PR, self.PR_HEAD),
                      self.said)

    def test_a_pull_request_run_whose_merge_commit_merges_another_head_runs_its_checks(self):
        """The plan keyed the merge commit in head/: an event head that is not its second parent, even with the
        App's marker for that head and equal keys, runs the checks."""
        for why, head in (("its first parent", self.MERGE_BASE), ("a commit it does not hold", "9" * 40)):
            with self.subTest(case=why):
                out = self.pr_run(head=head)
                self.assertEqual(out["checked_elsewhere"], "false")
                self.assertIn("this run's merge commit merges %s, not the event's head %s" % (self.PR_HEAD, head),
                              self.said)
        shutil.rmtree(os.path.join(self.dir, "head"))
        out = self.pr_run()
        self.assertEqual(out["checked_elsewhere"], "false")
        self.assertIn("this run's merge commit merges no second parent", self.said)

    def test_a_pull_request_run_whose_keys_equal_its_marker_s_runs_no_check(self):
        for hold in ("none", "label"):
            with self.subTest(hold=hold):
                out = self.pr_run(hold=hold)
                self.assertEqual(out["checked_elsewhere"], "true", self.said)
                self.assertIn("#%d %s (pvc): https://github.com/%s/pull/1#issuecomment-1"
                              % (self.PR, self.PR_HEAD, REPOSITORY), out["checked_elsewhere_note"])
                self.assertIn("pull request %d was checked on a VM" % self.PR, self.said)
                self.assertIn("2 part(s), each with the key its check of record ran on", self.said)
                with open(os.path.join(self.dir, "plan.json")) as f:
                    self.assertEqual(f.read(), "")

    def test_a_pull_request_run_whose_key_differs_from_its_marker_s_runs_its_checks(self):
        """Its head moved after the check of record, or something the check reads moved on the base: the checks
        run here, and the run does not fail, since no queue entry is there to take out."""
        unit = self.UNITS[0][0]
        for why, moved in (("its proofs", {"proofs": "pf1"}), ("theories/", {"theories": "th1"})):
            with self.subTest(case=why):
                out = self.pr_run(planned={unit: self.comp(unit, **moved)})
                self.assertEqual(out["checked_elsewhere"], "false")
                self.assertIn("pull request %d's VM evidence recorded key %s for %s and this run's key for it is %s"
                              % (self.PR, self.key_of(self.comp(unit)), unit,
                                 self.key_of(self.comp(unit, **moved))), self.said)
                self.assertNotIn("::error::", self.said)
                self.assertNotIn("leaves the merge queue", self.said)
                with open(os.path.join(self.dir, "plan.json")) as f:
                    self.assertIn('"parts"', f.read())

    def test_a_pull_request_run_whose_marker_is_for_another_head_runs_its_checks(self):
        keys = [(u, self.key_of(self.comp(u))) for u, _n in self.UNITS]
        out = self.pr_run(said=self.comment("9" * 40, unit_keys=keys))
        self.assertEqual(out["checked_elsewhere"], "false")
        self.assertIn("pull request %d has no VM evidence comment for its head %s" % (self.PR, self.PR_HEAD),
                      self.said)

    def test_a_pull_request_run_ignores_a_marker_the_app_did_not_write(self):
        keys = [(u, self.key_of(self.comp(u))) for u, _n in self.UNITS]
        for why, said in (("another author", self.comment(self.PR_HEAD, by="someone", kind="User", unit_keys=keys)),
                          ("a user of the App's name", self.comment(self.PR_HEAD, kind="User", unit_keys=keys))):
            with self.subTest(case=why):
                out = self.pr_run(said=said)
                self.assertEqual(out["checked_elsewhere"], "false")
                self.assertIn("pull request %d has no VM evidence comment" % self.PR, self.said)

    def test_a_pull_request_run_ignores_a_marker_anyone_else_edited(self):
        for why, edits in (("another editor", self.edits(self.APP, ("User", "someone"))),
                           ("an editor GitHub no longer names", self.edits(None)),
                           ("a read that fails", "error")):
            with self.subTest(case=why):
                out = self.pr_run(edits=edits)
                self.assertEqual(out["checked_elsewhere"], "false")
                self.assertIn("pull request %d has no VM evidence comment" % self.PR, self.said)

    def test_a_pull_request_run_with_a_path_the_keys_do_not_hold_runs_its_checks(self):
        for path in ("theories/Premises.v", "projects/zlib/checksum_fuzzer/harness.yaml", ".github/workflows/pr.yml"):
            with self.subTest(path=path):
                out = self.pr_run(paths=self.PATHS + [path])
                self.assertEqual(out["checked_elsewhere"], "false")
                self.assertIn("changed path(s) a check reads", self.said)

    def test_a_draft_pull_request_run_is_left_as_it_was(self):
        """A draft's check waits until it is ready for review, and required reads a draft first (PrHoldTest)."""
        out = self.pr_run(hold="draft")
        self.assertEqual(out["checked_elsewhere"], "false")
        self.assertIn("the checks run here: a draft", self.said)
        with open(os.path.join(self.dir, "plan.json")) as f:
            self.assertIn('"parts"', f.read())

    def test_a_pull_request_run_without_its_number_or_head_runs_its_checks(self):
        for why, kw in (("no number", dict(pr="")), ("no head", dict(pr_head="")),
                        ("a head that is no sha", dict(pr_head="main"))):
            with self.subTest(case=why):
                out = self.group(event="pull_request", **dict(dict(pr=str(self.PR), pr_head=self.PR_HEAD), **kw))
                self.assertEqual(out["checked_elsewhere"], "false")

    def test_a_deferred_check_is_the_same_answer_with_the_pin_s_check_of_record(self):
        """One pair for both changes whose checks are of record elsewhere: the step answers the pinned tree's
        deferred check before it reads anything of a group, and the tools that judged the tree do not enter into it
        (the pin names the tree, and what it defers is the check jobs, not the rules that judged it).  A deferral
        that names no check of record fails here, as it does in the plan step."""
        out = self.group(deferred="true", record=RECORD, event="pull_request")
        self.assertEqual((out["checked_elsewhere"], out["checked_elsewhere_note"]),
                         ("true", "the check of record: " + RECORD))
        self.group(deferred="true", record="", event="pull_request")
        self.assertEqual(self.rc, 1, self.said)
        self.assertIn("a deferred check with no check of record", self.said)

    def test_a_comment_anyone_else_wrote_or_edited_leaves_the_group_its_checks(self):
        """GraphQL names an App `Bot` and gives its login without the `[bot]` REST appends: the comment's author
        must be that Bot, and so must every editor of it (GitHub lets an editor rewrite a comment's body).  An
        editor GitHub no longer names, a user of the App's name, an edit list that is no list, more edits than the
        page holds, and a read that fails all leave the comment unread."""
        for why, edits in (("another editor", self.edits(self.APP, ("User", "someone"))),
                           ("a user of the App's name", self.edits(("User", "sjawhar-agent"))),
                           ("an editor GitHub no longer names", self.edits(None)),
                           ("another author", self.edits(author=("User", "sjawhar-agent"))),
                           ("an author GitHub no longer names", self.edits(author=None)),
                           ("the edits are no list", self.edits(nodes="many")),
                           ("more edits than the page holds", self.edits(self.APP, total=101)),
                           ("a read that fails", "error")):
            with self.subTest(case=why):
                out = self.group(edits=edits)
                self.assertEqual(out["checked_elsewhere"], "false")
        for why, edits in (("no edit", self.edits()),
                           ("the App's own edits", self.edits(self.APP, self.APP))):
            with self.subTest(case=why):
                self.assertEqual(self.group(edits=edits)["checked_elsewhere"], "true")

    def test_the_newest_marker_of_every_page_answers_not_of_each_page(self):
        """--paginate --slurp hands one jq program the whole list: a later page's comment is the newest, and an
        earlier page's stale key lines do not answer for it.  When the newest is the stale one, its key differs
        from this group head's and that entry leaves the queue."""
        stale = self.comment(self.head_of(563), unit_keys=[(self.UNITS[0][0], "b" * 64)])
        right = self.comment(self.head_of(563), unit_keys=[(self.UNITS[0][0], self.key_of(self.comp(self.UNITS[0][0])))])
        out = self.group(comments={563: stale, 565: self.comment(self.head_of(565),
                                                                 unit_keys=[(self.UNITS[1][0],
                                                                             self.key_of(self.comp(self.UNITS[1][0])))])},
                         pages={563: right})
        self.assertEqual(out["checked_elsewhere"], "true")
        self.group(comments={563: right, 565: self.comment(self.head_of(565),
                                                           unit_keys=[(self.UNITS[1][0],
                                                                       self.key_of(self.comp(self.UNITS[1][0])))])},
                   pages={563: stale}, fails=True, **self.ends_at(563))
        self.assertIn("::error::pull request 563's VM evidence recorded key %s for %s"
                      % ("b" * 64, self.UNITS[0][0]), self.said)

    def test_the_answer_reaches_the_check_job_and_required(self):
        jobs = load("pr.yml")["jobs"]
        self.assertEqual(jobs["plan"]["outputs"]["checked_elsewhere"],
                         "${{ steps.elsewhere.outputs.checked_elsewhere }}")
        self.assertEqual(jobs["plan"]["outputs"]["checked_elsewhere_note"],
                         "${{ steps.elsewhere.outputs.checked_elsewhere_note }}")
        for job in ("check", "fetch-drafts"):
            self.assertIn("&& needs.plan.outputs.checked_elsewhere != 'true'", " ".join(jobs[job]["if"].split()), job)
        # the two answers of the pinned tree's deferred check are the elsewhere step's to read, not required's
        for job in ("check", "fetch-drafts"):
            self.assertNotIn("deferred", " ".join(jobs[job]["if"].split()), job)
        collect = step(jobs["required"], "every job green, and something checked when the plan named anything")
        self.assertEqual((collect["env"]["CHECKED_ELSEWHERE"], collect["env"]["CHECKED_ELSEWHERE_NOTE"]),
                         ("${{ needs.plan.outputs.checked_elsewhere }}",
                          "${{ needs.plan.outputs.checked_elsewhere_note }}"))
        self.assertNotIn("DEFERRED", collect["env"])


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class PlanSizeTest(unittest.TestCase):
    """A plan of every harness outgrows what one environment value may hold (131,072 bytes on Linux; weekly.yml's was
    51,715 bytes on 2026-10-26 and a full sweep's plan reached 166,794): only a matrix reads the whole plan, and the
    determinism job reads the plan job's sample instead."""

    def test_no_step_takes_the_whole_plan_into_its_environment(self):
        for workflow in ("pr.yml", "weekly.yml"):
            for name, job in load(workflow)["jobs"].items():
                for s in [job] + job.get("steps", []):
                    for key, value in (s.get("env") or {}).items():
                        with self.subTest(workflow=workflow, job=name, env=key):
                            self.assertIsNone(re.search(r"needs\s*\.\s*plan\s*\.\s*outputs\s*\.\s*plan\b(?!_)",
                                                        str(value)), value)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_sample_is_the_first_job_with_published_builds(self):
        jobs = load("weekly.yml")["jobs"]
        snapshot = step(jobs["determinism"], "snapshot a sample of ELF files with the pinned elf-snapshot")
        self.assertEqual(snapshot["env"]["SAMPLE"], "${{ needs.plan.outputs.sample }}")
        self.assertEqual(snapshot["env"]["SAMPLE_PROJECTS"], "${{ needs.plan.outputs.sample_projects }}")
        text = step(jobs["plan"], "plan")["run"]
        end = '} >> "$GITHUB_OUTPUT"'
        start = text.index("sample='")
        script = text[start:text.index(end, start) + len(end)]
        plan = {"units": ["a/x", "b/y", "c/z"],
                "jobs": [{"index": 0, "check_units": "", "projects": "a"},
                         {"index": 1, "check_units": "b/y c/z", "projects": "b c"},
                         {"index": 2, "check_units": "d/w", "projects": "d"}]}
        with tempfile.TemporaryDirectory(prefix="oft-sample-") as d:
            with open(os.path.join(d, "plan.json"), "w") as f:
                json.dump(plan, f)
            out = os.path.join(d, "output")
            r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", script],
                               env=dict(os.environ, RUNNER_TEMP=d, GITHUB_OUTPUT=out), capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stderr)
            with open(out) as f:
                got = dict(line.rstrip("\n").split("=", 1) for line in f)
        self.assertEqual(got["sample"], "b/y c/z")
        self.assertEqual(got["sample_projects"], "b c")
        self.assertEqual(json.loads(got["plan"]), plan["jobs"])
        self.assertEqual(got["units"], "3")

        none = {"units": ["a/x"], "jobs": [{"index": 0, "check_units": "", "projects": "a"}]}
        with tempfile.TemporaryDirectory(prefix="oft-sample-") as d:
            with open(os.path.join(d, "plan.json"), "w") as f:
                json.dump(none, f)
            out = os.path.join(d, "output")
            subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", script], check=True,
                           env=dict(os.environ, RUNNER_TEMP=d, GITHUB_OUTPUT=out), capture_output=True, text=True)
            with open(out) as f:
                got = dict(line.rstrip("\n").split("=", 1) for line in f)
        self.assertEqual((got["sample"], got["sample_projects"]), ("", ""))


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class CheckTreeTest(unittest.TestCase):
    """pr.yml's check job checks a change that is not a release on a worktree of the base with only the change's
    proofs/, counterexamples/ and findings/ in it.  Every generated file of that tree is rendered again by the base's
    tools, from the base's facts and those proofs: a project's first proofs bring a proofs package that the base's
    dune-project lacks, and without it dune stops at the first proof's dune file.  A release brings its own facts and
    generated files, which lint holds to their rendering, so the step does not run for one."""

    def test_the_check_renders_the_tree_it_checks_with_the_base_s_tools(self):
        job = load("pr.yml")["jobs"]["check"]
        names = [s.get("name") for s in job["steps"]]
        render = step(job, "the generated files of that tree, by the base's tools")
        self.assertEqual(render["if"], "env.KIND != 'release'")
        self.assertEqual(render["run"].strip(), 'PYTHONPATH="$RUNNER_TEMP/tools" python -m oft --root base generate')
        # the tools it runs are the copy the plan job named (the base's, but the change's own where the base pins
        # it), made before this step, outside the tree it writes; the check comes after it
        self.assertEqual(step(job, "the tools, copied out of the tree they check")["run"].strip(),
                         'cp -r -- "${{ needs.plan.outputs.tools }}/tools" "$RUNNER_TEMP/tools"')
        at = names.index("the generated files of that tree, by the base's tools")
        self.assertLess(names.index("the tools, copied out of the tree they check"), at)
        self.assertLess(at, names.index("check"))
        # and base/ is the tree the check reads for such a change
        work = step(job, "statements from the base; proofs, counterexamples and findings from this change")["run"]
        self.assertIn('echo "work=$GITHUB_WORKSPACE/base" >> "$GITHUB_OUTPUT"', work)



def git(cwd, *args):
    return subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=",
                           "-c", "init.defaultBranch=main", *args],
                          cwd=cwd, check=True, capture_output=True, text=True).stdout.strip()


# A gh that answers `gh api repos/<r>/compare/<commit>...<branch> --jq <filter>` as GitHub would for the repository
# at FAKE_ORIGIN: identical, ahead (the branch is after the commit), behind or diverged, with their merge base;
# `gh api repos/<r>/pulls/<n>` with FAKE_BASE_REF as the pull request's base branch; and `gh api
# repos/<r>/commits/<commit>` with the commit's parents.
FAKE_COMPARE_GH = r"""#!/usr/bin/env bash
[ "$1" = api ] || exit 9; shift
filter=. endpoint=
while [ $# -gt 0 ]; do case $1 in --jq) filter=$2; shift 2 ;; *) endpoint=$1; shift ;; esac; done
# the open pull requests whose head is a branch: FAKE_STACK's "head=base" pairs (lane into main unless given)
case $endpoint in */pulls\?*)
  h=${endpoint#*head=}; h=${h%%&*}; h=${h#*:}; r=
  for p in ${FAKE_STACK-lane=main}; do [ "${p%%=*}" = "$h" ] && r=${p#*=}; done
  if [ -n "$r" ]; then jq -n --arg r "$r" '[{base: {ref: $r}}]'; else echo '[]'; fi | jq -r "$filter"; exit ;; esac
case $endpoint in */pulls/*) jq -n --arg r "$FAKE_BASE_REF" '{base: {ref: $r}}' | jq -r "$filter"; exit ;; esac
case $endpoint in */commits/*)
  git -C "$FAKE_ORIGIN" rev-list --parents -n 1 "${endpoint##*/commits/}" | cut -s -d' ' -f2- |
    jq -R '{parents: [split(" ")[] | select(. != "") | {sha: .}]}' | jq -r "$filter"; exit ;; esac
spec=${endpoint##*/compare/}; a=${spec%%...*}; b=$(git -C "$FAKE_ORIGIN" rev-parse --verify -q "refs/heads/${spec#*...}") ||
  { echo "gh: Not Found (HTTP 404)" >&2; exit 1; }
mb=$(git -C "$FAKE_ORIGIN" merge-base "$a" "$b")
if [ "$a" = "$b" ]; then s=identical; elif [ "$mb" = "$a" ]; then s=ahead; elif [ "$mb" = "$b" ]; then s=behind
else s=diverged; fi
jq -n --arg s "$s" --arg mb "$mb" '{status: $s, merge_base_commit: {sha: $mb}}' | jq -r "$filter"
"""


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
@unittest.skipUnless(shutil.which("git") and shutil.which("jq"), "git or jq is not installed")
class BaseStepTest(unittest.TestCase):
    """pr.yml's plan job takes the base of a pull request from the merge commit GitHub built for the run, and the lint
    job takes the plan job's base (each case runs both, lint after plan with plan's answers), not
    from the event: a pull request reopened right after its base moved was sent the old base, and the moved base's
    own commits were judged as the change's.  Here the base moves from b1 to b2 (which adds moved.txt) after the
    change (proofs/p.v) branched from b1; GitHub's merge commit (refs/pull/1/merge) is b2 + the change.  A branch
    lane (b1 + lane.txt) has its own merge commit with the change (refs/pull/2/merge), as GitHub leaves it for a
    while after the pull request's base is changed from lane to main."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="oft-base-")
        d = self.dir = self._tmp.name
        origin = os.path.join(d, "origin")
        os.mkdir(origin)
        git(origin, "init", "-q")
        for rel, text in (("tools/oft/x.py", "x\n"), ("README.md", "r\n"),
                          # what the plan job's base step requires of the base: the shared actions the workflow runs
                          # from the base
                          (".github/actions/plan-drafts/action.yml", "a\n"),
                          (".github/actions/place-drafts/action.yml", "a\n")):
            os.makedirs(os.path.join(origin, os.path.dirname(rel)), exist_ok=True)
            with open(os.path.join(origin, rel), "w") as f:
                f.write(text)
        git(origin, "add", "-A")
        git(origin, "commit", "-qm", "b1")
        self.b1 = git(origin, "rev-parse", "HEAD")
        git(origin, "checkout", "-qb", "topic")
        os.mkdir(os.path.join(origin, "proofs"))
        with open(os.path.join(origin, "proofs", "p.v"), "w") as f:
            f.write("p\n")
        git(origin, "add", "-A")
        git(origin, "commit", "-qm", "the change")
        git(origin, "checkout", "-q", "main")
        with open(os.path.join(origin, "moved.txt"), "w") as f:
            f.write("m\n")
        git(origin, "add", "-A")
        git(origin, "commit", "-qm", "b2")
        self.b2 = git(origin, "rev-parse", "HEAD")
        git(origin, "merge", "-q", "--no-ff", "-m", "merge", "topic")
        git(origin, "update-ref", "refs/pull/1/merge", "HEAD")
        git(origin, "reset", "-q", "--hard", self.b2)
        git(origin, "checkout", "-q", "-b", "lane", self.b1)
        with open(os.path.join(origin, "lane.txt"), "w") as f:
            f.write("l\n")
        git(origin, "add", "-A")
        git(origin, "commit", "-qm", "lane")
        git(origin, "merge", "-q", "--no-ff", "-m", "merge", "topic")
        git(origin, "update-ref", "refs/pull/2/merge", "HEAD")
        git(origin, "reset", "-q", "--hard", "HEAD^1")
        git(origin, "checkout", "-q", "main")
        self.origin = origin
        bin_dir = os.path.join(d, "bin")
        os.mkdir(bin_dir)
        with open(os.path.join(bin_dir, "gh"), "w") as f:
            f.write(FAKE_COMPARE_GH)
        os.chmod(os.path.join(bin_dir, "gh"), 0o755)
        self.path = bin_dir + os.pathsep + os.environ["PATH"]

    def tearDown(self):
        self._tmp.cleanup()

    def run_base(self, job, event, event_base, ref="refs/pull/1/merge", base_ref="main", ws=None, event_base_ref=None):
        """The job's base step, in a fresh workspace (ws, or a new one) whose head/ is a clone one commit deep of
        `ref`, as actions/checkout leaves it: its exit status, its output, the base it chose and the paths it found
        changed.  The lint job's base step takes the plan job's answers (needs.plan.outputs.base and routed): it runs
        after the plan job's, which runs in a workspace of its own, with what that one wrote, and the output holds
        both.  base_ref is the pull request's base as the API names it; event_base_ref, the event's base.ref
        (github.base_ref), is base_ref unless given."""
        said = ""
        lint_env = {}
        base_refs = {"FAKE_BASE_REF": base_ref, "BASE_REF": base_ref if event_base_ref is None else event_base_ref,
                     "PR": "1"}
        if job == "lint":
            _rc, said, _base, _changed, planned = self.run_step_of("plan", event, event_base, ref, base_refs, {})
            lint_env = {"PLAN_BASE": planned.get("base", ""), "PLAN_ROUTED": planned.get("routed", "")}
        rc, out, base, changed, _got = self.run_step_of(job, event, event_base, ref, base_refs, lint_env, ws)
        return rc, said + out, base, changed

    def run_step_of(self, job, event, event_base, ref, base_refs, extra, ws=None):
        ws = ws or tempfile.mkdtemp(dir=self.dir)
        head = os.path.join(ws, "head")
        os.mkdir(head)
        git(head, "init", "-q")
        git(head, "remote", "add", "origin", "file://" + self.origin)
        git(head, "fetch", "-q", "--depth=1", "origin", ref)
        git(head, "checkout", "-q", "--detach", "FETCH_HEAD")
        text = step(load("pr.yml")["jobs"][job], "the base branch, whose tools judge this change")["run"]
        runner, output = os.path.join(ws, "runner"), os.path.join(ws, "output")
        os.mkdir(runner)
        # a runner sets GITHUB_STEP_SUMMARY for every step, and the plan job's base step writes the change to it
        env = dict(os.environ, GITHUB_WORKSPACE=ws, RUNNER_TEMP=runner, GITHUB_OUTPUT=output, GITHUB_EVENT_NAME=event,
                   GITHUB_STEP_SUMMARY=os.path.join(runner, "summary"), EVENT_BASE=event_base, KIND="maintainer",
                   GIT_ALLOW_PROTOCOL="file", PATH=self.path, FAKE_ORIGIN=self.origin, GH_TOKEN="t",
                   GITHUB_REPOSITORY="acme/proofs", **base_refs, **extra)
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", text], cwd=ws, env=env,
                           capture_output=True, text=True)
        got, changed = {}, []
        if os.path.exists(output):
            with open(output) as f:
                got = dict(line.rstrip("\n").split("=", 1) for line in f if "=" in line)
        if os.path.exists(os.path.join(runner, "changed.txt")):
            with open(os.path.join(runner, "changed.txt")) as f:
                changed = f.read().split()
        return r.returncode, r.stdout + r.stderr, got.get("base"), changed, got

    def test_a_pull_request_is_judged_against_the_base_its_merge_commit_was_built_on(self):
        """EVENT_BASE is empty for a pull request (the event's base.sha is not read at all), and the base step reads
        the merge commit's first parent: the change is proofs/p.v alone, never the moved base's moved.txt."""
        for job in ("plan", "lint"):
            with self.subTest(job=job):
                rc, out, base, changed = self.run_base(job, "pull_request", "")
                self.assertEqual(rc, 0, out)
                self.assertEqual(base, self.b2)
                self.assertEqual(changed, ["proofs/p.v"])

    def test_the_event_s_base_is_not_read_for_a_pull_request(self):
        """Even an old base in EVENT_BASE (the value the event carried before this change) gives way to the merge
        commit's: had the step used it, moved.txt would be listed as the change's."""
        for job in ("plan", "lint"):
            with self.subTest(job=job):
                rc, out, base, changed = self.run_base(job, "pull_request", self.b1)
                self.assertEqual(rc, 0, out)
                self.assertEqual((base, changed), (self.b2, ["proofs/p.v"]))

    def test_a_pull_request_whose_head_is_no_merge_commit_is_refused(self):
        for job in ("plan", "lint"):
            with self.subTest(job=job):
                rc, out, base, _ = self.run_base(job, "pull_request", "", ref="refs/heads/topic")
                self.assertEqual(rc, 1, out)
                self.assertIn("not the merge commit GitHub builds for a pull request", out)
                self.assertIsNone(base)

    def test_a_push_is_judged_against_the_commit_before_it(self):
        for job in ("plan", "lint"):
            with self.subTest(job=job):
                rc, out, base, changed = self.run_base(job, "push", self.b1, ref="refs/heads/main")
                self.assertEqual(rc, 0, out)
                self.assertEqual((base, changed), (self.b1, ["moved.txt"]))

    def test_a_merge_commit_built_on_another_branch_than_the_base_is_refused(self):
        """The pull request's base was changed from lane to main, and GitHub has not rebuilt the merge commit yet:
        judged against lane, it would carry a green earned against lane's tools to main."""
        for job in ("plan", "lint"):
            with self.subTest(job=job):
                rc, out, base, _ = self.run_base(job, "pull_request", "", ref="refs/pull/2/merge", base_ref="main")
                self.assertEqual(rc, 1, out)
                self.assertIn("which is not on main", out)
                # a re-run checks the same merge commit, so it cannot clear this
                self.assertIn("push, or close and reopen the pull request", out)
                self.assertNotIn("re-run this run", out)
                self.assertIsNone(base)
        rc, out, base, changed = self.run_base("plan", "pull_request", "", ref="refs/pull/2/merge", base_ref="lane")
        self.assertEqual(rc, 0, out)
        self.assertEqual(changed, ["proofs/p.v"])

    def test_the_top_of_a_stack_is_judged_against_the_base_the_api_names(self):
        """GitHub's event names the stack's trunk, main, as the base of a stack's top pull request, whose base is the
        branch below it (lane here; measured on #714, #724 and #765): the step takes the base from the API, so the
        merge commit built on lane passes, and one built on main is refused for a pull request whose base is lane."""
        rc, out, base, changed = self.run_base("plan", "pull_request", "", ref="refs/pull/2/merge", base_ref="lane",
                                               event_base_ref="main")
        self.assertEqual(rc, 0, out)
        self.assertEqual(changed, ["proofs/p.v"])
        rc, out, base, _ = self.run_base("plan", "pull_request", "", ref="refs/pull/1/merge", base_ref="lane",
                                         event_base_ref="main")
        self.assertEqual(rc, 1, out)
        self.assertIn("which is not on lane", out)

    def stacked(self, below, number):
        """GitHub's merge commit for a pull request of topic into lane that sits on another pull request of a stack:
        built on `below`, the merge commit GitHub made for the pull request below (lane into main), at
        refs/pull/<number>/merge."""
        git(self.origin, "checkout", "-q", "--detach", below)
        git(self.origin, "merge", "-q", "--no-ff", "-m", "merge", "topic")
        git(self.origin, "update-ref", "refs/pull/%d/merge" % number, "HEAD")
        git(self.origin, "checkout", "-q", "main")

    def test_a_pull_request_of_a_stack_is_judged_on_the_merge_commit_of_the_one_below(self):
        """For a pull request of a stack, GitHub builds the merge commit on the merge commit of the pull request below
        it: the base branch (lane) merged into main, whose second parent is lane's tip (measured on stack #873).  The
        step takes that commit as the base, so the change is proofs/p.v alone."""
        git(self.origin, "checkout", "-q", "--detach", self.b2)
        git(self.origin, "merge", "-q", "--no-ff", "-m", "merge", "lane")
        lane_into_main = git(self.origin, "rev-parse", "HEAD")
        git(self.origin, "update-ref", "refs/pull/9/merge", lane_into_main)
        git(self.origin, "checkout", "-q", "main")
        self.stacked(lane_into_main, 3)
        for job in ("plan", "lint"):
            with self.subTest(job=job):
                rc, out, base, changed = self.run_base(job, "pull_request", "", ref="refs/pull/3/merge",
                                                       base_ref="lane", event_base_ref="main")
                self.assertEqual(rc, 0, out)
                self.assertEqual((base, changed), (lane_into_main, ["proofs/p.v"]))

    def test_a_commit_after_the_base_branch_that_is_no_merge_of_it_is_refused(self):
        """A merge commit built on a commit that holds lane's tip but is not the merge commit of a pull request below
        (here lane's tip and one more commit, as when lane is pushed back after GitHub built the merge commit) is
        stale: judged so, the change would hide that commit."""
        git(self.origin, "checkout", "-q", "--detach", "lane")
        with open(os.path.join(self.origin, "dropped.txt"), "w") as f:
            f.write("d\n")
        git(self.origin, "add", "-A")
        git(self.origin, "commit", "-qm", "dropped from lane")
        dropped = git(self.origin, "rev-parse", "HEAD")
        git(self.origin, "checkout", "-q", "main")
        self.stacked(dropped, 4)
        for job in ("plan", "lint"):
            with self.subTest(job=job):
                rc, out, base, _ = self.run_base(job, "pull_request", "", ref="refs/pull/4/merge", base_ref="lane")
                self.assertEqual(rc, 1, out)
                self.assertIn("is not the merge commit of the pull request below", out)
                self.assertIsNone(base)

    def test_a_merge_of_the_base_branch_s_tip_over_another_first_parent_is_refused(self):
        """The base's first parent passes the same rule against the base branch of the pull request below (lane into
        main): a merge whose first parent is lane and one more commit, and whose second parent is lane's tip, would
        hide that commit from the change while its tools judge it; so would a merge over an unrelated root.  The
        merge of lane into main, the measured case (#864 on 6ed2b55805cf, #562's merge commit), still passes."""
        o = self.origin
        lane = git(o, "rev-parse", "lane")
        git(o, "checkout", "-q", "--detach", "lane")
        with open(os.path.join(o, "extra.txt"), "w") as f:
            f.write("e\n")
        git(o, "add", "-A")
        git(o, "commit", "-qm", "extra on top of lane")
        extra = git(o, "rev-parse", "HEAD")
        git(o, "checkout", "-q", "--orphan", "evil")
        git(o, "rm", "-rqf", ".")
        os.makedirs(os.path.join(o, "tools", "oft"))
        with open(os.path.join(o, "tools", "oft", "x.py"), "w") as f:
            f.write("evil\n")
        git(o, "add", "-A")
        git(o, "commit", "-qm", "unrelated root")
        root = git(o, "rev-parse", "HEAD")
        git(o, "checkout", "-q", "-f", "main")
        for number, first in ((5, extra), (6, root)):
            wrapped = git(o, "commit-tree", first + "^{tree}", "-p", first, "-p", lane, "-m", "wrap")
            self.stacked(wrapped, number)
            for job in ("plan", "lint"):
                with self.subTest(first=first, job=job):
                    rc, out, base, _ = self.run_base(job, "pull_request", "", ref="refs/pull/%d/merge" % number,
                                                     base_ref="lane")
                    self.assertEqual(rc, 1, out)
                    self.assertIn("which is not on main", out)
                    self.assertIsNone(base)
        git(o, "checkout", "-q", "--detach", self.b2)
        git(o, "merge", "-q", "--no-ff", "-m", "merge", "lane")
        lane_into_main = git(o, "rev-parse", "HEAD")
        git(o, "checkout", "-q", "main")
        self.stacked(lane_into_main, 7)
        rc, out, base, changed = self.run_base("plan", "pull_request", "", ref="refs/pull/7/merge", base_ref="lane")
        self.assertEqual(rc, 0, out)
        self.assertEqual((base, changed), (lane_into_main, ["proofs/p.v"]))

    def test_a_merge_over_a_branch_that_heads_no_open_pull_request_is_refused(self):
        git(self.origin, "checkout", "-q", "--detach", self.b2)
        git(self.origin, "merge", "-q", "--no-ff", "-m", "merge", "lane")
        lane_into_main = git(self.origin, "rev-parse", "HEAD")
        git(self.origin, "checkout", "-q", "main")
        self.stacked(lane_into_main, 8)
        os.environ["FAKE_STACK"] = ""
        try:
            rc, out, base, _ = self.run_base("plan", "pull_request", "", ref="refs/pull/8/merge", base_ref="lane")
        finally:
            del os.environ["FAKE_STACK"]
        self.assertEqual(rc, 1, out)
        self.assertIn("no open pull request has lane as its head", out)

    def test_a_base_that_moved_on_after_the_merge_commit_was_built_still_holds_it(self):
        with open(os.path.join(self.origin, "later.txt"), "w") as f:
            f.write("later\n")
        git(self.origin, "add", "-A")
        git(self.origin, "commit", "-qm", "b3")
        for job in ("plan", "lint"):
            with self.subTest(job=job):
                rc, out, base, changed = self.run_base(job, "pull_request", "")
                self.assertEqual(rc, 0, out)
                self.assertEqual((base, changed), (self.b2, ["proofs/p.v"]))

    def test_the_workflow_reads_no_base_from_a_pull_request_event(self):
        with open(os.path.join(WORKFLOWS, "pr.yml")) as f:
            self.assertNotIn("pull_request.base.sha", f.read())

    def both_layouts(self):
        """A commit on main whose files are the base's findings, a statement and a proof library in both layouts, and
        one more commit on it, the push: the first commit, the base."""
        for rel in ("findings/zlib/unpatched.yaml", "findings/zlib/fz/s/finding.yaml", "proofs/zlib/fz/lib/A.v",
                    "projects/zlib/project.yaml", "projects/zlib/unpatched.yaml", "projects/zlib/fz/Statements.v",
                    "projects/zlib/fz/findings/s/finding.yaml", "projects/zlib/fz/proofs/lib/A.v",
                    "projects/zlib/fz/proofs/s/Proof.v"):
            os.makedirs(os.path.join(self.origin, os.path.dirname(rel)), exist_ok=True)
            with open(os.path.join(self.origin, rel), "w") as f:
                f.write(rel + "\n")
        git(self.origin, "add", "-A")
        git(self.origin, "commit", "-qm", "both layouts")
        base = git(self.origin, "rev-parse", "HEAD")
        with open(os.path.join(self.origin, "later.txt"), "w") as f:
            f.write("later\n")
        git(self.origin, "add", "-A")
        git(self.origin, "commit", "-qm", "the push")
        return base

    def base_files(self, job):
        """The files of the base worktree the job's base step leaves, for a push on both_layouts()."""
        base = self.both_layouts()
        ws = tempfile.mkdtemp(dir=self.dir)
        rc, out, chosen, _ = self.run_base(job, "push", base, ref="refs/heads/main", ws=ws)
        self.assertEqual((rc, chosen), (0, base), out)
        root = os.path.join(ws, "base")
        return sorted(os.path.relpath(os.path.join(dp, f), root) for dp, dns, fns in os.walk(root)
                      for f in fns if not os.path.relpath(dp, root).split(os.sep)[0] == ".git" and f != ".git")

    def test_lint_takes_the_base_s_findings_in_both_layouts_and_no_other_folder(self):
        """The findings ledger lint compares with the base's (lint --base): findings/, projects/<p>/unpatched.yaml and
        projects/<p>/<h>/findings/, with the tools and the files at the top of the tree; no statement, no proof."""
        self.assertEqual(self.base_files("lint"), [
            "README.md", "findings/zlib/fz/s/finding.yaml", "findings/zlib/unpatched.yaml", "moved.txt",
            "projects/zlib/fz/findings/s/finding.yaml", "projects/zlib/unpatched.yaml", "tools/oft/x.py"])

    def test_plan_takes_every_file_of_the_base_but_the_proof_libraries_of_both_layouts(self):
        got = self.base_files("plan")
        self.assertNotIn("proofs/zlib/fz/lib/A.v", got)
        self.assertNotIn("projects/zlib/fz/proofs/lib/A.v", got)
        self.assertLessEqual({"projects/zlib/fz/Statements.v", "projects/zlib/fz/proofs/s/Proof.v",
                              "projects/zlib/fz/findings/s/finding.yaml", "findings/zlib/unpatched.yaml",
                              ".github/actions/plan-drafts/action.yml"}, set(got))


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
@unittest.skipUnless(shutil.which("git"), "git is not installed")
class LintBaseTest(unittest.TestCase):
    """pr.yml's lint step compares the findings ledger with the base's (--base) when the base has one, in either
    layout: findings/, a projects/<p>/unpatched.yaml or a projects/<p>/<h>/findings/."""

    def lint_args(self, base_files, planned_tools="base"):
        """The arguments the step gives `python -m oft`, with a base worktree that holds base_files beside its tools,
        and the workspace (deleted by then): the base's run's, then, when the plan judged the change with its own
        tools (planned_tools head), the change's own run's."""
        with tempfile.TemporaryDirectory(prefix="oft-lint-") as ws:
            for rel in ["tools/oft/__main__.py"] + base_files:
                os.makedirs(os.path.join(ws, "base", os.path.dirname(rel)), exist_ok=True)
                with open(os.path.join(ws, "base", rel), "w") as f:
                    f.write("x\n")
            for d in ("head", "runner", "bin"):
                os.mkdir(os.path.join(ws, d))
            open(os.path.join(ws, "runner", "changed.txt"), "w").close()
            with open(os.path.join(ws, "bin", "python"), "w") as f:
                f.write('#!/usr/bin/env bash\nprintf "%s\\n" "$@" "--" >> "$GITHUB_WORKSPACE/args"\n')
            os.chmod(os.path.join(ws, "bin", "python"), 0o755)
            text = step(load("pr.yml")["jobs"]["lint"], "lint, by the base's rules")["run"]
            env = dict(os.environ, GITHUB_WORKSPACE=ws, RUNNER_TEMP=os.path.join(ws, "runner"), KIND="maintainer",
                       EVENT="push", BASE="b" * 40, BASE_REF="", ROUTED="true", INTO="refs/heads/main",
                       PLANNED_TOOLS=planned_tools, GITHUB_STEP_SUMMARY=os.path.join(ws, "runner", "summary"), SINCE="",
                       PATH=os.path.join(ws, "bin") + os.pathsep + os.environ["PATH"])
            r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", text], cwd=ws, env=env,
                               capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            with open(os.path.join(ws, "args")) as f:
                return f.read().splitlines(), ws

    def test_the_ledger_is_compared_with_a_base_that_has_one_in_either_layout(self):
        """By the base's rules, and by the change's own when the base pins its tools."""
        for files, compared in (([], False), (["projects/zlib/fz/Statements.v"], False),
                                (["findings/zlib/unpatched.yaml"], True), (["projects/zlib/unpatched.yaml"], True),
                                (["projects/zlib/fz/findings/s/finding.yaml"], True)):
            for planned in ("base", "head"):
                with self.subTest(files=files, planned=planned):
                    args, ws = self.lint_args(files, planned)
                    runs = [[]]
                    for a in args:
                        if a == "--":
                            runs.append([])
                        else:
                            runs[-1].append(a)
                    runs = [r for r in runs if r]
                    self.assertEqual(len(runs), 1 if planned == "base" else 2, args)
                    for run in runs:
                        self.assertEqual(run[:6], ["-m", "oft", "--root", "head", "lint", "--changed"])
                        base = run[run.index("--base") + 1] if "--base" in run else None
                        self.assertEqual(base, os.path.join(ws, "base") if compared else None, run)


def sparse_lists(workflow):
    """Each sparse checkout's patterns in a workflow: (where, [pattern]) of each actions/checkout `sparse-checkout`
    and each `git ... sparse-checkout set` line of a step's script."""
    out = []
    for name, job in load(workflow)["jobs"].items():
        for s in job.get("steps", []):
            where = "%s: %s %s" % (workflow, name, s.get("name") or s.get("uses"))
            if "sparse-checkout" in (s.get("with") or {}):
                out.append((where, s["with"]["sparse-checkout"].split()))
            for line in (s.get("run") or "").splitlines():
                if "sparse-checkout set" in line:
                    words = shlex.split(line)
                    out.append((where, words[words.index("set") + 1:]))
    return out


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class SparseCheckoutTest(unittest.TestCase):
    """Until L3 removes the old layout's reading, every sparse checkout reads both: proofs/<p>/<h>/lib/ and
    projects/<p>/<h>/proofs/lib/ hold the proof libraries, nearly all of the tree's bytes; findings/ and
    projects/<p>/unpatched.yaml with projects/<p>/<h>/findings/ hold the findings ledger."""

    TWINS = {"!/proofs/*/*/lib/": "!/projects/*/*/proofs/lib/", "!/proofs/*/*/lib/*": "!/projects/*/*/proofs/lib/*",
             "/proofs/*/*/lib/dune": "/projects/*/*/proofs/lib/dune"}

    def test_every_sparse_pattern_that_skips_proof_libraries_skips_both_layouts(self):
        seen = set()
        for workflow in sorted(f for f in os.listdir(WORKFLOWS) if f.endswith(".yml")):
            for where, patterns in sparse_lists(workflow):
                for old, new in self.TWINS.items():
                    if old in patterns:
                        seen.add(workflow)
                        self.assertIn(new, patterns, where)
        self.assertLessEqual({"pr.yml", "release-check.yml", "images.yml"} | ENROLL_YML, seen)

    def test_pr_steps_takes_release_check_s_checkout(self):
        """pr-steps.sh --workflow release-check rehearses the plan job on the checkout release-check.yml makes: every
        proof library it leaves out, in either layout, pr-steps.sh leaves out too."""
        with open(os.path.join(REPO, "tools", "oft", "ci", "pr-steps.sh")) as f:
            m = re.search(r"printf '(/\*\\n!/[^']*)' > \"\$checkout/\.git/info/sparse-checkout\"", f.read())
        self.assertIsNotNone(m)
        rehearsed = m.group(1).encode().decode("unicode_escape").split()
        plan = next(s for s in load("release-check.yml")["jobs"]["plan"]["steps"] if "sparse-checkout" in
                    (s.get("with") or {}))
        skipped = [p for p in plan["with"]["sparse-checkout"].split() if p.startswith("!")]
        self.assertEqual(sorted(p for p in rehearsed if p.startswith("!")), sorted(skipped))
        self.assertEqual(sorted(skipped), ["!/projects/*/*/proofs/lib/", "!/proofs/*/*/lib/"])

    def test_every_sparse_checkout_of_the_base_s_findings_ledger_takes_both_layouts(self):
        """pr.yml's lint job and enroll.yml's facts job lint with --base, which reads the base's findings ledger."""
        seen = set()
        for workflow in sorted(f for f in os.listdir(WORKFLOWS) if f.endswith(".yml")):
            for where, patterns in sparse_lists(workflow):
                if "findings" in patterns or "/findings/" in patterns:
                    seen.add(workflow)
                    self.assertLessEqual({"/findings/", "/projects/*/unpatched.yaml", "/projects/*/*/findings/"},
                                         set(patterns), where)
        self.assertLessEqual({"pr.yml"} | ENROLL_YML, seen)


RELEASE_CHECK = "the tagged commit is on main, and the publishing App passed exactly it"
PUBLIC = "theorem-labs/oss-verify-proofs"


def check_run(id, name="ossv-publish/checked", app=77, conclusion="success", status="completed", sha=HEAD):
    """A check run as GitHub lists it for a commit."""
    return {"id": id, "name": name, "app": {"id": app}, "head_sha": sha, "status": status, "conclusion": conclusion,
            "output": {"title": "run %d" % id}}


def gate_run(id, **kw):
    return check_run(id, **dict({"name": "ossv-gate/publish", "app": 5447700}, **kw))


@unittest.skipUnless(shutil.which("jq"), "jq is not installed")
class ReleaseCheckRunTest(StandIn):
    """release.yml publishes a tag only when the newest check run on exactly the tagged commit, of those the
    publishing workflow makes (ossv-publish/checked, by the App PUBLISH_APP_ID names: the OSS Verify App 5447700) and
    of those the publishing gate makes (ossv-gate/publish, by App 5447700), passed.  The cases set PUBLISH_APP_ID to
    another App's id, so the two pairs stay apart; an empty one trusts only the gate's runs, so a tag with no gate run
    fails closed."""

    def setUp(self):
        super().setUp()
        self.step = step(load("release.yml")["jobs"]["publish"], RELEASE_CHECK)

    def publish(self, runs=(), app_id="77", on_main="identical", answers=None):
        """The step against a stand-in GitHub whose main has the tagged commit as `on_main` says and whose check runs
        on it are `runs`, with PUBLISH_APP_ID set to app_id: (its exit status, its output).  With answers, each call of
        the check-runs list gets the next of them in turn, the last one staying: a list of runs, or "error", a failed
        call (the step asks for the publishing App's pair first, when it asks for it, then for the gate's)."""
        with open(os.path.join(self.api, ("repos/%s/compare/main...%s" % (REPOSITORY, HEAD)).replace("/", "_")
                               + ".json"), "w") as f:
            json.dump({"status": on_main}, f)
        listed = ("repos/%s/commits/%s/check-runs" % (REPOSITORY, HEAD)).replace("/", "_")
        for name in os.listdir(self.api):   # a sequence left by an earlier call of this test
            if name.startswith(listed + "."):
                os.remove(os.path.join(self.api, name))
        for suffix, answer in ([(".json", list(runs))] if answers is None else
                               [(".%d.json" % n, a) for n, a in enumerate(answers, 1)]):
            with open(os.path.join(self.api, listed + suffix), "w") as f:
                json.dump(answer if answer == "error" else {"check_runs": answer}, f)
        env = dict(self.step["env"], GH_TOKEN="t", PUBLISH_APP_ID=app_id, GITHUB_REPOSITORY=REPOSITORY,
                   GITHUB_SHA=HEAD, RUNNER_TEMP=self.dir)
        rc, out, _ = self.run_step(self.step["run"], env)
        return rc, out

    def test_an_api_error_on_either_pair_fails_closed(self):
        """A failed call is no answer.  With the publishing App's call failing, the gate's older pass must not decide:
        a newer ossv-publish/checked run may have withdrawn it.  A failed gate call fails as well, with or without the
        variable."""
        for app_id, answers in (("77", ["error", [gate_run(10)]]), ("77", [[check_run(10)], "error"]),
                                ("", ["error"])):
            with self.subTest(app_id=app_id, answers=answers):
                rc, out = self.publish(app_id=app_id, answers=answers)
                self.assertEqual(rc, 1, out)
                self.assertIn("HTTP 502", out)
                self.assertNotIn("the publishing check passed", out)

    def test_a_publish_app_id_that_is_not_a_number_is_refused(self):
        """The variable goes into the API's query: anything but an App id is refused before any check run is read."""
        for app_id in ("abc", "77 ", "77&app_id=5447700", "-1"):
            with self.subTest(app_id=app_id):
                rc, out = self.publish([check_run(10), gate_run(11)], app_id=app_id)
                self.assertEqual(rc, 1, out)
                self.assertIn("not an App id", out)
                self.assertNotIn("the publishing check passed", out)

    def test_a_passing_run_of_the_publishing_app_publishes(self):
        rc, out = self.publish([check_run(10)])
        self.assertEqual(rc, 0, out)
        self.assertIn("ossv-publish/checked check run 10 (App 77)", out)

    def test_a_passing_run_of_the_gate_publishes_with_or_without_the_variable(self):
        for app_id in ("77", ""):
            with self.subTest(app_id=app_id):
                rc, out = self.publish([gate_run(10)], app_id=app_id)
                self.assertEqual(rc, 0, out)
                self.assertIn("ossv-gate/publish check run 10 (App 5447700)", out)

    def test_with_the_variable_unset_and_no_gate_run_it_fails_closed(self):
        """No App id to trust: a run named ossv-publish/checked counts for nothing, whichever App made it."""
        for runs in ([], [check_run(10)], [check_run(10, app=5447700)]):
            with self.subTest(runs=runs):
                rc, out = self.publish(runs, app_id="")
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::", out)
                self.assertIn("PUBLISH_APP_ID is not set", out)

    def test_a_run_of_another_name_app_or_commit_does_not_count(self):
        for runs in ([check_run(10, app=78)], [check_run(10, name="ossv-publish/other")],
                     [gate_run(10, app=77)], [check_run(10, sha="d" * 40)], [gate_run(10, sha="d" * 40)]):
            with self.subTest(runs=runs):
                rc, out = self.publish(runs)
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::", out)

    def test_the_newest_run_of_either_decides(self):
        """Either side can withdraw a pass by creating a newer run; one still running is no pass."""
        for runs, want in (([gate_run(10), check_run(11, conclusion="failure")], 1),
                           ([check_run(10, conclusion="failure"), gate_run(11)], 0),
                           ([check_run(12), gate_run(11, conclusion="failure")], 0),
                           ([check_run(10), check_run(12, conclusion=None, status="in_progress")], 1),
                           ([gate_run(10), gate_run(9, conclusion="failure")], 0)):
            with self.subTest(runs=runs):
                rc, out = self.publish(runs)
                self.assertEqual(rc, want, out)

    def test_a_commit_that_is_not_on_main_is_refused(self):
        for status in ("ahead", "diverged"):
            with self.subTest(status=status):
                rc, out = self.publish([check_run(10)], on_main=status)
                self.assertEqual(rc, 1, out)
                self.assertIn("is not on main", out)


@unittest.skipUnless(shutil.which("jq"), "jq is not installed")
class ReleaseLatestTest(unittest.TestCase):
    """GitHub makes a release "Latest" when it is published unless it is told otherwise: make_latest "Defaults to true
    for newly published releases", on create and on update (docs.github.com/en/rest/releases/releases, "Create a
    release" and "Update a release").  So release.yml says it for each tag: v<release> is Latest unless a published
    full release (not -src, not a release candidate) has a higher version, as when a heal tags v<rel> just before the
    same run tags v<rel+1>, or a failed run is re-run after a newer release; v<release>-src (the source files, which
    may be published second) never is; and a release candidate, a pre-release, never is."""

    CHANGELOG = "".join("## %s (2026-11-01)\n\nnotes of %s\n\n" % (r, r)
                        for r in ("2026.11.1", "2026.11.1-rc.1", "2026.11.0", "2026.11.0-rc.1", "2026.10.10"))
    GH = ('#!/bin/sh\ncase "$1 $2" in\n'
          # the published releases, as the step asks for them (PUBLISHED: one tag a line; LIST_RC: the call's exit)
          '  "release list") shift; printf "%s\\n" "$*" >> "$GH_LOG"; printf "%s" "$PUBLISHED"\n'
          '    exit "${LIST_RC:-0}" ;;\n'
          '  release*) shift; printf "%s\\n" "$*" >> "$GH_LOG" ;;\n'
          # the release list the step checks the draft's assets against once more, just before it publishes
          "  api*) printf '[{\"tag_name\": \"%s\", \"assets\": "
          "[{\"name\": \"a.tar.zst\", \"digest\": \"sha256:aa\"}]}]\\n' \"$GITHUB_REF_NAME\" ;;\n"
          "  *) exit 9 ;;\nesac\n")

    def run_publish(self, tag, draft, published="", list_rc=0):
        """release.yml's publishing step for tag, a draft when draft (else a release with no file, which the step
        creates), with `published` the tags of the published releases gh lists: (its exit, its output, each `gh
        release` command it ran, as words)."""
        s = step(load("release.yml")["jobs"]["publish"], "release notes from CHANGELOG.md, and publish")
        text = s["run"].replace("${{ steps.draft.outputs.exists }}", "true" if draft else "false")
        self.assertNotIn("${{", text)
        with tempfile.TemporaryDirectory(prefix="oft-latest-") as d:
            for name, data in (("CHANGELOG.md", self.CHANGELOG), ("want.txt", "a.tar.zst sha256:aa\n"),
                               ("gh", self.GH)):
                with open(os.path.join(d, name), "w") as f:
                    f.write(data)
            os.chmod(os.path.join(d, "gh"), 0o755)
            log = os.path.join(d, "gh.log")
            env = dict(os.environ, PATH=d + os.pathsep + os.environ["PATH"], RUNNER_TEMP=d, GITHUB_REF_NAME=tag,
                       GITHUB_REPOSITORY=REPOSITORY, GH_TOKEN="t", GH_LOG=log, PUBLISHED=published,
                       LIST_RC=str(list_rc))
            r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", text], cwd=d, env=env,
                               capture_output=True, text=True)
            ran = []
            if os.path.exists(log):
                with open(log) as f:
                    ran = [line.split() for line in f.read().splitlines()]
        return r.returncode, r.stdout + r.stderr, ran

    def publish(self, tag, draft, published=""):
        """The one command that publishes tag (edit or create), as words, after the step passed."""
        rc, out, ran = self.run_publish(tag, draft, published)
        self.assertEqual(rc, 0, out)
        made = [words for words in ran if words[0] in ("edit", "create")]
        self.assertEqual(len(made), 1, ran)
        return made[0]

    def latest(self, words):
        return [w for w in words if w.startswith("--latest")]

    def test_only_v_release_is_latest(self):
        for tag, draft, verb, latest in (("v2026.11.0", True, "edit", "--latest=true"),
                                         ("v2026.11.0-src", True, "edit", "--latest=false"),
                                         ("v2026.11.0-rc.1", True, "edit", "--latest=false"),
                                         ("v2026.11.0-rc.1-src", True, "edit", "--latest=false"),
                                         ("v2026.11.1", False, "create", "--latest=true"),
                                         ("v2026.11.1-rc.1", False, "create", "--latest=false")):
            with self.subTest(tag=tag, draft=draft):
                words = self.publish(tag, draft)
                self.assertEqual(words[:2], [verb, tag], words)
                self.assertEqual(self.latest(words), [latest], words)
                if draft:
                    self.assertIn("--draft=false", words)
                elif "-rc." in tag:
                    self.assertIn("--prerelease", words)

    def test_an_older_release_published_after_a_newer_one_is_not_latest(self):
        """Versions compare as versions (sort -V: 2026.10.10 is newer than 2026.10.9).  A -src release, a release
        candidate and any release whose tag is not v<version> never count as newer."""
        for tag, published, latest in (
                ("v2026.11.0", "v2026.11.1\nv2026.11.1-src\nv2026.10.10\n", "--latest=false"),   # a heal, late
                ("v2026.11.1", "v2026.11.0\nv2026.11.0-src\nv2026.10.10\n", "--latest=true"),    # the newest
                ("v2026.10.10", "v2026.10.9\nv2026.10.9-src\n", "--latest=true"),
                ("v2026.11.0", "v2026.11.1-src\nv2026.10.10\n", "--latest=true"),   # the newer one's -src only
                ("v2026.11.1", "v2026.11.1-src\n", "--latest=true"),                # its own -src, published first
                ("v2026.11.1", "v2026.12.0-rc.1\nfindings-zlib\nsources-v9\n", "--latest=true")):
            with self.subTest(tag=tag, published=published):
                for draft in (True, False):
                    self.assertEqual(self.latest(self.publish(tag, draft, published)), [latest])

    def test_the_published_releases_are_listed_without_drafts_and_pre_releases(self):
        _rc, out, ran = self.run_publish("v2026.11.1", True, "v2026.11.0\n")
        listed = [words for words in ran if words[0] == "list"]
        self.assertEqual(len(listed), 1, ran)
        self.assertLessEqual({"--exclude-drafts", "--exclude-pre-releases"}, set(listed[0]), listed)
        # a -src tag and a release candidate are never Latest: no list is read for them
        for tag in ("v2026.11.1-src", "v2026.11.0-rc.1"):
            with self.subTest(tag=tag):
                _rc, _out, ran = self.run_publish(tag, True, "v2026.11.0\n")
                self.assertEqual([words for words in ran if words[0] == "list"], [], ran)

    def test_a_failed_list_of_the_published_releases_fails_the_step(self):
        """Fail closed: without the list, whether a newer release is published is unknown, and nothing is published."""
        for draft in (True, False):
            with self.subTest(draft=draft):
                rc, out, ran = self.run_publish("v2026.11.1", draft, "", list_rc=1)
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::", out)
                self.assertEqual([words for words in ran if words[0] in ("edit", "create")], [], ran)


class ReleaseSweepTest(unittest.TestCase):
    """release.yml's sweep runs weekly.yml on the units of the projects with a file attached to this release
    (v<release> or v<release>-src), against the files as published; a release that attaches no file starts none."""

    def units(self, t, tag):
        """release.yml's ready job, run as GitHub runs it in a checkout of t at `tag`, with every release published:
        its `published` step, which lists what the facts attach ($RUNNER_TEMP/pinned.txt), then its units step, which
        reads that list.  The units it wrote."""
        steps = load("release.yml")["jobs"]["ready"]["steps"]
        ids = [s.get("id") for s in steps]
        self.assertLess(ids.index("published"), ids.index("units"))
        self.assertNotIn("oft fetch", steps[ids.index("units")]["run"], "the list is read once, by `published`")
        shutil.copy(os.path.join(REPO, "oft"), t.path("oft"))
        if not os.path.lexists(t.path("tools")):
            os.symlink(os.path.join(REPO, "tools"), t.path("tools"))
        with tempfile.TemporaryDirectory(prefix="oft-sweep-") as d:
            for name, text in (("python", 'exec "%s" "$@"' % sys.executable), ("gh", "echo false")):  # isDraft
                with open(os.path.join(d, name), "w") as f:
                    f.write("#!/bin/sh\n%s\n" % text)
                os.chmod(os.path.join(d, name), 0o755)
            out = os.path.join(d, "output")
            env = dict(os.environ, PATH=d + os.pathsep + os.environ["PATH"], RUNNER_TEMP=d, GITHUB_OUTPUT=out,
                       GITHUB_REF_NAME=tag, PYTHONDONTWRITEBYTECODE="1", GH_TOKEN="t")
            for at in (ids.index("published"), ids.index("units")):
                r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", steps[at]["run"]],
                                   cwd=t.root, env=env, capture_output=True, text=True)
                self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            with open(out) as f:
                wrote = dict(line.rstrip("\n").split("=", 1) for line in f)
        self.assertEqual(wrote["all"], "true")
        return wrote["units"]

    def test_the_units_are_those_of_the_projects_a_release_attaches_a_file_to(self):
        with tree() as t:
            self.assertEqual(self.units(t, "v2026.11.0"),
                             "json/fuzzer-parse_bjdata zlib/api-driver zlib/checksum_fuzzer")
        # json's new archive in v2026.12.0, its source assets and the new recipe in v2026.12.0-src; zlib's stay put
        with tree() as t:
            later_release(t)
            for tag in ("v2026.12.0", "v2026.12.0-src"):
                with self.subTest(tag=tag):
                    self.assertEqual(self.units(t, tag), "json/fuzzer-parse_bjdata")

    def test_either_tag_of_a_release_sweeps_the_projects_of_both(self):
        """v<release>-src publishes last as often as first: zlib's rebuilt archive is in v2026.12.0, and v2026.12.0-src
        holds only the recipe, which is no project's file."""
        with tree() as t:
            recipe_only_rebuild(t, record=False)
            for tag in ("v2026.12.0", "v2026.12.0-src"):
                with self.subTest(tag=tag):
                    self.assertEqual(self.units(t, tag), "zlib/api-driver zlib/checksum_fuzzer")

    def test_a_release_that_attaches_no_file_has_no_units_and_no_sweep(self):
        """A release of proofs and documents only (docs/versioning.md): weekly.yml's Monday run checks them again."""
        with tree() as t:
            self.assertEqual(self.units(t, "v2026.11.1"), "")



@unittest.skipUnless(shutil.which("jq"), "jq is not installed")
class PublicPushTest(unittest.TestCase):
    """On theorem-labs/oss-verify-proofs, release-check.yml checks each push to main on that commit alone, the parts
    it changes, and pr.yml's run of the same push would check the same parts again.  So there pr.yml's plan step
    plans no check part for a push, and says why; lint, tests and controls still run in full (the reach step's merge
    path).  Every other repository and event is planned as before."""

    def plan_step(self, repository, event):
        """pr.yml's plan step, run in an empty workspace: (its exit, its output, what it wrote to GITHUB_OUTPUT, its
        summary, the path of its plan.json or None, in a directory that lives as long as the test)."""
        d = tempfile.mkdtemp(prefix="oft-public-push-")
        self.addCleanup(shutil.rmtree, d)
        out, summary, plan = (os.path.join(d, n) for n in ("output", "summary", "plan.json"))
        env = dict(os.environ, GITHUB_REPOSITORY=repository, GITHUB_EVENT_NAME=event, RUNNER_TEMP=d,
                   GITHUB_OUTPUT=out, GITHUB_STEP_SUMMARY=summary, BASE="b" * 40, KIND="release")
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c",
                            step(load("pr.yml")["jobs"]["plan"], "plan")["run"]],
                           cwd=d, env=env, capture_output=True, text=True)
        texts = []
        for p in (out, summary):
            with open(p) if os.path.exists(p) else open(os.devnull) as f:
                texts.append(f.read())
        return (r.returncode, r.stdout + r.stderr, texts[0], texts[1], plan if os.path.exists(plan) else None)

    def test_a_public_push_plans_no_check_in_pr_yml(self):
        rc, output, wrote, summary, plan = self.plan_step(PUBLIC, "push")
        self.assertEqual(rc, 0, output)
        # every answer the required job reads: no unit, no deferred check, and the base's tools
        self.assertEqual(wrote, "units=0\ndeferred=false\ntools=base\n")
        self.assertIn("release-check.yml checks a push to main", summary)
        with open(plan) as f:
            got = json.load(f)
        self.assertEqual((got["parts"], got["units"], got["check_units"], got["jobs"]), ([], [], [], []))
        # the check job runs only when the plan names a unit (required then wants it skipped)
        self.assertIn("needs.plan.outputs.units != '0'", " ".join(load("pr.yml")["jobs"]["check"]["if"].split()))
        # and the drafts step, which writes the plan output the check matrix reads, lists no group and no draft
        action = yamlio.load_file(os.path.join(REPO, ".github", "actions", "plan-drafts", "action.yml"))
        drafts = os.path.join(os.path.dirname(plan), "drafts-output")
        script = action["runs"]["steps"][0]["run"]
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", script],
                           env=dict(os.environ, PLAN=plan, GITHUB_OUTPUT=drafts), capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        with open(drafts) as f:
            self.assertEqual(f.read(), "plan=[]\ndraft_legs=[]\n")

    def test_every_other_repository_and_event_is_planned_as_before(self):
        """Here the step goes on to its next answer: with no release.yaml in head/ (no facts yet), no harness.  A push
        in any other repository (the stand-in's here; the internal repository is one) is planned as before."""
        for repository, event in ((REPOSITORY, "push"), (PUBLIC, "pull_request"),
                                  (PUBLIC, "merge_group")):
            with self.subTest(repository=repository, event=event):
                rc, output, wrote, summary, plan = self.plan_step(repository, event)
                self.assertEqual((rc, wrote, plan), (0, "plan=[]\nunits=0\ndeferred=false\ntools=base\n", None),
                                 output)
                self.assertNotIn("release-check.yml", output + summary)


PR_STEPS = os.path.join(REPO, "tools", "oft", "ci", "pr-steps.sh")
# A workflow with the steps pr-steps.sh's STEPS table names, each one line of bash: the plan job counts the units the
# head's file `units` holds, and check, which pr-steps.sh never runs, starts when that count is not 0, as pr.yml's does.
FIXTURE_PR_YML = """\
on: pull_request
env:
  PYTHONDONTWRITEBYTECODE: "1"
  KIND: ${{ github.event_name }}
jobs:
  plan:
    if: ${{ !cancelled() }}
    outputs:
      base: ${{ steps.base.outputs.base }}
      routed: ${{ steps.base.outputs.routed }}
      units: ${{ steps.plan.outputs.units }}
      tools: ${{ steps.plan.outputs.tools }}
      tests: ${{ steps.reach.outputs.tests }}
      repository_lint: ${{ steps.reach.outputs.repository_lint }}
      controls: ${{ steps.reach.outputs.controls }}
      stream_tools: ${{ steps.reach.outputs.stream_tools }}
      farm_tests: ${{ steps.reach.outputs.farm_tests }}
      checked_elsewhere: ${{ steps.elsewhere.outputs.checked_elsewhere }}
      checked_elsewhere_note: ${{ steps.elsewhere.outputs.checked_elsewhere_note }}
    steps:
      - id: base
        run: '{ echo "base=$(git -C head rev-parse HEAD^1)"; echo routed=true; } >> "$GITHUB_OUTPUT"'
      - id: plan
        env:
          BASE: ${{ steps.base.outputs.base }}
        run: '[ -n "$BASE" ] && { echo "units=$(cat head/units)"; echo tools=base; } >> "$GITHUB_OUTPUT"'
      - name: the parts a check of record outside this run checked
        id: elsewhere
        env:
          DEFERRED: ${{ steps.plan.outputs.deferred }}
        run: 'echo "checked_elsewhere=${DEFERRED:-false}" >> "$GITHUB_OUTPUT"'
      - id: reach
        run: >-
          { echo tests=true; echo repository_lint=false; echo controls=false;
          echo "stream_tools=$(cat head/stream 2>/dev/null || echo false)";
          echo "farm_tests=$(cat head/farm 2>/dev/null || echo false)"; } >> "$GITHUB_OUTPUT"
  lint:
    needs: [plan]
    if: ${{ !cancelled() }}
    steps:
      - id: base
        env:
          PLAN_BASE: ${{ needs.plan.outputs.base }}
        run: '[ -n "$PLAN_BASE" ] && { echo "base=$PLAN_BASE"; echo routed=true; } >> "$GITHUB_OUTPUT"'
      - name: the findings ledger over the change's history, by the base's rules
        run: "true"
      - name: lint, by the base's rules
        run: "true"
      - name: generated files equal their rendering
        run: "true"
  tests:
    needs: [plan, lint]
    if: >-
      ${{ !cancelled() && needs.plan.result == 'success' && needs.lint.result == 'success'
      && needs.plan.outputs.tests == 'true' }}
    steps:
      - name: the tools' own tests, at this change, one process per test class
        working-directory: head
        run: echo "ran 1 test(s) in 1 class(es) over 1 process(es) in 0.0 s"
  check:
    needs: [plan, lint]
    if: ${{ !cancelled() && needs.plan.result == 'success' && needs.plan.outputs.units != '0' }}
    steps:
      - run: "false"
  stream_tools:
    needs: [plan, lint]
    if: >-
      ${{ !cancelled() && needs.plan.result == 'success' && needs.lint.result == 'success'
      && needs.plan.outputs.stream_tools == 'true' }}
    steps:
      - run: "false"
  rekey:
    needs: [plan, lint]
    if: >-
      ${{ !cancelled() && needs.plan.result == 'success' && needs.lint.result == 'success'
      && (github.event_name == 'pull_request' || github.event_name == 'merge_group') }}
    steps:
      - id: base
        env:
          BASE: ${{ needs.plan.outputs.base }}
        run: '[ -n "$BASE" ]'
      - id: rekey
        env:
          BASE: ${{ needs.plan.outputs.base }}
          BASE_REF: ${{ github.base_ref }}
          WINDOW: ${{ vars.OSSV_REKEY_WINDOW }}
        run: '[ -n "$BASE" ] && [ "$BASE_REF" = main ] && echo "window=$WINDOW"'
  farm_tests:
    needs: [plan, lint]
    if: >-
      ${{ !cancelled() && needs.plan.result == 'success' && needs.lint.result == 'success'
      && needs.plan.outputs.farm_tests == 'true' }}
    strategy:
      matrix:
        leg: [0, 1]
    steps:
      - run: "false"
  required:
    needs: [plan, lint, tests, check, stream_tools, rekey, farm_tests]
    if: always()
    steps:
      - name: every job green, and something checked when the plan named anything
        if: needs.plan.outputs.tools != 'none'
        env:
          UNITS: ${{ needs.plan.outputs.units }}
          TESTS_RESULT: ${{ needs.tests.result }}
          CHECK_RESULT: ${{ needs.check.result }}
          CHECKED_ELSEWHERE: ${{ needs.plan.outputs.checked_elsewhere }}
          CHECKED_ELSEWHERE_NOTE: ${{ needs.plan.outputs.checked_elsewhere_note }}
          STREAM_TOOLS: ${{ needs.plan.outputs.stream_tools }}
          STREAM_TOOLS_RESULT: ${{ needs.stream_tools.result }}
          FARM_TESTS: ${{ needs.plan.outputs.farm_tests }}
          FARM_TESTS_RESULT: ${{ needs.farm_tests.result }}
        run: >-
          [ "$UNITS" = 0 ] && [ "$TESTS_RESULT" = success ] && [ "$CHECK_RESULT" = skipped ]
          && [ "$STREAM_TOOLS" = false ] && [ "$STREAM_TOOLS_RESULT" = skipped ]
          && [ "$FARM_TESTS" = false ] && [ "$FARM_TESTS_RESULT" = skipped ]
"""
FIXTURE_REQUIREMENTS = "# the fixture's tools need nothing\n"


def run(args, **env):
    """A command with this environment but REPO and WORK, and `env` added."""
    full = {k: v for k, v in os.environ.items() if k not in ("REPO", "WORK")}
    full.update(env)
    return subprocess.run(args, env=full, capture_output=True, text=True)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class PrStepsTest(unittest.TestCase):
    """tools/oft/ci/pr-steps.sh runs the steps of pr.yml (and of release-check.yml's plan job) that its STEPS table
    names, each taken from the workflow by its job and its step id or name, so a step renamed here would leave the
    rehearsal running nothing; it checks out the merge commit GitHub builds for a pull request, the base its first
    parent and the head its second, which the base step reads; and it starts each job as the job's `if:` says, reads a
    job's outputs through its `outputs:` block, and fails when GitHub would start a job it does not run (check)."""

    def commit(self, d, files, message):
        for rel, text in files.items():
            os.makedirs(os.path.dirname(os.path.join(d, rel)) or d, exist_ok=True)
            with open(os.path.join(d, rel), "w") as f:
                f.write(text)
        git(d, "add", "-A")
        git(d, "commit", "-qm", message)
        return git(d, "rev-parse", "HEAD")

    def fixture(self, d, workflow=FIXTURE_PR_YML):
        """A repository whose base commit has `workflow` as its pr.yml, and the venv pr-steps.sh would build for its
        requirements already in VENVS (named as the script names it, by the requirements' SHA-256): this test's own
        Python, which has PyYAML, so that no run needs the network."""
        repo = os.path.join(d, "repo")
        os.mkdir(repo)
        git(repo, "init", "-q")
        base = self.commit(repo, {".github/workflows/pr.yml": workflow, "tools/oft/requirements.txt": FIXTURE_REQUIREMENTS,
                                  "units": "0\n"}, "base")
        venv = os.path.join(d, "venvs",
                            "py3.12-" + hashlib.sha256(FIXTURE_REQUIREMENTS.encode()).hexdigest()[:16])
        os.makedirs(os.path.join(venv, "bin"))
        with open(os.path.join(venv, "bin", "python"), "w") as f:
            f.write("#!/bin/sh\nexec %s \"$@\"\n" % shlex.quote(sys.executable))
        os.chmod(os.path.join(venv, "bin", "python"), 0o755)
        open(os.path.join(venv, ".complete"), "w").close()
        return repo, base

    def rehearse(self, d, repo, head, base, **env):
        """pr-steps.sh's run of HEAD into BASE: its exit status, OUT/summary.txt, and its output."""
        out = os.path.join(d, "out")
        r = run(["bash", PR_STEPS, head, base, "maintainer", out], REPO=repo, WORK=os.path.join(d, "work"),
                VENVS=os.path.join(d, "venvs"), GITHUB_REPOSITORY="acme/proofs", **env)
        summary = ""
        if os.path.exists(os.path.join(out, "summary.txt")):
            with open(os.path.join(out, "summary.txt")) as f:
                summary = f.read()
        return r.returncode, summary, r.stdout + r.stderr

    def rows(self):
        """The STEPS here-document at the top of the script: one row per step, workflow<TAB>job<TAB>short
        name<TAB>step id or name."""
        self.assertTrue(os.path.isfile(PR_STEPS), "no " + PR_STEPS)
        with open(PR_STEPS) as f:
            lines = f.read().splitlines()
        start = [i for i, line in enumerate(lines) if line.endswith("<<'STEPS'")]
        self.assertEqual(len(start), 1, "one STEPS here-document")
        end = lines.index("STEPS", start[0] + 1)
        rows = [tuple(line.split("\t")) for line in lines[start[0] + 1:end]]
        for row in rows:
            self.assertEqual(len(row), 4, row)
        return rows

    def test_every_step_it_runs_is_a_step_of_this_repository_s_pr_yml(self):
        rows = [row for row in self.rows() if row[0] == "pr.yml"]
        jobs = load("pr.yml")["jobs"]
        missing = []
        for _workflow, job, _short, key in rows:
            found = [s for s in jobs.get(job, {}).get("steps", []) if key in (s.get("id"), s.get("name"))]
            if len(found) != 1 or "run" not in found[0]:
                missing.append((job, key))
        self.assertEqual(missing, [])
        self.assertEqual(sorted((job, short) for _workflow, job, short, _key in rows),
                         sorted([("plan", "base"), ("plan", "plan"), ("plan", "elsewhere"), ("plan", "reach"),
                                 ("lint", "base"), ("lint", "ledger"), ("lint", "lint"), ("lint", "generate"),
                                 ("tests", "tests"), ("rekey", "base"), ("rekey", "rekey"), ("required", "collect")]))

    @unittest.skipUnless(shutil.which("git"), "git is not installed")
    def test_the_merge_ref_has_the_base_then_the_head_as_parents(self):
        self.assertTrue(os.path.isfile(PR_STEPS), "no " + PR_STEPS)
        with tempfile.TemporaryDirectory(prefix="oft-pr-steps-") as d:
            git(d, "init", "-q")
            root = self.commit(d, {"root.txt": "root\n"}, "root")
            head = self.commit(d, {"head.txt": "head\n"}, "head")
            git(d, "checkout", "-q", "-b", "other", root)
            # BASE has a commit HEAD lacks, so the merge's tree is neither's
            base = self.commit(d, {"base.txt": "base\n"}, "base")
            r = run(["bash", PR_STEPS, "--merge-ref-only", head, base], REPO=d)
            self.assertEqual(r.returncode, 0, r.stderr)
            merge = r.stdout.strip()
            parents = git(d, "log", "-1", "--format=%P", merge).split()
            self.assertEqual(parents, [base, head])
            self.assertEqual(git(d, "ls-tree", "--name-only", merge).split(), ["base.txt", "head.txt", "root.txt"])
            # the same HEAD and BASE give the same commit
            self.assertEqual(run(["bash", PR_STEPS, "--merge-ref-only", head, base], REPO=d).stdout.strip(), merge)
            # a push checks out the pushed commit itself, with BASE as the event's `before`
            r = run(["bash", PR_STEPS, "--merge-ref-only", "--event", "push", head, base], REPO=d)
            self.assertEqual((r.returncode, r.stdout.strip()), (0, head), r.stderr)
            # a HEAD that conflicts with BASE has no merge commit, as GitHub builds none
            conflict = self.commit(d, {"head.txt": "another head\n"}, "conflict")
            r = run(["bash", PR_STEPS, "--merge-ref-only", head, conflict], REPO=d)
            self.assertEqual((r.returncode, r.stdout), (1, ""), r.stderr)
            self.assertIn("conflicts with BASE", r.stderr)

    def test_a_usage_error_exits_2(self):
        self.assertEqual(run(["bash", PR_STEPS]).returncode, 2)
        for args in (["--event", "edited", "h", "b", "maintainer", "out"], ["h", "b", "owner", "out"],
                     ["--workflow", "release-check", "h", "b", "release", "out"], ["--merge-ref-only", "h"]):
            with self.subTest(args=args):
                self.assertEqual(run(["bash", PR_STEPS, *args], REPO="r", WORK="w").returncode, 2)

    def test_the_release_check_step_it_runs_is_in_release_check_yml(self):
        rows = [row for row in self.rows() if row[0] == "release-check.yml"]
        self.assertEqual([(job, short) for _workflow, job, short, _key in rows], [("plan", "plan")])
        wf = load("release-check.yml")
        steps = wf["jobs"]["plan"]["steps"]
        self.assertEqual(len([s for s in steps if rows[0][3] in (s.get("id"), s.get("name")) and "run" in s]), 1)
        self.assertIn("plan", [s.get("name") for s in wf["jobs"]["plan"]["steps"]])

    def test_it_is_no_part_of_the_checker(self):
        """A check job never opens it, so a change to it changes no content key (keys.NOT_THE_CHECKER); the scripts
        beside it that a check runs stay in the checker."""
        self.assertTrue(keys.not_the_checker("tools/oft/ci/pr-steps.sh"))
        for name in ("ci/check-units.sh", "ci/cache-key.sh", "ci/pr-steps.sh~", "ci/pr-stepsXsh"):
            self.assertFalse(keys.not_the_checker("tools/oft/" + name), name)

    @unittest.skipUnless(shutil.which("git") and shutil.which("flock"), "git or flock is not installed")
    def test_a_job_github_would_start_and_it_does_not_run_fails_the_rehearsal(self):
        """With units planned, the fixture's check job starts on GitHub, and pr-steps.sh does not run it: the
        rehearsal fails and gives required no verdict, rather than judge required with check skipped.  With none, check
        stays skipped, and required passes on what the rehearsed jobs gave."""
        for units, code in (("3", 1), ("0", 0)):
            with self.subTest(units=units), tempfile.TemporaryDirectory(prefix="oft-pr-steps-") as d:
                repo, base = self.fixture(d)
                head = self.commit(repo, {"units": units + "\n", "change.txt": "c\n"}, "the change")
                rc, summary, out = self.rehearse(d, repo, head, base)
                self.assertEqual(rc, code, summary + out)
                lines = [re.sub(r" \(\d+ s\)$", "", line) for line in summary.splitlines()]
                for step in ("plan/base", "plan/plan", "plan/elsewhere", "plan/reach", "lint/base", "lint/ledger",
                             "lint/lint", "lint/generate", "tests/tests", "rekey/base", "rekey/rekey"):
                    self.assertIn("PASS " + step, lines)
                self.assertIn("plan: tools=base checked_elsewhere=false units=%s" % units, lines)
                self.assertIn("note: tests: ran 1 test(s) in 1 class(es) over 1 process(es) in 0.0 s", lines)
                if units == "3":
                    self.assertIn("FAIL(-) check/not-run (GitHub starts it: units=3)", lines)
                    self.assertIn("SKIP required/collect (GitHub starts a job this script does not run (above): no "
                                  "verdict to rehearse)", lines)
                else:
                    self.assertIn("PASS required/collect", lines)
                    self.assertEqual([line for line in lines if "FAIL" in line], [])
                # the run removed its workspace
                self.assertEqual(sorted(os.listdir(os.path.join(d, "work"))), ["run.lock"])

    @unittest.skipUnless(shutil.which("git") and shutil.which("flock"), "git or flock is not installed")
    def test_the_rekey_job_takes_the_plan_s_base_and_the_window_from_the_caller(self):
        """The rekey job's steps (rule D11) get the plan job's base, the pull request's base branch and, for the
        repository variable OSSV_REKEY_WINDOW, the caller's variable of that name: unset, a closed window, as the
        repository variable's absence is."""
        for window in (None, "open"):
            with self.subTest(window=window), tempfile.TemporaryDirectory(prefix="oft-pr-steps-") as d:
                repo, base = self.fixture(d)
                head = self.commit(repo, {"change.txt": "c\n"}, "the change")
                env = {} if window is None else {"OSSV_REKEY_WINDOW": window}
                rc, summary, out = self.rehearse(d, repo, head, base, **env)
                self.assertEqual(rc, 0, summary + out)
                with open(os.path.join(d, "out", "rekey-rekey.log")) as f:
                    self.assertEqual(f.read(), "window=%s\n" % (window or ""))

    @unittest.skipUnless(shutil.which("git") and shutil.which("flock"), "git or flock is not installed")
    def test_a_stream_tools_job_github_would_start_fails_the_rehearsal(self):
        """With dev/stream/ changed the plan answers stream_tools=true, GitHub starts the stream_tools job, and
        pr-steps.sh does not run it: the rehearsal fails and gives required no verdict, as for check.  With false
        (every case above), required reads the plan's answer and the job's result, false and skipped, and passes
        (the fixture's required step requires exactly that pair)."""
        with tempfile.TemporaryDirectory(prefix="oft-pr-steps-") as d:
            repo, base = self.fixture(d)
            head = self.commit(repo, {"units": "0\n", "stream": "true\n"}, "a change under dev/stream/")
            rc, summary, out = self.rehearse(d, repo, head, base)
            self.assertEqual(rc, 1, summary + out)
            lines = [re.sub(r" \(\d+ s\)$", "", line) for line in summary.splitlines()]
            self.assertIn("FAIL(-) stream_tools/not-run (GitHub starts it: dev/stream/ changed)", lines)
            self.assertIn("SKIP required/collect (GitHub starts a job this script does not run (above): no "
                          "verdict to rehearse)", lines)

    @unittest.skipUnless(shutil.which("git") and shutil.which("flock"), "git or flock is not installed")
    def test_a_farm_tests_job_github_would_start_fails_the_rehearsal(self):
        """With a file the farm runner's tests read changed the plan answers farm_tests=true, GitHub starts the
        farm_tests legs, and pr-steps.sh runs none of them: the rehearsal fails and gives required no verdict, as for
        stream_tools.  With false (every other case here), required reads the plan's answer and the job's result,
        false and skipped, and passes (the fixture's required step requires exactly that pair)."""
        with tempfile.TemporaryDirectory(prefix="oft-pr-steps-") as d:
            repo, base = self.fixture(d)
            head = self.commit(repo, {"units": "0\n", "farm": "true\n"}, "a change to bin/ossv-job-farm")
            rc, summary, out = self.rehearse(d, repo, head, base)
            self.assertEqual(rc, 1, summary + out)
            lines = [re.sub(r" \(\d+ s\)$", "", line) for line in summary.splitlines()]
            self.assertIn("FAIL(-) farm_tests/not-run (GitHub starts it: a file the farm runner's tests read, or "
                          "their job, changed)", lines)
            self.assertNotIn("FAIL(-) stream_tools/not-run (GitHub starts it: dev/stream/ changed)", lines)
            self.assertIn("SKIP required/collect (GitHub starts a job this script does not run (above): no "
                          "verdict to rehearse)", lines)

    @unittest.skipUnless(shutil.which("git") and shutil.which("flock"), "git or flock is not installed")
    def test_a_job_s_output_is_read_through_its_outputs_block(self):
        """The plan step writes units=0, but the plan job's outputs: block reads another name: GitHub then gives
        needs.plan.outputs.units as '', check's `'' != '0'` starts it, and the rehearsal says so."""
        with tempfile.TemporaryDirectory(prefix="oft-pr-steps-") as d:
            repo, base = self.fixture(d, FIXTURE_PR_YML.replace("${{ steps.plan.outputs.units }}",
                                                                "${{ steps.plan.outputs.count }}"))
            head = self.commit(repo, {"change.txt": "c\n"}, "the change")
            rc, summary, out = self.rehearse(d, repo, head, base)
            self.assertEqual(rc, 1, summary + out)
            self.assertIn("plan: tools=base checked_elsewhere=false units=-", summary.splitlines())
            self.assertIn("FAIL(-) check/not-run (GitHub starts it: units=-)", summary.splitlines())

    @unittest.skipUnless(shutil.which("git") and shutil.which("flock"), "git or flock is not installed")
    def test_what_it_cannot_read_stops_it_before_the_first_step(self):
        """An `if:` that reads what pr-steps.sh does not know, a job output that is not a step's output, and a step
        script with a `${{ }}` in it, which GitHub fills in and pr-steps.sh would not."""
        for old, new, said in (
                ("if: always()", "if: always() && github.event.pull_request.draft == false",
                 "github.event.pull_request.draft"),
                ("${{ steps.plan.outputs.tools }}", "${{ steps.plan.outputs.tools || 'base' }}", "job plan's output tools"),
                ("run: '[ -n \"$PLAN_BASE\" ]", "run: '[ -n \"${{ needs.plan.outputs.base }}\" ]", "holds ${{ }}")):
            with self.subTest(said=said), tempfile.TemporaryDirectory(prefix="oft-pr-steps-") as d:
                self.assertIn(old, FIXTURE_PR_YML)
                repo, base = self.fixture(d, FIXTURE_PR_YML.replace(old, new))
                head = self.commit(repo, {"change.txt": "c\n"}, "the change")
                rc, summary, out = self.rehearse(d, repo, head, base)
                self.assertEqual(rc, 1, summary + out)
                self.assertTrue(summary.startswith("FAIL setup: "), summary)
                with open(os.path.join(d, "out", "setup.log")) as f:
                    self.assertIn(said, f.read())
                self.assertFalse(os.path.exists(os.path.join(d, "out", "plan-base.log")))

    @unittest.skipUnless(shutil.which("git") and shutil.which("flock"), "git or flock is not installed")
    def test_a_work_run_it_did_not_make_is_left_alone(self):
        with tempfile.TemporaryDirectory(prefix="oft-pr-steps-") as d:
            repo, base = self.fixture(d)
            head = self.commit(repo, {"change.txt": "c\n"}, "the change")
            os.makedirs(os.path.join(d, "work", "run"))
            with open(os.path.join(d, "work", "run", "mine.txt"), "w") as f:
                f.write("a person's file\n")
            rc, _summary, out = self.rehearse(d, repo, head, base)
            self.assertEqual(rc, 2, out)
            self.assertIn("pr-steps.sh did not make it", out)
            self.assertTrue(os.path.exists(os.path.join(d, "work", "run", "mine.txt")))
            # nor is OUT taken inside WORK/run, which every run removes
            r = run(["bash", PR_STEPS, head, base, "maintainer", os.path.join(d, "work", "run", "out")], REPO=repo,
                    WORK=os.path.join(d, "work"), GITHUB_REPOSITORY="acme/proofs")
            self.assertEqual(r.returncode, 2, r.stderr)
            self.assertIn("OUT is inside WORK/run", r.stderr)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class SharedFilesTest(unittest.TestCase):
    """pr.yml's lint step leaves the shared generated files to the line's render, and still compares every file
    when the tools it runs are older than --skip-shared."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="oft-shared-")
        self.addCleanup(self._tmp.cleanup)
        self.ws = self._tmp.name
        bin_dir = os.path.join(self.ws, "bin")
        os.mkdir(bin_dir)
        with open(os.path.join(bin_dir, "python"), "w") as f:
            f.write('#!/usr/bin/env bash\necho "python $*"\n')
        os.chmod(os.path.join(bin_dir, "python"), 0o755)
        self.path = bin_dir + os.pathsep + os.environ["PATH"]
        for d in ("head", os.path.join("base", "tools", "oft"), os.path.join("head", "tools", "oft"), "runner"):
            os.makedirs(os.path.join(self.ws, d), exist_ok=True)
        with open(os.path.join(self.ws, "head", "release.yaml"), "w") as f:
            f.write("release: x\n")
        with open(os.path.join(self.ws, "runner", "changed.txt"), "w") as f:
            f.write("proofs/zlib/checksum_fuzzer/plain_halts/proof.yaml\n")

    def run_lint_step(self, main_py):
        with open(os.path.join(self.ws, "base", "tools", "oft", "__main__.py"), "w") as f:
            f.write(main_py)
        text = step(load("pr.yml")["jobs"]["lint"], "generated files equal their rendering")["run"]
        env = dict(os.environ, PATH=self.path, RUNNER_TEMP=os.path.join(self.ws, "runner"), KIND="contributor")
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", text], cwd=self.ws, env=env,
                           capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        return (r.stdout + r.stderr).strip().splitlines()[-1]

    def test_lint_skips_the_shared_files_when_the_tools_can(self):
        line = self.run_lint_step('g.add_argument("--skip-shared", action="store_const")\n')
        self.assertTrue(line.endswith("generate --check --skip-shared"), line)

    def test_older_tools_compare_every_file(self):
        line = self.run_lint_step('g.add_argument("--check", action="store_true")\n')
        self.assertTrue(line.endswith("generate --check"), line)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
@unittest.skipUnless(os.path.exists(INDEX), "no .github/workflows/index.yml: the internal repository alone has it")
class IndexQueueTest(unittest.TestCase):
    """index.yml's decision on main (OSSV-276): a push straight to main makes GitHub rebuild every merge-queue group,
    so a push renders only while the queue is empty or the index is older than 3 h, and any other push skips with a
    notice in the job summary that gives the queue's count and the index's age.  The hourly run renders whatever the
    queue holds: a render commit is in no unit's key (test_keys.test_the_shared_generated_files_are_in_no_key), so it
    costs a group one rebuild, never correctness.  A tip that is already a render is left alone, and a hand run renders
    at once."""

    RENDER = "index: render the shared generated files at %s [skip ci]\n\nRendered-From: %s"

    def run_queue_step(self, answer, event="push", tip=None, history=(("merge", 1.0), ("render", 1.5)),
                       checked=None, refused=(), hand=()):
        """The decision step of render-main, against a stand-in gh: its exit status, its output, the step outputs it
        wrote, the calls the stand-in saw, and the job summary.  `answer` is what gh prints for the queue, or None for
        a gh that fails as the API does; `tip` is main's tip as the commits endpoint gives it (subject, parent), or
        None for a tip that is no render commit; `history` is main's last commits, newest first, each ("merge" or
        "render", its age in hours); `checked` is the index in `history` of the tip of the last hourly run whose
        render succeeded, or None for no such run; `refused` holds the indexes of newer hourly runs' tips whose
        push was refused (green, but not marked as rendered); `hand` holds (index in `history`, whether its marker
        step succeeded) for hand runs (workflow_dispatch).  The stand-in answers the runs list one event at a time,
        as GitHub does, and answers a read with no event with a busy day's page of twenty push runs (OSSV-276)."""
        with tempfile.TemporaryDirectory(prefix="oft-queue-") as d:
            bin_dir = os.path.join(d, "bin")
            os.mkdir(bin_dir)
            subject, parent = tip or ("Merge pull request #1: a proof", "p" * 40)
            commit = json.dumps({"commit": {"message": subject}, "parents": [{"sha": parent}]})
            listed = []
            for i, (kind, hours) in enumerate(history):
                at = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(time.time() - hours * 3600))
                message = (self.RENDER % ("e" * 12, "e" * 40) if kind == "render"
                           else "Merge pull request #%d: a proof" % (i + 2))
                listed.append({"sha": "%040x" % (i + 1), "commit": {"message": message, "committer": {"date": at}}})
            marker = "the index is current at this run's tip"
            scheduled = [(i, False) for i in refused] + ([(checked, True)] if checked is not None else [])

            def runs_of(start, entries, kind):
                return [{"id": start + n, "event": kind, "head_sha": listed[i]["sha"],
                         "created_at": listed[i]["commit"]["committer"]["date"]}
                        for n, (i, _ok) in enumerate(entries)]

            per_event = (("schedule", runs_of(901, scheduled, "schedule")),
                         ("workflow_dispatch", runs_of(951, hand, "workflow_dispatch")))
            # A busy day: every row of the page a read with no event gets is a push run, and no checked run is on it.
            now = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
            pushes = {"workflow_runs": [{"id": 800 + n, "event": "push", "head_sha": "f" * 40, "created_at": now}
                                        for n in range(20)]}
            runs = "".join("  *'/runs?'*event=%s*) cat <<'JSON'\n%s\nJSON\n  ;;\n"
                           % (name, json.dumps({"workflow_runs": rows})) for name, rows in per_event)
            runs += "  *'/runs?'*) cat <<'JSON'\n%s\nJSON\n  ;;\n" % json.dumps(pushes)
            jobs = "".join(
                "  *runs/%d/jobs*) cat <<'JSON'\n%s\nJSON\n  ;;\n"
                % (start + n, json.dumps({"jobs": [{"steps": [{"name": marker,
                                                               "conclusion": "success" if ok else "skipped"}]}]}))
                for start, entries in ((901, scheduled), (951, hand))
                for n, (_i, ok) in enumerate(entries))
            with open(os.path.join(bin_dir, "gh"), "w") as f:
                f.write('#!/usr/bin/env bash\necho "$@" >> "%s/calls"\n' % d
                        + 'case "$*" in\n'
                        + '  *graphql*) %s ;;\n' % ('echo "gh: HTTP 502: Server Error" >&2; exit 1'
                                                    if answer is None else 'printf "%%s\\n" %s' % answer)
                        + "  *'commits?'*) cat <<'JSON'\n%s\nJSON\n  ;;\n" % json.dumps(listed)
                        + runs
                        + jobs
                        + "  *) cat <<'JSON'\n%s\nJSON\n  ;;\n" % commit
                        + 'esac\n')
            os.chmod(os.path.join(bin_dir, "gh"), 0o755)
            out_file = os.path.join(d, "output")
            summary_file = os.path.join(d, "summary")
            open(out_file, "w").close()
            text = step(load("index.yml")["jobs"]["render-main"],
                        "whether to render, from the event, main's merge queue and the index's age")["run"]
            r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", text], cwd=d,
                               env=dict(os.environ, PATH=bin_dir + os.pathsep + os.environ["PATH"],
                                        GITHUB_OUTPUT=out_file, GITHUB_STEP_SUMMARY=summary_file,
                                        GITHUB_REF_NAME="main", GITHUB_EVENT_NAME=event,
                                        GITHUB_REPOSITORY=REPOSITORY, GH_TOKEN="t"),
                               capture_output=True, text=True)
            with open(out_file) as f:
                outputs = dict(line.rstrip("\n").split("=", 1) for line in f if "=" in line)
            calls = []
            if os.path.exists(os.path.join(d, "calls")):
                with open(os.path.join(d, "calls")) as f:
                    calls = f.read().splitlines()
            summary = ""
            if os.path.exists(summary_file):
                with open(summary_file) as f:
                    summary = f.read()
            return r.returncode, r.stdout + r.stderr, outputs, calls, summary

    def test_an_empty_queue_renders(self):
        rc, out, outputs, calls, _summary = self.run_queue_step("0")
        self.assertEqual(rc, 0, out)
        self.assertEqual(outputs.get("render"), "true")
        self.assertEqual("\n".join(calls).count("api graphql"), 1, calls)

    def test_a_busy_queue_on_a_push_with_a_fresh_index_skips_with_a_notice(self):
        rc, out, outputs, _calls, summary = self.run_queue_step("2", history=(("merge", 1.2), ("render", 1.5)))
        self.assertEqual(rc, 0, out)
        self.assertEqual((outputs.get("render"), outputs.get("stale")), ("false", "false"))
        self.assertIn("::notice title=index render skipped::", out)
        self.assertIn("merge queue has 2 entries", summary)
        self.assertRegex(summary, r"the index is 1 commits behind, unrendered for 1 h 1[0-9] min \(since 20")
        self.assertNotIn("::notice", summary)

    def test_an_old_render_with_main_unrendered_for_minutes_is_fresh(self):
        """A run with nothing to render makes no commit, so the newest render commit can be hours old while main
        has been unrendered for minutes: a quiet spell is not staleness, and the busy-queue push still skips."""
        for history, checked in (((("merge", 0.1), ("merge", 4.0), ("render", 6.0)), 1),
                                 ((("merge", 0.1), ("render", 6.0)), None)):
            with self.subTest(history=history, checked=checked):
                rc, out, outputs, _calls, summary = self.run_queue_step("3", history=history, checked=checked)
                self.assertEqual(rc, 0, out)
                self.assertEqual((outputs.get("render"), outputs.get("stale")), ("false", "false"), summary)
                self.assertIn("1 commits behind, unrendered for 0 h", summary)

    def test_a_refused_hourly_render_does_not_reset_the_age(self):
        """A refused push ends the hourly run green, but its tip was not rendered: the age runs from the older run
        that did render, so repeated refusals still reach the limit and go red."""
        history = (("merge", 0.1), ("merge", 1.0), ("merge", 3.5), ("merge", 5.0))
        rc, out, outputs, _calls, summary = self.run_queue_step("3", history=history, checked=3, refused=(0, 1))
        self.assertEqual(rc, 0, out)
        self.assertEqual((outputs.get("render"), outputs.get("stale")), ("true", "true"), summary)
        self.assertIn("3 commits behind, unrendered for 3 h", summary)

    def test_the_marker_step_runs_only_after_a_render_that_was_not_refused(self):
        steps = load("index.yml")["jobs"]["render-main"]["steps"]
        marker = [x for x in steps if x.get("name") == "the index is current at this run's tip"][0]
        self.assertEqual(marker["if"], "steps.render.outcome == 'success' && steps.render.outputs.refused != 'true'")
        render = [x for x in steps if "regenerate-shared.sh" in x.get("run", "")][0]
        self.assertEqual(render["id"], "render")
        self.assertIn('echo "refused=true" >> "$GITHUB_OUTPUT"', render["run"])

    def test_a_render_or_checked_tip_on_the_tip_is_current(self):
        rc, out, outputs, _calls, summary = self.run_queue_step("3", history=(("merge", 5.0), ("render", 6.0)),
                                                                checked=0)
        self.assertEqual(rc, 0, out)
        self.assertEqual((outputs.get("render"), outputs.get("stale")), ("false", "false"))
        self.assertIn("the index is current", summary)

    def test_a_busy_day_of_push_runs_does_not_hide_the_checked_tip(self):
        """OSSV-276: the runs list is newest-first over every event, so a day of many merges fills a page of it with
        push runs and the hourly run that checked the tip is not on the page at all.  Reading one page and keeping
        its hourly and hand runs found none, and a current index read as hours stale: runs 41856762721 and
        41866198140 said "9 commits behind, unrendered for 4 h 12 min" and "5 commits behind, 3 h 51 min" of an
        index that was current.  Each checking event is read on its own, so the push runs hide nothing."""
        history = (("merge", 0.1), ("merge", 4.0), ("render", 6.0))
        rc, out, outputs, calls, summary = self.run_queue_step("4", history=history, checked=1)
        self.assertEqual(rc, 0, out)
        self.assertEqual((outputs.get("render"), outputs.get("stale")), ("false", "false"), summary)
        self.assertIn("1 commits behind, unrendered for 0 h", summary)
        self.assertNotIn("runs/800/jobs", "\n".join(calls), "no push run's jobs are read")

    def test_a_hand_run_newer_than_the_hourly_one_is_the_checked_tip(self):
        """The two checking events are read apart, so the newer of the two answers: here the hand run's tip, which
        is four hours after the hourly run's."""
        history = (("merge", 0.1), ("merge", 4.0), ("merge", 8.0), ("render", 9.0))
        rc, out, outputs, _calls, summary = self.run_queue_step("4", history=history, checked=2, hand=((1, True),))
        self.assertEqual(rc, 0, out)
        self.assertEqual((outputs.get("render"), outputs.get("stale")), ("false", "false"), summary)
        self.assertIn("1 commits behind, unrendered for 0 h", summary)

    def test_a_stale_index_renders_on_a_push_whatever_the_queue_holds(self):
        for history in ((("merge", 0.1), ("merge", 3.5), ("render", 4.0)), (("merge", 0.1), ("merge", 0.2))):
            with self.subTest(history=history):
                rc, out, outputs, _calls, summary = self.run_queue_step("4", history=history)
                self.assertEqual(rc, 0, out)
                self.assertEqual((outputs.get("render"), outputs.get("stale")), ("true", "true"))
                self.assertIn("past the 3 h limit: rendering though main's merge queue has 4 entries", summary)

    def test_a_busy_queue_on_the_hourly_run_renders(self):
        """The queue is almost never empty: a render the queue made a push skip lands within the hour, and a run
        whose tip is already rendered makes no commit (test_regenerate_shared.test_a_fresh_tip_gets_no_commit)."""
        rc, out, outputs, _calls, summary = self.run_queue_step("1", event="schedule",
                                                                history=(("merge", 0.2), ("render", 0.5)))
        self.assertEqual(rc, 0, out)
        self.assertEqual((outputs.get("render"), outputs.get("stale")), ("true", "false"))
        self.assertIn("the hourly run renders whatever main's merge queue holds (entries: 1)", summary)

    def test_a_queue_that_cannot_be_read_fails_the_job(self):
        rc, out, outputs, _calls, _summary = self.run_queue_step(None)
        self.assertNotEqual(rc, 0, out)
        self.assertNotEqual(outputs.get("render"), "true")

    def test_an_answer_that_is_no_number_fails_the_job(self):
        rc, out, outputs, _calls, _summary = self.run_queue_step('"not a number"')
        self.assertNotEqual(rc, 0, out)
        self.assertNotEqual(outputs.get("render"), "true")
        self.assertIn("did not read as a number", out)

    def test_a_hand_run_renders_whatever_the_queue_holds(self):
        rc, out, outputs, calls, _summary = self.run_queue_step("7", event="workflow_dispatch")
        self.assertEqual(rc, 0, out)
        self.assertEqual(outputs.get("render"), "true")
        self.assertEqual(calls, [], "a hand run asks the API nothing")

    def test_a_tip_that_is_a_render_commit_renders_nothing(self):
        """The hourly run after a render finds its own commit on the tip: nothing to render, and no key read."""
        parent = "a" * 40
        rc, out, outputs, _calls, summary = self.run_queue_step(
            "0", event="schedule", tip=(self.RENDER % (parent[:12], parent), parent))
        self.assertEqual(rc, 0, out)
        self.assertEqual(outputs.get("render"), "false")
        self.assertIn("is the render of", summary)

    def test_a_tip_whose_trailer_names_another_commit_is_rendered(self):
        message = "index: render the shared generated files at %s\n\nRendered-From: %s" % ("b" * 12, "b" * 40)
        rc, out, outputs, _calls, _summary = self.run_queue_step("0", event="schedule", tip=(message, "c" * 40))
        self.assertEqual(rc, 0, out)
        self.assertEqual(outputs.get("render"), "true")

    def test_a_branch_with_no_merge_queue_reads_as_empty(self):
        """`mergeQueue` is null where no queue is set up, and `// 0` makes that an empty queue."""
        rc, out, outputs, _calls, _summary = self.run_queue_step("null")
        self.assertEqual(rc, 0, out)
        self.assertEqual(outputs.get("render"), "true")


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
@unittest.skipUnless(os.path.exists(INDEX), "no .github/workflows/index.yml: the internal repository alone has it")
class IndexRenderStepTest(unittest.TestCase):
    """What the render step does with the script's answer: main passes --skip-ci and one try and reads its exit
    status.  main is the one line rendered here since the release line joined it."""

    def run_render_step(self, job, ref, exit_code=0, stale="false", says=""):
        """A job's render step against a stand-in script that records its arguments, prints `says` and exits
        `exit_code`: the step's exit status, its output, and the arguments the script saw.  The job summary it wrote
        is left in self.summary."""
        with tempfile.TemporaryDirectory(prefix="oft-render-") as d:
            subprocess.run(["git", "init", "-q", d], check=True, capture_output=True)
            os.makedirs(os.path.join(d, "tools", "oft", "ci"))
            stub = os.path.join(d, "tools", "oft", "ci", "regenerate-shared.sh")
            with open(stub, "w") as f:
                f.write('#!/usr/bin/env bash\necho "$@" > "%s/called"\necho %s\nexit %d\n'
                        % (d, shlex.quote(says), exit_code))
            os.chmod(stub, 0o755)
            text = [s["run"] for s in load("index.yml")["jobs"][job]["steps"]
                    if "regenerate-shared.sh" in s.get("run", "")][0]
            runner = os.path.join(d, "runner")
            os.mkdir(runner)
            r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", text], cwd=d,
                               env=dict(os.environ, GITHUB_REF_NAME=ref, GITHUB_WORKSPACE=d, RUNNER_TEMP=runner,
                                        GITHUB_REPOSITORY=REPOSITORY,
                                        DEPLOY_KEY="a-key", STALE=stale, GITHUB_STEP_SUMMARY=os.path.join(d, "summary"),
                                        GITHUB_OUTPUT=os.path.join(d, "output"),
                                        GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1"),
                               capture_output=True, text=True)
            called = ""
            if os.path.exists(os.path.join(d, "called")):
                with open(os.path.join(d, "called")) as f:
                    called = f.read().strip()
            self.summary = ""
            if os.path.exists(os.path.join(d, "summary")):
                with open(os.path.join(d, "summary")) as f:
                    self.summary = f.read()
            return r.returncode, r.stdout + r.stderr, called

    def test_every_green_render_says_in_the_summary_what_it_did(self):
        """A green run with no commit says why: the render found nothing to change, or main moved under it."""
        rc, out, _called = self.run_render_step("render-main", "main",
                                                says="regenerate-shared.sh: main 7df85b3dcc77 is rendered; nothing to do")
        self.assertEqual(rc, 0, out)
        self.assertIn("no shared file changed: no commit to make", self.summary)
        rc, out, _called = self.run_render_step("render-main", "main")
        self.assertEqual(rc, 0, out)
        self.assertIn("pushed a render commit onto main", self.summary)
        rc, out, _called = self.run_render_step("render-main", "main", exit_code=5)
        self.assertEqual(rc, 0, out)
        self.assertIn("not rendered: main moved during the render", self.summary)

    def test_main_is_the_one_line_rendered(self):
        """After the join of the release line into main, ossv/recipes goes: no push to it starts this workflow and no
        job renders it, so the only job is main's."""
        wf = load("index.yml")
        self.assertEqual(wf["on"]["push"]["branches"], ["main"])
        self.assertEqual(sorted(wf["jobs"]), ["render-main"])
        self.assertEqual(wf["jobs"]["render-main"]["if"], "github.ref == 'refs/heads/main'")

    def test_main_is_rendered_with_one_try_and_the_marker(self):
        rc, out, called = self.run_render_step("render-main", "main")
        self.assertEqual(rc, 0, out)
        for want in ("--branch main", "--remote index-ssh", "--tries 1", "--skip-ci"):
            self.assertIn(want, called, called)

    def test_a_refused_push_on_main_ends_the_run_green(self):
        """Exit 5 is the line having moved, and the push that moved it starts this workflow again."""
        rc, out, _called = self.run_render_step("render-main", "main", exit_code=5)
        self.assertEqual(rc, 0, out)
        self.assertIn("moved during the render", out)

    def test_the_render_step_reads_stale_from_the_decision_step(self):
        """The red refusal hangs on this wiring: without it, set -u would fail every refused push."""
        render = [s for s in load("index.yml")["jobs"]["render-main"]["steps"]
                  if "regenerate-shared.sh" in s.get("run", "")][0]
        self.assertEqual(render["env"]["STALE"], "${{ steps.queue.outputs.stale }}")
        self.assertIn('echo "stale=$stale" >> "$GITHUB_OUTPUT"',
                      step(load("index.yml")["jobs"]["render-main"],
                           "whether to render, from the event, main's merge queue and the index's age")["run"])

    def test_a_refused_push_of_a_stale_index_fails_the_run(self):
        """OSSV-276: an index past its age limit that the run could not render is red, never green."""
        rc, out, _called = self.run_render_step("render-main", "main", exit_code=5, stale="true")
        self.assertEqual(rc, 1, out)
        self.assertIn("past its age limit: not rendered", out)

    def test_every_other_non_zero_exit_fails_the_run(self):
        """Exit 7 is a rule or the credential refusing the push, and the rest are faults too: only exit 5, the
        line having moved, is green."""
        for code in (1, 3, 4, 7, 8):
            rc, out, _called = self.run_render_step("render-main", "main", exit_code=code)
            self.assertEqual(rc, code, out)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
@unittest.skipUnless(shutil.which("git"), "git is not installed")
class LintRecordTest(unittest.TestCase):
    """pr.yml lints a push to a pull request against the tree its last passing lint read, when that lint's record
    holds (the plan job's lint_since step), and reads it whole otherwise.  Here the base b changes nothing; the pull
    request's first push h1 changes a.txt (merge commit m1, the record's), its second push h2 changes b.txt too
    (m2, this run's), and its third push h3 changes c.txt too (m3).  b2, on the base, changes a.txt as h1 does not,
    so b2 and h1 do not merge.  hx is h1 with a new lint-exceptions.yaml (mx).  b3, on the base, adds d.txt and
    leaves tools/ as it is, and mb is h2 merged onto b3: the base moved under the pull request.  b's
    lint-exceptions.yaml has a licence-pending entry for p/t, whose proof hp changes (mp); hq1 adds one for p/u
    with its proof (mq1), whose next push hq2 changes it (mq2); hbad's lint-exceptions.yaml is no YAML (mbad)."""

    PR = "7"
    KIND = "maintainer"
    INTO = "refs/heads/main"

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="oft-lint-record-")
        d = self.dir = self._tmp.name
        origin = self.origin = os.path.join(d, "origin")
        os.mkdir(origin)
        git(origin, "init", "-q")

        def commit(files, message):
            for rel, text in files.items():
                os.makedirs(os.path.join(origin, os.path.dirname(rel)) or origin, exist_ok=True)
                with open(os.path.join(origin, rel), "w") as f:
                    f.write(text)
            git(origin, "add", "-A")
            git(origin, "commit", "-qm", message)
            return git(origin, "rev-parse", "HEAD")

        def merged(head, ref, base=None):
            """GitHub's merge commit of the pull request whose head is `head`, on `base` (b), kept at `ref`."""
            git(origin, "checkout", "-q", "--detach", base or self.b)
            git(origin, "merge", "-q", "--no-ff", "-m", "merge", head)
            git(origin, "update-ref", ref, "HEAD")
            return git(origin, "rev-parse", "HEAD")

        self.b = commit({"tools/oft/x.py": "x\n", "tools/oft/lint-exceptions.yaml": self.pending("p/t"),
                         "projects/p/t/proofs/P.v": "(* t *)\n", "a.txt": "a\n", "b.txt": "b\n", "c.txt": "c\n"}, "b")
        git(origin, "checkout", "-qb", "topic")
        self.h1 = commit({"a.txt": "a1\n"}, "h1")
        self.h2 = commit({"b.txt": "b2\n"}, "h2")
        self.h3 = commit({"c.txt": "c3\n"}, "h3")
        git(origin, "checkout", "-qb", "exceptions", self.h1)
        self.hx = commit({"tools/oft/lint-exceptions.yaml": "[]\n"}, "hx")
        git(origin, "checkout", "-qb", "moved", self.b)
        self.b2 = commit({"a.txt": "a from the base\n"}, "b2")
        git(origin, "checkout", "-qb", "later", self.b)
        self.b3 = commit({"d.txt": "d\n"}, "b3")
        git(origin, "checkout", "-qb", "pending", self.h1)
        self.hp = commit({"projects/p/t/proofs/P.v": "(* t, its licence lines applied *)\n"}, "hp")
        git(origin, "checkout", "-qb", "own", self.h1)
        self.hq1 = commit({"tools/oft/lint-exceptions.yaml": self.pending("p/t", "p/u"),
                           "projects/p/u/proofs/Q.v": "(* u *)\n"}, "hq1")
        self.hq2 = commit({"projects/p/u/proofs/Q.v": "(* u, its licence lines applied *)\n"}, "hq2")
        git(origin, "checkout", "-qb", "unreadable", self.h1)
        self.hbad = commit({"tools/oft/lint-exceptions.yaml": "exceptions: [\n"}, "hbad")
        self.m1 = merged(self.h1, "refs/pull/7/first")
        self.m2 = merged(self.h2, "refs/pull/7/merge")
        self.m3 = merged(self.h3, "refs/pull/7/third")
        self.mx = merged(self.hx, "refs/pull/7/exceptions")
        self.mb = merged(self.h2, "refs/pull/7/moved", self.b3)
        self.mp = merged(self.hp, "refs/pull/7/pending")
        self.mq1 = merged(self.hq1, "refs/pull/7/own1")
        self.mq2 = merged(self.hq2, "refs/pull/7/own2")
        self.mbad = merged(self.hbad, "refs/pull/7/unreadable")
        git(origin, "checkout", "-q", "main")
        self.tools = git(origin, "rev-parse", self.b + ":tools")
        self.wf = load("pr.yml")

    def tearDown(self):
        self._tmp.cleanup()

    @staticmethod
    def pending(*units):
        """A lint-exceptions.yaml with a licence-pending entry for each unit."""
        return "exceptions:\n" + "".join(
            "- unit: %s\n  rule: licence-pending\n  due: '2099-01-01'\n  series: pending\n  reason: later\n" % u
            for u in units)

    def tree(self, commit):
        return git(self.origin, "rev-parse", commit + "^{tree}")

    def workspace(self, ref="refs/pull/7/merge", base=None):
        """A runner's workspace whose head/ is a clone one commit deep of `ref`, as actions/checkout leaves it, on
        the base `base` (b), checked out at base/ as both jobs' base step does.  base/tools/ is this repository's,
        which the steps import (oft), while git reads the base commit's files there (HEAD:...); bin/ holds the
        `python` that setup-python puts on PATH in CI: here, the interpreter running this test."""
        ws = tempfile.mkdtemp(dir=self.dir)
        head = os.path.join(ws, "head")
        os.mkdir(head)
        git(head, "init", "-q")
        git(head, "remote", "add", "origin", "file://" + self.origin)
        git(head, "fetch", "-q", "--depth=1", "origin", ref)
        git(head, "checkout", "-q", "--detach", "FETCH_HEAD")
        # the base, one commit deep, as both jobs' base step fetches it
        git(head, "fetch", "-q", "--depth=1", "origin", base or self.b)
        git(head, "worktree", "add", "-q", "--detach", os.path.join(ws, "base"), base or self.b)
        shutil.rmtree(os.path.join(ws, "base", "tools"))
        os.symlink(os.path.join(REPO, "tools"), os.path.join(ws, "base", "tools"))
        os.mkdir(os.path.join(ws, "bin"))
        os.symlink(sys.executable, os.path.join(ws, "bin", "python"))
        os.mkdir(os.path.join(ws, "runner"))
        return ws

    def record(self, ws, pr=None, tools=None, parents=None, tree=None, kind=KIND, into=INTO):
        """The record of a lint of m1 into main, or of what the arguments change (kind or into None: a record
        without that line): its path."""
        rec = os.path.join(ws, "runner", "lint-record", "record")
        os.makedirs(os.path.dirname(rec), exist_ok=True)
        p1, p2 = parents or (self.b, self.h1)
        with open(rec, "w") as f:
            f.write("pr %s\n" % (pr or self.PR) + ("" if kind is None else "kind %s\n" % kind)
                    + ("" if into is None else "into %s\n" % into)
                    + "tools %s\nparents %s %s\ntree %s\n" % (
                        tools or self.tools, p1, p2, tree or git(self.origin, "rev-parse", self.m1 + "^{tree}")))
        return rec

    def run_step(self, job, step_id, ws, env):
        """The step of `job` whose id is step_id, as GitHub runs it in workspace ws: exit status, output, outputs."""
        s = next(s for s in self.wf["jobs"][job]["steps"] if s.get("id") == step_id)
        output = os.path.join(ws, "runner", "output")
        if os.path.exists(output):
            os.remove(output)
        full = dict(os.environ, GITHUB_WORKSPACE=ws, RUNNER_TEMP=os.path.join(ws, "runner"), GITHUB_OUTPUT=output,
                    GIT_ALLOW_PROTOCOL="file", GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1",
                    PATH=os.path.join(ws, "bin") + os.pathsep + os.environ["PATH"])
        full.update(env)
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", s["run"]], cwd=ws, env=full,
                           capture_output=True, text=True)
        got = {}
        if os.path.exists(output):
            with open(output) as f:
                got = dict(line.rstrip("\n").split("=", 1) for line in f if "=" in line)
        return r.returncode, r.stdout + r.stderr, got

    def ours(self, base=None, into=None):
        """The env GitHub gives the record steps of a run of this pull request (KIND is the workflow's own)."""
        return {"BASE": base or self.b, "PR": self.PR, "KIND": self.KIND, "INTO": into or self.INTO}

    def since(self, ws, matched="the-key", record=None, job="plan", base=None, into=None):
        rec = record or os.path.join(ws, "runner", "lint-record", "record")
        return self.run_step(job, "lint_since", ws, dict(self.ours(base, into), MATCHED=matched, RECORD=rec))

    def test_the_plan_and_the_lint_job_read_a_record_with_one_step(self):
        """The plan job reads a record to choose the lint job's runner and the lint job reads it again for its
        verdict: one text, so the two cannot read a record differently."""
        plan, lint = (next(s for s in self.wf["jobs"][j]["steps"] if s.get("id") == "lint_since")
                      for j in ("plan", "lint"))
        self.assertEqual((plan["name"], plan["env"], plan["run"]), (lint["name"], lint["env"], lint["run"]))
        # the kind of change both read, and the lint job writes, is the workflow's KIND: no step sets its own
        self.assertIn("KIND", self.wf["env"])
        writer = next(s for s in self.wf["jobs"]["lint"]["steps"] if s.get("id") == "lint_record")
        key = next(s for s in self.wf["jobs"]["plan"]["steps"] if s.get("id") == "lint_record_key")
        for s in (plan, lint, writer, key):
            self.assertNotIn("KIND", s.get("env", {}), s["name"])
            self.assertIn("$KIND", s["run"], s["name"])
            # the branch the pull request goes into, as the record writer names it
            self.assertEqual(" ".join(s["env"]["INTO"].split()), " ".join(writer["env"]["INTO"].split()), s["name"])
            self.assertRegex(s["run"], r"\$\{?INTO\b", s["name"])

    def test_a_record_that_holds_is_the_tree_its_lint_read_and_a_changed_file_is_read(self):
        """The record of m1 holds for m2: lint compares with m1's tree, so b.txt (changed since m1) is read and a.txt
        (changed since the base, not since m1) is not read again."""
        from oft import lint
        for job in ("plan", "lint"):
            with self.subTest(job=job):
                ws = self.workspace()
                self.record(ws)
                rc, out, got = self.since(ws, job=job)
                self.assertEqual(rc, 0, out)
                self.assertEqual(got["record"], "the-key", out)
                head = os.path.join(ws, "head")
                self.assertEqual(git(head, "rev-parse", got["since"] + "^{tree}"),
                                 git(self.origin, "rev-parse", self.m1 + "^{tree}"))
                self.assertEqual(lint.changed_since(head, got["since"]), {"b.txt"})
                self.assertEqual(lint.changed_since(head, self.b), {"a.txt", "b.txt"})

    def test_any_doubt_is_no_record(self):
        """No record, or a record any part of which does not hold, is none: lint then reads as it would without one."""
        gone = "f" * 40
        m2_tree = git(self.origin, "rev-parse", self.m2 + "^{tree}")
        cases = (
            ("no entry was restored, or the cache could not be read", {"matched": ""}, {}, "none was restored"),
            ("the entry holds no record", {"record": "/nonexistent/record"}, {}, "holds no record"),
            ("another pull request's record", {}, {"pr": "8"}, "names pull request '8', not 7"),
            ("another kind of change", {}, {"kind": "contributor"},
             "names the kind of change 'contributor', and this run's is maintainer"),
            ("a record with no kind", {}, {"kind": None}, "names the kind of change '', and this run's is maintainer"),
            ("a lint into another branch (the pull request was retargeted since)", {}, {"into": "refs/heads/lane"},
             "the record is of a lint into 'refs/heads/lane', and this run's is into refs/heads/main"),
            ("a record with no branch", {}, {"into": None}, "the record is of a lint into '', and this run's is into"),
            ("other tools", {}, {"tools": gone}, "base tools/ tree is " + gone),
            ("not object ids", {}, {"tools": "tools"}, "does not name four object ids"),
            ("a parent that cannot be fetched", {}, {"parents": (self.b, gone)}, "cannot be fetched"),
            ("parents that do not merge", {}, {"parents": (self.b2, self.h1)}, "do not merge cleanly"),
            ("parents that merge to another tree", {}, {"tree": m2_tree}, "not to the tree %s" % m2_tree),
        )
        for name, call, rec, said in cases:
            for job in ("plan", "lint"):
                with self.subTest(name, job=job):
                    ws = self.workspace()
                    self.record(ws, **rec)
                    rc, out, got = self.since(ws, job=job, **call)
                    self.assertEqual(rc, 0, out)
                    self.assertEqual((got.get("since"), got.get("record")), ("", ""), out)
                    self.assertIn("no lint record is read: ", out)
                    self.assertIn(said, out)

    def test_the_record_a_passing_lint_keeps_holds_for_the_next_push(self):
        """The lint job's record of its lint of m2, read on the next push (m3): lint compares with m2's tree and
        reads c.txt alone."""
        from oft import lint
        ws = self.workspace()
        rc, out, got = self.run_step("lint", "lint_record", ws, self.ours())
        self.assertEqual(rc, 0, out)
        m2_tree = git(self.origin, "rev-parse", self.m2 + "^{tree}")
        self.assertEqual(got["key"], "lint-pass-3-pr7-maintainer-refs/heads/main-%s-%s" % (self.tools, m2_tree))
        # the plan job's prefix finds it (restore-keys)
        rc, out, key = self.run_step("plan", "lint_record_key", self.workspace(), self.ours())
        self.assertTrue(got["key"].startswith(key["prefix"]), (got["key"], key, out))
        nxt = self.workspace("refs/pull/7/third")
        rc, out, got = self.since(nxt, record=os.path.join(ws, "runner", "lint-record", "record"))
        self.assertEqual(rc, 0, out)
        head = os.path.join(nxt, "head")
        self.assertEqual(git(head, "rev-parse", got["since"] + "^{tree}"), m2_tree)
        self.assertEqual(lint.changed_since(head, got["since"]), {"c.txt"})

    def test_the_record_is_not_written_without_the_base_s_tools_or_a_merge_commit(self):
        """The lint job keeps no record when the base has no tools/ tree (nothing names the rules that lint ran),
        nor when HEAD is not a merge commit (no two parents to rebuild its tree from)."""
        ws = self.workspace()
        head = os.path.join(ws, "head")
        empty = git(head, "hash-object", "-t", "tree", "-w", "/dev/null")
        bare = git(head, "-c", "user.name=t", "-c", "user.email=t@invalid", "commit-tree", empty, "-m", "no tools")
        rc, out, got = self.run_step("lint", "lint_record", ws, self.ours(base=bare))
        self.assertEqual((rc, got.get("key")), (0, None), out)
        self.assertIn("the base has no tools/ tree: no record is kept", out)
        self.assertFalse(os.path.exists(os.path.join(ws, "runner", "lint-record", "record")))
        ws = self.workspace("refs/heads/topic")
        rc, out, got = self.run_step("lint", "lint_record", ws, self.ours())
        self.assertEqual((rc, got.get("key")), (0, None), out)
        self.assertIn("HEAD is not a merge commit: no record is kept", out)
        self.assertFalse(os.path.exists(os.path.join(ws, "runner", "lint-record", "record")))

    def test_a_record_holds_on_a_moved_base_with_the_same_tools_and_its_change_is_read(self):
        """The base moved from b to b3 (d.txt added, tools/ the same) after the lint of m1: the record still holds,
        and lint reads what changed since m1's tree, the pull request's b.txt and the base's d.txt."""
        from oft import lint
        for job in ("plan", "lint"):
            with self.subTest(job=job):
                ws = self.workspace("refs/pull/7/moved", base=self.b3)
                self.record(ws)
                rc, out, got = self.since(ws, job=job, base=self.b3)
                self.assertEqual(rc, 0, out)
                self.assertEqual(got["record"], "the-key", out)
                self.assertEqual(lint.changed_since(os.path.join(ws, "head"), got["since"]), {"b.txt", "d.txt"})

    def test_a_record_the_lint_job_cannot_read_where_the_plan_did_is_warned_of(self):
        """The plan read a record and chose the runner by it; the lint job's own reading of that entry gives none
        (here, the restore failed: no matched key, whatever the record path holds): lint_since says so, the lint
        step takes the rule without a record, and the warning step names the entry."""
        ws = self.workspace()
        self.record(ws)
        rc, out, got = self.since(ws, job="lint", matched="")
        self.assertEqual((rc, got.get("since"), got.get("record")), (0, "", ""), out)
        self.assertIn("no lint record is read: none was restored", out)
        warn = step(self.wf["jobs"]["lint"], "the record the plan read still holds here")
        # it warns only when the plan chose the small runner by that record
        for clause in ("needs.plan.outputs.lint_record != ''", "needs.plan.outputs.lint_changed_only == 'true'",
                       "steps.lint_since.outputs.since == ''"):
            self.assertIn(clause, warn["if"])
        steps = [s.get("name") for s in self.wf["jobs"]["lint"]["steps"]]
        self.assertLess(steps.index("the tree of the last passing lint, when its record holds"),
                        steps.index("the record the plan read still holds here"))
        self.assertLess(steps.index("the record the plan read still holds here"), steps.index("lint, by the base's rules"))
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", warn["run"]], capture_output=True,
                           text=True, env=dict(os.environ, RECORD_KEY="lint-pass-3-pr7-k"))
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertTrue(r.stdout.startswith("::warning::the plan job read lint record lint-pass-3-pr7-k "), r.stdout)

    def test_the_record_is_kept_only_after_a_passing_lint_by_the_base_s_tools(self):
        """The record is written after the lint step, only when every step before it passed and the base's tools
        gave the verdict, and saved before the first step that runs the change's own code; the lint job restores
        only the entry the plan job read, under the path it was saved under (a cache entry is found only by both)."""
        steps = self.wf["jobs"]["lint"]["steps"]
        names = [s.get("name") for s in steps]
        order = [names.index(n) for n in ("the record of this pull request's last passing lint, by the base's tools",
                                          "the tree of the last passing lint, when its record holds",
                                          "lint, by the base's rules",
                                          "the record of this lint, for the pull request's next push",
                                          "keep the record of this lint",
                                          "generated files equal their rendering")]
        self.assertEqual(order, sorted(order))
        write = step(self.wf["jobs"]["lint"], "the record of this lint, for the pull request's next push")
        for clause in ("success()", "github.event_name == 'pull_request'", "needs.plan.outputs.tools != 'head'"):
            self.assertIn(clause, write["if"])
        save = step(self.wf["jobs"]["lint"], "keep the record of this lint")
        self.assertEqual(save["with"]["key"], "${{ steps.lint_record.outputs.key }}")
        restore = next(s for s in steps if s.get("id") == "lint_record_restore")
        self.assertEqual(restore["with"]["key"], "${{ needs.plan.outputs.lint_record }}")
        self.assertNotIn("restore-keys", restore["with"])
        plan_restore = next(s for s in self.wf["jobs"]["plan"]["steps"] if s.get("id") == "lint_record_restore")
        self.assertEqual(plan_restore["with"]["restore-keys"], "${{ steps.lint_record_key.outputs.prefix }}")
        self.assertEqual(self.wf["jobs"]["plan"]["outputs"]["lint_record"], "${{ steps.lint_since.outputs.record }}")
        self.assertEqual({save["with"]["path"], restore["with"]["path"], plan_restore["with"]["path"]},
                         {"${{ runner.temp }}/lint-record"})
        # the key names the pull request and the base's tools, which the plan job's prefix reads
        rc, out, got = self.run_step("plan", "lint_record_key", self.workspace(), self.ours())
        self.assertEqual((rc, got.get("prefix")), (0, "lint-pass-3-pr7-maintainer-refs/heads/main-%s-" % self.tools),
                         out)
        # a cache key holds no comma: a branch name with one is written %2C there, as it is in the record
        rc, out, got = self.run_step("plan", "lint_record_key", self.workspace(), self.ours(into="refs/heads/a,b"))
        self.assertEqual((rc, got.get("prefix")), (0, "lint-pass-3-pr7-maintainer-refs/heads/a%%2Cb-%s-" % self.tools),
                         out)

    def test_the_lint_step_compares_with_the_record_s_tree_before_the_base(self):
        lint_step = step(self.wf["jobs"]["lint"], "lint, by the base's rules")
        text = lint_step["run"]
        self.assertEqual(lint_step["env"]["SINCE"], "${{ steps.lint_since.outputs.since }}")
        self.assertIn('if [ -n "$SINCE" ] && [ "$PLANNED_TOOLS" != head ]', text)
        self.assertLess(text.index('args+=(--changed-only "$SINCE")'), text.index('args+=(--changed-only "$BASE")'))

    def lint_args(self, since, into, planned_tools="base", changed_only=True):
        """The arguments the lint step gives `oft lint`, one list for each run of it, for a routed pull request into
        `into` whose record gave `since` ("" for none), with the plan's tools answer `planned_tools`, base tools that
        offer --changed-only or not, and a stand-in python that records them instead of linting."""
        ws = self.workspace()
        # stand-ins for the base's tools and for python, in place of the workspace's own
        os.unlink(os.path.join(ws, "base", "tools"))
        os.unlink(os.path.join(ws, "bin", "python"))
        oft = os.path.join(ws, "base", "tools", "oft")
        os.makedirs(oft)
        with open(os.path.join(oft, "__main__.py"), "w") as f:
            f.write('# the options the base\'s tools take: %s "--pending-base"\n'
                    % ('"--changed-only"' if changed_only else ""))
        bin_dir = os.path.join(ws, "bin")
        called = os.path.join(ws, "called")
        with open(os.path.join(bin_dir, "python"), "w") as f:
            f.write('#!/usr/bin/env bash\nprintf "%%s\\n" "$@" "--" >> %s\n' % shlex.quote(called))
        os.chmod(os.path.join(bin_dir, "python"), 0o755)
        s = step(self.wf["jobs"]["lint"], "lint, by the base's rules")
        output = os.path.join(ws, "runner", "output")
        env = dict(os.environ, GITHUB_WORKSPACE=ws, RUNNER_TEMP=os.path.join(ws, "runner"), GITHUB_OUTPUT=output,
                   GITHUB_STEP_SUMMARY=os.path.join(ws, "runner", "summary"), KIND="maintainer",
                   PATH=bin_dir + os.pathsep + os.environ["PATH"], ROUTED="true", BASE=self.b, INTO=into,
                   PLANNED_TOOLS=planned_tools, SINCE=since)
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", s["run"]], cwd=ws, env=env,
                           capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        runs = [[]]
        with open(called) as f:
            for line in f.read().splitlines():
                if line == "--":
                    runs.append([])
                else:
                    runs[-1].append(line)
        return runs[:-1]

    def test_the_lint_step_takes_the_record_s_tree_and_without_one_the_base(self):
        """A record that holds: --changed-only against its tree, into main or any other branch.  No record:
        --changed-only against the base, into main or any other branch."""
        for into in ("refs/heads/main", "refs/heads/lane"):
            [args] = self.lint_args("f" * 40, into)
            self.assertEqual(args[args.index("--changed-only") + 1], "f" * 40, (into, args))
            [args] = self.lint_args("", into)
            self.assertEqual(args[args.index("--changed-only") + 1], self.b, (into, args))

    def test_a_pull_request_into_another_branch_lints_only_its_changed_files(self):
        """A routed pull request into a branch other than main, with no record: the lint step takes --changed-only
        against the base, and the gate answers true, so the lint runs on the 4-core runner.  Before 2026-11-03 it
        linted every file on 16 cores: 152 of 158 lint jobs into other branches in 14:00-22:00Z 2026-11-02."""
        [args] = self.lint_args("", "refs/heads/lane")
        self.assertEqual(args[args.index("--changed-only") + 1], self.b, args)
        self.assertEqual(self.gate("refs/pull/7/merge", None)[0], "true")

    def test_the_record_s_tree_is_not_taken_by_the_change_s_own_tools_or_by_tools_without_changed_only(self):
        """A record that holds is no --changed-only against its tree when the plan named the change's own tools
        (head: the base's run against the base, then the change's own over every file) or when the base's tools take
        no --changed-only (every file), into main or another branch."""
        since = "f" * 40
        for into in ("refs/heads/main", "refs/heads/lane"):
            with self.subTest(into=into, planned_tools="head"):
                runs = self.lint_args(since, into, planned_tools="head")
                self.assertEqual(len(runs), 2, runs)
                for args in runs:
                    self.assertNotIn(since, args, runs)
                self.assertNotIn("--changed-only", runs[1], runs)
                self.assertEqual(runs[0][runs[0].index("--changed-only") + 1], self.b, runs)
            with self.subTest(into=into, changed_only=False):
                [args] = self.lint_args(since, into, changed_only=False)
                self.assertNotIn("--changed-only", args)
                self.assertNotIn(since, args)

    def test_a_cache_that_cannot_be_read_is_no_record_and_fails_nothing(self):
        """actions/cache/restore can fail its step on a service error; both restores carry continue-on-error, so
        the plan and the lint job go on, and lint_since, given no matched key, reads no record (the tests above
        run that).  The action itself cannot run here (it needs the Actions cache service), so its failure is
        held by its configuration."""
        for job in ("plan", "lint"):
            restore = next(s for s in self.wf["jobs"][job]["steps"] if s.get("id") == "lint_record_restore")
            self.assertIs(restore.get("continue-on-error"), True, job)
            since = next(s for s in self.wf["jobs"][job]["steps"] if s.get("id") == "lint_since")
            self.assertEqual(since["env"]["MATCHED"], "${{ steps.lint_record_restore.outputs.cache-matched-key }}")

    def gate(self, ref, since_of):
        """The plan job's lint_gate for a pull request into a branch other than main whose head is `ref`, with the
        record of a lint of `since_of` (None: no record): its answer and output."""
        ws = self.workspace(ref)
        since = ""
        if since_of:
            self.record(ws, parents=since_of[0], tree=self.tree(since_of[1]), into="refs/heads/lane")
            rc, out, got = self.since(ws, into="refs/heads/lane")
            self.assertEqual(rc, 0, out)
            since = got["since"]
        with open(os.path.join(ws, "runner", "changed.txt"), "w") as f:
            f.write("a.txt\nb.txt\n")
        rc, out, got = self.run_step("plan", "lint_gate", ws, {"ROUTED": "true", "PLANNED_TOOLS": "base", "SINCE": since,
                                                               "INTO": "refs/heads/lane", "PYTHONPATH": ""})
        self.assertEqual(rc, 0, out)
        return got["lint_changed_only"], out

    def test_the_gate_takes_the_small_runner_only_for_a_per_file_lint(self):
        """Into a branch other than main, the gate answers true with a record that holds, or with none (the base
        is compared with), and false when a changed path is one every verdict reads: lint-exceptions.yaml, changed
        since m1 in mx, has lint read every file."""
        self.assertEqual(self.gate("refs/pull/7/merge", None)[0], "true")
        self.assertEqual(self.gate("refs/pull/7/merge", ((self.b, self.h1), self.m1))[0], "true")
        answer, out = self.gate("refs/pull/7/exceptions", ((self.b, self.h1), self.m1))
        self.assertEqual(answer, "false")
        self.assertIn("a verdict on another file may read tools/oft/lint-exceptions.yaml", out)

    def test_a_change_to_a_licence_pending_unit_since_the_record_is_no_record(self):
        """Whether a licence-pending entry is still needed ("unit U has no licence finding") only a lint of every
        file says (lint.apply_pending).  A file of p/t, which the base's entry names, changed since m1 (mp), and a
        file of p/u, which only this tree's entry names (hq1 added it), changed since mq1 (mq2): neither record
        is read, so the gate and the lint step take the rule without one: --changed-only against the base, as into
        main.  Entries that cannot be read are no record either (mbad)."""
        cases = (("refs/pull/7/pending", (self.b, self.h1), self.m1, "a file of p/t, which a licence-pending"),
                 ("refs/pull/7/own2", (self.b, self.hq1), self.mq1, "a file of p/u, which a licence-pending"),
                 ("refs/pull/7/unreadable", (self.b, self.h1), self.m1,
                  "the licence-pending entries of the base and of this tree cannot be read"))
        for ref, parents, of, said in cases:
            for job in ("plan", "lint"):
                with self.subTest(ref, job=job):
                    ws = self.workspace(ref)
                    self.record(ws, parents=parents, tree=self.tree(of))
                    rc, out, got = self.since(ws, job=job)
                    self.assertEqual((rc, got.get("since"), got.get("record")), (0, "", ""), out)
                    self.assertIn("no lint record is read: " + said, out)
            with self.subTest(ref, step="lint_gate"):
                self.assertEqual(self.gate(ref, (parents, of))[0], "true")
        [args] = self.lint_args("", "refs/heads/lane")
        self.assertEqual(args[args.index("--changed-only") + 1], self.b, args)


REKEY_VERDICT = "keys.checker moved only in an announced re-key window (rule D11)"


@unittest.skipUnless(HAVE_WORKFLOWS and shutil.which("git"), "no .github/workflows, or git is not installed")
class RekeyGuardTest(StandIn):
    """Rule D11: until the platform tag, and outside an announced re-key window, nothing that moves keys.checker merges
    into main.  pr.yml's rekey job computes keys.checker of the base by the base's tools, and of the head by the base's
    tools and by the change's own, prints all three, and fails a change into main when either head id differs from the
    base's, unless the repository variable OSSV_REKEY_WINDOW is exactly `open`; required fails with it.  The steps run
    as GitHub runs them, over a repository whose every commit carries its own tools/oft: the modules keys.checker runs
    (keys.py and what it imports, copied from this repository), a stand-in checker file (check.py) and a file no check
    opens (lint.py).  Each worktree runs the tools it checked out, so a head whose keys.py lies runs that keys.py."""

    # what `from oft import keys` loads
    MODULES = ("__init__.py", "keys.py", "layout.py", "names.py", "paths.py", "unitpaths.py")

    def setUp(self):
        super().setUp()
        self.jobs = load("pr.yml")["jobs"]
        with open(os.path.join(self.dir, "bin", "python"), "w") as f:
            f.write("#!/bin/sh\nexec %s \"$@\"\n" % shlex.quote(sys.executable))
        os.chmod(os.path.join(self.dir, "bin", "python"), 0o755)
        self.origin = os.path.join(self.dir, "origin")
        os.mkdir(self.origin)
        git(self.origin, "init", "-q")
        tools = {}
        for name in self.MODULES:
            with open(os.path.join(REPO, "tools", "oft", name)) as f:
                tools["tools/oft/" + name] = f.read()
        self.base = self.commit(dict(tools, **{"tools/oft/check.py": "check\n", "tools/oft/lint.py": "lint\n",
                                               ".gitattributes": "* text=auto eol=lf\n"}), "base")
        # files keys.NOT_THE_CHECKER names, and a workflow, which is outside tools/: keys.checker stays
        self.outside = self.commit({"tools/oft/lint.py": "lint, changed\n", "tools/oft/tests/test_x.py": "x\n",
                                    ".github/workflows/pr.yml": "on: push\n"}, "outside the checker")
        self.moved = self.commit({"tools/oft/check.py": "check, changed\n"}, "the checker")
        git(self.origin, "checkout", "-q", "-b", "hidden", self.base)
        # A checker file changes, and the change's keys.checker answers every commit with the base's id.
        self.hidden = self.commit({
            "tools/oft/check.py": "check, changed\n",
            "tools/oft/keys.py": tools["tools/oft/keys.py"] + (
                "\n\n_checker = checker\n\n\ndef checker(repo, commit):\n    return _checker(repo, %r)\n"
                % self.base)}, "a checker move its own tools hide")

    def commit(self, files, message):
        for rel, text in files.items():
            os.makedirs(os.path.dirname(os.path.join(self.origin, rel)), exist_ok=True)
            with open(os.path.join(self.origin, rel), "w") as f:
                f.write(text)
        git(self.origin, "add", "-A")
        git(self.origin, "commit", "-qm", message)
        return git(self.origin, "rev-parse", "HEAD")

    def step(self, name):
        return next(s for s in self.jobs["rekey"]["steps"] if name in (s.get("id"), s.get("name")))

    def guard(self, head, window="", event="pull_request", base_ref="main", repository=REPOSITORY):
        """The job's base step, then its guard step, in a workspace whose head/ is a clone of the origin at head:
        (the guard's exit status, its output, its job summary, keys.checker of the base and of head, each by this
        repository's keys.py, which is the base's)."""
        ws = tempfile.mkdtemp(dir=self.dir)
        clone = os.path.join(ws, "head")
        git(ws, "clone", "-q", self.origin, clone)
        git(clone, "checkout", "-q", "--detach", head)
        env = {"GITHUB_WORKSPACE": ws, "BASE": self.base, "GITHUB_EVENT_NAME": event,
               "GITHUB_REPOSITORY": repository, "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}
        rc, out, _ = self.run_step(self.step("base")["run"], env, cwd=ws)
        self.assertEqual(rc, 0, out)
        # two copies of the tools, each the one its commit has, and no link to one copy
        for tree, commit in (("base", self.base), ("head", head)):
            self.assertFalse(os.path.islink(os.path.join(ws, tree, "tools")), tree)
            with open(os.path.join(ws, tree, "tools", "oft", "keys.py")) as f:
                self.assertEqual(f.read().strip(), git(self.origin, "show", commit + ":tools/oft/keys.py"), tree)
        rc, out, summary = self.run_step(self.step("rekey")["run"],
                                         dict(env, BASE_REF=base_ref, WINDOW=window), cwd=ws)
        return rc, out, summary, keys.checker(clone, self.base), keys.checker(clone, head)

    def said(self, before, after):
        return ("this change moves keys.checker from %s to %s (re-keys every unit); it can merge only in an "
                "announced re-key window (rule D11); ask the CI/CD lead" % (before, after))

    def ids(self, summary, head, before, by_base, by_own):
        self.assertIn("- the base %s, by the base's tools: `%s`" % (self.base, before), summary)
        self.assertIn("- this change %s, by the base's tools: `%s`" % (head, by_base), summary)
        self.assertIn("- this change %s, by its own tools: `%s`" % (head, by_own), summary)

    def test_an_unchanged_checker_passes_and_prints_all_three_ids(self):
        rc, out, summary, before, after = self.guard(self.outside)
        self.assertEqual(before, after)
        self.assertEqual(rc, 0, out)
        self.ids(summary, self.outside, before, after, after)
        self.assertIn("keys.checker is unchanged", summary)

    def test_a_moved_checker_fails_while_the_window_is_closed(self):
        """An absent variable (empty) is a closed window, and only exactly `open` opens it; a merge queue group, which
        is main's, is held as a pull request into main is."""
        for window, event, base_ref in (("", "pull_request", "main"), ("closed", "pull_request", "main"),
                                        ("Open", "pull_request", "main"), ("open ", "pull_request", "main"),
                                        ("", "merge_group", "")):
            with self.subTest(window=window, event=event):
                rc, out, summary, before, after = self.guard(self.moved, window, event, base_ref)
                self.assertNotEqual(before, after)
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::" + self.said(before, after), out)
                self.assertIn(self.said(before, after), summary)
                self.ids(summary, self.moved, before, after, after)

    def test_a_move_the_change_s_own_tools_hide_fails(self):
        """The head changes a checker file and its keys.checker answers with the base's id: its own tools say
        nothing moved, and the base's tools, reading the same head, say it did.  The base's judge it."""
        rc, out, summary, before, after = self.guard(self.hidden)
        self.assertNotEqual(before, after)
        self.assertEqual(rc, 1, out)
        self.ids(summary, self.hidden, before, after, before)
        self.assertIn("::error::" + self.said(before, after), out)
        self.assertIn("different ids: %s and %s" % (after, before), summary)
        # and an open window still lets it through, as any move
        self.assertEqual(self.guard(self.hidden, "open")[0], 0)

    def test_a_moved_checker_passes_in_an_open_window(self):
        for event, base_ref in (("pull_request", "main"), ("merge_group", "")):
            with self.subTest(event=event):
                rc, out, summary, before, after = self.guard(self.moved, "open", event, base_ref)
                self.assertEqual(rc, 0, out)
                self.assertIn("the re-key window is open", summary)
                self.ids(summary, self.moved, before, after, after)

    def test_a_merge_that_is_not_into_this_repository_s_main_is_not_held(self):
        """A pull request into another base, and the public repository, whose checker moves only by releases cut on
        the internal one: the ids and a notice."""
        for base_ref, repository in (("lane", REPOSITORY), ("main", PUBLIC)):
            with self.subTest(base_ref=base_ref, repository=repository):
                rc, out, summary, before, after = self.guard(self.moved, "", "pull_request", base_ref, repository)
                self.assertEqual(rc, 0, out)
                self.assertIn("::notice::this change moves keys.checker from %s to %s" % (before, after), out)
                self.ids(summary, self.moved, before, after, after)

    def test_the_job_runs_after_lint_reads_the_variable_and_checks_out_tools_oft_alone(self):
        job = self.jobs["rekey"]
        self.assertEqual(job["needs"], ["plan", "lint"])
        self.assertEqual(" ".join(job["if"].split()),
                         "${{ !cancelled() && needs.plan.result == 'success' && needs.lint.result == 'success' "
                         "&& (github.event_name == 'pull_request' || github.event_name == 'merge_group') }}")
        self.assertEqual(job["permissions"], {"contents": "read"})
        checkouts = [s for s in job["steps"] if s.get("uses", "").startswith("actions/checkout@")]
        self.assertEqual([(s["with"]["filter"], s["with"]["sparse-checkout"]) for s in checkouts],
                         [("blob:none", "tools/oft")])
        self.assertIn("git -C base sparse-checkout set --cone tools/oft", self.step("base")["run"])
        self.assertEqual(self.step("rekey")["env"], {"BASE": "${{ needs.plan.outputs.base }}",
                                                     "BASE_REF": "${{ github.base_ref }}",
                                                     "WINDOW": "${{ vars.OSSV_REKEY_WINDOW }}"})
        self.assertEqual(self.step("base")["env"], {"BASE": "${{ needs.plan.outputs.base }}"})

    def test_required_fails_on_a_pull_request_or_group_the_guard_did_not_pass(self):
        """A draft skips lint and with it rekey: required's step before this one judges the draft."""
        job = self.jobs["required"]
        self.assertIn("rekey", job["needs"])
        s = step(job, REKEY_VERDICT)
        self.assertEqual(" ".join(s["if"].split()),
                         "github.event_name == 'pull_request' || github.event_name == 'merge_group'")
        self.assertEqual(s["env"], {"REKEY_RESULT": "${{ needs.rekey.result }}",
                                    "HOLD": "${{ needs.plan.outputs.hold }}"})
        for result, hold, want in (("success", "none", 0), ("failure", "none", 1), ("skipped", "none", 1),
                                   ("cancelled", "none", 1), ("skipped", "draft", 0), ("failure", "draft", 1),
                                   ("", "none", 1)):
            with self.subTest(result=result, hold=hold):
                rc, out, _ = self.run_step(s["run"], {"REKEY_RESULT": result, "HOLD": hold})
                self.assertEqual(rc, want, out)

    def test_the_guard_is_no_part_of_the_checker(self):
        """It must not move keys.checker itself: pr.yml is outside tools/, which keys.checker alone lists, and the
        files of tools/ it changes are ones keys.NOT_THE_CHECKER names."""
        for path in ("tools/oft/tests/test_workflow_verdicts.py", "tools/oft/tests/test_lint.py",
                     "tools/oft/ci/pr-steps.sh"):
            self.assertTrue(keys.not_the_checker(path), path)


MADE_FROM_STEP = "each made-from record this change touches equals its generator's (the head's made_from.py --check)"
# A made_from.py that prints two rows and exits with the code its file `rc` beside it holds, after logging, to
# MADE_FROM_LOG, its own path and arguments.
FAKE_MADE_FROM = """\
import os, sys
here = os.path.dirname(os.path.abspath(__file__))
with open(os.environ["MADE_FROM_LOG"], "a") as f:
    f.write(" ".join([os.path.relpath(__file__, os.environ["HEAD_DIR"])] + sys.argv[1:]) + "\\n")
print("+ row added\\n- row removed")
with open(os.path.join(here, "rc")) as f:
    sys.exit(int(f.read()))
"""


# A made_from.py that is made from its unit's proofs, as a real one is: it reads proofs/lib/Proof.v, four
# directories above itself, logs its path and whether that file is there, and exits 1 when it is not -- which is
# what a generator run on a checkout without the proof libraries answers.
PROOF_READING_MADE_FROM = """\
import os, sys
proofs = os.path.abspath(__file__)
for _ in range(4):
    proofs = os.path.dirname(proofs)
found = os.path.exists(os.path.join(proofs, "lib", "Proof.v"))
with open(os.environ["MADE_FROM_LOG"], "a") as f:
    f.write("%s %s\\n" % (os.path.relpath(__file__, os.environ["HEAD_DIR"]), found))
print("- lib/Proof.v" if not found else "the record matches")
sys.exit(0 if found else 1)
"""


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
@unittest.skipUnless(shutil.which("git"), "git is not installed")
class MadeFromStepTest(StandIn):
    """pr.yml's lint runs the head's made_from.py --check of each unit whose proofs/provenance/ tree the change
    touches: exit 0 passes, 1 fails with the rows it printed, 2 warns and passes, 124 (the 900 s timeout) and any
    other exit fail; a unit with a made-from record and no made_from.py fails, one with neither passes with a line,
    and a change that touches no provenance tree passes with a line.  Before it runs anything of the change's it
    unsets the token actions/checkout persisted in head/.git/config, it runs nothing at all for KIND=contributor,
    and it prints what the script wrote between ::stop-commands:: and that block's token."""

    EVIDENCE = "proofs/provenance/evidence/licence/made_from.py"

    def setUp(self):
        super().setUp()
        self.ws = os.path.join(self.dir, "ws")
        self.head = os.path.join(self.ws, "head")
        os.makedirs(self.head)
        os.mkdir(os.path.join(self.ws, "tmp"))
        self.log = os.path.join(self.dir, "made-from.log")
        git(self.head, "init", "-q")
        self.write({"README": "r\n"})
        self.base = self.commit("base")

    def write(self, files):
        for rel, text in files.items():
            path = os.path.join(self.head, rel)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w") as f:
                f.write(text)

    def commit(self, message):
        git(self.head, "add", "-A")
        git(self.head, "commit", "-qm", message)
        return git(self.head, "rev-parse", "HEAD")

    def unit(self, unit, rc):
        """Unit projects/<unit>/ with the stand-in made_from.py exiting rc, and a record beside it."""
        d = "projects/%s/%s" % (unit, os.path.dirname(self.EVIDENCE))
        return {d + "/made_from.py": FAKE_MADE_FROM, d + "/rc": "%d\n" % rc, d + "/made-from.tsv": "row\n"}

    def step(self, kind="maintainer"):
        s = step(load("pr.yml")["jobs"]["lint"], MADE_FROM_STEP)
        self.assertEqual(s["env"], {"BASE": "${{ steps.base.outputs.base }}"})  # KIND is the workflow's own env
        self.assertNotIn("if", s)  # every event, pull_request and merge_group alike
        rc, out, _summary = self.run_step(s["run"], {"BASE": self.base, "RUNNER_TEMP": os.path.join(self.ws, "tmp"),
                                                     "KIND": kind,
                                                     "MADE_FROM_LOG": self.log, "HEAD_DIR": self.head}, cwd=self.ws)
        calls = []
        if os.path.exists(self.log):
            with open(self.log) as f:
                calls = f.read().splitlines()
        return rc, out, calls

    def test_a_change_that_touches_no_provenance_tree_runs_nothing(self):
        self.write({"projects/curl/fuzz_bufq/proofs/Proof.v": "(* a proof *)\n"})
        self.commit("a proof")
        rc, out, calls = self.step()
        self.assertEqual((rc, calls), (0, []), out)
        self.assertEqual(out.strip(), "no file under projects/<p>/<h>/proofs/provenance/ changed: "
                                      "no made-from record to check")

    def test_exit_0_passes(self):
        self.write(self.unit("curl/fuzz_bufq", 0))
        self.commit("a record")
        rc, out, calls = self.step()
        self.assertEqual((rc, calls), (0, ["projects/curl/fuzz_bufq/" + self.EVIDENCE + " --check"]), out)
        self.assertIn("the record matches its generator", out)
        self.assertNotIn("::error::", out)
        self.assertNotIn("::warning::", out)

    def test_exit_1_fails_and_shows_the_rows(self):
        """And says not to clear it with --apply: a record that differs from its generator is the unit owner's
        question, not a file to regenerate (curl/fuzz_bufq's own exit 1 waits on OSSV-162)."""
        self.write(self.unit("curl/fuzz_bufq", 1))
        self.commit("a stale record")
        rc, out, _calls = self.step()
        self.assertEqual(rc, 1, out)
        self.assertIn("+ row added\n- row removed\n", out)
        self.assertIn("::error::projects/curl/fuzz_bufq/%s --check exited 1: the record differs from what its "
                      "generator gives" % self.EVIDENCE, out)
        self.assertIn("Do not run made_from.py --apply to clear this; the unit's owner decides the record", out)
        # nothing anywhere in the step tells a reader to regenerate the record and commit it
        self.assertNotIn("commit what it writes", step(load("pr.yml")["jobs"]["lint"], MADE_FROM_STEP)["run"])

    def test_exit_2_warns_with_the_output_and_passes(self):
        self.write(self.unit("curl/fuzz_bufq", 2))
        self.commit("an undecided record")
        rc, out, _calls = self.step()
        self.assertEqual(rc, 0, out)
        self.assertIn("::warning::projects/curl/fuzz_bufq/%s --check exited 2" % self.EVIDENCE, out)
        self.assertIn("%0A+ row added%0A- row removed", out)
        self.assertNotIn("::error::", out)

    def test_any_other_exit_fails(self):
        self.write(self.unit("curl/fuzz_bufq", 3))
        self.commit("a broken generator")
        rc, out, _calls = self.step()
        self.assertEqual(rc, 1, out)
        self.assertIn("--check exited 3: the check did not finish", out)

    def test_a_unit_with_neither_a_generator_nor_a_record_is_skipped(self):
        self.write({"projects/curl/fuzz_x/proofs/provenance/notes.txt": "n\n"})
        self.commit("provenance with no generator")
        rc, out, calls = self.step()
        self.assertEqual((rc, calls), (0, []), out)
        self.assertIn("projects/curl/fuzz_x: its provenance tree changed, and it has no made_from.py and no "
                      "made-from.tsv", out)

    def test_a_record_whose_generator_is_gone_fails(self):
        """Deleting made_from.py must not turn the check off: the record is still there and nothing can check it."""
        self.write(self.unit("curl/fuzz_bufq", 0))
        self.base = self.commit("the generator and its record")
        os.remove(os.path.join(self.head, "projects/curl/fuzz_bufq", self.EVIDENCE))
        self.write({"projects/curl/fuzz_bufq/proofs/provenance/evidence/licence/made-from.tsv": "forged\n"})
        self.commit("the generator deleted and the record rewritten")
        rc, out, calls = self.step()
        self.assertEqual((rc, calls), (1, []), out)
        self.assertIn("::error::projects/curl/fuzz_bufq holds 1 made-from record(s) under proofs/provenance/ and "
                      "no made_from.py", out)

    def test_a_unit_deleted_whole_passes(self):
        """Its record is gone with its generator, so there is nothing left to check."""
        self.write(self.unit("curl/fuzz_bufq", 0))
        self.base = self.commit("a unit")
        shutil.rmtree(os.path.join(self.head, "projects/curl/fuzz_bufq"))
        self.commit("the unit deleted")
        rc, out, calls = self.step()
        self.assertEqual((rc, calls), (0, []), out)
        self.assertIn("projects/curl/fuzz_bufq: its provenance tree changed, and it has no made_from.py and no "
                      "made-from.tsv", out)

    def test_the_generator_runs_under_a_900_s_timeout_and_a_timeout_fails(self):
        """`timeout 900` fails closed: its 124 has a message of its own, and the step fails on it."""
        self.assertIn('timeout 900 python3 "$s" --check',
                      step(load("pr.yml")["jobs"]["lint"], MADE_FROM_STEP)["run"])
        self.write(self.unit("curl/fuzz_bufq", 124))
        self.commit("a generator that does not finish")
        rc, out, _calls = self.step()
        self.assertEqual(rc, 1, out)
        self.assertIn("::error::projects/curl/fuzz_bufq/%s --check did not finish within 900 s" % self.EVIDENCE, out)

    def test_a_contributor_s_generator_is_not_run(self):
        """An outside contributor's code runs only in the tests job, as the rendering step beside this one has it;
        the record is left unchecked, and the unit is still held to having a generator."""
        self.write(self.unit("curl/fuzz_bufq", 1))
        self.commit("a contributor's record")
        rc, out, calls = self.step(kind="contributor")
        self.assertEqual((rc, calls), (0, []), out)
        self.assertIn("KIND=contributor: no made_from.py of this change is run in this job", out)
        self.assertNotIn("::error::", out)
        for kind in ("maintainer", "release"):
            with self.subTest(kind=kind):
                self.assertEqual(self.step(kind=kind)[0], 1)

    def test_a_contributor_s_record_still_needs_its_generator(self):
        self.write({"projects/curl/fuzz_bufq/proofs/provenance/evidence/licence/made-from.tsv": "row\n"})
        self.commit("a record with no generator")
        rc, out, calls = self.step(kind="contributor")
        self.assertEqual((rc, calls), (1, []), out)
        self.assertIn("::error::projects/curl/fuzz_bufq holds 1 made-from record(s)", out)

    def test_the_persisted_token_is_unset_before_any_generator_runs(self):
        """Both checkouts of head/ leave the job's token in head/.git/config as an http extraheader, and the job
        holds actions: write; the step takes the header away before it runs a file of the change's."""
        git(self.head, "config", "http.https://github.com/.extraheader", "AUTHORIZATION: basic xxx")
        self.write(self.unit("curl/fuzz_bufq", 0))
        self.commit("a record")
        rc, out, calls = self.step()
        self.assertEqual((rc, calls), (0, ["projects/curl/fuzz_bufq/" + self.EVIDENCE + " --check"]), out)
        left = subprocess.run(["git", "-C", self.head, "config", "--get-all",
                               "http.https://github.com/.extraheader"], capture_output=True, text=True)
        self.assertEqual((left.returncode, left.stdout), (1, ""))
        # the lint job gives the step a write scope, which is why the header must go
        self.assertEqual(load("pr.yml")["jobs"]["lint"]["permissions"],
                         {"contents": "read", "packages": "read", "actions": "write"})

    def test_the_generator_s_output_cannot_emit_a_workflow_command(self):
        """What the script writes, on stdout and stderr alike, is printed between ::stop-commands:: and its token,
        so the runner acts on no workflow command of the script's."""
        d = "projects/curl/fuzz_bufq/" + os.path.dirname(self.EVIDENCE)
        self.write({d + "/made_from.py": "import sys\n"
                                         "print('::error::forged on stdout')\n"
                                         "sys.stderr.write('::set-output name=x::forged on stderr\\n')\n",
                    d + "/made-from.tsv": "row\n"})
        self.commit("a generator that prints workflow commands")
        rc, out, _calls = self.step()
        self.assertEqual(rc, 0, out)
        token = re.search(r"::stop-commands::([0-9a-f]{32})\n", out)
        self.assertIsNotNone(token, out)
        body = out.split(token.group(0), 1)[1].split("::%s::\n" % token.group(1), 1)
        self.assertEqual(len(body), 2, out)
        # python's stdout is a buffered pipe here and its stderr is not, so the two reach the block in either order
        self.assertEqual(sorted(body[0].splitlines()),
                         ["::error::forged on stdout", "::set-output name=x::forged on stderr"])
        # nothing the script wrote is outside the block, and each run picks a token of its own
        self.assertNotIn("forged", body[1])
        second = re.search(r"::stop-commands::([0-9a-f]{32})\n", self.step()[1])
        self.assertNotEqual(second.group(1), token.group(1))

    def test_two_units_each_run_and_one_failure_fails(self):
        self.write(self.unit("curl/fuzz_bufq", 0))
        self.write(self.unit("curl/fuzz_fnmatch", 1))
        self.commit("two records")
        rc, out, calls = self.step()
        self.assertEqual(rc, 1, out)
        self.assertEqual(calls, ["projects/curl/fuzz_bufq/" + self.EVIDENCE + " --check",
                                 "projects/curl/fuzz_fnmatch/" + self.EVIDENCE + " --check"])
        self.assertIn("::error::projects/curl/fuzz_fnmatch/", out)
        self.assertNotIn("::error::projects/curl/fuzz_bufq/", out)

    def test_a_change_to_a_unit_s_record_alone_runs_its_generator(self):
        """The generator is found in the unit's tree, not among the changed files: a change to the record alone
        is checked."""
        self.write(self.unit("curl/fuzz_bufq", 0))
        self.base = self.commit("the generator")
        self.write({"projects/curl/fuzz_bufq/proofs/provenance/evidence/licence/made-from.tsv": "edited\n"})
        self.commit("an edit to the record")
        rc, out, calls = self.step()
        self.assertEqual((rc, calls), (0, ["projects/curl/fuzz_bufq/" + self.EVIDENCE + " --check"]), out)

    def sparse_unit(self, unit):
        """A unit whose generator is made from its proofs: projects/<unit>/proofs/lib/Proof.v, the generator and a
        record beside it."""
        d = "projects/%s/%s" % (unit, os.path.dirname(self.EVIDENCE))
        return {d + "/made_from.py": PROOF_READING_MADE_FROM, d + "/made-from.tsv": "row\n",
                "projects/%s/proofs/lib/Proof.v" % unit: "(* a proof *)\n"}

    def sparse(self):
        """head/ as the lint job checks it out when the plan says lint_files_left_out: every file but the proof
        libraries."""
        git(self.head, "sparse-checkout", "set", "--no-cone", "/*", "!/proofs/*/*/lib/*",
            "!/projects/*/*/proofs/lib/*")

    def test_a_sparse_checkout_gets_the_touched_unit_s_proofs_back(self):
        """The job's sparse set leaves out exactly what a record is made from, so a generator run on it answers `-`
        for every row (run 41933939559 on #1784).  The step writes the unit's proofs back first."""
        self.write(self.sparse_unit("curl/fuzz_bufq"))
        self.commit("a unit whose generator reads its proofs")
        self.sparse()
        proof = os.path.join(self.head, "projects/curl/fuzz_bufq/proofs/lib/Proof.v")
        self.assertFalse(os.path.exists(proof))  # as the lint job's checkout leaves it
        rc, out, calls = self.step()
        self.assertEqual((rc, calls), (0, ["projects/curl/fuzz_bufq/" + self.EVIDENCE + " True"]), out)
        self.assertTrue(os.path.exists(proof))
        # made_from.py, made-from.tsv and the proof that was missing
        self.assertIn("projects/curl/fuzz_bufq/proofs: 3 file(s) in the working tree for the generator", out)

    def test_the_proofs_of_a_unit_the_change_did_not_touch_stay_out(self):
        """Only the touched units are written back, so the rest of the lint checkout stays sparse, and the step
        adds no pattern to it."""
        self.write(self.sparse_unit("curl/fuzz_other"))
        self.base = self.commit("another unit, which this change does not touch")
        self.write(self.sparse_unit("curl/fuzz_bufq"))
        self.commit("the unit this change touches")
        self.sparse()
        rc, out, _calls = self.step()
        self.assertEqual(rc, 0, out)
        self.assertTrue(os.path.exists(os.path.join(self.head, "projects/curl/fuzz_bufq/proofs/lib/Proof.v")))
        self.assertFalse(os.path.exists(os.path.join(self.head, "projects/curl/fuzz_other/proofs/lib/Proof.v")))
        self.assertEqual(git(self.head, "sparse-checkout", "list").split(),
                         ["/*", "!/proofs/*/*/lib/*", "!/projects/*/*/proofs/lib/*"])

    def test_a_whole_tree_checkout_is_left_as_it_is(self):
        """The other arm of the lint job: every file is there already, and the write-back changes nothing."""
        self.write(self.sparse_unit("curl/fuzz_bufq"))
        self.commit("a unit whose generator reads its proofs")
        rc, out, calls = self.step()
        self.assertEqual((rc, calls), (0, ["projects/curl/fuzz_bufq/" + self.EVIDENCE + " True"]), out)
        self.assertEqual(git(self.head, "status", "--porcelain"), "")

    def partial(self):
        """head/ as the lint job really has it: the same sparse patterns over a `filter: blob:none` clone, whose
        promisor remote holds the blobs no pattern asked for.  Returns that remote, so a test can take it away."""
        bare = os.path.join(self.dir, "promisor.git")
        git(self.head, "clone", "-q", "--bare", self.head, bare)
        git(bare, "config", "uploadpack.allowfilter", "true")
        git(bare, "config", "uploadpack.allowanysha1inwant", "true")
        shutil.rmtree(self.head)
        # file://, so this is a real fetch: a clone from a path copies or hardlinks every object and ignores
        # --filter, and then nothing would be missing to fetch later
        git(self.ws, "clone", "-q", "--filter=blob:none", "--no-checkout", "file://" + bare, self.head)
        self.sparse()
        git(self.head, "checkout", "-q", "--detach", "HEAD")
        return bare

    def test_a_blob_none_checkout_fetches_the_proofs_before_the_token_goes(self):
        """The lint job's sparse checkout is `filter: blob:none`, so a proof library's blobs are not in the clone
        and writing them out of HEAD is a fetch from the promisor remote, which on this private repository needs
        the credential actions/checkout persisted.  So the write-back runs before the step unsets that header."""
        run = step(load("pr.yml")["jobs"]["lint"], MADE_FROM_STEP)["run"]
        self.assertLess(run.index("--ignore-skip-worktree-bits"),
                        run.index("config --unset-all http.https://github.com/.extraheader"), run)
        self.write(self.sparse_unit("curl/fuzz_bufq"))
        self.commit("a unit whose generator reads its proofs")
        self.partial()
        proof = os.path.join(self.head, "projects/curl/fuzz_bufq/proofs/lib/Proof.v")
        self.assertFalse(os.path.exists(proof))
        rc, out, calls = self.step()
        self.assertEqual((rc, calls), (0, ["projects/curl/fuzz_bufq/" + self.EVIDENCE + " True"]), out)
        self.assertTrue(os.path.exists(proof))

    def test_a_promisor_it_cannot_reach_fails_the_step_and_runs_no_generator(self):
        """What an unauthenticated fetch looks like: the write-back exits non-zero, and the step says so and stops
        rather than running a generator over a tree it knows is incomplete."""
        self.write(self.sparse_unit("curl/fuzz_bufq"))
        self.commit("a unit whose generator reads its proofs")
        shutil.rmtree(self.partial())
        rc, out, calls = self.step()
        self.assertEqual((rc, calls), (1, []), out)
        self.assertIn("::error::projects/curl/fuzz_bufq/proofs could not be written out of HEAD", out)
        self.assertNotIn("checking projects/curl/fuzz_bufq", out)

    def test_the_lint_checkout_holds_the_head_s_tools(self):
        """The generator may read the head's tools (curl's #1784 reads tools/oft/rocq.py), and made_from.py --check
        exits 2 without them.  So every checkout of head/ in the lint job keeps tools/: the whole-tree one has no
        sparse set at all, and the lint_files_left_out one is a non-cone set of `/*` whose only exclusions are the
        proof libraries."""
        checkouts = [s for s in load("pr.yml")["jobs"]["lint"]["steps"]
                     if s.get("uses", "").startswith("actions/checkout@") and s["with"].get("path") == "head"]
        self.assertEqual(len(checkouts), 2, checkouts)
        full, sparse = checkouts
        self.assertNotIn("sparse-checkout", full["with"])
        self.assertIs(sparse["with"]["sparse-checkout-cone-mode"], False)
        lines = sparse["with"]["sparse-checkout"].split()
        self.assertEqual(lines[0], "/*")
        # No exclusion reaches tools/oft/rocq.py, the file curl's #1784 made_from.py reads: each `!` pattern is
        # matched against that path and against every directory above it, since a pattern naming a directory
        # leaves out everything under it.  fnmatch's `*` crosses `/`, which git's does not, so this is the
        # stricter reading of the two: a pattern this passes cannot leave the file out.
        rocq = ("/tools", "/tools/oft", "/tools/oft/rocq.py")
        for line in lines[1:]:
            if line.startswith("!"):
                pattern = line[1:].rstrip("/")
                for path in rocq:
                    self.assertFalse(fnmatch.fnmatchcase(path, pattern), "%s leaves out %s" % (line, path))
                # and nothing but the proof libraries is left out at all
                self.assertIn("/lib/", line, line)


if __name__ == "__main__":
    unittest.main()
