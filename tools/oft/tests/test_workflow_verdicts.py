"""The one verdict of each workflow run: pr.yml's
triggers (no edit starts a run), and the jobs that collect a run's results in images.yml and weekly.yml, each run as
GitHub runs a step, against a stand-in gh; images.yml's verification of the attestation it stores, and the fork
checker build's tag, legs and checks; the base pr.yml
judges a change against, which its router reads the change from, with the files of the base its jobs check out and
lint compares the findings ledger with; the patterns of every sparse checkout, in both layouts; and
tools/oft/ci/pr-steps.sh, which rehearses a pull request's pr.yml run on a full clone.  And what the public
repository's workflows publish and check: the check run release.yml accepts on a tagged commit, the units its sweep
hands weekly.yml, and pr.yml's plan of a push to the public main."""
import ast
import collections
import contextlib
import hashlib
import importlib.util
import io
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tarfile
import tempfile
import textwrap
import time
import unittest

from oft import facts, keys, pack, paths, plan, port, yamlio
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
# A gh that answers `gh api [--method M] [-f/-F K=V ...] [-H <header>] <endpoint> [--jq <filter>]` from
# <FAKE_GH>/<endpoint>.json, the endpoint's slashes as underscores and its query string dropped, through --jq as gh
# applies it (a -f or -F field is logged with the call and nothing else, so `gh api graphql` is answered from
# graphql.json; a -H header is dropped, so a file's raw text is an answer that is one JSON string); when
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
    -H|--header) shift 2 ;;
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
    """.github/workflows/<name>, with each step that runs a script of .github/scripts/pr/ given that script's text
    (helpers.with_scripts)."""
    return helpers.with_scripts(yamlio.load_file(os.path.join(WORKFLOWS, name)))


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
            text = helpers.inline_scripts(f.read())
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


# Stand-ins for the head's dev/stream/bin/ossv-tools-check, which pr.yml's reach step ran (`--write-changed -`) for
# the hunk rows of a change under dev/stream/ until the stream_tools job took that call.  Each says that it ran, in
# RUNNER_TEMP/planted-ran.  The honest one writes one hunk row.  The other two do what any code of a change can do
# on the runner it runs on, whatever variables its caller takes out of its environment: rewrite the step's outputs,
# which GitHub reads from a file under RUNNER_TEMP (_runner_file_commands/set_output_<id>) when the step ends, and
# rewrite the base's tools, which later steps of the job run.
PLANTED_RAN = 'open(os.path.join(os.environ["RUNNER_TEMP"], "planted-ran"), "a").write(%r)\n'
HEAD_CHECKERS = {
    "honest": "import os\n" + PLANTED_RAN % "honest\n" + 'print("dev/stream/bin/ossv-x:1-1")\n',
    "outputs": "import glob, os, re\n" + PLANTED_RAN % "outputs\n" + textwrap.dedent("""\
        for f in glob.glob(os.path.join(os.environ["RUNNER_TEMP"], "_runner_file_commands", "set_output_*")):
            with open(f) as g:
                text = g.read()
            text = re.sub(r"^(repository_lint|tests|controls|lps_pin|theories)=true$", r"\\1=false", text, flags=re.M)
            with open(f, "w") as g:
                g.write(text)
        """),
    "base tools": "import os\n" + PLANTED_RAN % "base tools\n" + textwrap.dedent("""\
        with open("base/tools/oft/lint.py", "a") as f:
            f.write("import os\\n" + %r)
        """) % (PLANTED_RAN % "a base tool ran the change's code\n")}


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
@unittest.skipUnless(shutil.which("jq"), "jq is not installed")
class PlanRunsNoChangeCodeTest(StandIn):
    """The plan job decides which judging jobs run and what `required` demands of them, so it runs no code of the
    change: its reach step, run on a change under dev/stream/, tools/ and theories/ with each stand-in above as the
    head's dev/stream/bin/ossv-tools-check, gives the same answers, leaves the base's tools as they were and runs the
    stand-in not at all.  The hunk rows are the stream_tools job's to work out (StreamChangedRowsTest)."""

    OUTPUT = "set_output_0f1e2d3c-4b5a-6978-8796-a5b4c3d2e1f0"

    def setUp(self):
        super().setUp()
        with open(os.path.join(self.dir, "bin", "python"), "w") as f:
            f.write('#!/bin/sh\nexec "%s" "$@"\n' % sys.executable)
        os.chmod(os.path.join(self.dir, "bin", "python"), 0o755)
        self.reach = next(s for s in load("pr.yml")["jobs"]["plan"]["steps"] if s.get("id") == "reach")

    def run_reach(self, checker):
        """The reach step, as the plan job runs it in its workspace: head/, a clone whose HEAD changes a file under
        dev/stream/, tools/oft/check.py and a file of theories/ from BASE and holds `checker` as its
        dev/stream/bin/ossv-tools-check; base/tools/oft/, a stand-in of the base's tools; changed.txt, the base
        step's list.  (its exit and output, its outputs, the artifact's rows, what the stand-in said it ran, the
        base's lint.py after the step; a later step imports the base's tools as the lint_since step does first)."""
        work = os.path.join(self.dir, "work-" + checker.replace(" ", "-"))
        head = os.path.join(work, "head")
        os.makedirs(head)
        files = {"dev/stream/bin/ossv-tools-check": HEAD_CHECKERS["honest"], "dev/stream/bin/ossv-x": "a\n",
                 "tools/oft/check.py": "X = 1\n", "theories/T.v": "Definition t := 1.\n"}
        for rel, text in files.items():
            os.makedirs(os.path.dirname(os.path.join(head, rel)), exist_ok=True)
            with open(os.path.join(head, rel), "w") as f:
                f.write(text)
        git(head, "init", "-q")
        git(head, "add", "-A")
        git(head, "commit", "-q", "-m", "the base")
        base = git(head, "rev-parse", "HEAD")
        for rel, text in (("dev/stream/bin/ossv-tools-check", HEAD_CHECKERS[checker]),
                          ("dev/stream/bin/ossv-x", "b\n"), ("tools/oft/check.py", "X = 2\n"),
                          ("theories/T.v", "Definition t := 2.\n")):
            with open(os.path.join(head, rel), "w") as f:
                f.write(text)
        git(head, "commit", "-q", "-am", "the change")
        tools = os.path.join(work, "base", "tools", "oft")
        os.makedirs(tools)
        for name, text in (("__init__.py", ""), ("layout.py", ""), ("lint.py", "LINT = 1\n")):
            with open(os.path.join(tools, name), "w") as f:
                f.write(text)
        temp = os.path.join(work, "runner-temp")
        os.makedirs(os.path.join(temp, "_runner_file_commands"))
        with open(os.path.join(temp, "changed.txt"), "w") as f:
            f.write(git(head, "diff", "--no-renames", "--name-only", base, "HEAD") + "\n")
        self.output = os.path.join(temp, "_runner_file_commands", self.OUTPUT)
        code, out, _ = self.run_step(self.reach["run"], {"BASE": base, "ROUTED": "true", "RUNNER_TEMP": temp},
                                     cwd=work)
        outputs = self.outputs()
        rows = None
        rows_file = os.path.join(temp, "stream-changed", "stream-changed.txt")
        if os.path.exists(rows_file):
            with open(rows_file) as f:
                rows = f.read().splitlines()
        with open(os.path.join(tools, "lint.py")) as f:
            lint_py = f.read()
        # a later step of the plan job, as lint_since runs the base's tools
        later = subprocess.run([sys.executable, "-c", "from oft import layout, lint"], cwd=work, capture_output=True,
                               text=True, env=dict(os.environ, PYTHONPATH="base/tools", RUNNER_TEMP=temp))
        said = ""
        if os.path.exists(os.path.join(temp, "planted-ran")):
            with open(os.path.join(temp, "planted-ran")) as f:
                said = f.read()
        return code, out + later.stderr, outputs, rows, said, lint_py

    def test_the_change_s_checker_runs_nowhere_in_the_plan_job(self):
        runs = {checker: self.run_reach(checker) for checker in HEAD_CHECKERS}
        honest = runs["honest"][2]
        for checker, (code, out, outputs, rows, said, lint_py) in runs.items():
            with self.subTest(checker=checker):
                self.assertEqual(code, 0, out)
                # the stand-in ran nowhere, and the base's tools are as they were, after a later step ran them
                self.assertEqual((said, lint_py), ("", "LINT = 1\n"), out)
                self.assertEqual(outputs, honest, out)
                # the rows the plan job hands the stream_tools job: the changed paths under dev/stream/ alone
                changed = ["dev/stream/bin/ossv-x"] + (["dev/stream/bin/ossv-tools-check"] if checker != "honest"
                                                       else [])
                self.assertEqual(sorted(rows), sorted(changed), out)
        self.assertEqual({k: honest[k] for k in ("repository_lint", "tests", "controls", "lps_pin", "theories",
                                                 "stream_tools")},
                         dict.fromkeys(("repository_lint", "tests", "controls", "lps_pin", "theories", "stream_tools"),
                                       "true"))

    def test_the_step_names_no_file_of_the_head_s_dev_stream(self):
        """The text as well as the run: no path of the head's dev/stream/ is run or put on a path in this step."""
        self.assertNotIn("ossv-tools-check", self.reach["run"])


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class StreamChangedRowsTest(StandIn):
    """The stream_tools job adds the hunk rows to the plan's path rows itself, with the change's own checker
    (`--write-changed -` from the plan's base), before its check reads them; the plan job runs no code of the change
    (PlanRunsNoChangeCodeTest)."""

    LINES = "the lines this change wrote under dev/stream/, by its own checker"

    def setUp(self):
        super().setUp()
        with open(os.path.join(self.dir, "bin", "python"), "w") as f:
            f.write('#!/bin/sh\nexec "%s" "$@"\n' % sys.executable)
        os.chmod(os.path.join(self.dir, "bin", "python"), 0o755)
        self.job = load("pr.yml")["jobs"]["stream_tools"]
        self.head = os.path.join(self.dir, "head")
        os.makedirs(os.path.join(self.head, "dev", "stream", "bin"))
        # a stand-in checker: it writes the arguments it was given, and one hunk row
        with open(os.path.join(self.head, "dev", "stream", "bin", "ossv-tools-check"), "w") as f:
            f.write("import os, sys\nwith open(os.path.join(os.environ['RUNNER_TEMP'], 'argv'), 'w') as f:\n"
                    "    f.write(' '.join(sys.argv[1:]))\nprint('dev/stream/bin/ossv-x:3-4')\n")
        git(self.head, "init", "-q")
        git(self.head, "add", "-A")
        git(self.head, "commit", "-q", "-m", "the base")
        self.base = git(self.head, "rev-parse", "HEAD")
        self.temp = os.path.join(self.dir, "runner-temp")
        os.makedirs(os.path.join(self.temp, "stream-changed"))
        self.rows = os.path.join(self.temp, "stream-changed", "stream-changed.txt")
        with open(self.rows, "w") as f:
            f.write("dev/stream/bin/ossv-x\n")

    def lines(self, base, routed):
        code, out, _ = self.run_step(step(self.job, self.LINES)["run"],
                                     {"BASE": base, "ROUTED": routed, "RUNNER_TEMP": self.temp}, cwd=self.head)
        with open(self.rows) as f:
            rows = f.read().splitlines()
        argv = os.path.join(self.temp, "argv")
        called = None
        if os.path.exists(argv):
            with open(argv) as f:
                called = f.read()
        return code, out, rows, called

    def test_the_change_s_checker_adds_its_hunks_from_the_plan_s_base(self):
        code, out, rows, called = self.lines(self.base, "true")
        self.assertEqual(code, 0, out)
        self.assertEqual(rows, ["dev/stream/bin/ossv-x", "dev/stream/bin/ossv-x:3-4"], out)
        self.assertEqual(called, "--root dev/stream --changed-since %s --write-changed -" % self.base, out)
        self.assertIn("the stream tools check reads 1 hunk(s)", out)

    def test_a_run_with_no_base_writes_no_hunk_and_a_base_that_is_no_commit_fails(self):
        code, out, rows, called = self.lines("", "false")
        self.assertEqual((code, rows, called), (0, ["dev/stream/bin/ossv-x"], None), out)
        code, out, rows, called = self.lines("not-a-commit", "true")
        self.assertEqual((code, called), (1, None), out)
        self.assertIn("the plan named no base commit", out)

    def test_the_rows_are_complete_before_the_check_reads_them(self):
        names = [s.get("name") for s in self.job["steps"]]
        download = names.index("the paths under dev/stream/ this change touches, from the plan job")
        self.assertEqual(names[download + 1:download + 3], [self.LINES, "the stream tools' check"])
        self.assertEqual(step(self.job, self.LINES)["env"],
                         {"BASE": "${{ needs.plan.outputs.base }}", "ROUTED": "${{ needs.plan.outputs.routed }}"})


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
                 lint="success", queued="false", made_from="false", made_from_result="skipped", made_from_proofs="[]",
                 public_rows="false", public_rows_result="skipped"):
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
                  # the LPS pin check: no release.yaml, toolchain/ or theories/ file changes in these cases, so it is
                  # skipped
                  "LPS_PIN": "false", "LPS_PIN_RESULT": "skipped",
                  # the made-from records' check: the plan's two answers and the made_from job's result
                  "MADE_FROM": made_from, "MADE_FROM_PROOFS": made_from_proofs, "MADE_FROM_RESULT": made_from_result,
                  # the public-before-hold rows' check: the plan's answer and the public_rows job's result
                  "PUBLIC_ROWS": public_rows, "PUBLIC_ROWS_RESULT": public_rows_result,
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

    def test_required_wants_the_made_from_job_exactly_when_the_plan_named_a_unit(self):
        """On the answer true the job must have passed, and on false it must not have run: a failure, a cancellation
        and a time-out (which GitHub gives as failure or cancelled) fail, and so does a job that did not run when it
        had to, or ran when nothing it reads changed.  A draft skips it with lint.  An answer that is neither true
        nor false fails."""
        for answer, result, want in (("true", "success", 0), ("true", "failure", 1), ("true", "cancelled", 1),
                                     ("true", "skipped", 1), ("false", "success", 1), ("false", "skipped", 0),
                                     ("", "skipped", 1), ("yes", "skipped", 1), ("yes", "success", 1)):
            with self.subTest(made_from=answer, result=result):
                rc, out = self.required("none", "0", "skipped", made_from=answer, made_from_result=result)
                self.assertEqual(rc, want, out)
        for result, want in (("skipped", 0), ("success", 1)):
            with self.subTest(draft=True, result=result):
                rc, out = self.required("draft", "0", "skipped", lint="skipped", queued="true", made_from="true",
                                        made_from_result=result)
                self.assertEqual(rc, want, out)

    def test_required_wants_the_made_from_job_for_a_unit_s_proofs_only_when_nothing_is_held(self):
        """made_from false and made_from_proofs a list: with the hold none the job must have passed, as on made_from
        true, and with the hold label it must not have run, as the job's if: says.  With the list [] it must not have
        run either.  Each error names the one cause that applies.  A made_from_proofs that does not start with [ and end
        with ] fails, whatever the job did."""
        proofs = '["projects/curl/fuzz_bufq"]'
        for hold, result, want in (("none", "success", 0), ("none", "skipped", 1), ("none", "failure", 1),
                                   ("none", "cancelled", 1), ("label", "skipped", 0), ("label", "success", 1)):
            with self.subTest(hold=hold, result=result):
                rc, out = self.required(hold, "0", "skipped", made_from_proofs=proofs, made_from_result=result)
                self.assertEqual(rc, want, out)
                if want:
                    self.assertIn("::error::the made-from records' check failed or did not run" if hold == "none" else
                                  "::error::the plan named only units whose proofs changed outside "
                                  "proofs/provenance/, and its hold is label, not none, yet the made_from job ran", out)
        with self.subTest(made_from_proofs="[]", result="success"):
            rc, out = self.required("none", "0", "skipped", made_from_result="success")
            self.assertEqual(rc, 1, out)
            self.assertIn("::error::the plan named no unit for the made_from job, yet it ran", out)
            self.assertNotIn("hold is", out)
        for answer in ("", "x", '["projects/curl/fuzz_bufq"', "{}"):
            for result in ("skipped", "success"):
                with self.subTest(made_from_proofs=answer, result=result):
                    rc, out = self.required("none", "0", "skipped", made_from_proofs=answer, made_from_result=result)
                    self.assertEqual(rc, 1, out)
                    self.assertIn("::error::the plan answered made_from_proofs '%s', not a JSON list" % answer, out)

    def test_required_wants_the_public_rows_job_exactly_when_the_record_changed(self):
        """As for made_from: on the answer true the job must have passed, and on false it must not have run; a draft
        skips it with lint; an answer that is neither true nor false fails."""
        for answer, result, want in (("true", "success", 0), ("true", "failure", 1), ("true", "cancelled", 1),
                                     ("true", "skipped", 1), ("false", "success", 1), ("false", "skipped", 0),
                                     ("", "skipped", 1), ("yes", "skipped", 1)):
            with self.subTest(public_rows=answer, result=result):
                rc, out = self.required("none", "0", "skipped", public_rows=answer, public_rows_result=result)
                self.assertEqual(rc, want, out)
        for result, want in (("skipped", 0), ("success", 1)):
            with self.subTest(draft=True, result=result):
                rc, out = self.required("draft", "0", "skipped", lint="skipped", queued="true", public_rows="true",
                                        public_rows_result=result)
                self.assertEqual(rc, want, out)

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

    def test_the_sweep_plans_as_many_shards_as_it_runs_at_once_and_as_its_units_need(self):
        """The sweep's --max-jobs is its matrix's max-parallel, so no shard waits for another, and it is at least
        what the units pack.SWEEP_TIMES times, less the ones --hosted leaves out, need for a shard of several of
        them to stay inside pack.CAP (pack.jobs_needed).  It stands above that floor because the plan gives a job
        of its own to each proved unit no run ever saw finish as well.  At 32 and with no measured table, run
        42556340137 lost two shards to the 6-hour limit and run 42597756616 lost seven."""
        jobs = load("weekly.yml")["jobs"]
        run = step(jobs["plan"], "plan")["run"]
        [planned] = re.findall(r"--max-jobs (\d+) --hosted", run)
        self.assertEqual(int(planned), jobs["sweep"]["strategy"]["max-parallel"])
        skip = pack.too_long_for_hosted(pack.sweep())
        floor = pack.jobs_needed(pack.load(), pack.times(), skip=skip)
        self.assertEqual(floor, 35)
        self.assertGreaterEqual(int(planned), floor)
        self.assertEqual(jobs["sweep"]["timeout-minutes"], 360)

    def test_the_sweep_s_summary_carries_a_line_for_every_unit_it_leaves_out(self):
        """The plan's `skipped` sentences reach the run summary, so a unit no hosted job can check is named
        there with the farm check of record that still stands for it, rather than quietly missing."""
        run = step(load("weekly.yml")["jobs"]["plan"], "plan")["run"]
        self.assertIn("jq -r '.skipped[]' \"$RUNNER_TEMP/plan.json\"", run)
        self.assertIn('>> "$GITHUB_STEP_SUMMARY"', run.split("jq -r '.skipped[]'")[1])

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
                     # the LPS pin check: these cases touch no release.yaml, toolchain/ or theories/ file, so it is
                     # skipped
                     "LPS_PIN": "false", "LPS_PIN_RESULT": "skipped",
                     # the made-from records' check: these cases touch no record, no unit's proofs and nothing every
                     # record reads
                     "MADE_FROM": "false", "MADE_FROM_PROOFS": "[]", "MADE_FROM_RESULT": "skipped",
                     # the public-before-hold rows' check: these cases touch no record
                     "PUBLIC_ROWS": "false", "PUBLIC_ROWS_RESULT": "skipped",
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


def image_job():
    """images.yml's image job."""
    return load("images.yml")["jobs"]["image"]


def image_step(step_id):
    """The image job's step of that id."""
    return next(s for s in image_job()["steps"] if s.get("id") == step_id)


# the names of the image job's env that pin the fork release, and the stock checker the fork checker is compared with
FORK_PINS = ("ROCQ_FORK_REPOSITORY", "ROCQ_FORK_TAG", "ROCQ_FORK_BRANCH", "ROCQ_FORK_COMMIT",
             "ROCQ_FORK_ARCHIVE_SHA256", "ROCQ_FORK_OPAM_VERSION", "STOCK_CHECKER")
# git as images.yml's steps call it, each call logged to $FAKE_GIT_LOG, a line each: `init DIR` makes DIR, `fetch`
# exits $FAKE_FETCH_RC (0 by default), `diff` prints $FAKE_GIT_DIFF and `ls-remote` prints $FAKE_LS_REMOTE; the -c and
# -C options before the command are passed over.
IMAGES_GIT = r"""#!/usr/bin/env bash
printf '%s\n' "$*" >> "$FAKE_GIT_LOG"
while [ "$1" = -c ] || [ "$1" = -C ]; do shift 2; done
case $1 in
  init) mkdir -p "${@: -1}" ;;
  fetch) exit "${FAKE_FETCH_RC:-0}" ;;
  diff) cat "$FAKE_GIT_DIFF" ;;
  ls-remote) cat "$FAKE_LS_REMOTE" ;;
  *) exit 9 ;;
esac
"""
# curl as the release step calls it, `curl -fsSL -o FILE URL`, each call logged to $FAKE_CURL_LOG: it writes the bytes
# of $FAKE_ARCHIVE to FILE
IMAGES_CURL = r"""#!/usr/bin/env bash
printf '%s\n' "$*" >> "$FAKE_CURL_LOG"
out=
while [ $# -gt 0 ]; do case $1 in -o) out=$2; shift 2 ;; *) shift ;; esac; done
[ -n "$out" ] || exit 9
cp "$FAKE_ARCHIVE" "$out"
"""
# docker as the checker's steps call it (a Python script, after its #! line), each call's arguments logged to
# $FAKE_DOCKER_LOG as a JSON list: `pull` passes, and `run [OPTIONS] IMAGE COMMAND...` answers from
# $FAKE_DOCKER_ANSWERS, {"IMAGE LAST-ARGUMENT": [exit, stdout, stderr]} (a rocq compile's last argument is its file,
# opam list's is --short, rocqchk's is -compare); a run it has no answer for exits 97.  A rocq compile first checks
# that the directory mounted at /work holds the six files of the proofs of False and their controls.
IMAGES_DOCKER = r"""
import json, os, sys
a = sys.argv[1:]
with open(os.environ["FAKE_DOCKER_LOG"], "a") as f:
    f.write(json.dumps(a) + "\n")
if a[:1] == ["pull"]:
    sys.exit(0)
if a[:1] != ["run"]:
    sys.exit(9)
i, mounts = 1, []
while a[i].startswith("-"):
    if a[i] == "--rm":
        i += 1
        continue
    if a[i] == "-v":
        mounts.append(a[i + 1])
    i += 2
image, command = a[i], a[i + 1:]
if command[:2] == ["rocq", "compile"]:
    work = [m[:-len(":/work")] for m in mounts if m.endswith(":/work")]
    files = ["Bad51.v", "Ok51.v", "Bad60.v", "Ok60.v", "Bad72.v", "Ok72.v"]
    if len(work) != 1 or not all(os.path.isfile(os.path.join(work[0], n)) and os.path.getsize(os.path.join(work[0], n))
                                 for n in files):
        sys.exit("docker stand-in: the directory mounted at /work, %r, lacks one of %s" % (work, files))
with open(os.environ["FAKE_DOCKER_ANSWERS"]) as f:
    answers = json.load(f)
key = "%s %s" % (image, command[-1])
if key not in answers:
    sys.stderr.write("docker stand-in: no answer for a run in %s of %s\n" % (image, " ".join(command)))
    sys.exit(97)
rc, out, err = answers[key]
sys.stdout.write(out)
sys.stderr.write(err)
sys.exit(rc)
"""


class ImagesStepStandIn(StandIn):
    """A step of images.yml, run as GitHub runs it with the fork release's pins as the image job's env writes them,
    against stand-ins that answer from files under the test's directory and reach no network: git, curl and docker
    (IMAGES_GIT, IMAGES_CURL, IMAGES_DOCKER), and a `python` that runs this test's own Python, which has PyYAML, as
    setup-python gives the job one.  The tests read the pins from images.yml and name no repository of the fork."""

    SHA = "b" * 40

    def setUp(self):
        super().setUp()
        env = image_job()["env"]
        self.assertEqual(sorted(k for k in env if k.startswith("ROCQ_FORK_") or k == "STOCK_CHECKER"),
                         sorted(FORK_PINS))
        self.pins = {k: str(env[k]) for k in FORK_PINS}
        stand_ins = {"git": IMAGES_GIT, "curl": IMAGES_CURL, "docker": "#!%s\n%s" % (sys.executable, IMAGES_DOCKER),
                     "python": '#!/bin/sh\nexec %s "$@"\n' % shlex.quote(sys.executable)}
        for name, text in stand_ins.items():
            path = os.path.join(self.dir, "bin", name)
            with open(path, "w") as f:
                f.write(text)
            os.chmod(path, 0o755)
        self.logs = {name: os.path.join(self.dir, name + ".log") for name in ("git", "curl", "docker")}
        self.answers = os.path.join(self.dir, "docker-answers.json")

    def answer(self, answers):
        """The stand-in docker's answers: {(image, last argument): (exit, stdout, stderr)}."""
        with open(self.answers, "w") as f:
            json.dump({"%s %s" % key: list(value) for key, value in answers.items()}, f)

    def logged(self, name):
        """The calls the stand-in `name` logged in the last step: a line each, and docker's as argument lists."""
        if not os.path.exists(self.logs[name]):
            return []
        with open(self.logs[name]) as f:
            lines = f.read().splitlines()
        return [json.loads(line) for line in lines] if name == "docker" else lines

    def run_images_step(self, s, env, cwd=None):
        """images.yml's step `s`, in `cwd` (by default the test's directory), with the fork release's pins, a fresh
        RUNNER_TEMP and `env`, which gives every name of the step's own env; the stand-ins' logs start empty.  (its
        exit, its output, the outputs it wrote)."""
        self.assertEqual(sorted(set(s.get("env", {})) - set(env)), [], "the step's env names the test gives no value")
        for path in list(self.logs.values()) + [self.output, os.path.join(self.api, "calls")]:
            if os.path.exists(path):
                os.remove(path)
        full = dict(self.pins, RUNNER_TEMP=tempfile.mkdtemp(prefix="runner-temp-", dir=self.dir),
                    FAKE_GIT_LOG=self.logs["git"], FAKE_CURL_LOG=self.logs["curl"],
                    FAKE_DOCKER_LOG=self.logs["docker"], FAKE_DOCKER_ANSWERS=self.answers)
        full.update(env)
        rc, out, _summary = self.run_step(s["run"], full, cwd=cwd or self.dir)
        return rc, out, self.outputs()

    def run_image_step(self, step_id, env, cwd=None):
        """The image job's step of that id, as run_images_step runs it."""
        return self.run_images_step(image_step(step_id), env, cwd)

    def url(self):
        """GitHub's archive of ROCQ_FORK_COMMIT, as the release step gives it (archive_url)."""
        return "%s/archive/%s.tar.gz" % (self.pins["ROCQ_FORK_REPOSITORY"], self.pins["ROCQ_FORK_COMMIT"])

    def name_step(self, key, build, run_id="19876543210", attempt="2"):
        """The name step of the image `key` and the build `build`, at the commit SHA, in run `run_id` (11 digits)
        and attempt `attempt`, in a checkout whose release.yaml pins ImagesAttestationTest.PINS."""
        checkout = os.path.join(self.dir, "checkout")
        os.makedirs(checkout, exist_ok=True)
        pins = ImagesAttestationTest.PINS
        with open(os.path.join(checkout, "release.yaml"), "w") as f:
            f.write("images:\n  checker: %s\n  runner: %s\n" % (pins["checker"], pins["runner"]))
        return self.run_image_step("name", {"KEY": key, "BUILD": build, "GITHUB_SHA": self.SHA,
                                            "GITHUB_RUN_ID": run_id, "GITHUB_RUN_ATTEMPT": attempt}, cwd=checkout)


def errors_in(out):
    """The ::error:: lines of a step's output."""
    return [line for line in out.splitlines() if line.startswith("::error::")]


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class ImagesForkTagTest(ImagesStepStandIn):
    """Each checker build of one run pushes under a tag of its own, so that no tag is ever moved: the name step gives
    the stock build <name>:build-<commit>-<run>-<attempt>, and the fork build a tag that starts with fork- (a reader
    that takes the package's newest build- tag never takes it), names the fork release (its tag, with / written as -,
    and the first 8 digits of its commit) and the run, and is a docker tag of at most 128 characters.  The runner has
    no fork build."""

    def test_the_stock_and_the_fork_build_of_one_run_have_two_tags(self):
        name, tags = ImagesAttestationTest.NAME, {}
        for build in ("stock", "fork"):
            with self.subTest(build=build):
                rc, out, got = self.name_step("checker", build)
                self.assertEqual(rc, 0, out)
                tags[build] = got.get("tag", "")
        self.assertNotEqual(tags["stock"], tags["fork"])
        self.assertEqual(tags["stock"], "%s:build-%s-19876543210-2" % (name, self.SHA))
        self.assertTrue(tags["fork"].startswith(name + ":fork-"), tags["fork"])
        part = tags["fork"][len(name) + 1:]
        self.assertIn(self.pins["ROCQ_FORK_TAG"].replace("/", "-"), part)
        self.assertIn(self.pins["ROCQ_FORK_COMMIT"][:8], part)
        self.assertRegex(part, r"\A[A-Za-z0-9_][A-Za-z0-9_.-]*\Z")
        self.assertLessEqual(len(part), 128)
        # another run, or another attempt of this one, pushes its fork image under another tag
        for run_id, attempt in (("19876543211", "2"), ("19876543210", "3")):
            with self.subTest(run=run_id, attempt=attempt):
                rc, out, got = self.name_step("checker", "fork", run_id, attempt)
                self.assertEqual(rc, 0, out)
                self.assertNotIn(got.get("tag"), (tags["fork"], None), out)

    def test_the_runner_has_no_fork_build(self):
        rc, out, got = self.name_step("runner", "fork")
        self.assertEqual(rc, 1, out)
        self.assertIn("::error::only the checker has a fork build, not runner", out)
        self.assertNotIn("tag", got)
        rc, out, got = self.name_step("runner", "stock")
        self.assertEqual((rc, got.get("tag")),
                         (0, "%s:build-%s-19876543210-2" % (ImagesAttestationTest.IMAGE % "runner", self.SHA)), out)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class ImagesGhcrOnlyTest(ImagesStepStandIn):
    """The fork build is pushed as the stock build is, to ghcr.io and nowhere else: under the checker's own package
    name, by the one push of the image job, the push step's `docker push` of the tag the build step gave the image.  No
    step gives the image another name, pushes it by another command or signs in to another registry, and the job uses
    no action but checkout, setup-python, attest-build-provenance and upload-artifact."""

    ACTIONS = ("actions/checkout", "actions/setup-python", "actions/attest-build-provenance", "actions/upload-artifact")
    # a command that would give the image another name, or push or copy it
    PUSHERS = (r"\bdocker\s+(?:image\s+)?tag\s", r"\bimagetools\s+create\b", r"\b(?:crane|skopeo|oras)\b", r"--push\b",
               r"\btype=registry\b", r"\bpush=true\b")

    def test_the_fork_build_has_the_stock_build_s_package_name(self):
        for build in ("stock", "fork"):
            with self.subTest(build=build):
                rc, out, got = self.name_step("checker", build)
                self.assertEqual(rc, 0, out)
                self.assertEqual(got.get("name"), ImagesAttestationTest.NAME, out)

    def test_the_one_push_is_the_push_step_s_of_the_built_tag(self):
        pushes, builds = [], []
        for s in image_job()["steps"]:
            with self.subTest(step=s.get("id") or s.get("name") or s.get("uses")):
                if "uses" in s:
                    self.assertIn(s["uses"].split("@")[0], self.ACTIONS)
                    continue
                run = s["run"]
                for pattern in self.PUSHERS:
                    self.assertIsNone(re.search(pattern, run), pattern)
                self.assertEqual(set(re.findall(r"\bdocker\s+login\s+(\S+)", run)) - {"ghcr.io"}, set())
                pushes += [(s.get("id"), line.strip()) for line in run.splitlines()
                           if re.search(r"\bdocker\s+push\s", line)]
                if re.search(r"\bdocker\s+buildx\s+build\s", run):
                    builds.append(s)
        self.assertEqual(pushes, [("push", 'docker push --quiet "$TAG"')])
        self.assertEqual(len(builds), 1)
        self.assertEqual(re.findall(r"(?<!\S)(?:-t|--tag)(?:\s+|=)(\S+)", builds[0]["run"]), ['"$TAG"'])
        for s in (builds[0], image_step("push")):
            self.assertEqual(s["env"]["TAG"], "${{ steps.name.outputs.tag }}")


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class ImagesLegsTest(unittest.TestCase):
    """The image job's legs when the plan names both images: the checker's stock and fork builds and the runner's
    stock build, and no fork build of the runner.  Each step whose condition reads matrix.build runs on the checker's
    fork build alone, the checks of the fork release and of the fork image among them; the package list runs on both
    checker builds and not on the runner's."""

    FORK_ONLY = ("release", "context", "record", "refusals", "compare", "scan")

    def legs(self):
        """The legs GitHub makes of the job's matrix when the plan names both images: [(image, build)]."""
        matrix = image_job()["strategy"]["matrix"]
        self.assertNotIn("include", matrix)
        scope = {"needs": {"plan": {"outputs": {"images": '["checker","runner"]'}}}}
        images = helpers.gh_value(matrix["image"], scope, {"fromJSON": json.loads})
        return [(i, b) for i in images for b in matrix["build"]
                if not any(all({"image": i, "build": b}.get(k) == v for k, v in e.items())
                           for e in matrix.get("exclude", []))]

    def runs_on(self, s):
        """The legs the step `s` runs on, its condition read as GitHub reads it when every step before it passed."""
        functions = {"always": lambda: True, "success": lambda: True}
        return [(i, b) for i, b in self.legs()
                if helpers.gh_truthy(helpers.gh_value("${{ %s }}" % s.get("if", "success()"),
                                                      {"matrix": {"image": i, "build": b}}, functions))]

    def test_the_checker_is_built_twice_and_the_runner_once(self):
        self.assertEqual(sorted(self.legs()), [("checker", "fork"), ("checker", "stock"), ("runner", "stock")])

    def test_each_step_that_reads_the_build_runs_on_the_checker_s_fork_build_alone(self):
        fork_only = []
        for s in image_job()["steps"]:
            if re.search(r"\bmatrix\.build\b", str(s.get("if", ""))):
                with self.subTest(step=s.get("id") or s["name"]):
                    self.assertEqual(self.runs_on(s), [("checker", "fork")])
                    fork_only.append(s.get("id"))
        for step_id in self.FORK_ONLY:
            self.assertIn(step_id, fork_only)

    def test_the_package_list_runs_on_both_checker_builds(self):
        self.assertEqual(sorted(self.runs_on(image_step("packages"))), [("checker", "fork"), ("checker", "stock")])


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class ImagesPushAfterChecksTest(unittest.TestCase):
    """A checker is pushed only after each check of it passed, since a push makes the image public at once: in the
    image job the push step comes after the build and after each check of the built image (its build record, its
    package list and, on the fork build, the refusal of the three proofs of False, rocqchk's -compare and the scan of
    the release gate's image job), no such check goes on past its own failure (continue-on-error), and on no leg does
    the push run once a step before it has failed.  So a fork checker that compiles a proof of False, or whose scan
    leaves a hit, never reaches ghcr.io (OSSV-582 R1 and R2)."""

    CHECKS = ("record", "packages", "refusals", "compare", "scan")
    LEGS = (("checker", "stock"), ("checker", "fork"), ("runner", "stock"))
    # GitHub adds success() && to a step's condition that calls none of these
    STATUS = re.compile(r"\b(?:success|failure|always|cancelled)\s*\(")

    def runs(self, s, leg, failed):
        """Whether GitHub runs the step `s` on `leg` (image, build) when a step before it failed (`failed`) or none
        did, the run not cancelled."""
        text = s.get("if", "success()")
        if isinstance(text, bool):
            return text
        text = str(text).strip()
        whole = re.fullmatch(r"\$\{\{(.*)\}\}", text, re.S)
        text = whole.group(1) if whole else text
        if not self.STATUS.search(text):
            text = "success() && (%s)" % text
        functions = {"success": lambda: not failed, "failure": lambda: failed, "always": lambda: True,
                     "cancelled": lambda: False}
        return helpers.gh_truthy(helpers.gh_value("${{ %s }}" % text, {"matrix": dict(zip(("image", "build"), leg))},
                                                  functions))

    def test_the_push_comes_after_the_build_and_each_check(self):
        steps = image_job()["steps"]
        ids = [s.get("id") for s in steps]
        builds = [i for i, s in enumerate(steps) if re.search(r"\bdocker\s+buildx\s+build\s", s.get("run", ""))]
        self.assertEqual(len(builds), 1)
        push = ids.index("push")
        for check in self.CHECKS:
            with self.subTest(check=check):
                self.assertIn(check, ids)
                self.assertLess(builds[0], ids.index(check), "the step %s comes before the build" % check)
                self.assertLess(ids.index(check), push, "the step %s comes after the push" % check)
                self.assertFalse(steps[ids.index(check)].get("continue-on-error", False),
                                 "a failure of the step %s does not fail the leg" % check)
        self.assertFalse(steps[builds[0]].get("continue-on-error", False))

    def test_a_failed_step_before_the_push_stops_the_push_on_each_leg(self):
        push = image_step("push")
        for leg in self.LEGS:
            with self.subTest(leg=leg):
                self.assertTrue(self.runs(push, leg, failed=False), "the push does not run when every step passed")
                self.assertFalse(self.runs(push, leg, failed=True), "the push runs after a step before it failed")


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
@unittest.skipUnless(shutil.which("jq"), "jq is not installed")
class ImagesPlanInputTest(ImagesStepStandIn):
    """images.yml is an input of the checker, since it names the fork release and holds the fork build's steps: the
    plan step of a push to main whose diff from the push before holds images.yml alone names the checker (both of its
    builds) and reads nothing of the public tools (no gh call); a push that changes no input names nothing."""

    BEFORE = "d" * 40

    def plan(self, changed):
        """The plan step of a push whose diff from BEFORE holds the paths `changed`."""
        diff = os.path.join(self.dir, "diff.txt")
        with open(diff, "w") as f:
            f.write("".join(path + "\n" for path in changed))
        plan = next(s for s in load("images.yml")["jobs"]["plan"]["steps"] if s.get("id") == "plan")
        return self.run_images_step(plan, {"GH_TOKEN": "t", "EVENT": "push", "CHOICE": "", "BEFORE": self.BEFORE,
                                           "GITHUB_REF": "refs/heads/main", "GITHUB_REPOSITORY_OWNER": "acme",
                                           "FAKE_GIT_DIFF": diff})

    def test_a_push_that_changes_images_yml_alone_builds_the_checker(self):
        for changed, images in (([".github/workflows/images.yml"], '["checker"]'), (["README.md"], "[]")):
            with self.subTest(changed=changed):
                rc, out, got = self.plan(changed)
                self.assertEqual(rc, 0, out)
                self.assertEqual(got.get("images"), images, out)
                self.assertEqual(self.calls(), [], out)
                calls = self.logged("git")
                self.assertTrue(any(c.split()[:1] == ["fetch"] and self.BEFORE in c for c in calls), calls)
                self.assertTrue(any(" diff " in " %s " % c and self.BEFORE in c for c in calls), calls)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class ImagesForkReleaseTest(ImagesStepStandIn):
    """The release step checks the fork release before anything is built from it: the fork's repository has the tag
    (its peeled line, for an annotated tag) and the branch at ROCQ_FORK_COMMIT, and GitHub's archive of that commit has
    the sha256 ROCQ_FORK_ARCHIVE_SHA256.  Each failure is one ::error:: that names what failed, and a ref that fails
    stops the step before the download."""

    ARCHIVE = b"the fork's archive, as the stand-in curl downloads it\n"
    OTHER = "e" * 40

    def refs(self, tag_at=None, branch=True):
        """What ls-remote prints of the fork's repository: another branch, the release branch at the commit (unless
        `branch` is false), the annotated tag's own line, and its peeled line at `tag_at` (by default the commit)."""
        commit, tag = self.pins["ROCQ_FORK_COMMIT"], self.pins["ROCQ_FORK_TAG"]
        lines = ["%s\trefs/heads/main" % self.OTHER]
        if branch:
            lines.append("%s\trefs/heads/%s" % (commit, self.pins["ROCQ_FORK_BRANCH"]))
        lines += ["%s\trefs/tags/%s" % ("d" * 40, tag), "%s\trefs/tags/%s^{}" % (tag_at or commit, tag)]
        return "".join(line + "\n" for line in lines)

    def release(self, refs, archive=ARCHIVE):
        """The release step, ls-remote printing `refs` and curl downloading `archive`, with ROCQ_FORK_ARCHIVE_SHA256
        the sha256 of ARCHIVE and the other pins images.yml's."""
        env = {"FAKE_LS_REMOTE": os.path.join(self.dir, "ls-remote.txt"),
               "FAKE_ARCHIVE": os.path.join(self.dir, "archive.tar.gz"),
               "ROCQ_FORK_ARCHIVE_SHA256": hashlib.sha256(self.ARCHIVE).hexdigest()}
        with open(env["FAKE_LS_REMOTE"], "w") as f:
            f.write(refs)
        with open(env["FAKE_ARCHIVE"], "wb") as f:
            f.write(archive)
        return self.run_image_step("release", env)

    def test_the_release_passes_when_its_refs_and_its_archive_are_the_pinned_ones(self):
        rc, out, got = self.release(self.refs())
        self.assertEqual(rc, 0, out)
        self.assertEqual(errors_in(out), [], out)
        self.assertEqual(got.get("archive_url"), self.url(), out)
        self.assertEqual(self.logged("git"), ["ls-remote " + self.pins["ROCQ_FORK_REPOSITORY"]], out)
        self.assertEqual([c.split()[-1] for c in self.logged("curl")], [self.url()], out)

    def test_the_release_fails_when_a_ref_is_elsewhere_or_the_archive_differs(self):
        changed = self.ARCHIVE + b"and a changed byte\n"
        for name, refs, archive, named, downloads in (
                ("the tag at another commit", self.refs(tag_at=self.OTHER), self.ARCHIVE,
                 ["the tag %s" % self.pins["ROCQ_FORK_TAG"], self.OTHER], False),
                ("no branch", self.refs(branch=False), self.ARCHIVE,
                 ["the branch %s at ''" % self.pins["ROCQ_FORK_BRANCH"]], False),
                ("another archive", self.refs(), changed, [self.url(), hashlib.sha256(changed).hexdigest()], True)):
            with self.subTest(case=name):
                rc, out, got = self.release(refs, archive)
                self.assertEqual(rc, 1, out)
                errors = errors_in(out)
                self.assertEqual(len(errors), 1, out)
                for text in named:
                    self.assertIn(text, errors[0])
                self.assertNotIn("archive_url", got)
                self.assertEqual(bool(self.logged("curl")), downloads, out)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class ImagesProofsOfFalseTest(ImagesStepStandIn):
    """The refusals step passes, and sets its verdict, only when each of the three public proofs of False, Bad51.v,
    Bad60.v and Bad72.v, compiles in STOCK_CHECKER and is refused in the fork image with a type error (its output, with
    blanks and newlines squeezed, holds "while it is expected to have type"), and each control, Ok51.v, Ok60.v and
    Ok72.v, compiles in the fork image."""

    TAG = ImagesAttestationTest.NAME + ":fork-test"
    # Rocq's refusal, its words across a newline as Rocq breaks a long message
    TYPE_ERROR = ('File "./%s", line 4, characters 7-80:\nError:\nThe term "eq_refl" has type "q = q"\n'
                  'while it is\n      expected to have type "q = p".\n')
    NUMBERS = ("51", "60", "72")

    def refusals(self, changes=None):
        """The refusals step, the stand-in docker compiling each proof of False in STOCK_CHECKER, refusing it in TAG
        with TYPE_ERROR and compiling each control in TAG, except as `changes`, {(stock or fork, file): (exit,
        output)}, says.  (its exit, its output, its outputs)."""
        images = {"stock": self.pins["STOCK_CHECKER"], "fork": self.TAG}
        answers = {}
        for n in self.NUMBERS:
            answers[(images["stock"], "Bad%s.v" % n)] = (0, "", "")
            answers[(images["fork"], "Bad%s.v" % n)] = (1, "", self.TYPE_ERROR % ("Bad%s.v" % n))
            answers[(images["fork"], "Ok%s.v" % n)] = (0, "", "")
        for (kind, name), (rc, text) in (changes or {}).items():
            answers[(images[kind], name)] = (rc, "", text)
        self.answer(answers)
        return self.run_image_step("refusals", {"TAG": self.TAG})

    def test_the_fork_image_refuses_each_proof_of_false_that_the_stock_checker_compiles(self):
        rc, out, got = self.refusals()
        self.assertEqual(rc, 0, out)
        self.assertEqual(errors_in(out), [], out)
        self.assertTrue(got.get("verdict"), out)
        stock, fork = self.pins["STOCK_CHECKER"], self.TAG
        compiled = sorted((c[c.index("rocq") - 1], c[-1]) for c in self.logged("docker") if c[0] == "run")
        self.assertEqual(compiled, sorted([(stock, "Bad%s.v" % n) for n in self.NUMBERS] +
                                          [(fork, k + n + ".v") for k in ("Bad", "Ok") for n in self.NUMBERS]))

    def test_the_step_fails_unless_each_proof_and_each_control_does_as_it_must(self):
        anomaly = 'Error: Anomaly "Uncaught exception Not_found." Please report.\n'
        for name, changes, error in (
                ("a proof of False compiles in the fork image", {("fork", "Bad60.v"): (0, "")},
                 "Bad60.v, a proof of False, compiles in the fork image"),
                ("a proof of False is refused with no type error", {("fork", "Bad72.v"): (1, anomaly)},
                 "Bad72.v fails in the fork image"),
                ("a proof of False fails in the stock checker", {("stock", "Bad51.v"): (1, anomaly)},
                 "Bad51.v does not compile in the stock checker"),
                ("a control fails in the fork image", {("fork", "Ok60.v"): (1, self.TYPE_ERROR % "Ok60.v")},
                 "Ok60.v, the control of Bad60.v, does not compile in the fork image")):
            with self.subTest(case=name):
                rc, out, got = self.refusals(changes)
                self.assertEqual(rc, 1, out)
                errors = errors_in(out)
                self.assertEqual(len(errors), 1, out)
                self.assertIn(error, errors[0])
                self.assertNotIn("verdict", got)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class ImagesCompareTest(ImagesStepStandIn):
    """The compare step: the fork image's rocqchk takes -compare, so that, given it with no argument, rocqchk exits 1
    and prints on stderr its usage, one line of which starts, after blanks, with "-compare config".  A rocqchk that
    exits 0, or whose usage on stderr has no such line, fails the step."""

    TAG = ImagesAttestationTest.NAME + ":fork-test"
    USAGE = "Usage: rocqchk <options> modules\n\n  -norec <module>  check <module> but none of its dependencies\n"
    LINE = " \t-compare config  compare the libraries with those a config file names\n"
    # a usage with no line that starts with the option: the line that names it starts with rocqchk
    REFUSED = "rocqchk: unknown option -compare config\n" + USAGE

    def compare(self, rc, stdout, stderr):
        """The compare step, rocqchk -compare in TAG exiting `rc` and printing `stdout` and `stderr`."""
        self.answer({(self.TAG, "-compare"): (rc, stdout, stderr)})
        return self.run_image_step("compare", {"TAG": self.TAG})

    def test_a_rocqchk_that_exits_1_with_the_line_on_stderr_passes(self):
        rc, out, got = self.compare(1, "", self.USAGE + self.LINE)
        self.assertEqual(rc, 0, out)
        self.assertEqual(errors_in(out), [], out)
        self.assertIn("its usage line: -compare config", out)
        self.assertTrue(got.get("verdict"), out)
        self.assertEqual([c[c.index(self.TAG):] for c in self.logged("docker")], [[self.TAG, "rocqchk", "-compare"]])

    def test_a_rocqchk_that_exits_0_or_has_no_such_line_on_stderr_fails(self):
        for name, rc, stdout, stderr, error in (
                ("no line starts with -compare config", 1, "", self.REFUSED,
                 "prints on stderr no usage line that starts with -compare config"),
                ("the line on stdout alone", 1, self.USAGE + self.LINE, self.USAGE,
                 "prints on stderr no usage line that starts with -compare config"),
                ("an exit of 0", 0, "", self.USAGE + self.LINE, "exits 0, not 1")):
            with self.subTest(case=name):
                rc_, out, got = self.compare(rc, stdout, stderr)
                self.assertEqual(rc_, 1, out)
                self.assertEqual(errors_in(out), ["::error::rocqchk -compare in %s %s" % (self.TAG, error)], out)
                self.assertNotIn("verdict", got)


# docker as the scan step calls it: `save TAG` writes the saved image $FAKE_SAVED, `pull` passes, and `image inspect
# -f FORMAT IMAGE` prints the base image's layers, $FAKE_BASE_LAYERS
SCAN_DOCKER = r"""#!/usr/bin/env bash
case $1 in
  save) cat "$FAKE_SAVED" ;;
  pull) ;;
  image) cat "$FAKE_BASE_LAYERS" ;;
  *) exit 9 ;;
esac
"""
# ossv-imgverify of an image none of whose members it proves public (run as python3 ossv-imgverify OUT OCI ADDED
# DOCKERFILE ... [--hits HITS.tsv] ...): members.tsv lists no proven member; with --hits, every uncleared flag hit of
# HITS.tsv that is not of the embedded or encoded class remains, as ossv-imgverify's read_failing_hits takes them, and
# it exits 1 when one remains
SCAN_IMGVERIFY = r"""
import csv, os, sys
a = sys.argv[1:]
out = a[0]
os.makedirs(out, exist_ok=True)
with open(os.path.join(out, "members.tsv"), "w") as f:
    f.write("member\tverdict\tevidence\n")
summary = "members by verdict\nupstream\t0\nderived\t0\nunproven\t0\n"
if "--hits" not in a:
    with open(os.path.join(out, "summary.txt"), "w") as f:
        f.write(summary + "failing hits\tnot supplied\n")
    sys.exit(0)
with open(a[a.index("--hits") + 1], newline="") as f:
    rows = [r for r in csv.DictReader(f, delimiter="\t")
            if r["tier"] == "flag" and r["class"] not in ("embedded", "encoded") and r["cleared_by"] == "-"]
with open(os.path.join(out, "remaining.tsv"), "w") as f:
    f.write("file\toffset\tneedle\treason\n" + "".join("%s\t%s\t%s\tunproven\n" % (r["file"], r["offset"], r["needle"])
                                                       for r in rows))
with open(os.path.join(out, "summary.txt"), "w") as f:
    f.write(summary + "failing hits\t%d\ncleared hits\t0\nremaining hits\t%d\n" % (len(rows), len(rows)))
sys.exit(1 if rows else 0)
"""


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
@unittest.skipUnless(os.path.isfile(os.path.join(REPO, "dev", "stream", "bin", "ossv-binscan")),
                     "no dev/stream/bin/ossv-binscan: the internal repository alone has it")
class ImagesForkScanHeldTest(ImagesStepStandIn):
    """The scan step scans the fork image for the held fuzz targets too, as the release gate's image job does
    (tools/publish/gate-job, job_image and held_list): it reads the held entries of the checkout's tools/publish with
    tools/publish/release_pins.py held-lines and gives them to dev/stream/bin/ossv-binscan as --held, whose hits no
    row of the exception table clears.  So a fork image whose added layer holds a held entry's name fails the step,
    before its push, and the same image without that name passes; the held entries are in none of the step's outputs
    that the run uploads.  The case runs the step in a checkout whose dev/stream/bin/ holds the real ossv-binscan, the
    exception table and the scanner's release_pins.py beside it, and a stand-in ossv-imgverify that proves no member
    public and so clears no hit, and whose tools/publish/ holds the real release_pins.py and a withheld.yaml of one
    made-up held entry; it runs on a saved image of a base layer and one added layer (a stand-in docker), with the
    image unpacked under the test's directory in place of /var/tmp/gate/oci."""

    HELD = "acme/fuzz_held"
    OCI = "/var/tmp/gate/oci"
    # the tools the step installs when the runner lacks them: here each is on PATH, and the image they would read
    # (an uncompressed tar) never needs them
    TOOLS = ("zstd", "lz4", "ar", "bzip2", "xz")

    def setUp(self):
        super().setUp()
        # a sudo that fails, so that a step that would install a tool here fails rather than reaching apt-get
        sudo = "#!/bin/sh\necho \"sudo $*: not in this case\" >&2\nexit 97\n"
        for name, text in [("docker", SCAN_DOCKER), ("sudo", sudo)] + [(t, "#!/bin/sh\nexit 9\n") for t in self.TOOLS]:
            path = os.path.join(self.dir, "bin", name)
            with open(path, "w") as f:
                f.write(text)
            os.chmod(path, 0o755)

    def saved(self, notes):
        """A saved image (docker save) of a base layer and one added layer, whose file home/opam/notes.txt holds the
        bytes NOTES: (the saved tar's path, the path of the base's layers as docker image inspect prints them)."""
        def tar(members):
            data = io.BytesIO()
            with tarfile.open(fileobj=data, mode="w") as tf:
                for path, body in members.items():
                    info = tarfile.TarInfo(path)
                    info.size = len(body)
                    tf.addfile(info, io.BytesIO(body))
            return data.getvalue()
        blob = lambda body: "blobs/sha256/" + hashlib.sha256(body).hexdigest()
        base = tar({"etc/os-release": b"NAME=base\n"})
        added = tar({"home/opam/README": b"a layer of the checker image\n", "home/opam/notes.txt": notes})
        diff_ids = ["sha256:" + hashlib.sha256(layer).hexdigest() for layer in (base, added)]
        config = json.dumps({"rootfs": {"diff_ids": diff_ids}}).encode()
        manifest = json.dumps([{"Config": blob(config), "Layers": [blob(base), blob(added)]}]).encode()
        saved = tempfile.mkstemp(prefix="saved-", suffix=".tar", dir=self.dir)[1]
        with open(saved, "wb") as f:
            f.write(tar({"manifest.json": manifest, blob(config): config, blob(base): base, blob(added): added}))
        layers = tempfile.mkstemp(prefix="base-layers-", dir=self.dir)[1]
        with open(layers, "w") as f:
            f.write(diff_ids[0] + "\n")
        return saved, layers

    def scan(self, notes):
        """The scan step on the image saved(NOTES): (its exit, its output, its outputs, its RUNNER_TEMP)."""
        checkout = tempfile.mkdtemp(prefix="checkout-", dir=self.dir)
        stream_bin = os.path.join(checkout, "dev", "stream", "bin")
        publish = os.path.join(checkout, "tools", "publish")
        os.makedirs(stream_bin)
        os.makedirs(publish)
        # the real scanner and the files beside it whose names start with its name (the table it reads and the
        # retired one it does not), and its own release_pins.py (the held-entry rule of its --held)
        source = os.path.join(REPO, "dev", "stream", "bin")
        for name in [n for n in os.listdir(source) if n.startswith("ossv-binscan")] + ["release_pins.py"]:
            shutil.copy(os.path.join(source, name), stream_bin)
        with open(os.path.join(stream_bin, "ossv-imgverify"), "w") as f:
            f.write(SCAN_IMGVERIFY)
        # the reader of the held entries, beside the withheld.yaml it reads
        shutil.copy(os.path.join(REPO, "tools", "publish", "release_pins.py"), publish)
        with open(os.path.join(publish, "withheld.yaml"), "w") as f:
            f.write("withheld: []\nheld_harnesses:\n- %s\n" % self.HELD)
        temp = tempfile.mkdtemp(prefix="runner-temp-", dir=self.dir)
        with open(os.path.join(temp, "fork-build.json"), "w") as f:
            f.write("{}\n")
        s = image_step("scan")
        self.assertIn(self.OCI, s["run"])
        s = dict(s, run=s["run"].replace(self.OCI, os.path.join(self.dir, "gate", "oci")))
        saved, layers = self.saved(notes)
        rc, out, got = self.run_images_step(s, {"TAG": ImagesAttestationTest.NAME + ":fork-test",
                                                "BASE": "ocaml/opam:base@sha256:" + "6e" * 32, "RUNNER_TEMP": temp,
                                                "FAKE_SAVED": saved, "FAKE_BASE_LAYERS": layers}, cwd=checkout)
        return rc, out, got, temp

    def test_an_image_without_a_held_name_passes_and_its_outputs_name_no_held_entry(self):
        rc, out, got, temp = self.scan(b"a file of the checker image\n")
        self.assertEqual(rc, 0, out)
        self.assertEqual(errors_in(out), [], out)
        self.assertIn("held entries, the --held of the scan: 1", out)
        self.assertTrue(got.get("verdict", "").startswith("no hit remains"), out)
        for root, _dirs, files in os.walk(os.path.join(temp, "fork-scan")):
            for name in files:
                with open(os.path.join(root, name), "rb") as f:
                    self.assertNotIn(self.HELD.encode(), f.read(), os.path.join(root, name))

    def test_an_image_that_holds_a_held_name_fails_the_scan(self):
        rc, out, got, temp = self.scan(("built for %s\n" % self.HELD).encode())
        self.assertEqual(rc, 1, out)
        self.assertNotIn("verdict", got)
        errors = errors_in(out)
        self.assertEqual(len(errors), 1, out)
        self.assertIn("hits remain", errors[0])
        with open(os.path.join(temp, "fork-scan", "scan-image", "hits.tsv")) as f:
            needles = [line.split("\t")[3] for line in f.read().splitlines()[1:]]
        self.assertTrue(needles, out)
        self.assertEqual([n for n in needles if not n.startswith("held:%s:" % self.HELD)], [], out)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class ImagesOpamPackagesTest(ImagesStepStandIn):
    """The fork build's OPAM_PACKAGES is the Dockerfile's default with rocq-runtime.9.2.0 and rocq-core.9.2.0 at the
    fork's version and coq-core added at it: the context step refuses a default that lacks either, before it fetches
    anything.  The package list step holds the fork image to that list: rocq-runtime, rocq-core and coq-core at
    ROCQ_FORK_OPAM_VERSION, and every other package of the default at the version the default names.  For the stock
    build it checks no version."""

    TAGS = {"stock": ImagesAttestationTest.NAME + ":build-test", "fork": ImagesAttestationTest.NAME + ":fork-test"}

    def dockerfile(self):
        """toolchain/checker.Dockerfile as it is."""
        with open(os.path.join(REPO, "toolchain", "checker.Dockerfile")) as f:
            return f.read()

    def default(self):
        """The packages of the Dockerfile's default OPAM_PACKAGES."""
        found = re.findall(r'^ARG OPAM_PACKAGES="([^"]*)"$', self.dockerfile(), re.M)
        self.assertEqual(len(found), 1)
        return found[0].split()

    def checkout(self, dockerfile):
        """A checkout whose toolchain/checker.Dockerfile is `dockerfile`."""
        root = tempfile.mkdtemp(prefix="checkout-", dir=self.dir)
        os.mkdir(os.path.join(root, "toolchain"))
        with open(os.path.join(root, "toolchain", "checker.Dockerfile"), "w") as f:
            f.write(dockerfile)
        return root

    def test_the_context_step_refuses_a_default_that_lacks_a_package_the_fork_replaces(self):
        for token in ("rocq-core.9.2.0", "rocq-runtime.9.2.0"):
            with self.subTest(lacks=token):
                cut, n = re.subn(r'^ARG OPAM_PACKAGES="([^"]*)"$',
                                 lambda m: 'ARG OPAM_PACKAGES="%s"' % " ".join(t for t in m.group(1).split()
                                                                               if t != token),
                                 self.dockerfile(), flags=re.M)
                self.assertEqual(n, 1)
                self.assertNotEqual(cut, self.dockerfile())
                rc, out, got = self.run_image_step("context", {"ARCHIVE_URL": self.url()}, cwd=self.checkout(cut))
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::the default OPAM_PACKAGES of toolchain/checker.Dockerfile lacks %s" % token,
                              out)
                self.assertEqual((self.logged("git"), self.logged("docker")), ([], []), out)
                self.assertNotIn("opam_packages", got)
        # the Dockerfile as it is lacks neither: the step names the fork build's packages and goes on to its first
        # fetch, which the stand-in git refuses here
        version = self.pins["ROCQ_FORK_OPAM_VERSION"]
        want = []
        for t in self.default():
            want += {"rocq-runtime.9.2.0": ["rocq-runtime." + version],
                     "rocq-core.9.2.0": ["rocq-core." + version, "coq-core." + version]}.get(t, [t])
        rc, out, got = self.run_image_step("context", {"ARCHIVE_URL": self.url(), "FAKE_FETCH_RC": "1"},
                                           cwd=self.checkout(self.dockerfile()))
        self.assertEqual(rc, 1, out)
        self.assertIn("OPAM_PACKAGES of the fork build: " + " ".join(want), out)
        self.assertIn("::error::the fetch of rocq-prover/opam", out)

    def listed(self, build):
        """{name: version} of the packages opam lists in the checker of `build`, as it must be: the default's, the
        fork's three at its version in the fork build, and two packages they depend on."""
        version = self.pins["ROCQ_FORK_OPAM_VERSION"]
        packages = {"ocaml": "4.14.2", "ocamlfind": "1.9.8"}
        for t in self.default():
            name, v = t.split(".", 1)
            packages[name] = version if build == "fork" and name in ("rocq-runtime", "rocq-core") else v
        if build == "fork":
            packages["coq-core"] = version
        return packages

    def package_list(self, build, packages):
        """The package list step of `build`, opam listing `packages` in its image and listed("stock") in
        STOCK_CHECKER.  (its exit, its output, its outputs)."""
        def text(listing):
            return "".join("%s %s\n" % item for item in sorted(listing.items()))
        self.answer({(self.TAGS[build], "--short"): (0, text(packages), ""),
                     (self.pins["STOCK_CHECKER"], "--short"): (0, text(self.listed("stock")), "")})
        return self.run_image_step("packages", {"TAG": self.TAGS[build], "BUILD": build},
                                   cwd=self.checkout(self.dockerfile()))

    def test_the_fork_image_with_each_package_at_its_version_passes(self):
        rc, out, _got = self.package_list("fork", self.listed("fork"))
        self.assertEqual(rc, 0, out)
        self.assertEqual(errors_in(out), [], out)

    def test_the_fork_image_with_a_package_at_another_version_or_missing_fails(self):
        version = self.pins["ROCQ_FORK_OPAM_VERSION"]
        other, at = next(t.split(".", 1) for t in self.default()
                         if t.split(".", 1)[0] not in ("rocq-runtime", "rocq-core"))
        for name, change, error in (
                ("%s at another version" % other, {other: at + ".1"},
                 "the fork image has %s %s.1, not %s %s" % (other, at, other, at)),
                ("rocq-core at the stock version", {"rocq-core": "9.2.0"},
                 "the fork image has rocq-core 9.2.0, not rocq-core " + version),
                ("no coq-core", {"coq-core": None},
                 "the fork image has coq-core (not installed), not coq-core " + version)):
            with self.subTest(case=name):
                packages = {k: v for k, v in {**self.listed("fork"), **change}.items() if v is not None}
                rc, out, _got = self.package_list("fork", packages)
                self.assertEqual(rc, 1, out)
                self.assertEqual(errors_in(out), ["::error::" + error], out)

    def test_the_stock_image_s_versions_are_not_checked(self):
        rc, out, _got = self.package_list("stock", {**self.listed("stock"), "rocq-core": "9.1.0"})
        self.assertEqual(rc, 0, out)
        self.assertEqual(errors_in(out), [], out)
        # its list is printed, and STOCK_CHECKER is not pulled to compare with
        self.assertEqual([c[0] for c in self.logged("docker")], ["run"], out)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class ImagesDifferencesTest(ImagesStepStandIn):
    """The fork checker's summary gives the list of differences: the comment beside the build step, read from
    images.yml, from its first line up to the build step's name, each line without its leading blanks and `# `.  The
    step fails when images.yml lacks the build step's name, so that the list never runs on past the comment."""

    STEP = "the image, for a pull request that pins it"
    FIRST = "# The fork build differs from the stock build in these ways, each with its reason:"
    END = "- name: build and self-test"

    def summary(self, text):
        """The summary step of the fork checker, in a checkout whose images.yml is `text`.  (its exit, its output)."""
        checkout = tempfile.mkdtemp(prefix="checkout-", dir=self.dir)
        os.makedirs(os.path.join(checkout, ".github", "workflows"))
        with open(os.path.join(checkout, ".github", "workflows", "images.yml"), "w") as f:
            f.write(text)
        temp = tempfile.mkdtemp(prefix="runner-temp-", dir=self.dir)
        with open(os.path.join(temp, "fork-build.json"), "w") as f:
            f.write("{}\n")
        tag = ImagesAttestationTest.NAME + ":fork-test"
        env = {"REF": tag + "@" + ImagesAttestationTest.DIGEST, "SIZE": "1 GB", "TAG": tag, "ATTESTATION": "1",
               "REFUSALS": "refused", "COMPARE": "takes it", "SCAN": "no hit", "BUILD": "fork", "KEY": "checker",
               "RUNNER_TEMP": temp}
        rc, out, _got = self.run_images_step(step(image_job(), self.STEP), env, cwd=checkout)
        return rc, out

    def test_the_list_is_the_comment_and_a_copy_without_the_build_step_s_name_fails(self):
        with open(os.path.join(WORKFLOWS, "images.yml")) as f:
            lines = f.read().splitlines()
        first = [i for i, line in enumerate(lines) if line.strip() == self.FIRST]
        end = [i for i, line in enumerate(lines) if line.strip().startswith(self.END)]
        self.assertEqual((len(first), len(end)), (1, 1))
        want = [re.sub(r"^ *# ?", "", line) for line in lines[first[0]:end[0]]]
        rc, out = self.summary("\n".join(lines) + "\n")
        self.assertEqual(rc, 0, out)
        self.assertIn("```text\n%s\n```\n" % "\n".join(want), out)
        rc, out = self.summary("\n".join(lines[:end[0]] + lines[end[0] + 1:]) + "\n")
        self.assertEqual(rc, 1, out)
        errors = errors_in(out)
        self.assertEqual(len(errors), 1, out)
        self.assertIn("has no list of differences beside the build step", errors[0])
        self.assertNotIn("```text", out)


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
        # every plan run takes those tools, and none names base/tools again
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
            # GITHUB_REPOSITORY is the stand-in: on PUBLIC a push plans no part (PublicPushTest), and a CI run there
            # has that name in its environment
            env = dict(os.environ, PATH=os.path.join(d, "bin") + os.pathsep + os.environ["PATH"], RUNNER_TEMP=d,
                       GITHUB_WORKSPACE=d, GITHUB_OUTPUT=os.path.join(d, "output"),
                       GITHUB_STEP_SUMMARY=os.path.join(d, "summary.md"), KIND=kind, BASE="b" * 40, ROUTED="true",
                       GITHUB_EVENT_NAME=event, GITHUB_REPOSITORY=REPOSITORY)
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
            return out, runs

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

    def test_the_verdict_plan_runs_with_the_workflow_s_own_kind(self):
        """The plan step plans with the workflow's own kind.  A maintainer's or a contributor's change is checked with
        the base's statements, and oft plan keys those only when told the kind: its default, release, keys the
        change's own statements, which no check job of such a change reads.  It runs once, with the tools it chose,
        whatever the kind."""
        for kind in ("maintainer", "contributor", "release"):
            for pin, tools in (("absent", "base"), ("right", "head")):
                with self.subTest(kind=kind, pin=pin):
                    out, runs = self.plan_step(kind=kind, pin=pin)
                    self.assertEqual(out["tools"], tools)
                    self.assertEqual(len(runs), 1)
                    self.assertTrue(runs[0].startswith("%s/tools " % tools), runs[0])
                    self.assertIn("--pr-kind %s" % kind, runs[0])

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
    PATHS = ["projects/zlib/checksum_fuzzer/proofs/sum/Proof.v", "proofs/json/fuzzer-parse_bjdata/parse/Proof.v",
             "CHANGELOG.md", "tools/oft/lint-exceptions.yaml"]
    # the units of the group, each with the pull request that brought it
    UNITS = (("zlib/checksum_fuzzer", 563), ("json/fuzzer-parse_bjdata", 565))
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
        # base branch and its second the pull request's head, which PR_HEAD is.  Its tools/ is what the step
        # reads the checker id of this tree from (keys.checker), the id every marker must name.
        head = os.path.join(self.dir, "head")
        git = ["git", "-C", head, "-c", "user.name=t", "-c", "user.email=t@x", "-c", "commit.gpgsign=false"]
        subprocess.run(["git", "init", "-q", "-b", "main", head], check=True)
        os.makedirs(os.path.join(head, "tools", "oft"))
        with open(os.path.join(head, "tools", "oft", "check.py"), "w") as f:
            f.write("# the checker of this tree\n")
        for args in (["add", "tools/oft/check.py"], ["commit", "-q", "-m", "base"], ["checkout", "-q", "-b", "pr"],
                     ["commit", "-q", "--allow-empty", "-m", "the pull request"], ["checkout", "-q", "main"],
                     ["commit", "-q", "--allow-empty", "-m", "main moved"],
                     ["merge", "-q", "--no-ff", "-m", "merge", "pr"]):
            subprocess.run(git + args, check=True, capture_output=True)
        self.PR_HEAD, self.MERGE_BASE = (subprocess.run(git + ["rev-parse", "HEAD^2", "HEAD^1"], check=True,
                                                        capture_output=True, text=True).stdout.split())
        self.CHECKER = keys.checker(head, "HEAD")

    def api_file(self, endpoint, body):
        with open(os.path.join(self.api, endpoint.replace("/", "_") + ".json"), "w") as f:
            json.dump(body, f)

    def comment(self, head, mode="pvc", by="sjawhar-agent[bot]", kind="Bot", first=True, unit_keys=(), node="C_1",
                checkers=None):
        """merge-pr.sh's evidence comment: its marker as the first line, a key line per unit after it, and the
        checker line of the tree its check of record ran on (this tree's, unless `checkers` says otherwise)."""
        marker = "<!-- vm-evidence head=%s mode=%s -->" % (head, mode)
        body = marker + "\nthe VM run" if first else "a word\n" + marker
        body += "".join("\n<!-- vm-evidence-key unit=%s key=%s -->" % (u, k) for u, k in unit_keys)
        body += "".join("\n<!-- vm-evidence-checker id=%s -->" % c
                        for c in ((self.CHECKER,) if checkers is None else checkers))
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
              fails=False, pr="", pr_head="", hold="none", checkers=None):
        """The step, over a group of `commits` (each a first line and the pull request it names), with `paths` as the
        group's diff from its base.  `heads` gives a pull request's head sha (the default is its own), `comments` its
        comments (the default is merge-pr.sh's marker for that head, with a key line per unit of UNITS), `pages` a
        second page of them; None for either of the first two leaves that call failing.  `planned` and `recorded`
        give a unit's components at this group head and at its check of record (the default of each is comp(unit); a
        recorded None leaves that unit no key line), `parts` the plan's parts outright, `plan=False` leaves the plan
        file empty, and `edits` is GitHub's answer for the comment's editors (the default is none).  `deferred` and
        `record` are the plan step's own answers, for the deferred check this step answers first.  `pr`, `pr_head`
        and `hold` are a pull request's run's number, head and hold; `checkers` gives a pull request's marker the
        checker ids it names, in place of this tree's one.  `fails` says the step is expected to fail,
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
            said = (self.comment(head, unit_keys=lines.get(number, ()),
                                 checkers=(checkers or {}).get(number)) if comments is None
                    else comments.get(number))
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

    def test_the_checker_the_markers_name_is_the_one_this_tree_holds(self):
        """The id the markers are held against is keys.checker of head/, the checkout the plan keyed, read with
        the base's tools: the step prints it, and a group whose markers name it passes."""
        out = self.group()
        self.assertEqual(out["checked_elsewhere"], "true")
        self.assertIn("the checker of the tree this run checks: " + self.CHECKER, self.said)
        self.assertEqual(self.CHECKER, keys.checker(os.path.join(self.dir, "head"), "HEAD"))

    def test_a_marker_with_no_checker_line_or_another_checker_s_leaves_the_group_its_checks(self):
        """A key says nothing about the tools that computed it: on 2026-11-06 a lane posted markers whose keys
        were computed with main's tools while its farm runs had executed the pull request heads' older tools,
        from before #2109 moved keys.checker, and every key matched.  The marker now names the checker its run
        used, and the step refuses a marker with none, with more than one, or with another id, naming both ids
        (the OSS Verify lead, 2026-11-06 18:10Z).  Every key here is the group's own, so the checker alone
        answers."""
        other = "d" * 64
        for case, number, ids, says in (
                ("no checker line", 563, (), "pull request 563's evidence comment names 0 checker ids"),
                ("two checker lines", 563, (self.CHECKER, self.CHECKER),
                 "pull request 563's evidence comment names 2 checker ids"),
                ("another checker", 563, (other,),
                 "pull request 563's evidence comment names checker %s and the tree this group checks has "
                 "checker %s" % (other, self.CHECKER)),
                ("another entry's marker", 565, (other,),
                 "pull request 565's evidence comment names checker %s and the tree this group checks has "
                 "checker %s" % (other, self.CHECKER))):
            with self.subTest(case=case):
                out = self.group(checkers={number: ids})
                self.assertEqual(out["checked_elsewhere"], "false")
                self.assertIn(says, self.said)

    def test_a_path_a_check_reads_leaves_the_group_its_checks(self):
        """plan.paths_a_check_reads says which (tools/oft/tests/test_keys.VmEvidence covers it path by path): a
        statement, the checker, the theories, the toolchain, the workflows, release.yaml, dune-project, and the
        parts no evidence line records -- a counterexample, a finding, a projects/<p>/unpatched.yaml."""
        for path in ("projects/zlib/checksum_fuzzer/harness.yaml", "projects/zlib/project.yaml", "tools/oft/check.py",
                     "tools/oft/keys.py", "theories/Premises.v", "toolchain/rocq.lock", ".github/workflows/pr.yml",
                     "release.yaml", "dune-project", "projects/zlib/unpatched.yaml",
                     "projects/zlib/checksum_fuzzer/findings/f/finding.yaml",
                     "counterexamples/json/fuzzer-parse_bjdata/parse/x.bin"):
            with self.subTest(path=path):
                out = self.group(paths=self.PATHS + [path])
                self.assertEqual(out["checked_elsewhere"], "false")
                self.assertIn("changed path(s) a check reads", self.said)

    def test_a_file_no_check_opens_is_no_reason_to_check(self):
        """A file of tools/ that keys.not_the_checker names, by the base's own tools, a file of dev/enroll/, the
        enrollment scripts (plan.ENROLLMENT_SCRIPTS), one of dev/licence/, the shared licence-record generator
        (plan.LICENCE_GENERATOR), one of dev/gateway-model/, the gateway's formal model (plan.GATEWAY_MODEL), one of
        dev/evals/, the tools that run the evals (plan.EVALS), the build service's release-test workflow or its table
        of memory classes (plan.BUILD_SERVICE_FILES), or a file of dev/stream/, the stream's operational tools
        (plan.STREAM_TOOLS): `oft check` opens none of them, so none of them is in a key (tools/oft/keys.py, checker)."""
        out = self.group(paths=["proofs/json/fuzzer-parse_bjdata/parse/Proof.v", "tools/oft/tests/test_lint.py",
                                "tools/oft/README.md", "dev/enroll/upload", "tools/publish/release.py",
                                "dev/licence/made_from.py", "dev/gateway-model/build.sh",
                                "dev/evals/paired-run/runner.py",
                                ".github/workflows/rocq-release.yml", ".github/theorem-rule-classes.tsv",
                                "dev/stream/bin/x.py"])
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


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class StatementBuildFilesTest(StandIn):
    """pr.yml's check job holds the build files above each unit's statements to the rendering of the base's tools, for
    every unit it checks, as oft check does for a unit whose proof library it builds (check.py, _lib_targets): the
    statement folder's dune, the proofs folder's barrier dune, and no other build file in a directory above the
    statements.  The fixture's three units have no proof library, so oft check holds none of theirs; a release's tree
    is checked as committed, and lint holds its generated files with the change's own tools when the change touches
    tools/oft/.  The tools the plan named ($RUNNER_TEMP/tools) are the change's own where the base pins it, so they
    judge nothing here: in these cases they are a copy whose harness_dune renders the changed dune and whose
    DUNE_FILES names no build file."""

    STEP = "the build files above each unit's statements are the base's tools' rendering"
    COPY = "the base's tools, copied out before any code of the change runs"
    UNITS = "zlib/checksum_fuzzer json/fuzzer-parse_bjdata"
    # the statement theory with a rule of the change's own, which dune runs before it compiles
    RULE = "(rule (mode promote) (targets Statements.v) (action (write-file %{targets} \"Definition x := True.\")))\n"

    def setUp(self):
        super().setUp()
        with open(os.path.join(self.dir, "bin", "python"), "w") as f:
            f.write('#!/bin/sh\nexec "%s" "$@"\n' % sys.executable)
        os.chmod(os.path.join(self.dir, "bin", "python"), 0o755)
        self.temp = os.path.join(self.dir, "runner-temp")
        os.mkdir(self.temp)
        os.symlink(os.path.join(REPO, "tools"), os.path.join(self.temp, "base-tools"))
        # the tools the plan named, as a change the base pins could bring them
        theirs = os.path.join(self.temp, "tools", "oft")
        shutil.copytree(os.path.join(REPO, "tools", "oft"), theirs, ignore=shutil.ignore_patterns("tests"))
        with open(os.path.join(theirs, "layout.py"), "a") as f:
            f.write("\nDUNE_FILES = ()\n")
        with open(os.path.join(theirs, "generate.py"), "a") as f:
            f.write("\n_harness_dune = harness_dune\n\n\ndef harness_dune(h):\n    return _harness_dune(h) + %r\n"
                    % self.RULE)
        self.job = load("pr.yml")["jobs"]["check"]

    def run_check(self, root, units=UNITS):
        code, out, _ = self.run_step(step(self.job, self.STEP)["run"],
                                     {"UNITS": units, "WORK": root, "RUNNER_TEMP": self.temp}, cwd=self.dir)
        return code, out

    def test_a_tree_as_the_tools_render_it_passes_and_any_other_build_file_fails(self):
        statement = "projects/zlib/checksum_fuzzer/dune"
        barrier = "projects/zlib/checksum_fuzzer/proofs/dune"
        from oft import generate
        with tree() as t:
            self.assertEqual(self.run_check(t.root)[0], 0)
            with open(os.path.join(t.root, statement)) as f:
                rendered = f.read()
            cases = [
                # the statement theory with a rule of the change's own, which dune runs before it compiles
                ("the statement folder's dune, changed", {statement: rendered + self.RULE}, 1,
                 statement + ": differs from its rendering"),
                ("the barrier, as the tools render it", {barrier: generate.barrier_dune()}, 0, ""),
                ("the barrier, changed", {barrier: generate.barrier_dune() + "(dirs :standard)\n"}, 1,
                 barrier + ": differs from its rendering"),
                ("a build file above the statements", {"projects/zlib/dune": "(env (_ (flags -w -all)))\n"}, 1,
                 "projects/zlib/dune: no directory above zlib/checksum_fuzzer's statements holds a build file"),
                ("a dune-workspace at the top", {"dune-workspace": "(lang dune 3.23)\n"}, 1,
                 "dune-workspace: no directory above"),
            ]
            for name, files, want, said in cases:
                with self.subTest(case=name):
                    for rel, text in files.items():
                        os.makedirs(os.path.dirname(os.path.join(t.root, rel)) or t.root, exist_ok=True)
                        with open(os.path.join(t.root, rel), "w") as f:
                            f.write(text)
                    code, out = self.run_check(t.root)
                    self.assertEqual(code, want, out)
                    self.assertIn(said, out)
                    for rel in files:
                        os.remove(os.path.join(t.root, rel))
                    with open(os.path.join(t.root, statement), "w") as f:
                        f.write(rendered)
            # a link to the very bytes is not the file: dune follows it, and the next run's target may differ
            os.rename(os.path.join(t.root, statement), os.path.join(t.root, statement + ".real"))
            os.symlink("dune.real", os.path.join(t.root, statement))
            code, out = self.run_check(t.root)
            self.assertEqual(code, 1, out)
            self.assertIn(statement + ": differs from its rendering", out)
            # a job with no unit's statements reads no facts
            self.assertEqual(self.run_check(t.root, units="")[0], 0)

    def test_the_step_holds_the_tree_the_check_reads_before_it_reads_it(self):
        names = [s.get("name") or s.get("uses", "").split("@")[0] for s in self.job["steps"]]
        at = names.index(self.STEP)
        self.assertLess(names.index("the generated files of that tree, by the base's tools"), at)
        self.assertLess(at, names.index("check"))
        self.assertEqual(step(self.job, self.STEP)["env"],
                         {"UNITS": "${{ matrix.job.check_units }}", "WORK": "${{ steps.work.outputs.work }}"})
        self.assertNotIn("if", step(self.job, self.STEP))
        self.assertIn('PYTHONPATH="$RUNNER_TEMP/base-tools" python -P -', step(self.job, self.STEP)["run"])
        # the copy of the base's tools, made from the base's worktree before anything of the change runs: after the
        # work step, only setup-python, the base's requirements and the copy of the tools the plan named come first
        self.assertEqual(step(self.job, self.COPY)["run"], 'cp -r -- base/tools "$RUNNER_TEMP/base-tools"')
        work = names.index("statements from the base; proofs, counterexamples and findings from this change")
        self.assertEqual(names[work + 1:names.index(self.COPY) + 1],
                         ["actions/setup-python",
                          "the tools' dependencies (PyYAML, idna), hash-pinned, for this runner and for the containers",
                          "the tools, copied out of the tree they check", self.COPY])
        deps = "the tools' dependencies (PyYAML, idna), hash-pinned, for this runner and for the containers"
        self.assertIn("-r base/tools/oft/requirements.txt", step(self.job, deps)["run"])

    def test_the_tools_the_plan_named_do_not_judge(self):
        """With $RUNNER_TEMP/tools rendering the changed dune and naming no build file, the changed dune still
        fails: the step reads the base's tools alone.  The control is the same step given those tools as the base's,
        which passes the dune, run from a working directory that holds this repository's own oft/ (tools/, where the
        tools' tests job runs): the step's python puts no working directory on its path, so the tools it names are
        the tools it imports wherever it runs."""
        statement = "projects/zlib/checksum_fuzzer/dune"
        with tree() as t:
            with open(os.path.join(t.root, statement), "a") as f:
                f.write(self.RULE)
            code, out = self.run_check(t.root)
            self.assertEqual(code, 1, out)
            self.assertIn(statement + ": differs from its rendering", out)
            theirs = os.path.join(self.dir, "runner-temp-theirs")
            os.mkdir(theirs)
            os.symlink(os.path.join(self.temp, "tools"), os.path.join(theirs, "base-tools"))
            code, out, _ = self.run_step(step(self.job, self.STEP)["run"],
                                         {"UNITS": self.UNITS, "WORK": t.root, "RUNNER_TEMP": theirs},
                                         cwd=os.path.join(REPO, "tools"))
            self.assertEqual(code, 0, out)
            self.assertIn("the build files above the statements of 2 unit(s) are the tools' own rendering", out)



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
            self.assertNotIn("pull_request.base.sha", helpers.inline_scripts(f.read()))

    def both_layouts(self):
        """A commit on main whose files are the base's findings, a statement and a proof library in both layouts and two
        files of the stream's tools, one of them in dev/stream/bin/ (the release gate's scan tools), and one more commit
        on it, the push: the first commit, the base."""
        for rel in ("findings/zlib/unpatched.yaml", "findings/zlib/fz/s/finding.yaml", "proofs/zlib/fz/lib/A.v",
                    "projects/zlib/project.yaml", "projects/zlib/unpatched.yaml", "projects/zlib/fz/Statements.v",
                    "projects/zlib/fz/findings/s/finding.yaml", "projects/zlib/fz/proofs/lib/A.v",
                    "projects/zlib/fz/proofs/s/Proof.v", "dev/stream/bin/ossv-binscan", "dev/stream/lane/notes.md"):
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
        projects/<p>/<h>/findings/, with the tools, the files at the top of the tree and the release gate's scan tools
        (dev/stream/bin/, whose scanner the step after lint runs); no statement, no proof, no other folder of the
        stream."""
        self.assertEqual(self.base_files("lint"), [
            "README.md", "dev/stream/bin/ossv-binscan", "findings/zlib/fz/s/finding.yaml",
            "findings/zlib/unpatched.yaml", "moved.txt", "projects/zlib/fz/findings/s/finding.yaml",
            "projects/zlib/unpatched.yaml", "tools/oft/x.py"])

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
             "/proofs/*/*/lib/dune": "/projects/*/*/proofs/lib/dune",
             "/proofs/*/*/lib/Instances/": "/projects/*/*/proofs/lib/Instances/"}

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
TAG = "v2026.11.3"
# .github/CODEOWNERS of the public main, in its form: the last line whose pattern matches a path decides its owners
CODEOWNERS = """\
# Who must approve a change to this repository, and why.
**/AGENTS.md @acme/engineering
skills/ @acme/engineering
#
# The last pattern that matches a file decides its owner, so these lines stay the last ones in this file.
/release.yaml @owner-one @owner-two  # an inline comment
/theories/ @owner-one @owner-two
/.github/ @owner-one @owner-two
/tools/ @owner-one @owner-two
"""
# An owner that is an e-mail address, built from its parts so that no address is in this file's bytes
EMAIL_OWNER = "someone" + "@" + "example.com"
# The lines of the step's run that accept a code owner's approval: from their first comment up to the comment on
# PUBLISH_APP_ID, which release.yml before them held right after the check that the commit is on main
APPROVAL_BLOCK = re.compile(r"^# The other evidence: .*?(?=^# An empty PUBLISH_APP_ID)", re.M | re.S)


def merged_pr(number=7, base="main", head=HEAD, merged=True):
    """A pull request as GitHub lists those of a commit."""
    return {"number": number, "merged_at": "2026-11-20T18:04:14Z" if merged else None, "base": {"ref": base},
            "head": {"sha": head}}


def review(id, login="owner-one", state="APPROVED", commit=HEAD):
    """A review as GitHub lists those of a pull request: commit_id is the head it reviewed."""
    return {"id": id, "user": {"login": login, "type": "User"}, "state": state, "commit_id": commit}


def check_run(id, name="ossv-publish/checked", app=77, conclusion="success", status="completed", sha=HEAD):
    """A check run as GitHub lists it for a commit."""
    return {"id": id, "name": name, "app": {"id": app}, "head_sha": sha, "status": status, "conclusion": conclusion,
            "output": {"title": "run %d" % id}}


def gate_run(id, **kw):
    return check_run(id, **dict({"name": "ossv-gate/publish", "app": 5447700}, **kw))


@unittest.skipUnless(shutil.which("jq"), "jq is not installed")
class ReleaseCheckRunTest(StandIn):
    """release.yml publishes a tag only when the tagged commit is on main and it has one of two kinds of evidence.
    Either the newest check run on exactly the tagged commit passed, of those the publishing workflow makes
    (ossv-publish/checked, by the App PUBLISH_APP_ID names: the OSS Verify App 5447700) and of those the publishing gate
    makes (ossv-gate/publish, by App 5447700).  Or the tagged commit is the head of a pull request merged into main,
    and a code owner of release.yaml, by .github/CODEOWNERS on main, approved that pull request at exactly that commit.
    The cases set PUBLISH_APP_ID to another App's id, so the two pairs stay apart; an empty one trusts only the gate's
    runs, so a tag with no gate run fails closed.  The tagged commit is the head of no merged pull request, unless a
    case says otherwise."""

    def setUp(self):
        super().setUp()
        self.step = step(load("release.yml")["jobs"]["publish"], RELEASE_CHECK)
        # the python that setup-python gives the job: this test's own, which the step's CODEOWNERS read runs
        with open(os.path.join(self.dir, "bin", "python"), "w") as f:
            f.write('#!/bin/sh\nexec "%s" "$@"\n' % sys.executable)
        os.chmod(os.path.join(self.dir, "bin", "python"), 0o755)

    def answer(self, endpoint, value, suffix=".json"):
        with open(os.path.join(self.api, endpoint.replace("/", "_") + suffix), "w") as f:
            json.dump(value, f)

    def publish(self, runs=(), app_id="77", on_main="identical", answers=None, pulls=(), reviews=None,
                codeowners=CODEOWNERS, step=None):
        """The step, or STEP (a copy of it), against a stand-in GitHub whose main has the tagged commit as `on_main`
        says and whose check runs on it are `runs`, with PUBLISH_APP_ID set to app_id: (its exit status, its output).
        With answers, each call of the check-runs list gets the next of them in turn, the last one staying: a list of
        runs, or "error", a failed call (the step asks for the publishing App's pair first, when it asks for it, then
        for the gate's).  The tagged commit's pull requests are `pulls` ("error": a failed call), the reviews of each
        are reviews[number] (a list of pages, or "error"), and .github/CODEOWNERS on main is `codeowners` (None: no
        such file).  The run is the run of the push of TAG, with the contexts and the variables that GitHub gives it:
        each env value is read from them, and the event's payload is a file of its own."""
        for name in os.listdir(self.api):   # the answers and the calls of an earlier call of this test
            os.remove(os.path.join(self.api, name))
        self.answer("repos/%s/compare/main...%s" % (REPOSITORY, HEAD), {"status": on_main})
        listed = "repos/%s/commits/%s/check-runs" % (REPOSITORY, HEAD)
        for suffix, answer in ([(".json", list(runs))] if answers is None else
                               [(".%d.json" % n, a) for n, a in enumerate(answers, 1)]):
            self.answer(listed, answer if answer == "error" else {"check_runs": answer}, suffix)
        self.answer("repos/%s/commits/%s/pulls" % (REPOSITORY, HEAD), pulls if pulls == "error" else list(pulls))
        for number, pages in (reviews or {}).items():
            endpoint = "repos/%s/pulls/%d/reviews" % (REPOSITORY, number)
            for n, page in enumerate(["error"] if pages == "error" else pages):
                self.answer(endpoint, page, ".json" + (".page%d" % (n + 1) if n else ""))
        if codeowners is not None:
            self.answer("repos/%s/contents/.github/CODEOWNERS" % REPOSITORY, codeowners)
        event = {"ref": "refs/tags/" + TAG, "after": HEAD, "sender": {"login": "a-maintainer", "type": "User"}}
        event_path = os.path.join(self.dir, "event.json")
        with open(event_path, "w") as f:
            json.dump(event, f)
        context = {"github": {"token": "t", "event_name": "push", "event": event, "ref": event["ref"],
                              "ref_name": TAG, "sha": HEAD, "repository": REPOSITORY, "actor": "a-maintainer"}}
        step = step or self.step
        env = {name: helpers.gh_text(helpers.gh_value(value, context)) for name, value in step["env"].items()}
        env.update(PUBLISH_APP_ID=app_id, GITHUB_REPOSITORY=REPOSITORY, GITHUB_SHA=HEAD, GITHUB_REF=event["ref"],
                   GITHUB_REF_NAME=TAG, GITHUB_EVENT_NAME="push", GITHUB_EVENT_PATH=event_path,
                   GITHUB_ACTOR="a-maintainer", RUNNER_TEMP=self.dir)
        rc, out, _ = self.run_step(step["run"], env)
        return rc, out

    def approved(self, **kw):
        """publish() with pull request 7 merged into main, its head the tagged commit, which owner-one approved
        there."""
        return self.publish(**dict(dict(pulls=[merged_pr()], reviews={7: [[review(70)]]}), **kw))

    def assertNeedsACheckRun(self, **kw):
        """publish(**KW) with no check run fails, as a tag with no evidence does; with a gate run it passes."""
        rc, out = self.publish(**kw)
        self.assertEqual(rc, 1, out)
        self.assertIn("no code owner of release.yaml approved a pull request merged into main at %s" % HEAD, out)
        self.assertIn("::error::no check run passed %s" % HEAD, out)
        rc, out = self.publish([gate_run(10)], **kw)
        self.assertEqual(rc, 0, out)
        self.assertIn("ossv-gate/publish check run 10 (App 5447700)", out)
        return out

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

    def test_a_code_owner_s_approval_at_the_merged_head_publishes_with_no_check_run(self):
        """Pull request 7 was merged into main, its head is the tagged commit, and owner-one, an owner of release.yaml
        on main, approved it at that commit: the step passes and reads no check run."""
        for on_main in ("identical", "behind"):
            with self.subTest(on_main=on_main):
                rc, out = self.approved(on_main=on_main)
                self.assertEqual(rc, 0, out)
                self.assertIn("pull request #7 was merged into main with %s as its head, and owner-one, a code owner "
                              "of release.yaml on main, approved it at that commit (review 70)" % HEAD, out)
                self.assertEqual([c for c in self.calls() if "check-runs" in c], [])
                self.assertIn("GET repos/%s/contents/.github/CODEOWNERS?ref=main" % REPOSITORY, self.calls())

    def test_an_approval_among_other_reviews_and_pull_requests_counts(self):
        # another pull request of the commit, still open, and the owner's earlier comment; owner-two, its login
        # written in another case, approves
        rc, out = self.publish(pulls=[merged_pr(3, merged=False), merged_pr()],
                               reviews={7: [[review(68, state="COMMENTED"), review(69, login="not-an-owner"),
                                             review(70, login="Owner-Two")]]})
        self.assertEqual(rc, 0, out)
        self.assertIn("and Owner-Two, a code owner of release.yaml on main, approved it", out)
        self.assertNotIn("pulls/3/reviews", " ".join(self.calls()))

    def test_an_approval_on_the_second_page_of_reviews_counts(self):
        """The reviews are read page by page: an approval after the first 100 reviews counts.  A copy of the step that
        reads the first page alone refuses it, so the case can fail."""
        pages = [[review(n, login="someone", state="COMMENTED") for n in range(1, 101)], [review(170)]]
        rc, out = self.publish(pulls=[merged_pr()], reviews={7: pages})
        self.assertEqual(rc, 0, out)
        self.assertIn("approved it at that commit (review 170)", out)
        call = 'gh api --paginate "repos/$GITHUB_REPOSITORY/pulls/$pr/reviews'
        self.assertEqual(self.step["run"].count(call), 1)
        one_page = dict(self.step, run=self.step["run"].replace(call, call.replace("--paginate ", "")))
        self.assertEqual(self.publish(pulls=[merged_pr()], reviews={7: pages}, step=one_page)[0], 1)

    def test_an_approval_at_an_earlier_head_does_not_count(self):
        self.assertNeedsACheckRun(pulls=[merged_pr()], reviews={7: [[review(70, commit="d" * 40)]]})

    def test_an_approval_by_someone_who_owns_no_release_yaml_does_not_count(self):
        out = self.assertNeedsACheckRun(pulls=[merged_pr()], reviews={7: [[review(70, login="not-an-owner")]]})
        self.assertIn("not-an-owner approved pull request #7 at %s (review 70), but is no code owner of release.yaml "
                      "on main (its owners: owner-one owner-two)" % HEAD, out)

    def test_an_owner_s_review_that_is_no_approval_does_not_count(self):
        for state in ("COMMENTED", "CHANGES_REQUESTED", "DISMISSED", "PENDING"):
            with self.subTest(state=state):
                self.assertNeedsACheckRun(pulls=[merged_pr()], reviews={7: [[review(70, state=state)]]})

    def test_a_pull_request_that_was_not_merged_into_main_at_the_tagged_commit_does_not_count(self):
        """Not merged, merged into another base, or the tagged commit is not its head: each is refused, though a code
        owner approved it at the tagged commit."""
        for pr in (merged_pr(merged=False), merged_pr(base="release"), merged_pr(head="d" * 40)):
            with self.subTest(pr=pr):
                self.assertNeedsACheckRun(pulls=[pr], reviews={7: [[review(70)]]})

    def test_an_approved_tag_on_a_commit_that_is_not_on_main_is_refused(self):
        for status in ("ahead", "diverged"):
            with self.subTest(status=status):
                rc, out = self.approved(on_main=status)
                self.assertEqual(rc, 1, out)
                self.assertIn("is not on main", out)
                self.assertNotIn("approved it at that commit", out)

    def test_the_owners_are_those_codeowners_on_main_gives_release_yaml(self):
        """Not a list of the step's own: the last line of .github/CODEOWNERS on main whose pattern matches
        release.yaml decides, a line with no owner leaves it with none, and a team or an e-mail address counts for
        nothing.  A pattern that names another file or a folder does not match."""
        def owners(*lines):
            return CODEOWNERS + "".join(line + "\n" for line in lines)
        others = ("/docs/release.yaml @someone-else", "release.yaml/ @someone-else", "/release.y[a]ml @someone-else",
                  "/release.yaml.bak @someone-else")
        for text, login, want in (
                (owners("/release.yaml @someone-else"), "owner-one", 1),
                (owners("/release.yaml @someone-else"), "someone-else", 0),
                (owners("*.yaml @someone-else"), "someone-else", 0),
                (owners("**/release.yaml @someone-else"), "someone-else", 0),
                (owners("/** @someone-else"), "someone-else", 0),
                (owners("release.yaml"), "owner-one", 1),
                (owners("/release.yaml @acme/release-team"), "owner-one", 1),
                (owners("/release.yaml " + EMAIL_OWNER), "owner-one", 1),
                (owners(*others), "owner-one", 0),
                (owners(*others), "someone-else", 1),
                ("* @owner-one\n", "owner-one", 0),
                ("# only comments\n", "owner-one", 1)):
            with self.subTest(codeowners=text[len(CODEOWNERS):] if text.startswith(CODEOWNERS) else text, login=login):
                rc, out = self.publish(pulls=[merged_pr()], reviews={7: [[review(70, login=login)]]}, codeowners=text)
                self.assertEqual(rc, want, out)

    def test_a_failed_read_of_the_pull_requests_the_reviews_or_codeowners_fails_closed(self):
        """A failed call is no answer, so the step fails, even with a passing check run."""
        for why, kw in (("list the pull requests of", dict(pulls="error")),
                        ("list the reviews of pull request #7", dict(pulls=[merged_pr()], reviews={7: "error"})),
                        ("read .github/CODEOWNERS on main", dict(pulls=[merged_pr()], reviews={7: [[review(70)]]},
                                                                 codeowners=None))):
            with self.subTest(why):
                rc, out = self.publish([gate_run(10)], **kw)
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::could not " + why, out)
                self.assertNotIn("the publishing check passed", out)

    def test_negative_control_the_step_without_the_approval_block_refuses_an_approved_tag(self):
        """The step with no APPROVAL_BLOCK, as release.yml held it before: the approved case fails there, and a check
        run still passes."""
        run, found = APPROVAL_BLOCK.subn("", self.step["run"])
        self.assertEqual(found, 1, "the step has no block that reads a code owner's approval")
        old = dict(self.step, run=run)
        rc, out = self.approved(step=old)
        self.assertEqual(rc, 1, out)
        self.assertIn("::error::no check run passed %s" % HEAD, out)
        self.assertEqual(self.approved(runs=[check_run(10)], step=old)[0], 0)


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


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
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
      made_from: ${{ steps.reach.outputs.made_from }}
      made_from_proofs: ${{ steps.reach.outputs.made_from_proofs }}
      public_rows: ${{ steps.reach.outputs.public_rows }}
      hold: ${{ steps.hold.outputs.hold }}
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
          echo "farm_tests=$(cat head/farm 2>/dev/null || echo false)";
          echo "made_from=$(cat head/made_from 2>/dev/null || echo false)";
          echo "made_from_proofs=$(cat head/made_from_proofs 2>/dev/null || echo '[]')";
          echo "public_rows=$(cat head/public_rows 2>/dev/null || echo false)"; } >> "$GITHUB_OUTPUT"
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
      - name: a proof file of a unit with a licence record keeps Anthropic's copyright line (the strip check)
        env:
          BASE: ${{ steps.base.outputs.base }}
        run: '[ -n "$BASE" ]'
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
        run: |
          { [ -n "$BASE" ] && [ "$BASE_REF" = main ]; } || exit 1
          entry=$(git -C head ls-tree "$BASE" -- .github/rekey-window)
          if [ -z "$entry" ]; then echo missing; else read -r _ _ oid _ <<< "$entry"
          git -C head cat-file blob "$oid"; fi
          echo may_move=true >> "$GITHUB_OUTPUT"
      - id: own
        env:
          BASE: ${{ needs.plan.outputs.base }}
          MAY_MOVE: ${{ steps.rekey.outputs.may_move }}
        run: '[ -n "$BASE" ] && [ "$MAY_MOVE" = true ]'
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
  made_from:
    needs: [plan, lint]
    if: >-
      ${{ !cancelled() && needs.plan.result == 'success' && needs.lint.result == 'success'
      && (needs.plan.outputs.made_from == 'true'
      || (needs.plan.outputs.made_from_proofs != '[]' && needs.plan.outputs.hold == 'none')) }}
    steps:
      - run: "false"
  public_rows:
    needs: [plan, lint]
    if: >-
      ${{ !cancelled() && needs.plan.result == 'success' && needs.lint.result == 'success'
      && needs.plan.outputs.public_rows == 'true' }}
    steps:
      - run: "false"
  required:
    needs: [plan, lint, tests, check, stream_tools, rekey, farm_tests, made_from, public_rows]
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
          MADE_FROM: ${{ needs.plan.outputs.made_from }}
          MADE_FROM_PROOFS: ${{ needs.plan.outputs.made_from_proofs }}
          MADE_FROM_RESULT: ${{ needs.made_from.result }}
          PUBLIC_ROWS: ${{ needs.plan.outputs.public_rows }}
          PUBLIC_ROWS_RESULT: ${{ needs.public_rows.result }}
        run: >-
          [ "$UNITS" = 0 ] && [ "$TESTS_RESULT" = success ] && [ "$CHECK_RESULT" = skipped ]
          && [ "$STREAM_TOOLS" = false ] && [ "$STREAM_TOOLS_RESULT" = skipped ]
          && [ "$FARM_TESTS" = false ] && [ "$FARM_TESTS_RESULT" = skipped ]
          && [ "$MADE_FROM" = false ] && [ "$MADE_FROM_PROOFS" = '[]' ] && [ "$MADE_FROM_RESULT" = skipped ]
          && [ "$PUBLIC_ROWS" = false ] && [ "$PUBLIC_ROWS_RESULT" = skipped ]
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
        """A repository whose base commit has `workflow` as its pr.yml, with this repository's .github/scripts/pr/,
        whose files the steps of this repository's pr.yml call (helpers.SCRIPT_CALL), and the venv pr-steps.sh would
        build for its requirements already in VENVS (named as the script names it, by the requirements' SHA-256): this
        test's own Python, which has PyYAML, so that no run needs the network."""
        repo = os.path.join(d, "repo")
        os.mkdir(repo)
        git(repo, "init", "-q")
        files = {".github/workflows/pr.yml": workflow, "tools/oft/requirements.txt": FIXTURE_REQUIREMENTS, "units": "0\n"}
        scripts = os.path.join(REPO, ".github", "scripts", "pr")
        for name in sorted(os.listdir(scripts)) if os.path.isdir(scripts) else ():
            with open(os.path.join(scripts, name), encoding="utf-8") as f:
                files[".github/scripts/pr/" + name] = f.read()
        base = self.commit(repo, files, "base")
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
                                 ("lint", "base"), ("lint", "ledger"), ("lint", "strip"), ("lint", "lint"),
                                 ("lint", "generate"), ("tests", "tests"), ("rekey", "base"), ("rekey", "rekey"),
                                 ("rekey", "own"), ("required", "collect")]))

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

    def test_it_records_a_result_for_every_job_that_required_needs(self):
        """judge.py reads required's `if:` with the result of every job that required needs, directly or through
        another job, and stops on one with no result (`job required needs <job>, which has no result yet`), so every
        rehearsal would stop at `decide required`.  Each such job of this repository's pr.yml has a `record <job>`
        line in the script, whether the script runs the job or takes it as skipped."""
        jobs = load("pr.yml")["jobs"]
        needs, todo = set(), list(jobs["required"]["needs"])
        while todo:
            job = todo.pop()
            if job not in needs:
                needs.add(job)
                more = jobs[job].get("needs", [])
                todo += [more] if isinstance(more, str) else more
        with open(PR_STEPS) as f:
            recorded = set(re.findall(r"^\s*record ([A-Za-z_][\w-]*) ", f.read(), re.M))
        self.assertEqual(sorted(needs - recorded), [])

    @unittest.skipUnless(shutil.which("git") and shutil.which("flock"), "git or flock is not installed")
    def test_this_repository_s_pr_yml_passes_the_checks_before_the_first_step(self):
        """The run makes its checks of the workflow before it runs any step (the header): each env: name of each step
        it may start has a value it gives, each `if:` and output it reads is one it can read.  With this repository's
        own pr.yml every one of them holds, so a rehearsal of a pull request into main starts its steps.  An env: name
        that pr.yml gains and vars_for does not give stops every rehearsal before its first step (`FAIL setup: pr.yml's
        step lint/lint-head-tools names SINCE in its env:, which pr-steps.sh does not set`), and a job that a later
        `if:` reads with no record in the script stops it there, after the step lines, with a `FAIL setup:` line of its
        own.  So no line of summary.txt says `FAIL setup: `, and the plan job's base step ran (a usage error writes no
        summary.txt)."""
        with open(os.path.join(WORKFLOWS, "pr.yml")) as f:
            workflow = f.read()
        with tempfile.TemporaryDirectory(prefix="oft-pr-steps-") as d:
            repo, base = self.fixture(d, workflow)
            head = self.commit(repo, {"change.txt": "c\n"}, "the change")
            _rc, summary, out = self.rehearse(d, repo, head, base)
            self.assertNotIn("FAIL setup: ", summary, summary + out)
            self.assertRegex(summary, r"(?m)^(PASS|FAIL\(\d+\)) plan/base( |$)", summary + out)

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
                             "lint/strip", "lint/lint", "lint/generate", "tests/tests", "rekey/base", "rekey/rekey",
                             "rekey/own"):
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
    def test_the_rekey_job_takes_the_plan_s_base_and_the_window_from_the_base_s_tree(self):
        """The rekey job's steps (rule D11) get the plan job's base and the pull request's base branch, and the window
        is .github/rekey-window in that base's tree, which the rekey step reads from the shared head/ clone as the job
        reads it on GitHub: the base's `open`, and `missing` for a base without the file."""
        for window in (None, "open\n"):
            with self.subTest(window=window), tempfile.TemporaryDirectory(prefix="oft-pr-steps-") as d:
                repo, base = self.fixture(d)
                if window is not None:
                    base = self.commit(repo, {".github/rekey-window": window}, "the window")
                head = self.commit(repo, {"change.txt": "c\n", ".github/rekey-window": "closed\n"}, "the change")
                rc, summary, out = self.rehearse(d, repo, head, base)
                self.assertEqual(rc, 0, summary + out)
                with open(os.path.join(d, "out", "rekey-rekey.log")) as f:
                    self.assertEqual(f.read(), window or "missing\n")

    @unittest.skipUnless(shutil.which("git") and shutil.which("flock"), "git or flock is not installed")
    def test_the_rekey_job_runs_its_own_step_after_a_passing_verdict_as_github_does(self):
        """With this repository's own rekey job in the fixture's pr.yml and the modules keys.checker runs in the
        fixture's tools/oft: in an open window, a change that moves keys.checker passes the verdict, and its own step
        then runs the change's keys.py, which fails the rehearsal when it cannot be imported, as GitHub's own step fails
        the job; the same change with a keys.py that works passes.  With the window closed the verdict fails first and
        the own step is skipped, also as on GitHub."""
        rekey = load("pr.yml")["jobs"]["rekey"]
        job = "".join("  " + line + "\n" if line else "\n" for line in yamlio.dump({"rekey": rekey}).splitlines())
        workflow = re.sub(r"  rekey:\n.*?(?=  farm_tests:\n)", lambda m: job, FIXTURE_PR_YML, flags=re.S)
        self.assertEqual(yamlio.load(workflow)["jobs"]["rekey"], rekey)
        tools = {}
        for name in RekeyGuardTest.MODULES:
            with open(os.path.join(REPO, "tools", "oft", name)) as f:
                tools["tools/oft/" + name] = f.read()
        broken = tools["tools/oft/keys.py"] + "\nraise ImportError('a keys.py that cannot be imported')\n"
        for window, keys_py, code, said in (("open\n", broken, 1, "FAIL(1) rekey/own"),
                                            ("open\n", None, 0, "PASS rekey/own"),
                                            ("closed\n", broken, 1, "SKIP rekey/own (the verdict failed")):
            with self.subTest(window=window, broken=keys_py is not None), \
                    tempfile.TemporaryDirectory(prefix="oft-pr-steps-") as d:
                repo, _ = self.fixture(d, workflow)
                base = self.commit(repo, dict(tools, **{"tools/oft/check.py": "check\n",
                                                        ".github/rekey-window": window}), "the tools and the window")
                change = {"tools/oft/check.py": "check, changed\n"}
                if keys_py is not None:
                    change["tools/oft/keys.py"] = keys_py
                head = self.commit(repo, change, "a change that moves keys.checker")
                rc, summary, out = self.rehearse(d, repo, head, base)
                self.assertEqual(rc, code, summary + out)
                lines = [re.sub(r" \(\d+ s\)$", "", line) for line in summary.splitlines()]
                self.assertIn("PASS rekey/base", lines)
                self.assertIn("PASS rekey/rekey" if window == "open\n" else "FAIL(1) rekey/rekey", lines)
                self.assertTrue([line for line in lines if line.startswith(said)], summary)
                if code == 1 and window == "open\n":
                    with open(os.path.join(d, "out", "rekey-own.log")) as f:
                        self.assertIn("this change's tools could not compute keys.checker of its head", f.read())

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
            self.assertIn("FAIL(-) stream_tools/not-run (GitHub starts it: dev/stream/, or a file of tools/publish/ "
                          "that its tests read, changed)", lines)
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
            self.assertNotIn("FAIL(-) stream_tools/not-run (GitHub starts it: dev/stream/, or a file of tools/publish/ "
                             "that its tests read, changed)", lines)
            self.assertIn("SKIP required/collect (GitHub starts a job this script does not run (above): no "
                          "verdict to rehearse)", lines)

    @unittest.skipUnless(shutil.which("git") and shutil.which("flock"), "git or flock is not installed")
    def test_a_made_from_job_github_would_start_fails_the_rehearsal(self):
        """When the plan names a unit with a made-from record or generator, it answers made_from=true, or a list of
        units whose proofs changed in made_from_proofs, which starts the job under the hold stand-in none.  GitHub
        starts the made_from job (the fixture's has pr.yml's own `if:`), and pr-steps.sh does not run it: the rehearsal
        fails and gives required no verdict, as for farm_tests.  With false and [] (every other case here), required
        reads the plan's two answers and the job's result, false, [] and skipped, and passes."""
        self.assertEqual(yamlio.load(FIXTURE_PR_YML)["jobs"]["made_from"]["if"],
                         load("pr.yml")["jobs"]["made_from"]["if"])
        for name, files in (("a change to a made-from record", {"made_from": "true\n"}),
                            ("a change to a unit's proofs", {"made_from_proofs": '["projects/curl/fuzz_bufq"]\n'})):
            with self.subTest(case=name), tempfile.TemporaryDirectory(prefix="oft-pr-steps-") as d:
                repo, base = self.fixture(d)
                head = self.commit(repo, dict({"units": "0\n"}, **files), name)
                rc, summary, out = self.rehearse(d, repo, head, base)
                self.assertEqual(rc, 1, summary + out)
                lines = [re.sub(r" \(\d+ s\)$", "", line) for line in summary.splitlines()]
                self.assertIn("FAIL(-) made_from/not-run (GitHub starts it: the plan named a unit with a made-from "
                              "record or generator)", lines)
                self.assertNotIn("FAIL(-) farm_tests/not-run (GitHub starts it: a file the farm runner's tests read, "
                                 "or their job, changed)", lines)
                self.assertIn("SKIP required/collect (GitHub starts a job this script does not run (above): no "
                              "verdict to rehearse)", lines)

    @unittest.skipUnless(shutil.which("git") and shutil.which("flock"), "git or flock is not installed")
    def test_a_public_rows_job_github_would_start_fails_the_rehearsal(self):
        """When the change touches tools/publish/public-before-hold.tsv the plan answers public_rows=true, GitHub
        starts the public_rows job (the fixture's has pr.yml's own `if:`), and pr-steps.sh does not run it: the
        rehearsal fails and gives required no verdict, as for made_from."""
        self.assertEqual(yamlio.load(FIXTURE_PR_YML)["jobs"]["public_rows"]["if"],
                         load("pr.yml")["jobs"]["public_rows"]["if"])
        with tempfile.TemporaryDirectory(prefix="oft-pr-steps-") as d:
            repo, base = self.fixture(d)
            head = self.commit(repo, {"units": "0\n", "public_rows": "true\n"}, "a change to the record")
            rc, summary, out = self.rehearse(d, repo, head, base)
            self.assertEqual(rc, 1, summary + out)
            lines = [re.sub(r" \(\d+ s\)$", "", line) for line in summary.splitlines()]
            self.assertIn("FAIL(-) public_rows/not-run (GitHub starts it: tools/publish/public-before-hold.tsv "
                          "changed)", lines)
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
                       checked=None, refused=(), hand=(), broken=None):
        """The decision step of render-main, against a stand-in gh: its exit status, its output, the step outputs it
        wrote, the calls the stand-in saw, and the job summary.  `answer` is what gh prints for the queue, or None for
        a gh that fails as the API does; `tip` is main's tip as the commits endpoint gives it (subject, parent), or
        None for a tip that is no render commit; `history` is main's last commits, newest first, each ("merge" or
        "render", its age in hours); `checked` is the index in `history` of the tip of the last hourly run whose
        render succeeded, or None for no such run; `refused` holds the indexes of newer hourly runs' tips whose
        push was refused (green, but not marked as rendered); `hand` holds (index in `history`, whether its marker
        step succeeded) for hand runs (workflow_dispatch).  The stand-in answers the runs list one event at a time,
        as GitHub does, and answers a read with no event with a busy day's page of twenty push runs (OSSV-276).
        `broken` maps a case pattern of the calls to what the stand-in answers instead: None for a call that fails
        as the API does, or a text it prints, succeeding."""
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
            failed = 'echo "gh: HTTP 502: Server Error" >&2; exit 1'
            with open(os.path.join(bin_dir, "gh"), "w") as f:
                f.write('#!/usr/bin/env bash\necho "$@" >> "%s/calls"\n' % d
                        + 'case "$*" in\n'
                        + "".join("  %s) %s ;;\n" % (pattern, failed if text is None else "echo %s" % shlex.quote(text))
                                  for pattern, text in (broken or {}).items())
                        + '  *graphql*) %s ;;\n' % (failed if answer is None else 'printf "%%s\\n" %s' % answer)
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

    def test_the_marker_step_runs_only_where_the_run_left_its_tip_rendered(self):
        """A step of the marker's name succeeds in render-main when the render found nothing to render, and in
        push-main when it pushed the render; a render that failed, a commit that main moved under (green, nothing
        pushed) and a push that failed after it pushed (exit 4, stale generated files) leave the run unmarked.  The
        outputs these conditions read are the ones the render and push steps write (IndexRenderStepTest,
        IndexPushTest)."""
        jobs = load("index.yml")["jobs"]
        marker = "the index is current at this run's tip"

        def marks(job, **steps):
            return helpers.gh_truthy(helpers.gh_value("${{ %s }}" % step(jobs[job], marker)["if"], {"steps": steps}))

        commit = {"commit": "c" * 40, "tip": "a" * 40}
        self.assertTrue(marks("render-main", render={"outcome": "success", "outputs": {"current": "true"}}))
        for name, render in (("a commit for push-main", {"outcome": "success", "outputs": commit}),
                             ("stale files", {"outcome": "failure", "outputs": dict(commit, stale_files="true")}),
                             ("a failed render", {"outcome": "failure", "outputs": {}}),
                             ("no render", {"outcome": "skipped", "outputs": {}})):
            with self.subTest(render=name):
                self.assertFalse(marks("render-main", render=render))
        self.assertTrue(marks("push-main", push={"outcome": "success", "outputs": {"pushed": "true"}}))
        for name, push in (("main moved", {"outcome": "success", "outputs": {}}),
                           ("pushed, with stale files", {"outcome": "failure", "outputs": {"pushed": "true"}}),
                           ("refused", {"outcome": "failure", "outputs": {}})):
            with self.subTest(push=name):
                self.assertFalse(marks("push-main", push=push))
        self.assertEqual([s.get("id") for s in jobs["render-main"]["steps"] if s.get("id") == "render"], ["render"])
        self.assertEqual([s.get("id") for s in jobs["push-main"]["steps"] if s.get("id") == "push"], ["push"])

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

    def test_a_runs_list_that_cannot_be_read_fails_the_step(self):
        """A failed read, or an answer that is no list, of either checking event's runs would read as no checked run
        and call a current index stale: the step fails and names the call.  Only an answer whose runs carry no
        marker is no checked run (test_a_refused_hourly_render_does_not_reset_the_age)."""
        history = (("merge", 0.1), ("merge", 4.0), ("render", 6.0))
        call = "gh api repos/%s/actions/workflows/index.yml/runs?status=success&branch=main&per_page=5&event=%s"
        answers = ((None, "could not be read"), ('{"message": "Bad credentials"}', "did not read as a list"))
        for event in ("schedule", "workflow_dispatch"):
            for text, said in answers:
                with self.subTest(event=event, text=text):
                    rc, out, outputs, _calls, _summary = self.run_queue_step(
                        "4", history=history, checked=1, broken={"*'/runs?'*event=%s*" % event: text})
                    self.assertEqual(rc, 1, out)
                    self.assertIn("::error::index.yml's %s runs %s: %s" % (event, said, call % (REPOSITORY, event)),
                                  out)
                    self.assertNotIn("render", outputs)

    def test_a_jobs_list_that_cannot_be_read_fails_the_step(self):
        """The same for a run's jobs, whose marker step says whether the run checked its tip."""
        history = (("merge", 0.1), ("merge", 4.0), ("render", 6.0))
        for text, said in ((None, "could not be read"), ('{"message": "Bad credentials"}', "did not read as a list")):
            with self.subTest(text=text):
                rc, out, outputs, _calls, _summary = self.run_queue_step("4", history=history, checked=1,
                                                                         broken={"*runs/901/jobs*": text})
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::the jobs of run 901 %s: gh api repos/%s/actions/runs/901/jobs"
                              % (said, REPOSITORY), out)
                self.assertNotIn("render", outputs)

    def test_render_main_may_read_every_api_its_decision_step_calls_and_write_nothing(self):
        """The decision step reads main's commits (contents), the merge queue, whose entries are pull requests
        (pull-requests), and this workflow's runs and their jobs (actions).  render-main's token reads each of them,
        and writes nothing and holds no Environment, since the job runs the pushed tip's code."""
        history = (("merge", 0.1), ("merge", 4.0), ("render", 6.0))
        rc, out, _outputs, calls, _summary = self.run_queue_step("4", history=history, checked=1)
        self.assertEqual(rc, 0, out)
        scope = {"graphql": "pull-requests"}
        prefix = "repos/%s/" % REPOSITORY
        needs = set()
        for call in calls:
            if call.startswith("api "):
                endpoint = call.split()[1]
                kind = endpoint[len(prefix):].split("/", 1)[0].split("?", 1)[0] if endpoint.startswith(prefix) else ""
                needs.add(scope.get(endpoint) or {"commits": "contents", "actions": "actions"}[kind])
        self.assertEqual(needs, {"contents", "pull-requests", "actions"}, calls)
        job = load("index.yml")["jobs"]["render-main"]
        self.assertEqual(job["permissions"], {name: "read" for name in needs})
        self.assertNotIn("environment", job)

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


INDEX_RENDER_STEP = "render the shared generated files at main's tip, as a commit for push-main"
INDEX_PUSH_STEP = "check render-main's commit against this file's rules, and push it with the deploy key"
# the render commit's message, as tools/oft/ci/regenerate-shared.sh writes it with --skip-ci
INDEX_RENDER_MESSAGE = "index: render the shared generated files at %s [skip ci]\n\nRendered-From: %s"


def index_render_step(ws, runner, exit_code=0, says="", commit=False):
    """render-main's render step, run as GitHub runs it in the checkout `ws`, whose HEAD is main's tip, against a
    stand-in tools/oft/ci/regenerate-shared.sh that records its arguments, makes a render commit of a new README.md on
    HEAD when `commit` is true and names it as the script does with --dry-run, prints `says` and exits `exit_code`:
    the step's exit status, its output, the arguments the script saw, the outputs it wrote and its job summary.  The
    bundle it writes is left in `runner`, its RUNNER_TEMP."""
    os.makedirs(os.path.join(ws, "tools", "oft", "ci"), exist_ok=True)
    stub = os.path.join(ws, "tools", "oft", "ci", "regenerate-shared.sh")
    made = textwrap.dedent("""\
        blob=$(echo "the index after the render" | git hash-object -w --stdin)
        export GIT_INDEX_FILE="$RUNNER_TEMP/stub-index"
        git read-tree HEAD
        git update-index --cacheinfo "100644,$blob,README.md"
        tip=$(git rev-parse HEAD)
        c=$(git commit-tree -p "$tip" -m "index: render the shared generated files at ${tip:0:12} [skip ci]" \\
          -m "Rendered-From: $tip" "$(git write-tree)")
        echo "regenerate-shared.sh: --dry-run: $c would be pushed to refs/heads/main"
        """) if commit else ""
    with open(stub, "w") as f:
        f.write('#!/usr/bin/env bash\nset -e\necho "$@" > "$RUNNER_TEMP/called"\n%secho %s\nexit %d\n'
                % (made, shlex.quote(says), exit_code))
    os.chmod(stub, 0o755)
    files = {name: os.path.join(runner, name) for name in ("called", "output", "summary", "render.bundle")}
    for path in files.values():
        if os.path.exists(path):
            os.remove(path)
    text = step(load("index.yml")["jobs"]["render-main"], INDEX_RENDER_STEP)["run"]
    r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", text], cwd=ws,
                       env=dict(os.environ, GITHUB_REF_NAME="main", GITHUB_WORKSPACE=ws, RUNNER_TEMP=runner,
                                GITHUB_REPOSITORY=REPOSITORY, GITHUB_STEP_SUMMARY=files["summary"],
                                GITHUB_OUTPUT=files["output"], GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1"),
                       capture_output=True, text=True)

    def text_of(path):
        if not os.path.exists(path):
            return ""
        with open(path) as f:
            return f.read()

    outputs = dict(line.split("=", 1) for line in text_of(files["output"]).splitlines() if "=" in line)
    return r.returncode, r.stdout + r.stderr, text_of(files["called"]).strip(), outputs, text_of(files["summary"])


def bundle_heads(path):
    """The prerequisites and the refs a git bundle's header names: ([commit, ...], {ref: commit})."""
    with open(path, "rb") as f:
        lines = f.read().split(b"\n\n", 1)[0].decode().splitlines()[1:]
    return ([line[1:].split(" ", 1)[0] for line in lines if line.startswith("-")],
            dict(reversed(line.split(" ", 1)) for line in lines if not line.startswith("-")))


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
@unittest.skipUnless(os.path.exists(INDEX), "no .github/workflows/index.yml: the internal repository alone has it")
@unittest.skipUnless(shutil.which("git"), "git is not installed")
class IndexRenderStepTest(unittest.TestCase):
    """What render-main's render step does with the script's answer.  The job runs the pushed tip's tools, so it holds
    no key: it renders main with one try, the skip-ci marker and --dry-run, which commits the render and pushes
    nothing, and hands the commit to push-main as a bundle on its parent, naming both as its outputs.  It reads the
    script's exit status, and every green render says in the job summary what it did.  main is the one line rendered
    here since the release line joined it."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="oft-render-")
        self.addCleanup(self._tmp.cleanup)
        self.ws, self.runner = os.path.join(self._tmp.name, "ws"), os.path.join(self._tmp.name, "runner")
        os.mkdir(self.runner)
        git(self._tmp.name, "init", "-q", self.ws)
        with open(os.path.join(self.ws, "README.md"), "w") as f:
            f.write("the index before the render\n")
        git(self.ws, "add", "README.md")
        git(self.ws, "commit", "-q", "-m", "a proof")
        self.tip = git(self.ws, "rev-parse", "HEAD")

    def render(self, **kw):
        return index_render_step(self.ws, self.runner, **kw)

    def test_main_is_the_one_line_rendered(self):
        """After the join of the release line into main, ossv/recipes goes: no push to it starts this workflow and no
        job renders it.  render-main runs on main alone, and push-main after it."""
        wf = load("index.yml")
        self.assertEqual(wf["on"]["push"]["branches"], ["main"])
        self.assertEqual(sorted(wf["jobs"]), ["push-main", "render-main"])
        self.assertEqual(wf["jobs"]["render-main"]["if"], "github.ref == 'refs/heads/main'")
        self.assertEqual(wf["jobs"]["push-main"]["needs"], "render-main")

    def test_push_main_runs_after_a_commit_that_passed_or_failed_only_for_stale_files(self):
        """render-main's exit 4 is a render made on a tip whose other generated files are stale: push-main pushes
        it all the same, and then fails the run.  Any other failure, no commit, another ref or a cancelled run
        pushes nothing."""
        cond = "${{ %s }}" % load("index.yml")["jobs"]["push-main"]["if"]

        def runs(result, commit="c" * 40, stale_files="", ref="refs/heads/main", cancelled=False):
            scope = {"github": {"ref": ref},
                     "needs": {"render-main": {"result": result,
                                               "outputs": {"commit": commit, "stale_files": stale_files}}}}
            return helpers.gh_truthy(helpers.gh_value(cond, scope, {"always": lambda: True,
                                                                     "cancelled": lambda: cancelled}))

        self.assertTrue(runs("success"))
        self.assertTrue(runs("failure", stale_files="true"))
        for name, kw in (("another failure", dict(result="failure")),
                         ("no commit", dict(result="success", commit="")),
                         ("stale files and no commit", dict(result="failure", commit="", stale_files="true")),
                         ("render-main skipped", dict(result="skipped", commit="")),
                         ("another ref", dict(result="success", ref="refs/heads/other")),
                         ("a cancelled run", dict(result="success", cancelled=True))):
            with self.subTest(case=name):
                self.assertFalse(runs(**kw))

    def test_main_is_rendered_with_one_try_the_marker_and_no_push(self):
        """--dry-run: the script commits the render and pushes nothing.  It fetches main's tip through origin, the
        checkout's remote, which fetches with the job's own token."""
        rc, out, called, _outputs, _summary = self.render(commit=True)
        self.assertEqual(rc, 0, out)
        for want in ("--branch main", "--remote origin", "--tries 1", "--skip-ci", "--dry-run"):
            self.assertIn(want, called, called)

    def test_every_green_render_says_in_the_summary_what_it_did(self):
        """A green run with no commit says why: the render found nothing to change, which marks the run's tip; and
        a render that made a commit says that push-main checks and pushes it (IndexPushTest says what then)."""
        rc, out, _called, outputs, summary = self.render(
            says="regenerate-shared.sh: main 7df85b3dcc77 is rendered; nothing to do")
        self.assertEqual(rc, 0, out)
        self.assertIn("no shared file changed: no commit to make", summary)
        self.assertEqual(outputs, {"current": "true"})
        rc, out, _called, outputs, summary = self.render(commit=True)
        self.assertEqual(rc, 0, out)
        self.assertIn("as the commit %s, which push-main checks and pushes" % outputs.get("commit"), summary)
        self.assertNotIn("current", outputs)

    def test_the_render_commit_goes_to_push_main_as_a_bundle_on_main_s_tip(self):
        """The bundle holds the commit as refs/index/render and needs its parent, main's tip as the script read it,
        which push-main fetches; the outputs name the two."""
        rc, out, _called, outputs, _summary = self.render(commit=True)
        self.assertEqual(rc, 0, out)
        self.assertEqual(outputs.get("tip"), self.tip)
        self.assertEqual(git(self.ws, "rev-parse", outputs["commit"] + "^"), self.tip)
        self.assertEqual(bundle_heads(os.path.join(self.runner, "render.bundle")),
                         ([self.tip], {"refs/index/render": outputs["commit"]}))

    def test_a_render_on_stale_files_is_handed_over_and_fails_the_job(self):
        """Exit 4: the render is made, but the tip's other generated files are stale.  The step fails and still
        hands the commit over, since the upload step runs after a failed step that named one; push-main pushes it
        and fails (IndexPushTest)."""
        rc, out, _called, outputs, _summary = self.render(commit=True, exit_code=4)
        self.assertEqual(rc, 4, out)
        self.assertEqual(outputs.get("stale_files"), "true")
        self.assertEqual(bundle_heads(os.path.join(self.runner, "render.bundle"))[1],
                         {"refs/index/render": outputs["commit"]})
        upload = next(s for s in load("index.yml")["jobs"]["render-main"]["steps"]
                      if "upload-artifact" in s.get("uses", ""))

        def uploads(outcome, named):
            return helpers.gh_truthy(helpers.gh_value(upload["if"], {"steps": {"render": {
                "outcome": outcome, "outputs": named}}}, {"cancelled": lambda: False}))

        self.assertTrue(uploads("failure", outputs))
        self.assertTrue(uploads("success", {"commit": outputs["commit"], "tip": self.tip}))
        self.assertFalse(uploads("success", {"current": "true"}))
        self.assertFalse(uploads("failure", {"stale_files": "true"}))

    def test_push_main_reads_its_facts_from_render_main_s_steps(self):
        """The red "main moved" of a stale index hangs on this wiring: without it, set -u would fail every run whose
        main moved."""
        jobs = load("index.yml")["jobs"]
        self.assertIn('echo "stale=$stale" >> "$GITHUB_OUTPUT"',
                      step(jobs["render-main"],
                           "whether to render, from the event, main's merge queue and the index's age")["run"])
        self.assertEqual(jobs["render-main"]["outputs"]["stale"], "${{ steps.queue.outputs.stale }}")
        push = step(jobs["push-main"], INDEX_PUSH_STEP)
        for name in ("commit", "tip", "stale_files"):
            self.assertEqual(jobs["render-main"]["outputs"][name], "${{ steps.render.outputs.%s }}" % name)
        for name in ("commit", "tip", "stale", "stale_files"):
            self.assertEqual(push["env"][name.upper()], "${{ needs.render-main.outputs.%s }}" % name)

    def test_every_other_non_zero_exit_fails_the_run_and_hands_nothing_over(self):
        """Exit 3 is a render that changed a file that is not a shared generated file, and the others are faults;
        with --dry-run the script pushes nothing, so 5, 7 and 8 do not come, and they would be red too.  A script
        that exits 0 and says neither that it made a commit nor that none is due fails the run."""
        for code in (1, 3, 4, 5, 7, 8):
            with self.subTest(code=code):
                rc, out, _called, outputs, _summary = self.render(exit_code=code)
                self.assertEqual(rc, code, out)
                self.assertNotIn("commit", outputs)
        rc, out, _called, outputs, _summary = self.render()
        self.assertEqual(rc, 1, out)
        self.assertIn("said neither that it made a commit nor that none is due", out)
        self.assertEqual(outputs, {})


# git, with GitHub's two addresses of the repository standing for the local repository $GITHUB_STANDIN.  RACE, when
# set, runs before a push and moves main under it; LOST makes a push land and then fail, as a push whose answer is
# lost does; UNREADABLE makes ls-remote fail as an unreachable remote does.
STANDIN_GIT = r"""#!/usr/bin/env bash
args=()
for a in "$@"; do
  case $a in
    "https://github.com/$GITHUB_REPOSITORY.git"|"git@github.com:$GITHUB_REPOSITORY.git") a=$GITHUB_STANDIN ;;
  esac
  args+=("$a")
done
case " $* " in
  *" push "*)
    [ -z "${RACE:-}" ] || "$RACE"
    if [ -n "${LOST:-}" ]; then
      "$REAL_GIT" "${args[@]}" || exit
      echo "fatal: the remote end hung up unexpectedly" >&2
      exit 128
    fi ;;
  *" ls-remote "*) [ -z "${UNREADABLE:-}" ] || { echo "fatal: unable to access the repository" >&2; exit 128; } ;;
esac
exec "$REAL_GIT" "${args[@]}"
"""


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
@unittest.skipUnless(os.path.exists(INDEX), "no .github/workflows/index.yml: the internal repository alone has it")
@unittest.skipUnless(shutil.which("git"), "git is not installed")
class IndexPushTest(StandIn):
    """push-main's push step, run as GitHub runs it against a bare repository that stands for GitHub: a git on PATH
    points both of GitHub's addresses of the repository at it, and it serves main's tip without its files' contents
    to a partial fetch, as GitHub does.  render-main runs the pushed tip's code, so the step trusts nothing it hands
    over: it pushes the commit with the deploy key only when its one parent is main's tip, its first line is the
    render's of that tip with the skip-ci marker, and every entry of its tree that it changes is a file SHARED names,
    left a plain file, or a directory on the way to one, which it changes or empties and never adds.  Anything else is
    refused, red, before the key is written, and main is left as it was.  main having moved ends the run green, or red
    for an index past its age limit; a push refused while main stood still is a rule or the credential (exit 7); main
    already at the render commit is the render pushed."""

    INDEX = "".join("line %d of the index\n" % n for n in range(60))
    FILES = {"README.md": INDEX, "index/STATUS.md": INDEX, "index/PROOFS.md": INDEX, "index/units.tsv": "unit\tstatus\n",
             "analyses/harness-checks/checks.tsv": "check\n", "analyses/known-issues.md": "none\n",
             "projects/zlib/README.md": INDEX, "projects/x/README.md": INDEX,
             "projects/zlib/fz/Statements.v": "Theorem the_statement : the_claim.\n",
             "tools/oft/paths.py": "SHARED = ()\n", ".github/workflows/index.yml": "name: index\n"}

    def setUp(self):
        super().setUp()
        d = self.dir
        self.github = os.path.join(d, "github.git")
        git(d, "init", "-q", "--bare", self.github)
        git(self.github, "config", "uploadpack.allowFilter", "true")
        self.src = os.path.join(d, "src")
        git(d, "init", "-q", self.src)
        for rel, text in self.FILES.items():
            os.makedirs(os.path.dirname(os.path.join(self.src, rel)), exist_ok=True)
            with open(os.path.join(self.src, rel), "w") as f:
                f.write(text)
        git(self.src, "add", "-A")
        git(self.src, "commit", "-q", "-m", "a proof (#1)")
        self.before = git(self.src, "rev-parse", "HEAD")
        self.tip = self.commit({"analyses/known-issues.md": "one\n"}, [self.before], "another proof (#2)")
        self.moved = self.commit({"analyses/known-issues.md": "two\n"}, [self.tip], "a third proof (#3)")
        git(self.src, "push", "-q", self.github, self.tip + ":refs/heads/main", self.moved + ":refs/heads/next")
        self.runner = os.path.join(d, "runner")
        self.bundle = os.path.join(self.runner, "render", "render.bundle")
        os.makedirs(os.path.dirname(self.bundle))
        for name, text in (("bin/git", STANDIN_GIT),
                           ("race", '#!/bin/sh\nexec "$REAL_GIT" --git-dir="$GITHUB_STANDIN" update-ref refs/heads/main '
                                    '%s\n' % self.moved)):
            with open(os.path.join(d, name), "w") as f:
                f.write(text)
            os.chmod(os.path.join(d, name), 0o755)

    def commit(self, files, parents, message, empty=()):
        """A commit on `parents` whose tree is the first parent's with `files`: {path: its text, (mode, text), or
        None to delete it}, where a 160000 entry's text is the commit it names; and with an empty directory at each
        path of `empty`, in place of whatever was there (git's index holds no directory, so these are made with
        git mktree)."""
        env = dict(os.environ, GIT_INDEX_FILE=os.path.join(self.dir, "index-of-commit"))

        def run(*args, input=None):
            return subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=", *args], cwd=self.src, env=env,
                                  input=input, check=True, capture_output=True, text=True).stdout.strip()

        def graft(tree, parts, oid):   # `tree` (None for none) with the directory `oid` at the path `parts`
            entries = [e for e in run("ls-tree", tree).splitlines() if e] if tree else []
            here = [e for e in entries if e.split("\t", 1)[1] == parts[0]]
            below = here[0].split()[2] if here and here[0].split()[1] == "tree" else None
            new = oid if len(parts) == 1 else graft(below, parts[1:], oid)
            kept = [e for e in entries if e not in here] + ["040000 tree %s\t%s" % (new, parts[0])]
            return run("mktree", input="\n".join(kept) + "\n")

        run("read-tree", parents[0])
        for rel, value in files.items():
            if value is None:
                run("update-index", "--force-remove", rel)
                continue
            mode, text = value if isinstance(value, tuple) else ("100644", value)
            oid = text if mode == "160000" else run("hash-object", "-w", "--stdin", input=text)
            run("update-index", "--add", "--cacheinfo", "%s,%s,%s" % (mode, oid, rel))
        tree = run("write-tree")
        for rel in empty:
            tree = graft(tree, rel.split("/"), run("mktree", input=""))
        args = ["commit-tree", tree, "-F", "-"]
        for parent in parents:
            args += ["-p", parent]
        return run(*args, input=message)

    def render(self, files, parents=None, message=None, prerequisites=None, empty=()):
        """render-main's hand-over: a commit of `files` and `empty` directories on `parents` (main's tip), with a
        render's message unless `message`, in a bundle of refs/index/render on `prerequisites` (the first parent),
        where push-main's download step puts it."""
        parents = parents or [self.tip]
        commit = self.commit(files, parents,
                             INDEX_RENDER_MESSAGE % (self.tip[:12], self.tip) if message is None else message, empty)
        git(self.src, "update-ref", "refs/index/render", commit)
        git(self.src, "bundle", "create", "--quiet", self.bundle, "refs/index/render",
            *("^" + p for p in prerequisites or parents[:1]))
        return commit

    def runs_after(self, rc):
        """The names of push-main's steps after the push step that run, given its exit status `rc` and the outputs
        it wrote, as GitHub reads their conditions."""
        steps = load("index.yml")["jobs"]["push-main"]["steps"]
        after = steps[steps.index(step(load("index.yml")["jobs"]["push-main"], INDEX_PUSH_STEP)) + 1:]
        scope = {"steps": {"push": {"outcome": "success" if rc == 0 else "failure", "outputs": self.outputs()}}}
        return [s["name"] for s in after
                if helpers.gh_truthy(helpers.gh_value("${{ %s }}" % s.get("if", "success()"), scope,
                                                      {"always": lambda: True, "success": lambda: rc == 0}))]

    def push(self, commit, tip=None, stale="false", stale_files="false", race=False, lost=False, unreadable=False):
        """The push step with render-main's outputs: its exit status, its output and its job summary.  The key's
        directory is gone before it, as the job's last step leaves it."""
        s = step(load("index.yml")["jobs"]["push-main"], INDEX_PUSH_STEP)
        shutil.rmtree(os.path.join(self.runner, "ssh"), ignore_errors=True)
        if os.path.exists(self.output):
            os.remove(self.output)
        return self.run_step(s["run"], dict(
            RUNNER_TEMP=self.runner, GITHUB_REPOSITORY=REPOSITORY, GH_TOKEN="a-token", DEPLOY_KEY="a-key",
            COMMIT=commit, TIP=self.tip if tip is None else tip, STALE=stale, STALE_FILES=stale_files,
            SHARED=s["env"]["SHARED"], GITHUB_STANDIN=self.github, REAL_GIT=shutil.which("git"),
            RACE=os.path.join(self.dir, "race") if race else "", LOST="1" if lost else "",
            UNREADABLE="1" if unreadable else ""), cwd=self.dir)

    def main(self):
        return git(self.github, "rev-parse", "refs/heads/main")

    def reset(self):
        git(self.github, "update-ref", "refs/heads/main", self.tip)

    def assertRefused(self, commit, why, **kw):
        """The push step refuses render-main's commit for `why`: red, main as it was, and no key on disk.  main is
        set back to its tip first, so that one case's push cannot fail the next."""
        self.reset()
        rc, out, summary = self.push(commit, **kw)
        self.assertEqual(rc, 1, out)
        self.assertIn("::error::render-main's commit is refused and not pushed: " + why, out)
        self.assertIn("index: NOT RENDERED: render-main's commit is refused: " + why, summary)
        self.assertEqual(self.main(), self.tip)
        self.assertNotIn("pushed", self.outputs())
        self.assertFalse(os.path.exists(os.path.join(self.runner, "ssh")), "the key is written only for a push")

    def test_a_render_of_shared_files_is_pushed(self):
        """A file changed, one added and one deleted, each of them shared: the commit reaches main whole, though
        the step's own repository holds main's tip without its files' contents.  The deleted file was the last of
        projects/x, so that directory goes with it."""
        commit = self.render({"README.md": self.INDEX + "one more line\n", "index/more.tsv": "unit\n",
                              "projects/x/README.md": None})
        rc, out, summary = self.push(commit)
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.main(), commit)
        self.assertIn("pushed %s to refs/heads/main (rendered from %s)" % (commit, self.tip), out)
        self.assertIn("index: pushed a render commit onto main", summary)
        self.assertEqual(self.outputs(), {"pushed": "true"})
        self.assertEqual(self.runs_after(rc), ["start proof-index.yml when a render moved main",
                                               "the index is current at this run's tip", "the key leaves no file behind"])
        self.assertEqual(git(self.github, "show", commit + ":README.md"), (self.INDEX + "one more line").strip())
        self.assertEqual(git(self.github, "ls-tree", "--name-only", commit, "projects/"), "projects/zlib")
        git(self.github, "fsck", "--no-progress")

    def test_an_empty_directory_is_refused(self):
        """git keeps an empty directory, which no file below it shows, so a list of files alone would pass each of
        these: one beside the render, under a directory on the way to no shared file or under one on the way to
        some, and one in place of a shared file, which reads as that file's deletion."""
        for empty, files, why in (
                ("tools/unreviewed", {"README.md": "rendered\n"},
                 "it changes the directory tools, on the way to no file SHARED names"),
                ("projects/zlib/unreviewed", {"README.md": "rendered\n"},
                 "it adds the directory projects/zlib/unreviewed"),
                ("README.md", {}, "it adds the directory README.md"),
                ("index/units.tsv", {"README.md": "rendered\n"}, "it adds the directory index/units.tsv")):
            with self.subTest(empty=empty):
                commit = self.render(files, empty=[empty])
                self.assertEqual(git(self.src, "ls-tree", commit, empty).split()[:2], ["040000", "tree"])
                self.assertRefused(commit, why)

    def test_a_render_that_changes_a_statement_is_refused_and_main_is_left_as_it_was(self):
        """The hole this step closes: a render commit that also changes a file no pattern of SHARED names -- a
        statement, the tools, a workflow, a fuzz target's own README -- is not pushed, whatever the tip's paths.py
        says."""
        for path in ("projects/zlib/fz/Statements.v", "tools/oft/paths.py", ".github/workflows/index.yml",
                     "projects/zlib/fz/README.md"):
            with self.subTest(path=path):
                commit = self.render({"README.md": "rendered\n", path: "Theorem weaker : True.\n"})
                self.assertRefused(commit, "it changes %s, which SHARED does not name" % path)

    def test_a_commit_whose_parent_is_not_main_s_tip_is_refused(self):
        """On the commit before main's tip (whose bundle verifies, since the step's partial repository fetches a
        missing commit from origin on demand), or on a commit of its own after main's tip: its parent is not main's
        tip."""
        self.assertRefused(self.render({"README.md": "rendered\n"}, parents=[self.before]),
                           "its parents are not main's tip %s alone" % self.tip)
        own = self.commit({"README.md": "a commit of its own\n"}, [self.tip], "a proof of its own")
        self.assertRefused(self.render({"README.md": "rendered\n"}, parents=[own], prerequisites=[self.tip]),
                           "its parents are not main's tip %s alone" % self.tip)

    def test_a_commit_with_two_parents_is_refused(self):
        other = self.commit({"projects/zlib/fz/Statements.v": "Theorem weaker : True.\n"}, [self.tip], "a side line")
        self.assertRefused(self.render({"README.md": "rendered\n"}, parents=[self.tip, other]),
                           "its parents are not main's tip %s alone" % self.tip)

    def test_a_link_an_executable_or_a_submodule_is_refused(self):
        for path, mode, text in (("projects/x/README.md", "120000", "../zlib/fz/Statements.v"),
                                 ("README.md", "100755", "#!/bin/sh\n"),
                                 ("projects/x/README.md", "160000", self.before)):
            with self.subTest(mode=mode):
                commit = self.render({path: (mode, text)})
                self.assertRefused(commit, "it leaves %s with mode %s, where a shared file is a plain file (100644)"
                                   % (path, mode))

    def test_a_message_that_is_no_render_s_is_refused(self):
        """The first line is the script's for main's tip, with the skip-ci marker: without it the key's push would
        start every workflow that runs on a push to main."""
        subject = "index: render the shared generated files at %s [skip ci]" % self.tip[:12]
        first = "its first line is not '%s'" % subject
        for message, why in (
                ("a proof (#4)\n\nRendered-From: %s" % self.tip, first),
                ("%s\n\nRendered-From: %s" % (subject[:-len(" [skip ci]")], self.tip), first),
                ("%s and Statements.v\n\nRendered-From: %s" % (subject, self.tip), first),
                ("%s\n\nRendered-From: %s" % (subject.replace(self.tip[:12], self.before[:12]), self.tip), first),
                ("%s\n\nRendered-From: %s" % (subject, self.before), "it carries no line Rendered-From: " + self.tip),
                (subject, "it carries no line Rendered-From: " + self.tip)):
            with self.subTest(message=message):
                self.assertRefused(self.render({"README.md": "rendered\n"}, message=message), why)

    def test_outputs_that_name_no_commit_or_another_one_are_refused(self):
        commit = self.render({"README.md": "rendered\n"})
        for kw, why in ((dict(commit="main"), "render-main's outputs commit and tip are no commit ids"),
                        (dict(commit=commit, tip="--upload-pack=touch x"),
                         "render-main's outputs commit and tip are no commit ids"),
                        (dict(commit=self.moved), "its bundle holds another commit than %s" % self.moved)):
            with self.subTest(**kw):
                self.assertRefused(why=why, **kw)
        os.remove(self.bundle)
        self.assertRefused(commit, "its bundle does not apply to main's tip %s" % self.tip)

    def test_main_moved_before_the_push_ends_the_run_green_or_red_for_a_stale_index(self):
        """Before the step reads main, or between that read and the push: either way the run pushes nothing, and
        the push that moved main starts this workflow again.  OSSV-276: an index past its age limit that the run
        could not render is red, never green."""
        for when in ("before the step", "during the push"):
            for stale, code, said in (("false", 0, "index: not rendered: main moved during the render"),
                                      ("true", 1, "index: NOT RENDERED: main moved during the render and the index "
                                                  "is past its age limit")):
                with self.subTest(when=when, stale=stale):
                    self.reset()
                    commit = self.render({"README.md": "rendered\n"})
                    if when == "before the step":
                        git(self.github, "update-ref", "refs/heads/main", self.moved)
                    rc, out, summary = self.push(commit, stale=stale, race=when == "during the push")
                    self.assertEqual(rc, code, out)
                    self.assertIn(said, summary)
                    self.assertEqual(self.main(), self.moved)
                    self.assertNotIn("pushed", self.outputs())

    def test_a_push_refused_while_main_stood_still_fails(self):
        """Exit 7 is a rule or the credential refusing the push, never a race; exit 8, a refusal whose cause the
        step could not read."""
        hook = os.path.join(self.github, "hooks", "pre-receive")
        with open(hook, "w") as f:
            f.write("#!/bin/sh\necho 'refused by a rule' >&2\nexit 1\n")
        os.chmod(hook, 0o755)
        commit = self.render({"README.md": "rendered\n"})
        rc, out, _summary = self.push(commit)
        self.assertEqual(rc, 7, out)
        self.assertIn("main did not move: a rule or the credential refused it", out)
        self.assertEqual(self.main(), self.tip)
        rc, out, _summary = self.push(commit, unreadable=True)
        self.assertEqual(rc, 8, out)
        self.assertIn("could not be read afterwards", out)

    def test_a_render_on_stale_files_is_pushed_and_fails_the_run(self):
        commit = self.render({"README.md": "rendered\n"})
        rc, out, summary = self.push(commit, stale_files="true")
        self.assertEqual(rc, 4, out)
        self.assertEqual(self.main(), commit)
        self.assertEqual(self.outputs(), {"pushed": "true"})
        self.assertIn("the shared files are rendered and pushed, but %s carries stale generated files" % self.tip, out)
        self.assertIn("index: pushed a render commit onto main", summary)
        self.assertEqual(self.runs_after(rc), ["start proof-index.yml when a render moved main",
                                               "the key leaves no file behind"])

    def test_main_already_at_the_render_commit_is_the_render_pushed(self):
        """A re-run of this job after its push (whose proof-index.yml dispatch failed, say): main's tip is the
        render commit, nothing is left to push and no key is written, and the steps that follow a push run, the
        index past its age limit or not.  Stale generated files still fail the run."""
        commit = self.render({"README.md": "rendered\n"})
        git(self.src, "push", "-q", self.github, commit + ":refs/heads/main")
        for stale, stale_files, code in (("false", "false", 0), ("true", "false", 0), ("false", "true", 4)):
            with self.subTest(stale=stale, stale_files=stale_files):
                rc, out, summary = self.push(commit, stale=stale, stale_files=stale_files)
                self.assertEqual(rc, code, out)
                self.assertIn("index: main's tip is already the render commit, pushed by an earlier attempt", summary)
                self.assertNotIn("main moved", out + summary)
                self.assertEqual(self.outputs(), {"pushed": "true"})
                self.assertIn("start proof-index.yml when a render moved main", self.runs_after(rc))
                self.assertEqual("the index is current at this run's tip" in self.runs_after(rc), code == 0)
                self.assertEqual(self.main(), commit)
                self.assertFalse(os.path.exists(os.path.join(self.runner, "ssh")), "no key is written")

    def test_a_push_that_landed_and_then_failed_is_the_render_pushed(self):
        """git push fails, as when its answer is lost, and main's tip read afterwards is the render commit: it
        landed, and the steps that follow a push run, the index past its age limit or not."""
        for stale in ("false", "true"):
            with self.subTest(stale=stale):
                self.reset()
                commit = self.render({"README.md": "rendered %s\n" % stale})
                rc, out, summary = self.push(commit, stale=stale, lost=True)
                self.assertEqual(rc, 0, out)
                self.assertIn("the remote end hung up unexpectedly", out)
                self.assertIn("index: pushed a render commit onto main, though git push reported a failure", summary)
                self.assertNotIn("main moved", out + summary)
                self.assertEqual(self.main(), commit)
                self.assertEqual(self.outputs(), {"pushed": "true"})
                self.assertEqual(self.runs_after(rc), ["start proof-index.yml when a render moved main",
                                                       "the index is current at this run's tip",
                                                       "the key leaves no file behind"])

    def test_each_shared_pattern_s_file_is_pushed_and_no_neighbour_of_it(self):
        """SHARED is read as tools/oft/paths.py reads its patterns: a file of each pattern is pushed, and a file
        beside it, one level below or above it, or whose placeholder segment starts with a dot is refused, as each
        is no shared file to paths.is_shared."""
        def fill(segments, name):
            return "/".join(name if s.startswith("{") else s.replace("*", "units") for s in segments)

        files, neighbours = {}, []
        for pattern in paths.SHARED:
            path = fill(pattern.split("/"), "zlib")
            self.assertTrue(paths.is_shared(path), path)
            files[path] = "rendered\n"
            head, _, last = path.rpartition("/")
            near = [(head, last + ".orig"), (head, "NOTES.md"), (head, "sub", last)]
            if head:
                near.append((head.rpartition("/")[0], last))
            near = ["/".join(p for p in parts if p) for parts in near]
            if "{" in pattern:
                near.append(fill(pattern.split("/"), ".zlib"))
            neighbours += [n for n in near if n not in neighbours and not paths.is_shared(n)]
        rc, out, _summary = self.push(self.render(files))
        self.assertEqual(rc, 0, out)
        for path in neighbours:
            with self.subTest(path=path):
                self.assertRefused(self.render({"README.md": "rendered\n", path: "rendered\n"}),
                                   "it changes %s, which SHARED does not name" % path)

    def test_the_files_the_key_may_change_are_paths_shared(self):
        """index.yml's own list is what push-main holds the commit to; paths.SHARED is what the tip's render writes.
        The two are kept equal here, pattern for pattern, so neither moves without the other."""
        shared = step(load("index.yml")["jobs"]["push-main"], INDEX_PUSH_STEP)["env"]["SHARED"]
        self.assertEqual(sorted(shared.split()), sorted(paths.SHARED))

    def test_the_bundle_render_main_hands_over_is_the_commit_push_main_pushes(self):
        """render-main's render step, its upload and push-main's download, as the workflow names them, and the push
        step: the render reaches main."""
        ws, runner = os.path.join(self.dir, "ws"), os.path.join(self.dir, "render-runner")
        os.mkdir(runner)
        git(self.dir, "clone", "-q", self.github, ws)
        rc, out, _called, outputs, _summary = index_render_step(ws, runner, commit=True)
        self.assertEqual(rc, 0, out)
        jobs = load("index.yml")["jobs"]
        upload = next(s for s in jobs["render-main"]["steps"] if "upload-artifact" in s.get("uses", ""))
        download = next(s for s in jobs["push-main"]["steps"] if "download-artifact" in s.get("uses", ""))
        self.assertEqual(upload["with"]["name"], download["with"]["name"])
        uploaded = helpers.gh_value(upload["with"]["path"], {"runner": {"temp": runner}})
        shutil.rmtree(os.path.dirname(self.bundle))
        into = helpers.gh_value(download["with"]["path"], {"runner": {"temp": self.runner}})
        os.makedirs(into)
        shutil.copy(uploaded, into)
        rc, out, _summary = self.push(outputs["commit"], tip=outputs["tip"])
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.main(), outputs["commit"])


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
    with its proof (mq1), whose next push hq2 changes it (mq2); hbad's lint-exceptions.yaml is no YAML (mbad).  b also
    holds the proof file PROOF, of p/w, which no licence-pending entry names: on h1, hd deletes it (md), hr renames it
    to MOVED, in another folder with the same base name (mr), and hy changes its bytes alone (my).  he, on h1, adds
    ACCENT, a proof file of p/w whose name holds é (me)."""

    PR = "7"
    KIND = "maintainer"
    INTO = "refs/heads/main"
    PROOF = "projects/p/w/proofs/lib/A/Strlen.v"
    MOVED = "projects/p/w/proofs/lib/A/Rt/Strlen.v"
    ACCENT = "projects/p/w/proofs/lib/A/Caf\u00e9.v"

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="oft-lint-record-")
        d = self.dir = self._tmp.name
        origin = self.origin = os.path.join(d, "origin")
        os.mkdir(origin)
        git(origin, "init", "-q")

        def commit(files, message, gone=()):
            for rel, text in files.items():
                os.makedirs(os.path.join(origin, os.path.dirname(rel)) or origin, exist_ok=True)
                with open(os.path.join(origin, rel), "w") as f:
                    f.write(text)
            for rel in gone:
                os.remove(os.path.join(origin, rel))
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
                         "projects/p/t/proofs/P.v": "(* t *)\n", self.PROOF: "(* w *)\n",
                         "a.txt": "a\n", "b.txt": "b\n", "c.txt": "c\n"}, "b")
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
        git(origin, "checkout", "-qb", "deleted", self.h1)
        self.hd = commit({}, "hd", gone=(self.PROOF,))
        git(origin, "checkout", "-qb", "renamed", self.h1)
        self.hr = commit({self.MOVED: "(* w *)\n"}, "hr", gone=(self.PROOF,))
        git(origin, "checkout", "-qb", "bytes", self.h1)
        self.hy = commit({self.PROOF: "(* w, its bytes changed *)\n"}, "hy")
        git(origin, "checkout", "-qb", "accented", self.h1)
        self.he = commit({self.ACCENT: "(* w, a name with a byte above 0x7f *)\n"}, "he")
        self.m1 = merged(self.h1, "refs/pull/7/first")
        self.m2 = merged(self.h2, "refs/pull/7/merge")
        self.m3 = merged(self.h3, "refs/pull/7/third")
        self.mx = merged(self.hx, "refs/pull/7/exceptions")
        self.mb = merged(self.h2, "refs/pull/7/moved", self.b3)
        self.mp = merged(self.hp, "refs/pull/7/pending")
        self.mq1 = merged(self.hq1, "refs/pull/7/own1")
        self.mq2 = merged(self.hq2, "refs/pull/7/own2")
        self.mbad = merged(self.hbad, "refs/pull/7/unreadable")
        self.md = merged(self.hd, "refs/pull/7/deleted")
        self.mr = merged(self.hr, "refs/pull/7/renamed")
        self.my = merged(self.hy, "refs/pull/7/bytes")
        self.me = merged(self.he, "refs/pull/7/accented")
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
        self.assertEqual(self.gate("refs/pull/7/merge", None)[0]["lint_changed_only"], "true")

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

    def route(self, ws):
        """The plan job's base step's routing (its text between `# routing` and `# end of routing`), run from b to
        ws's head: the bytes of the changed.txt it writes."""
        base = next(s for s in self.wf["jobs"]["plan"]["steps"] if s.get("id") == "base")
        [routing] = re.findall(r"# routing\n(.*?)# end of routing\n", base["run"], re.S)
        r = subprocess.run(["bash", "--noprofile", "--norc", "-euo", "pipefail", "-c",
                            "base=%s routed=true\n%s" % (self.b, routing)], cwd=ws, capture_output=True, text=True,
                           env=dict(os.environ, RUNNER_TEMP=os.path.join(ws, "runner"), GITHUB_OUTPUT=os.devnull,
                                    KIND=self.KIND, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1"))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        with open(os.path.join(ws, "runner", "changed.txt"), "rb") as f:
            return f.read()

    def gate(self, ref, since_of, event="pull_request", changed=("a.txt", "b.txt")):
        """The plan job's lint_gate, on GitHub's event `event`, for a pull request into a branch other than main whose
        head is `ref`, with the record of a lint of `since_of` (None: no record) and the base step's changed.txt
        listing `changed` (None: what that step's routing lists, from b to the head): every output the step gave, and
        the output of lint_since (with a record) and of the step."""
        ws = self.workspace(ref)
        since, said = "", ""
        if since_of:
            self.record(ws, parents=since_of[0], tree=self.tree(since_of[1]), into="refs/heads/lane")
            rc, said, got = self.since(ws, into="refs/heads/lane")
            self.assertEqual(rc, 0, said)
            since = got["since"]
        if changed is None:
            self.route(ws)
        else:
            with open(os.path.join(ws, "runner", "changed.txt"), "w") as f:
                f.write("".join(rel + "\n" for rel in changed))
        rc, out, got = self.run_step("plan", "lint_gate", ws, {"ROUTED": "true", "PLANNED_TOOLS": "base", "SINCE": since,
                                                               "INTO": "refs/heads/lane", "PYTHONPATH": "",
                                                               "GITHUB_EVENT_NAME": event})
        self.assertEqual(rc, 0, out)
        return got, said + out

    def test_the_gate_takes_the_small_runner_only_for_a_per_file_lint(self):
        """Into a branch other than main, the gate answers true with a record that holds, or with none (the base
        is compared with), and false when a changed path is one every verdict reads: lint-exceptions.yaml, changed
        since m1 in mx, has lint read every file."""
        self.assertEqual(self.gate("refs/pull/7/merge", None)[0]["lint_changed_only"], "true")
        self.assertEqual(self.gate("refs/pull/7/merge", ((self.b, self.h1), self.m1))[0]["lint_changed_only"], "true")
        got, out = self.gate("refs/pull/7/exceptions", ((self.b, self.h1), self.m1))
        self.assertEqual(got["lint_changed_only"], "false")
        self.assertIn("a verdict on another file may read tools/oft/lint-exceptions.yaml", out)

    # The left-out checkout, for a pull request that deletes, renames or changes a proof file, and for a merge queue
    # group that deletes one.  A case with a record compares with m1's tree (the record holds, so SINCE is set); one
    # with none compares with b through changed.txt, as the base step's routing lists it.  GITHUB_EVENT_NAME is each
    # case's own, never the environment's.

    def test_a_pull_request_that_deletes_renames_or_changes_a_proof_file_leaves_the_proof_libraries_out(self):
        """md deletes PROOF and mr renames it to MOVED, each with m1's record and with none; my changes its bytes, with
        the record.  The gate's left-out answer reads no path of the change, so each takes the checkout without the
        proof libraries."""
        held = ((self.b, self.h1), self.m1)
        cases = (("refs/pull/7/deleted", held, ("a.txt", "b.txt")),
                 ("refs/pull/7/renamed", held, ("a.txt", "b.txt")),
                 ("refs/pull/7/bytes", held, ("a.txt", "b.txt")),
                 ("refs/pull/7/deleted", None, None),
                 ("refs/pull/7/renamed", None, None))
        for ref, since_of, changed in cases:
            with self.subTest(ref, record=since_of is not None):
                got, out = self.gate(ref, since_of, changed=changed)
                if since_of:
                    self.assertIn("lint record the-key holds", out)
                self.assertEqual((got["lint_changed_only"], got["lint_files_left_out"]), ("true", "true"), out)

    def test_a_merge_group_that_deletes_a_proof_file_takes_the_whole_tree(self):
        """A merge queue group's lint reads the whole tree whatever its change: the event decides."""
        got, out = self.gate("refs/pull/7/deleted", None, event="merge_group", changed=None)
        self.assertEqual((got["lint_changed_only"], got["lint_files_left_out"]), ("true", "false"), out)

    def test_the_routing_lists_a_renamed_file_as_its_old_path_and_its_new_one(self):
        """The base step's routing lists mr's change from b with --no-renames: PROOF, the old path of the rename, and
        MOVED, its new one.  With renames, git lists MOVED alone."""
        listed = self.route(self.workspace("refs/pull/7/renamed")).decode().split("\n")
        self.assertLessEqual({self.PROOF, self.MOVED}, set(listed), listed)

    def test_the_routing_lists_a_name_with_a_byte_above_0x7f_as_it_is(self):
        """The base step's routing lists me's ACCENT, whose name holds é, byte for byte, with core.quotePath=false.
        With git's default, the name is listed quoted and its bytes above 0x7f in octal ("...Caf\\303\\251.v")."""
        listed = self.route(self.workspace("refs/pull/7/accented"))
        self.assertEqual(listed, b"a.txt\n" + self.ACCENT.encode() + b"\n")

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
                self.assertEqual(self.gate(ref, (parents, of))[0]["lint_changed_only"], "true")
        [args] = self.lint_args("", "refs/heads/lane")
        self.assertEqual(args[args.index("--changed-only") + 1], self.b, args)


REKEY_VERDICT = "keys.checker moved only in an announced re-key window (rule D11)"
REKEY_WINDOW = ".github/rekey-window"
# a run of the rekey job's steps: the rekey step's exit status, output and job summary, the base it was given, the
# head it checked out, keys.checker of each by this repository's keys.py (which is the base's), the head/ clone, and
# whether a head's keys.py rewrote the step that ran it (RekeyGuardTest.REWRITE)
RekeyRun = collections.namedtuple("RekeyRun", "rc out summary base head before after clone rewrote")


def stored(repo, spec):
    """Whether the object spec names is in repo's own store: GIT_NO_LAZY_FETCH fetches nothing to answer."""
    return subprocess.run(["git", "cat-file", "-e", spec], cwd=repo, capture_output=True,
                          env=dict(os.environ, GIT_NO_LAZY_FETCH="1")).returncode == 0


@unittest.skipUnless(HAVE_WORKFLOWS and shutil.which("git"), "no .github/workflows, or git is not installed")
class RekeyGuardTest(StandIn):
    """Rule D11: until the platform tag, and outside an announced re-key window, nothing that moves keys.checker merges
    into main.  pr.yml's rekey job computes keys.checker of the base by the base's tools, and of the head by the base's
    tools and by the change's own, prints all three, and fails a change into main when either head id differs from the
    base's, unless the base's own .github/rekey-window, with trailing newlines removed, is exactly `open`; a change that
    also adds, edits or deletes that file fails whatever it reads, and required fails with the job.  The verdict on the
    base's tools' id is one step that runs no code of the change, and the change's own id comes in the step after it,
    which runs only when the verdict passed, so a failed verdict shows two ids.  The steps run as
    GitHub runs them, over a repository whose every commit carries its own tools/oft: the modules keys.checker runs
    (keys.py and what it imports, copied from this repository), a stand-in checker file (check.py) and a file no check
    opens (lint.py).  Each worktree runs the tools it checked out, so a head whose keys.py lies runs that keys.py.  Each
    run's base is a commit on the first one with the window it names, and its head a commit on that base; both are
    written with git's plumbing, so a file's blob holds exactly the bytes given (`git add` would read the .gitattributes
    here and store a carriage return and newline as a newline)."""

    # what `from oft import keys` loads
    MODULES = ("__init__.py", "keys.py", "layout.py", "names.py", "paths.py", "shapes.py", "unitpaths.py")
    # the merges rule D11 holds: a pull request into main, and a merge queue group, which is main's
    EVENTS = (("pull_request", "main"), ("merge_group", ""))
    # a head that leaves the window file as its base has it; a base whose window is a directory (holding one file)
    SAME = object()
    DIRECTORY = object()

    class Link(bytes):
        """A tree entry that is a symbolic link whose target is these bytes."""

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
        self.keys_py = tools["tools/oft/keys.py"]
        self.base = self.commit(dict(tools, **{"tools/oft/check.py": "check\n", "tools/oft/lint.py": "lint\n",
                                               ".gitattributes": "* text=auto eol=lf\n"}), "base")
        self.commits = 0

    def commit(self, files, message):
        for rel, text in files.items():
            os.makedirs(os.path.dirname(os.path.join(self.origin, rel)), exist_ok=True)
            with open(os.path.join(self.origin, rel), "w") as f:
                f.write(text)
        git(self.origin, "add", "-A")
        git(self.origin, "commit", "-qm", message)
        return git(self.origin, "rev-parse", "HEAD")

    def plumb(self, *args, data=None, index=None):
        env = dict(os.environ, GIT_INDEX_FILE=index) if index else None
        return subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=", *args], cwd=self.origin, env=env,
                              input=data, check=True, capture_output=True).stdout.decode().strip()

    def derive(self, parent, files, message):
        """A commit of the origin whose parent is `parent` and whose tree is the parent's but for `files`: {path:
        bytes (a file of exactly those bytes: no filter of .gitattributes runs), a Link, DIRECTORY or None (no such
        entry)}.  A branch of its own names it, so that a clone has it."""
        index = os.path.join(self.dir, "index")
        self.plumb("read-tree", parent, index=index)
        for path, value in files.items():
            if value is None:
                self.plumb("update-index", "--force-remove", "--", path, index=index)
                continue
            mode = "120000" if isinstance(value, self.Link) else "100644"
            if value is self.DIRECTORY:
                path, value = path + "/x", b"open\n"
            oid = self.plumb("hash-object", "-w", "--no-filters", "--stdin", data=bytes(value))
            self.plumb("update-index", "--add", "--replace", "--cacheinfo", "%s,%s,%s" % (mode, oid, path),
                       index=index)
        commit = self.plumb("commit-tree", self.plumb("write-tree", index=index), "-p", parent, "-m", message)
        os.remove(index)
        self.commits += 1
        self.plumb("update-ref", "refs/heads/run-%d" % self.commits, commit)
        return commit

    # A keys.py tail that, once imported, rewrites the rest of the running step's script, which bash reads from its file
    # as it goes: the script is the first file named on the command line of a shell above this process (GitHub's
    # `bash -e {0}`, a file under RUNNER_TEMP, as run_step's is), and everything after the command that runs the
    # change's tools becomes a pass.  It leaves RUNNER_TEMP/rewrote when it did.
    REWRITE = textwrap.dedent("""\


        def _rewrite():
            import os
            pid = os.getpid()
            while pid > 1:
                with open("/proc/%d/stat" % pid) as f:
                    pid = int(f.read().rsplit(")", 1)[1].split()[1])
                with open("/proc/%d/cmdline" % pid, "rb") as f:
                    args = [a.decode(errors="replace") for a in f.read().split(b"\\0")]
                for path in args:
                    if not (path.endswith(".sh") and os.path.isfile(path)):
                        continue
                    with open(path) as f:
                        text = f.read()
                    lines = text.split("\\n")
                    at = next((i for i, line in enumerate(lines)
                               if "head/tools" in line and not line.lstrip().startswith("#")), None)
                    if at is None:
                        return
                    end = next(i for i in range(at, len(lines)) if lines[i].rstrip().endswith("exit 1; }"))
                    keep = len("\\n".join(lines[:end + 1])) + 1
                    with open(path, "r+") as f:
                        f.seek(keep)
                        f.write('echo "keys.checker is unchanged: this change re-keys no unit" >> '
                                '"$GITHUB_STEP_SUMMARY"\\nexit 0\\n')
                        f.truncate()
                    open(os.path.join(os.environ["RUNNER_TEMP"], "rewrote"), "w").close()
                    return


        _rewrite()
        """)

    def change(self, head, base):
        """The files a head of the kind `head` changes on base: none (None); files keys.NOT_THE_CHECKER names, and a
        workflow, which is outside tools/, so keys.checker stays (outside); a checker file (moved); a checker file and
        a keys.checker that answers every commit with base's id (hidden); a checker file and a keys.py that, once
        imported, makes head/ answer base's window blob with a blob that reads open (replacing): a git replace ref,
        which `git cat-file blob` follows; or a checker file and a keys.py that, once imported, rewrites the rest of
        the step that imported it into a pass (rewriting, REWRITE)."""
        if head is None:
            return {}
        if head == "outside":
            return {"tools/oft/lint.py": b"lint, changed\n", "tools/oft/tests/test_x.py": b"x\n",
                    ".github/workflows/pr.yml": b"on: push\n"}
        moved = {"tools/oft/check.py": b"check, changed\n"}
        if head == "moved":
            return moved
        if head == "hidden":
            tail = "\n\n_checker = checker\n\n\ndef checker(repo, commit):\n    return _checker(repo, %r)\n" % base
        elif head == "rewriting":
            tail = self.REWRITE
        else:
            self.assertEqual(head, "replacing")
            tail = ("\n\nimport subprocess as _sp\n_git = ['git', '-C', 'head']\n"
                    "_open = _sp.run(_git + ['hash-object', '-w', '--stdin'], input=b'open\\n', check=True,\n"
                    "                capture_output=True).stdout.decode().strip()\n"
                    "_window = _sp.run(_git + ['rev-parse', %r], check=True,\n"
                    "                  capture_output=True).stdout.decode().strip()\n"
                    "_sp.run(_git + ['replace', '-f', _window, _open], check=True, capture_output=True)\n"
                    % (base + ":" + REKEY_WINDOW))
        return dict(moved, **{"tools/oft/keys.py": (self.keys_py + tail).encode()})

    def step(self, name):
        return next(s for s in self.jobs["rekey"]["steps"] if name in (s.get("id"), s.get("name")))

    def guard(self, window=None, kind="moved", change=SAME, event="pull_request", base_ref="main",
              repository=REPOSITORY, blobless=False, cut_off=False):
        """The job's base step, then its rekey step (the verdict), then, when that passed, its own step (the change's
        own id, with the verdict's outputs), in a workspace whose head/ is a clone of the origin at the head; the
        exit status is the first that failed, as a job's is.
        The base is a commit on self.base whose .github/rekey-window is `window` (None: there is none); the head is a
        commit on that base with the files the kind `kind` changes (self.change) and with `change` as its window
        (SAME: the base's).  blobless: head/ is cloned over file:// with --filter=blob:none and checks out tools/oft
        alone, as actions/checkout makes it, and the base's window blob is still missing when the rekey step starts;
        cut_off: and the origin is gone once the base step has fetched the base, so no missing blob can be fetched.
        Each run has a RUNNER_TEMP of its own, and no variable of the caller's names the window."""
        base = self.derive(self.base, {} if window is None else {REKEY_WINDOW: window}, "the window")
        files = self.change(kind, base)
        if change is not self.SAME:
            files[REKEY_WINDOW] = change
        head = self.derive(base, files, "the change")
        ws = tempfile.mkdtemp(dir=self.dir)
        clone = os.path.join(ws, "head")
        if blobless:
            git(self.origin, "config", "uploadpack.allowFilter", "true")
            git(ws, "clone", "-q", "--filter=blob:none", "--no-checkout", "file://" + self.origin, clone)
            git(clone, "sparse-checkout", "set", "--cone", "tools/oft")
        else:
            git(ws, "clone", "-q", self.origin, clone)
        git(clone, "checkout", "-q", "--detach", head)
        env = {"GITHUB_WORKSPACE": ws, "BASE": base, "GITHUB_EVENT_NAME": event,
               "GITHUB_REPOSITORY": repository, "RUNNER_TEMP": tempfile.mkdtemp(dir=self.dir),
               "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}
        rc, out, _ = self.run_step(self.step("base")["run"], env, cwd=ws)
        self.assertEqual(rc, 0, out)
        # two copies of the tools, each the one its commit has, and no link to one copy
        for tree, commit in (("base", base), ("head", head)):
            self.assertFalse(os.path.islink(os.path.join(ws, tree, "tools")), tree)
            with open(os.path.join(ws, tree, "tools", "oft", "keys.py")) as f:
                self.assertEqual(f.read().strip(), git(self.origin, "show", commit + ":tools/oft/keys.py"), tree)
        if blobless and window is not None and window is not self.DIRECTORY:
            self.assertFalse(stored(clone, base + ":" + REKEY_WINDOW), "the window blob is already in head/")
        if cut_off:
            # keys.checker reads the checkout attributes, so the root .gitattributes of each commit must be in head/,
            # or checker_of would fail first
            for commit in (base, head):
                self.assertTrue(stored(clone, commit + ":.gitattributes"), commit)
            git(clone, "config", "remote.origin.url", os.path.join(self.dir, "gone"))
        if os.path.exists(self.output):
            os.remove(self.output)
        rc, out, summary = self.run_step(self.step("rekey")["run"], dict(env, BASE_REF=base_ref), cwd=ws)
        # the step after the verdict, as GitHub runs it: only when the verdict passed, with its outputs
        if rc == 0:
            own = self.step("own")
            values = {"${{ needs.plan.outputs.base }}": base}
            values.update({"${{ steps.rekey.outputs.%s }}" % k: v for k, v in self.outputs().items()})
            # an output the verdict did not write is empty, as GitHub gives it
            own_env = {k: values.get(v, "") for k, v in own["env"].items()}
            rc, more, more_summary = self.run_step(own["run"], dict(env, **own_env), cwd=ws)
            out, summary = out + more, summary + more_summary
        return RekeyRun(rc, out, summary, base, head, keys.checker(self.origin, base), keys.checker(self.origin, head),
                        clone, os.path.exists(os.path.join(env["RUNNER_TEMP"], "rewrote")))

    def state(self, window):
        """What the window line says of a base whose window is `window`."""
        if window is None:
            return "missing"
        if window is self.DIRECTORY:
            return "not a file (tree, mode 040000)"
        if isinstance(window, self.Link):
            return "not a file (blob, mode 120000)"
        return ascii(window)

    def moves(self, r):
        return "this change moves keys.checker from %s to %s (re-keys every unit)" % (r.before, r.after)

    def said(self, r):
        return self.moves(r) + "; it can merge only in an announced re-key window (rule D11); ask the CI/CD lead"

    def ids(self, r, by_base, by_own):
        """The ids in the summary; by_own None: the change's own tools ran not at all (the verdict failed first)."""
        self.assertIn("- the base %s, by the base's tools: `%s`" % (r.base, r.before), r.summary)
        self.assertIn("- this change %s, by the base's tools: `%s`" % (r.head, by_base), r.summary)
        if by_own is None:
            self.assertNotIn("by its own tools", r.summary)
        else:
            self.assertIn("- this change %s, by its own tools: `%s`" % (r.head, by_own), r.summary)

    def window_line(self, r, state):
        """The line that shows the window, the same in the log and in the summary: the base commit and its state;
        neither names another commit as the base (self.base, the commit the run's base derives from)."""
        line = "the re-key window: %s at the base %s: %s" % (REKEY_WINDOW, r.base, state)
        self.assertIn(line, r.out.splitlines())
        self.assertIn(line, r.summary.splitlines())
        self.assertNotIn(self.base, r.out + r.summary)

    def test_an_unchanged_checker_passes_and_prints_all_three_ids(self):
        r = self.guard(kind="outside")
        self.assertEqual(r.before, r.after)
        self.assertEqual(r.rc, 0, r.out)
        self.ids(r, r.after, r.after)
        self.assertIn("keys.checker is unchanged", r.summary)

    def test_an_unchanged_checker_passes_whatever_the_window_holds(self):
        """The window decides a move alone: the step passes an unchanged checker before it shows the window, so a base
        whose window cannot be read (a blobless checkout, and the origin gone) passes too."""
        for window, cut_off in ((b"open\n", False), (b"closed\n", False), (None, False), (b"open\n", True)):
            for event, base_ref in self.EVENTS:
                with self.subTest(window=window, cut_off=cut_off, event=event):
                    r = self.guard(window, "outside", event=event, base_ref=base_ref, blobless=cut_off,
                                   cut_off=cut_off)
                    self.assertEqual(r.before, r.after)
                    self.assertEqual(r.rc, 0, r.out)
                    self.assertIn("keys.checker is unchanged", r.summary)
                    self.assertNotIn("::error::", r.out)
                    self.assertNotIn("the re-key window:", r.out + r.summary)

    def test_a_moved_checker_passes_in_an_open_window(self):
        """Open is the base's file reading exactly `open`, with or without trailing newlines."""
        for window in (b"open", b"open\n", b"open\n\n"):
            for event, base_ref in self.EVENTS:
                with self.subTest(window=window, event=event):
                    r = self.guard(window, event=event, base_ref=base_ref)
                    self.assertNotEqual(r.before, r.after)
                    self.assertEqual(r.rc, 0, r.out)
                    notice = "%s; the re-key window is open (%s at the base %s reads open)" % (
                        self.moves(r), REKEY_WINDOW, r.base)
                    self.assertIn("::notice::" + notice, r.out)
                    self.assertIn(notice, r.summary)
                    self.window_line(r, self.state(window))
                    self.ids(r, r.after, r.after)

    def test_a_moved_checker_fails_while_the_window_is_closed(self):
        """No file, an empty one and any other bytes keep the window closed: another case, a space, a NUL byte (which
        bash's $(...) would drop, leaving open), a carriage return; and so do a symbolic link whose target is open
        (its blob holds the bytes `open`) and a directory."""
        for window in (b"closed\n", None, b"", b"Open\n", b"open ", b"op\0en", b"open\r\n", self.Link(b"open"),
                       self.DIRECTORY):
            for event, base_ref in self.EVENTS:
                with self.subTest(window=window, event=event):
                    r = self.guard(window, event=event, base_ref=base_ref)
                    self.assertNotEqual(r.before, r.after)
                    self.assertEqual(r.rc, 1, r.out)
                    self.assertIn("::error::" + self.said(r), r.out)
                    self.assertIn(self.said(r), r.summary)
                    self.assertNotIn("the re-key window is open", r.out + r.summary)
                    self.window_line(r, self.state(window))
                    self.ids(r, r.after, None)

    def test_a_blobless_checkout_fetches_the_window_when_the_step_reads_it(self):
        """As on GitHub, head/ holds no blob outside tools/oft and the root when the rekey step starts (guard asserts
        it): the step fetches the base's window blob as it reads it."""
        for event, base_ref in self.EVENTS:
            with self.subTest(event=event):
                r = self.guard(b"open\n", event=event, base_ref=base_ref, blobless=True)
                self.assertEqual(r.rc, 0, r.out)
                self.assertIn("::notice::%s; the re-key window is open" % self.moves(r), r.out)
                self.window_line(r, "b'open\\n'")

    def test_a_window_it_cannot_read_fails_with_an_error_that_names_it_and_the_base(self):
        """The base has the file, and its blob is neither in the blobless head/ nor to be fetched (the origin is gone
        after the base step): the read error, with git's message, and not the closed-window error, which would say
        the window is closed when nothing says so."""
        for event, base_ref in self.EVENTS:
            with self.subTest(event=event):
                r = self.guard(b"open\n", event=event, base_ref=base_ref, blobless=True, cut_off=True)
                self.assertNotEqual(r.before, r.after)
                self.assertEqual(r.rc, 1, r.out)
                error = "%s; the re-key window, %s at the base %s, could not be read: " % (
                    self.moves(r), REKEY_WINDOW, r.base)
                found = [line for line in r.out.splitlines() if line.startswith("::error::" + error)]
                self.assertEqual(len(found), 1, r.out)
                message = found[0][len("::error::" + error):]
                # git's own message, which names the origin it could not fetch from
                self.assertIn(os.path.join(self.dir, "gone"), message)
                self.assertIn(error + message, r.summary.splitlines())
                self.window_line(r, "unreadable (%s)" % message)
                self.assertNotIn(self.said(r), r.out + r.summary)

    def test_a_change_of_the_window_that_also_moves_the_checker_fails(self):
        """Rule D11 on the window itself: a change that adds, edits or deletes the file and moves keys.checker fails
        whatever the base's window reads, open too, with the error that names the file, not the closed-window one."""
        for window, change in ((None, b"open\n"), (b"open\n", b"closed\n"), (b"open\n", None),
                               (b"closed\n", b"open\n")):
            for event, base_ref in self.EVENTS:
                with self.subTest(window=window, change=change, event=event):
                    r = self.guard(window, "moved", change, event, base_ref)
                    self.assertNotEqual(r.before, r.after)
                    self.assertEqual(r.rc, 1, r.out)
                    error = ("%s; it also changes %s, and no change may both change the re-key window and move "
                             "keys.checker (rule D11)" % (self.moves(r), REKEY_WINDOW))
                    self.assertIn("::error::" + error, r.out)
                    self.assertIn(error, r.summary)
                    self.window_line(r, self.state(window))
                    self.assertNotIn(self.said(r), r.out + r.summary)
                    self.assertNotIn("the re-key window is open", r.out + r.summary)

    def test_a_change_of_the_window_alone_passes(self):
        """Opening or closing the window moves no checker: the change passes, whatever the base's window reads."""
        for window, change in ((None, b"open\n"), (b"closed\n", b"open\n"), (b"open\n", b"closed\n")):
            for event, base_ref in self.EVENTS:
                with self.subTest(window=window, change=change, event=event):
                    r = self.guard(window, None, change, event, base_ref)
                    self.assertEqual(r.before, r.after)
                    self.assertEqual(r.rc, 0, r.out)
                    self.assertIn("keys.checker is unchanged", r.summary)
                    self.assertNotIn("::error::", r.out)

    def test_a_move_the_change_s_own_tools_hide_fails(self):
        """The head changes a checker file and its keys.checker answers with the base's id: its own tools say
        nothing moved, and the base's tools, reading the same head, say it did.  The base's judge it."""
        r = self.guard(kind="hidden")
        self.assertNotEqual(r.before, r.after)
        self.assertEqual(r.rc, 1, r.out)
        self.ids(r, r.after, None)
        self.assertIn("::error::" + self.said(r), r.out)
        # and an open window still lets it through, as any move; its own tools then speak, and differ
        r = self.guard(b"open\n", "hidden")
        self.assertEqual(r.rc, 0, r.out)
        self.ids(r, r.after, r.before)
        self.assertIn("different ids: %s and %s" % (r.after, r.before), r.summary)

    def test_the_window_is_read_and_the_verdict_given_before_any_of_the_change_s_code_runs(self):
        """The change's keys.py could make head/ answer the base's window blob with one that reads open (a replace
        ref, which `git cat-file blob` follows): the verdict has read the window, and failed, before it could, and the
        step that runs that keys.py never starts, so no replace ref is made at all."""
        for event, base_ref in self.EVENTS:
            with self.subTest(event=event):
                r = self.guard(b"closed\n", "replacing", event=event, base_ref=base_ref)
                self.assertNotEqual(r.before, r.after)
                self.assertEqual(r.rc, 1, r.out)
                self.assertIn("::error::" + self.said(r), r.out)
                self.window_line(r, "b'closed\\n'")
                self.assertEqual(git(r.clone, "cat-file", "blob", r.base + ":" + REKEY_WINDOW), "closed")
                self.assertEqual(git(r.clone, "replace", "-l"), "")

    def test_the_change_s_code_cannot_rewrite_the_verdict(self):
        """The verdict runs no code of the change: a head whose keys.py rewrites the rest of the step that imports it
        into a pass still fails a move while the window is closed, and its code never runs, since the step that would
        run it comes after the verdict, and a failed step skips the steps after it.  The control is the honest head,
        `moved`, which test_a_moved_checker_fails_while_the_window_is_closed runs."""
        for event, base_ref in self.EVENTS:
            with self.subTest(event=event):
                r = self.guard(b"closed\n", "rewriting", event=event, base_ref=base_ref)
                self.assertNotEqual(r.before, r.after)
                self.assertEqual(r.rc, 1, r.out)
                self.assertIn("::error::" + self.said(r), r.out)
                self.assertFalse(r.rewrote, r.out)

    def test_a_merge_that_is_not_into_this_repository_s_main_is_not_held(self):
        """A pull request into another base, and the public repository, whose checker moves only by releases cut on
        the internal one: the ids and a notice, whatever the window reads, and with a change of the window too, since
        rule D11 holds neither."""
        for event, base_ref, repository in (("pull_request", "lane", REPOSITORY), ("pull_request", "main", PUBLIC),
                                            ("merge_group", "", PUBLIC)):
            for window, change in ((None, self.SAME), (None, b"open\n"), (b"open\n", None)):
                with self.subTest(event=event, base_ref=base_ref, repository=repository, window=window,
                                  change=change):
                    r = self.guard(window, "moved", change, event, base_ref, repository)
                    self.assertNotEqual(r.before, r.after)
                    self.assertEqual(r.rc, 0, r.out)
                    self.assertIn("::notice::%s; rule D11 holds a merge into main of the internal repository, and "
                                  "this is none" % self.moves(r), r.out)
                    self.assertNotIn("::error::", r.out)
                    self.ids(r, r.after, r.after)

    def test_the_log_and_the_summary_name_the_window_s_content_and_its_base(self):
        """The line names the commit the run read (the plan's base, in the merge queue the head of the entry before),
        not another (window_line checks that wherever it reads the line), and what its file holds as Python's ascii()
        of at most 256 bytes, so no byte of it can form a workflow command or a second line; a longer file shows its
        size too."""
        for window, state in ((b"\n::notice::open\n", "b'\\n::notice::open\\n'"),
                              (b"x" * 300, "b'%s' (300 bytes)" % ("x" * 256))):
            for event, base_ref in self.EVENTS:
                with self.subTest(window=window, event=event):
                    r = self.guard(window, event=event, base_ref=base_ref)
                    self.window_line(r, state)
                    self.assertNotIn("::notice::open", r.out.splitlines())

    def test_the_job_runs_after_lint_and_checks_out_tools_oft_alone(self):
        """The window comes from the base's tree alone: the rekey step's environment names no variable for it."""
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
                                                     "BASE_REF": "${{ github.base_ref }}"})
        self.assertEqual(self.step("base")["env"], {"BASE": "${{ needs.plan.outputs.base }}"})

    def test_the_verdict_runs_no_code_of_the_change_and_the_change_s_own_id_comes_after_it(self):
        """The steps in order: the checkout, setup-python, the base's tools, the base's requirements, the verdict, and
        the change's own id last.  The verdict's script names no file of the change's tools and puts nothing of them
        on a path; the last step does, and carries no `if:` (always() would run the change's code after a failed
        verdict), and no step carries continue-on-error."""
        job = self.jobs["rekey"]
        names = [s.get("id") or s.get("name") or s["uses"].split("@")[0] for s in job["steps"]]
        self.assertEqual(names, ["actions/checkout", "actions/setup-python", "base",
                                 "the tools' dependencies (PyYAML, idna), hash-pinned, from the base", "rekey", "own"])
        self.assertIn("-r base/tools/oft/requirements.txt", job["steps"][3]["run"])

        def code(s):
            return "\n".join(line for line in s["run"].splitlines() if not line.lstrip().startswith("#"))
        verdict, own = code(self.step("rekey")), code(self.step("own"))
        self.assertNotIn("head/tools", verdict)
        self.assertEqual(re.findall(r"PYTHONPATH=(\S+)", verdict), ["base/tools"])
        self.assertEqual(re.findall(r"PYTHONPATH=(\S+)", own), ["head/tools"])
        for s in job["steps"]:
            self.assertNotIn("continue-on-error", s)
        self.assertNotIn("if", self.step("own"))
        self.assertEqual(self.step("own")["env"],
                         dict({"BASE": "${{ needs.plan.outputs.base }}"},
                              **{name.upper(): "${{ steps.rekey.outputs.%s }}" % name
                                 for name in ("from", "to_base", "outside", "may_move", "why", "state")}))

    def own_step(self, to_own, **given):
        """The last step alone, over a stand-in of the change's tools whose keys.checker answers to_own."""
        ws = tempfile.mkdtemp(dir=self.dir)
        git(ws, "init", "-q", "head")
        git(os.path.join(ws, "head"), "commit", "-q", "--allow-empty", "-m", "the change")
        os.makedirs(os.path.join(ws, "head", "tools", "oft"))
        open(os.path.join(ws, "head", "tools", "oft", "__init__.py"), "w").close()
        with open(os.path.join(ws, "head", "tools", "oft", "keys.py"), "w") as f:
            f.write("def checker(repo, commit):\n    return %r\n" % to_own)
        env = dict({"BASE": "b" * 40, "FROM": "1" * 64, "TO_BASE": "1" * 64, "OUTSIDE": "false", "MAY_MOVE": "false",
                    "WHY": "it can merge only in an announced re-key window (rule D11); ask the CI/CD lead",
                    "STATE": "b'closed\\n'"}, **given)
        return self.run_step(self.step("own")["run"], env, cwd=ws)

    def test_the_change_s_own_id_holds_a_move_the_base_s_tools_did_not_see_to_the_verdict_s_answer(self):
        """Where the base's tools see no move and the change's own do: a move the verdict said may not merge fails,
        with its reason; one it said may (an open window) and one outside rule D11 pass with a notice; no answer
        fails.  Where the change's own tools see no move, or the base's saw one (the verdict judged it), nothing more
        is decided here, and a different id is a warning."""
        moved = "2" * 64
        moves = "this change moves keys.checker from %s to %s (re-keys every unit)" % ("1" * 64, moved)
        for given, code, said in (
                ({}, 1, "::error::%s; it can merge only in an announced re-key window (rule D11)" % moves),
                ({"MAY_MOVE": "true", "STATE": "b'open\\n'"}, 0, "::notice::%s; the re-key window is open" % moves),
                ({"OUTSIDE": "true", "MAY_MOVE": "true"}, 0,
                 "::notice::%s; rule D11 holds a merge into main of the internal repository" % moves),
                ({"MAY_MOVE": ""}, 1, "::error::the verdict gave no answer for whether keys.checker may move here"),
                # the base's tools saw a move of their own, which the verdict judged: a different id is a warning
                ({"TO_BASE": "3" * 64}, 0,
                 "::warning::the base's tools and this change's own give its head different")):
            with self.subTest(given=given):
                rc, out, summary = self.own_step(moved, **given)
                self.assertEqual(rc, code, out)
                self.assertIn(said, out)
        rc, out, summary = self.own_step("1" * 64)
        self.assertEqual(rc, 0, out)
        self.assertIn("keys.checker is unchanged: this change re-keys no unit", summary)
        rc, out, _ = self.own_step("not an id")
        self.assertEqual(rc, 1, out)
        self.assertIn("could not compute keys.checker of its head", out)

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


RELEASE_WINDOW_VERDICT = "no platform change merged while the release window was open"
RELEASE_WINDOW_TAG = "refs/tags/ossv/release-window"
RELEASE_WINDOW_OVERLAP = "the release window (tag ossv/release-window) and a re-key window must not be open together"
RELEASE_WINDOW_HELD = "the release-window rule holds a merge into main of the internal repository, and this is none"
# the condition of every release_window step after the window step: the drift steps run only while the tag exists
RELEASE_WINDOW_OPEN = "steps.window.outputs.release_window == 'open'"
# a run of the release_window job's steps as GitHub runs them: the job's exit status (the first failed step's, else 0),
# its output and job summary, the names of the steps that ran, its base and head, and its workspace
ReleaseWindowRun = collections.namedtuple("ReleaseWindowRun", "rc out summary ran base head ws")
# the internal repository alone has these (release_tree.INTERNAL), and a release's tests find neither: the fixture's
# base takes tools/publish/, whose overlay.py the job runs, and the job's drift checkouts are held to publish.yml's
PUBLISH_TOOLS = os.path.join(REPO, "tools", "publish")
PUBLISH_YML = os.path.join(WORKFLOWS, "publish.yml")
# the fixture base's release.yaml: the keys a project publication sets (release, date, counts), and the images a
# platform release pins
FIXTURE_RELEASE_YAML = """\
release: 2026.11.2
date: '2026-11-09'
opam_stem: acme
counts:
  proofs: 10
images:
  checker: ghcr.io/acme/checker@sha256:%s
  runner: ghcr.io/acme/runner@sha256:%s
  builder: ghcr.io/acme/builder@sha256:%s
""" % ("1" * 64, "2" * 64, "3" * 64)
# its dune-project: the shared forms every project's build reads, the core package, and one project's package
FIXTURE_DUNE_PROJECT = """\
(lang dune 3.23)
(package
 (name rocq-acme-core)
 (synopsis "the statement core"))
(package
 (name rocq-acme-libx)
 (synopsis "libx's proofs"))
"""
# the rendering files of a tools/ directory (argv[1]) as platform_drift reads them: tools/publish/plan.py's
# rendering_files, one JSON list
RENDERING_FILES = """\
import json, os, sys
sys.path.insert(0, os.path.join(sys.argv[1], "publish"))
import plan
print(json.dumps(sorted(plan.rendering_files(sys.argv[1]))))
"""


def fixture_tools():
    """{path: bytes} of this repository's tools/ but each tools/<x>/tests/ and the caches: the tools a base of the
    release-window fixture holds, which its job runs (the base's tools/publish/overlay.py and tools/oft)."""
    out = {}
    for d, dns, fns in os.walk(os.path.join(REPO, "tools")):
        rel = os.path.relpath(d, REPO).replace(os.sep, "/")
        dns[:] = [x for x in dns if x != "__pycache__" and not (rel.count("/") == 1 and x == "tests")]
        for f in fns:
            if not f.endswith(".pyc"):
                with open(os.path.join(d, f), "rb") as fh:
                    out[rel + "/" + f] = fh.read()
    return out


@unittest.skipUnless(HAVE_WORKFLOWS and shutil.which("git"), "no .github/workflows, or git is not installed")
@unittest.skipUnless(os.path.isdir(PUBLISH_TOOLS) and os.path.exists(PUBLISH_YML),
                     "no tools/publish/ or .github/workflows/publish.yml: the internal repository alone has them")
class ReleaseWindowTest(StandIn):
    """The release window (OSSV-122): while the tag refs/tags/ossv/release-window exists, pr.yml's release_window job
    fails a merge into main that changes a path only a platform release may change (the base's
    tools/publish/overlay.py platform_drift, on sparse checkouts of publish.yml's drift paths), and fails a change
    whose head's .github/rekey-window reads open (the release window and a re-key window must not be open together),
    but passes the change that closes a re-key window; it prints the state of both windows on every run, and required
    fails with it.  Without the tag it passes every change.  The steps run as GitHub runs them, over an origin whose
    base commit holds this repository's tools/ (but its tests) and a stand-in of every other path platform_drift
    reads; the tag is a ref of that origin, which the job reads with git ls-remote.  The checker file and the
    rendering template a case changes are chosen by the fixture's own checker rules (overlay_oft.py checker-rules,
    which platform_drift reads) and rendering files, not by a path written here."""

    EVENTS = (("pull_request", "main"), ("merge_group", ""))
    # a head that leaves the window file as its base has it
    SAME = object()
    # the changes k7 names, then the other paths platform_drift reads; each with the paths it drifts in (none: the
    # change may merge while the release window is open)
    KINDS = ("checker", "template", "theories", "images.checker", "projects", "content", "toolchain", "tests",
             ".gitattributes", "a nested .gitattributes", "dune-project", "a project's package")

    @classmethod
    def setUpClass(cls):
        cls._fixture = tempfile.TemporaryDirectory(prefix="oft-release-window-")
        cls.origin = os.path.join(cls._fixture.name, "origin")
        os.mkdir(cls.origin)
        git(cls.origin, "init", "-q")
        git(cls.origin, "config", "uploadpack.allowFilter", "true")
        files = dict(fixture_tools(), **{
            ".gitattributes": b"* text=auto eol=lf\n",
            "release.yaml": FIXTURE_RELEASE_YAML.encode(),
            "dune-project": FIXTURE_DUNE_PROJECT.encode(),
            "theories/Shapes.v": b"Definition x := 1.\n",
            "toolchain/allowed-axioms.txt": b"Classical_Prop.classic\n",
            "tests/README.md": b"The positive and negative controls.\n",
            "projects/libx/project.yaml": b"name: libx\n",
            "projects/libx/fuzz/harness.yaml": b"statements: {}\n",
            "CHANGELOG.md": b"# Changelog\n"})
        for rel, data in files.items():
            os.makedirs(os.path.dirname(os.path.join(cls.origin, rel)) or cls.origin, exist_ok=True)
            with open(os.path.join(cls.origin, rel), "wb") as f:
                f.write(data)
        git(cls.origin, "add", "-A")
        git(cls.origin, "commit", "-qm", "the fixture's base")
        cls.root = git(cls.origin, "rev-parse", "HEAD")
        cls.commits = 0
        tools = os.path.join(cls.origin, "tools")
        done = subprocess.run([sys.executable, os.path.join(tools, "publish", "overlay_oft.py"), "checker-rules"],
                              input="{}", cwd=tools, env=dict(os.environ, PYTHONPATH=tools), capture_output=True,
                              text=True, check=True)
        rules = json.loads(done.stdout)
        rendering = {"tools/" + r for r in json.loads(subprocess.run(
            [sys.executable, "-c", RENDERING_FILES, tools], capture_output=True, text=True, check=True).stdout)}
        not_checker, root, dirs = re.compile(rules["not_the_checker"]), rules["root"], tuple(rules["dirs"])

        # platform_drift's own rule
        def in_checker(rel):
            return not (rel.startswith(root) and not_checker.fullmatch(rel[len(root):])) and not rel.startswith(dirs)
        tracked = sorted(rel for rel in files if rel.startswith("tools/"))
        # a file of the checker that renders nothing, and a template of the rendering code that is no checker file
        cls.checker_file = next(rel for rel in tracked if rel.endswith(".py") and in_checker(rel)
                                and rel not in rendering)
        cls.template = next(rel for rel in tracked if rel in rendering and "/templates/" in rel and not in_checker(rel))

    @classmethod
    def tearDownClass(cls):
        cls._fixture.cleanup()

    def setUp(self):
        super().setUp()
        self.jobs = load("pr.yml")["jobs"]
        for name in ("python", "python3"):
            with open(os.path.join(self.dir, "bin", name), "w") as f:
                f.write("#!/bin/sh\nexec %s \"$@\"\n" % shlex.quote(sys.executable))
            os.chmod(os.path.join(self.dir, "bin", name), 0o755)

    def derive(self, parent, files, message):
        """A commit of the origin whose parent is `parent` and whose tree is the parent's but for `files`: {path: bytes
        (exactly those bytes) or None (no such entry)}.  A branch of its own names it, so that a clone has it."""
        index = os.path.join(self.dir, "index")
        env = dict(os.environ, GIT_INDEX_FILE=index)

        def plumb(*args, data=None):
            return subprocess.run(["git", "-c", "user.name=t", "-c", "user.email=", *args], cwd=self.origin,
                                  input=data, check=True, capture_output=True, env=env).stdout.decode().strip()
        plumb("read-tree", parent)
        for path, value in files.items():
            if value is None:
                plumb("update-index", "--force-remove", "--", path)
                continue
            oid = plumb("hash-object", "-w", "--no-filters", "--stdin", data=value)
            plumb("update-index", "--add", "--replace", "--cacheinfo", "100644,%s,%s" % (oid, path))
        commit = plumb("commit-tree", plumb("write-tree"), "-p", parent, "-m", message)
        os.remove(index)
        type(self).commits += 1
        plumb("update-ref", "refs/heads/run-%d" % self.commits, commit)
        return commit

    def blob(self, commit, path):
        return subprocess.run(["git", "show", "%s:%s" % (commit, path)], cwd=self.origin, capture_output=True,
                              check=True).stdout

    def edited(self, commit, path, *pairs):
        data = self.blob(commit, path)
        for old, new in pairs:
            self.assertIn(old, data, path)
            data = data.replace(old, new, 1)
        return data

    def change(self, kind, base):
        """The files a change of the kind `kind` writes on base, and the paths platform_drift reports for it."""
        if kind is None:
            return {}, []
        if kind in ("checker", "template"):
            path = self.checker_file if kind == "checker" else self.template
            return {path: self.blob(base, path) + b"\n# changed\n"}, [path]
        if kind in ("theories", "toolchain", "tests"):
            path = {"theories": "theories/Shapes.v", "toolchain": "toolchain/allowed-axioms.txt",
                    "tests": "tests/README.md"}[kind]
            return {path: self.blob(base, path) + b"changed\n"}, [path]
        if kind == "images.checker":
            return {"release.yaml": self.edited(base, "release.yaml", (b"checker@sha256:" + b"1" * 64,
                                                                        b"checker@sha256:" + b"4" * 64))}, ["release.yaml"]
        if kind == "projects":
            return {"projects/libx/fuzz/harness.yaml": b"statements:\n  s1: {status: proved}\n"}, []
        if kind == "content":
            # a platform release's content pull request: release.yaml's release, date and counts, the bootstrap
            # file, the port list, the changelog and files under projects/
            bootstrap = re.sub(rb"\b[0-9a-f]{40}\b", b"a" * 40,
                               self.blob(base, "tools/publish/bootstrap-public-commit.txt"))
            return {"release.yaml": self.edited(base, "release.yaml", (b"release: 2026.11.2", b"release: 2026.11.3"),
                                                (b"date: '2026-11-09'", b"date: '2026-11-16'"),
                                                (b"proofs: 10", b"proofs: 12")),
                    "tools/publish/bootstrap-public-commit.txt": bootstrap,
                    "tools/publish/ported-public-commits.txt":
                        self.blob(base, "tools/publish/ported-public-commits.txt") + b"b" * 40 + b"\n",
                    "CHANGELOG.md": self.blob(base, "CHANGELOG.md") + b"\n## v2026.11.3\n",
                    "projects/libx/fuzz/harness.yaml": b"statements:\n  s1: {status: proved}\n",
                    "projects/liby/project.yaml": b"name: liby\n"}, []
        if kind == "odd names":
            # paths whose names would run as workflow commands in the log, or split a line of it
            paths = ["theories/##[add-mask]x.v", "theories/a\\b\n::warning::w.v"]
            return {p: b"Definition y := 2.\n" for p in paths}, paths
        if kind == ".gitattributes":
            return {".gitattributes": b"* text=auto eol=lf\n*.v diff\n"}, [".gitattributes"]
        if kind == "a nested .gitattributes":
            return {"projects/libx/.gitattributes": b"*.bin binary\n"}, ["projects/libx/.gitattributes"]
        if kind == "dune-project":
            return {"dune-project": self.edited(base, "dune-project", (b"(lang dune 3.23)", b"(lang dune 3.24)"))}, \
                ["dune-project"]
        self.assertEqual(kind, "a project's package")
        return {"dune-project": self.edited(base, "dune-project", (b"libx's proofs", b"libx's proofs, again"))}, []

    def job(self, window=None, kind=None, change=SAME, tag=True, event="pull_request", base_ref="main",
            repository=REPOSITORY, unreadable_tag=False):
        """The release_window job's steps, in order, each as its `if:` says, stopping at the first that fails.  The
        base is a commit on the fixture's whose .github/rekey-window is `window` (None: there is none); the head is a
        commit on that base with the files the kind `kind` changes and `change` as its window (SAME: the base's).  The
        tag names the base when `tag`, and is missing otherwise.  head/ is a blobless clone of the origin with the
        checkout step's sparse patterns, as actions/checkout makes it; actions/setup-python and the pip install are
        GitHub's, and this test's Python stands in for both.  unreadable_tag: git ls-remote fails as on a network
        error, and every other git command works."""
        base = self.derive(self.root, {} if window is None else {REKEY_WINDOW: window}, "the window")
        files, drift = self.change(kind, base)
        if change is not self.SAME:
            files[REKEY_WINDOW] = change
        head = self.derive(base, files, "the change")
        if tag:
            git(self.origin, "update-ref", RELEASE_WINDOW_TAG, base)
        else:
            subprocess.run(["git", "update-ref", "-d", RELEASE_WINDOW_TAG], cwd=self.origin, capture_output=True)
        job = self.jobs["release_window"]
        [checkout] = [s for s in job["steps"] if s.get("uses", "").startswith("actions/checkout@")]
        ws = tempfile.mkdtemp(dir=self.dir)
        clone = os.path.join(ws, checkout["with"]["path"])
        git(ws, "clone", "-q", "--filter=" + checkout["with"]["filter"], "--no-checkout", "file://" + self.origin,
            clone)
        git(clone, "sparse-checkout", "set", "--no-cone", *checkout["with"]["sparse-checkout"].split())
        git(clone, "checkout", "-q", "--detach", head)
        env = {"GITHUB_WORKSPACE": ws, "GITHUB_EVENT_NAME": event, "GITHUB_REPOSITORY": repository,
               "RUNNER_TEMP": tempfile.mkdtemp(dir=self.dir), "GIT_CONFIG_GLOBAL": os.devnull,
               "GIT_CONFIG_NOSYSTEM": "1"}
        values = {"${{ needs.plan.outputs.base }}": base, "${{ github.base_ref }}": base_ref}
        path = self.path
        if unreadable_tag:
            failing = os.path.join(self.dir, "failing-git")
            os.makedirs(failing, exist_ok=True)
            with open(os.path.join(failing, "git"), "w") as f:
                f.write("#!/bin/sh\nfor a in \"$@\"; do [ \"$a\" != ls-remote ] || {\n"
                        "  echo \"fatal: unable to access 'https://github.com/acme/proofs/': Could not resolve host\" >&2"
                        "; exit 128; }\ndone\nexec %s \"$@\"\n" % shlex.quote(shutil.which("git")))
            os.chmod(os.path.join(failing, "git"), 0o755)
            self.path = failing + os.pathsep + self.path
        if os.path.exists(self.output):
            os.remove(self.output)
        rc, outs, summaries, ran = 0, [], [], []
        try:
            for s in job["steps"]:
                if "if" in s:
                    self.assertEqual(s["if"], RELEASE_WINDOW_OPEN, s)
                    if self.outputs().get("release_window") != "open":
                        continue
                if "uses" in s or s["run"].startswith("python -m pip install"):
                    if "run" in s:
                        # what the pip install reads is in the base's checkout
                        self.assertEqual(s["run"], "python -m pip install --quiet --require-hashes -r "
                                                   "base/tools/oft/requirements.txt")
                        self.assertTrue(os.path.isfile(os.path.join(ws, "base", "tools", "oft", "requirements.txt")))
                    continue
                step_env = {k: values.get(v, v) for k, v in (s.get("env") or {}).items()}
                for k, v in step_env.items():
                    self.assertNotIn("${{", v, k)
                rc, out, summary = self.run_step(s["run"], dict(env, **step_env), cwd=ws)
                ran.append(s.get("id") or s["name"])
                outs.append(out)
                summaries.append(summary)
                if rc:
                    break
        finally:
            self.path = path
        if kind is not None and tag and not unreadable_tag and "drift" in ran:
            self.assertEqual(self.drift_of(outs[-1], rc), [self.shown(p) for p in drift])
        return ReleaseWindowRun(rc, "".join(outs), "".join(summaries), ran, base, head, ws)

    @staticmethod
    def drift_of(out, rc):
        """The paths the drift step's output names: each on its own line, two spaces in, after its error."""
        return [line[2:] for line in out.splitlines() if line.startswith("  ")] if rc else []

    @staticmethod
    def shown(path):
        """A path as the log and the summary print it: on one line, its \\, CR and LF escaped."""
        return path.replace("\\", "\\\\").replace("\r", "\\r").replace("\n", "\\n")

    def stopped(self, out):
        """(the lines of each block of `out` between ::stop-commands::<token> and ::<token>::, the lines outside
        them): the runner reads no line of a block as a workflow command; each token is random."""
        blocks, outside, token = [], [], None
        for line in out.splitlines():
            if token is None:
                m = re.fullmatch(r"::stop-commands::(.*)", line)
                if m:
                    self.assertRegex(m.group(1), r"^[0-9a-f]{32}$")
                    token, block = m.group(1), []
                else:
                    outside.append(line)
            elif line == "::%s::" % token:
                blocks.append(block)
                token = None
            else:
                block.append(line)
        self.assertIsNone(token, out)
        return blocks, outside

    def state(self, window):
        return "missing" if window is None else ascii(window)

    def windows(self, r, release, base_state, head_state):
        """The three lines that show both windows, in the log and in the summary, before any verdict."""
        if release is True:
            release = "open (the tag exists: %s %s)" % (r.base, RELEASE_WINDOW_TAG)
        elif release is False:
            release = "closed (no such tag)"
        want = ["the release window: %s: %s" % (RELEASE_WINDOW_TAG, release),
                "the re-key window: %s at the base %s: %s" % (REKEY_WINDOW, r.base, base_state),
                "the re-key window: %s at this change's head %s: %s" % (REKEY_WINDOW, r.head, head_state)]
        lines = r.out.splitlines()
        for line in want:
            self.assertIn(line, lines)
            self.assertIn(line, r.summary.splitlines())
        at = [lines.index(line) for line in want]
        self.assertEqual(at, sorted(at))
        verdicts = [i for i, line in enumerate(lines) if line.startswith(("::error::", "::notice::"))]
        self.assertTrue(all(i > at[-1] for i in verdicts), r.out)

    def checked_out_nothing(self, r):
        """No checkout beyond the head's window file: no base worktree, and no other file in head/."""
        self.assertFalse(os.path.exists(os.path.join(r.ws, "base")))
        head = os.path.join(r.ws, "head")
        found = []
        for d, dns, fns in os.walk(head):
            dns[:] = [x for x in dns if x != ".git"]
            found += [os.path.relpath(os.path.join(d, f), head).replace(os.sep, "/") for f in fns]
        self.assertLessEqual(set(found), {REKEY_WINDOW})
        self.assertEqual(r.ran, ["window"])

    def verdicts(self, r):
        """required's release-window step and main-gate's step, given the job's result as GitHub gives it."""
        rc_required, out, _ = self.run_step(step(self.jobs["required"], RELEASE_WINDOW_VERDICT)["run"],
                                            {"RELEASE_WINDOW_RESULT": "success" if r.rc == 0 else "failure"})
        rc_gate, _, _ = self.run_step(step(self.jobs["main-gate"], "required passed")["run"],
                                      {"REQUIRED": "success" if rc_required == 0 else "failure"})
        return rc_required, rc_gate

    def drift_failure(self, paths):
        return ("this change changes %d path(s) that only a platform release may change (tools/publish/overlay.py "
                "platform_drift), and the release window (tag ossv/release-window) is open; it can merge after the "
                "release's content pull request merges and the tag ossv/release-window is deleted" % len(paths))

    def test_a_platform_change_fails_while_the_tag_exists_and_every_change_passes_without_it(self):
        """k7's six changes (a checker file, a rendering template, theories/, release.yaml's images.checker, a file
        under projects/, a content pull request) and the other paths platform_drift reads (toolchain/, tests/, a
        .gitattributes at the root and deeper, dune-project's shared forms, and not a project's package stanza), each
        as a pull request and as a merge queue group: with the tag, a change with drift fails and names each path, and
        required and main-gate fail with it; the others pass.  Without the tag every one passes, with no checkout but
        the head's window file."""
        for kind in self.KINDS:
            for event, base_ref in self.EVENTS:
                for tag in (True, False):
                    with self.subTest(kind=kind, event=event, tag=tag):
                        r = self.job(kind=kind, tag=tag, event=event, base_ref=base_ref)
                        self.windows(r, tag, "missing", "missing")
                        _, drift = self.change(kind, r.base)
                        if kind == "checker":
                            self.assertNotEqual(keys.checker(self.origin, r.base), keys.checker(self.origin, r.head))
                        if not tag:
                            self.assertEqual(r.rc, 0, r.out)
                            self.assertIn("the release window is closed: this rule holds no change back", r.out)
                            self.checked_out_nothing(r)
                            self.assertEqual(self.verdicts(r), (0, 0))
                            continue
                        self.assertEqual(r.ran, ["window", "the base's and this change's files that platform_drift "
                                                 "reads", "drift"][:len(r.ran)])
                        self.assertEqual(len(r.ran), 3, r.out)
                        if drift:
                            self.assertEqual(r.rc, 1, r.out)
                            said = self.drift_failure(drift)
                            self.assertIn("::error::" + said, r.out)
                            self.assertIn(said + ":", r.summary)
                            for path in drift:
                                self.assertIn("  " + path, r.out.splitlines())
                                self.assertIn("- " + path, r.summary.splitlines())
                            self.assertEqual(self.verdicts(r), (1, 1))
                        else:
                            self.assertEqual(r.rc, 0, r.out)
                            self.assertIn("this change changes no path that only a platform release may change: it "
                                          "may merge while the release window is open", r.out)
                            self.assertEqual(self.verdicts(r), (0, 0))

    def test_a_drifted_path_or_a_window_s_bytes_run_no_workflow_command(self):
        """A path is this change's text, and so is the head's window file, whose state is the ascii() of its bytes;
        the runner reads a log line that starts with :: (after white space) or holds ##[ anywhere as a workflow
        command.  The job still fails naming the release window; its list of paths, one per line with a line break
        escaped, and each window's state sit between ::stop-commands:: and their resume tokens, and the summary
        escapes the paths too."""
        change = b"::warning::w ##[add-mask]y\n"
        r = self.job(None, "odd names", change)
        self.assertEqual(r.rc, 1, r.out)
        _, drift = self.change("odd names", r.base)
        said = self.drift_failure(drift)
        self.assertIn("::error::" + said, r.out.splitlines())
        self.assertIn("release window (tag ossv/release-window) is open", said)
        self.windows(r, True, "missing", ascii(change))
        blocks, outside = self.stopped(r.out)
        self.assertEqual(blocks, [
            ["the re-key window: %s at the base %s: missing" % (REKEY_WINDOW, r.base)],
            ["the re-key window: %s at this change's head %s: %s" % (REKEY_WINDOW, r.head, ascii(change))],
            ["  " + self.shown(p) for p in drift]], r.out)
        self.assertEqual([line for line in outside if not line.startswith("::error::")
                          and ("##[" in line or line.lstrip().startswith("::"))], [], r.out)
        self.assertEqual(r.summary.splitlines()[-len(drift):], ["- " + self.shown(p) for p in drift])
        self.assertEqual(self.verdicts(r), (1, 1))

    def test_the_tag_with_a_re_key_window_open_at_the_base_fails(self):
        """Both windows open: every change but the one that closes the re-key window fails, whatever it changes, and
        no drift is read; without the tag the same change passes."""
        for kind in (None, "projects"):
            for event, base_ref in self.EVENTS:
                with self.subTest(kind=kind, event=event):
                    r = self.job(b"open\n", kind, event=event, base_ref=base_ref)
                    self.assertEqual(r.rc, 1, r.out)
                    self.windows(r, True, "b'open\\n'", "b'open\\n'")
                    said = ("%s: %s reads open at the base %s and at this change's head; only the change that closes "
                            "the re-key window can merge until the tag is deleted"
                            % (RELEASE_WINDOW_OVERLAP, REKEY_WINDOW, r.base))
                    self.assertIn("::error::" + said, r.out)
                    self.assertIn(said, r.summary)
                    self.assertEqual(r.ran, ["window"])
                    self.assertEqual(self.verdicts(r), (1, 1))
                    r = self.job(b"open\n", kind, tag=False, event=event, base_ref=base_ref)
                    self.assertEqual(r.rc, 0, r.out)
                    self.windows(r, False, "b'open\\n'", "b'open\\n'")
                    self.checked_out_nothing(r)

    def test_a_change_that_opens_a_re_key_window_while_the_tag_exists_fails(self):
        """Open is the head's file reading exactly `open`, with or without trailing newlines, as the rekey job reads
        it; the base's is closed or missing."""
        for window in (None, b"closed\n"):
            for change in (b"open\n", b"open", b"open\n\n"):
                for event, base_ref in self.EVENTS:
                    with self.subTest(window=window, change=change, event=event):
                        r = self.job(window, None, change, event=event, base_ref=base_ref)
                        self.assertEqual(r.rc, 1, r.out)
                        self.windows(r, True, self.state(window), ascii(change))
                        said = ("%s: this change makes %s read open at its head %s, which opens a re-key window"
                                % (RELEASE_WINDOW_OVERLAP, REKEY_WINDOW, r.head))
                        self.assertIn("::error::" + said, r.out)
                        self.assertIn(said, r.summary)
                        self.assertEqual(self.verdicts(r), (1, 1))
                        self.assertEqual(self.job(window, None, change, tag=False, event=event,
                                                  base_ref=base_ref).rc, 0)

    def test_a_head_window_that_does_not_read_exactly_open_opens_none(self):
        """Another case, a trailing space, a NUL byte (which bash's $(...) would drop, leaving open), a carriage
        return and an empty file keep the window closed, as for the rekey job."""
        for change in (b"Open\n", b"open ", b"op\0en", b"open\r\n", b""):
            with self.subTest(change=change):
                r = self.job(None, None, change)
                self.assertEqual(r.rc, 0, r.out)
                self.windows(r, True, "missing", ascii(change))
                self.assertNotIn(RELEASE_WINDOW_OVERLAP, r.out)

    def test_the_change_that_closes_the_re_key_window_passes_while_the_tag_exists(self):
        """Its head reads anything but open, or has no window file: failing it would leave no way out but deleting
        the tag.  It is still held to the drift rule."""
        for change in (b"closed\n", None):
            for event, base_ref in self.EVENTS:
                with self.subTest(change=change, event=event):
                    r = self.job(b"open\n", None, change, event=event, base_ref=base_ref)
                    self.assertEqual(r.rc, 0, r.out)
                    self.windows(r, True, "b'open\\n'", self.state(change))
                    self.assertIn("this change closes the re-key window: %s reads open at the base and not at its "
                                  "head" % REKEY_WINDOW, r.out)
                    self.assertIn("this change changes no path that only a platform release may change", r.out)
                    self.assertEqual(self.verdicts(r), (0, 0))
        r = self.job(b"open\n", "theories", b"closed\n")
        self.assertEqual(r.rc, 1, r.out)
        self.assertIn("::error::" + self.drift_failure(["theories/Shapes.v"]), r.out)

    def test_a_tag_that_cannot_be_read_fails(self):
        """git ls-remote fails (exit 128, as on a network error): the job fails, the tag present or not, since a
        failed read is never an absent tag, and the log still shows both windows first."""
        for tag in (True, False):
            for event, base_ref in self.EVENTS:
                with self.subTest(tag=tag, event=event):
                    r = self.job(None, "theories", tag=tag, event=event, base_ref=base_ref, unreadable_tag=True)
                    self.assertEqual(r.rc, 1, r.out)
                    error = ("git ls-remote exited 128: fatal: unable to access 'https://github.com/acme/proofs/': "
                             "Could not resolve host")
                    self.windows(r, "unreadable (%s)" % error, "missing", "missing")
                    said = ("the release window, %s, could not be read (a failed read is never an absent tag): %s"
                            % (RELEASE_WINDOW_TAG, error))
                    self.assertIn("::error::" + said, r.out)
                    self.assertIn(said, r.summary)
                    self.checked_out_nothing(r)
                    self.assertEqual(self.verdicts(r), (1, 1))

    def test_a_merge_that_is_not_into_this_repository_s_main_is_not_held(self):
        """A pull request into another base, and the public repository: both windows shown, then a notice, with the
        tag, a drift and both windows open."""
        for event, base_ref, repository in (("pull_request", "lane", REPOSITORY), ("pull_request", "main", PUBLIC),
                                            ("merge_group", "", PUBLIC)):
            with self.subTest(event=event, base_ref=base_ref, repository=repository):
                r = self.job(b"open\n", "theories", event=event, base_ref=base_ref, repository=repository)
                self.assertEqual(r.rc, 0, r.out)
                self.windows(r, True, "b'open\\n'", "b'open\\n'")
                self.assertIn("::notice::" + RELEASE_WINDOW_HELD, r.out)
                self.assertNotIn("::error::", r.out)
                self.checked_out_nothing(r)

    def test_required_fails_on_a_pull_request_or_group_the_rule_did_not_pass(self):
        """Drafts included: the job waits for the plan alone, so a draft runs it, and nothing but success passes."""
        job = self.jobs["required"]
        self.assertIn("release_window", job["needs"])
        s = step(job, RELEASE_WINDOW_VERDICT)
        self.assertEqual(" ".join(s["if"].split()),
                         "github.event_name == 'pull_request' || github.event_name == 'merge_group'")
        self.assertEqual(s["env"], {"RELEASE_WINDOW_RESULT": "${{ needs.release_window.result }}"})
        for result, want in (("success", 0), ("failure", 1), ("skipped", 1), ("cancelled", 1), ("", 1)):
            with self.subTest(result=result):
                rc, out, _ = self.run_step(s["run"], {"RELEASE_WINDOW_RESULT": result})
                self.assertEqual(rc, want, out)
                if want:
                    self.assertIn("::error::the release-window rule (job release_window) did not pass (%s)" % result,
                                  out)

    def test_the_job_needs_the_plan_alone_and_reads_publish_yml_s_drift_paths(self):
        """It waits for no lint, so a draft runs it; it checks out the head's window file alone, blobless; its drift
        checkouts take the very paths publish.yml's drift job checks out of S and of P; and pr.yml names no
        repository but the public one."""
        job = self.jobs["release_window"]
        self.assertEqual(job["needs"], ["plan"])
        self.assertEqual(" ".join(job["if"].split()),
                         "${{ !cancelled() && needs.plan.result == 'success' "
                         "&& (github.event_name == 'pull_request' || github.event_name == 'merge_group') }}")
        self.assertEqual(job["permissions"], {"contents": "read"})
        checkouts = [s for s in job["steps"] if s.get("uses", "").startswith("actions/checkout@")]
        self.assertEqual([s["with"] for s in checkouts],
                         [{"path": "head", "filter": "blob:none", "sparse-checkout-cone-mode": False,
                           "sparse-checkout": "/.github/rekey-window"}])
        trees = step(job, "the base's and this change's files that platform_drift reads")
        drift = [s for s in load("publish.yml")["jobs"]["drift"]["steps"]
                 if s.get("uses", "").startswith("actions/checkout@") and s["with"].get("path") in ("s", "p")]
        self.assertEqual(len(drift), 2)
        for s in drift:
            self.assertEqual(trees["env"]["DRIFT_PATHS"].split(), s["with"]["sparse-checkout"].split())
        # The private repository's name is written in parts: this file publishes, and the name is a needle of the
        # publication scan (ossv-binscan private-repo). The string the test looks for is the same.
        with open(os.path.join(WORKFLOWS, "pr.yml")) as f:
            self.assertNotIn("oss-verify-proofs" "-internal", helpers.inline_scripts(f.read()))


MADE_FROM_STEP = "each made-from record the plan named equals its generator's (the head's made_from.py --check)"
MADE_FROM_TESTS = "the tests of dev/licence/, when every made-from record is checked"
# A made_from.py that prints two rows and exits with the code its file `rc` beside it holds, after logging, to
# MADE_FROM_LOG, the directory it runs in (from HEAD_DIR), the path it was called by and its arguments.
FAKE_MADE_FROM = """\
import os, sys
here = os.path.dirname(os.path.abspath(__file__))
with open(os.environ["MADE_FROM_LOG"], "a") as f:
    f.write(" ".join([os.path.relpath(os.getcwd(), os.environ["HEAD_DIR"])] + sys.argv) + "\\n")
print("+ row added\\n- row removed")
with open(os.path.join(here, "rc")) as f:
    sys.exit(int(f.read()))
"""
# The shared generator, dev/licence/made_from.py, as --unit-file calls it: it logs as FAKE_MADE_FROM does, prints its
# reason, and exits with the code its file `rc` beside it holds.
FAKE_SHARED_MADE_FROM = """\
import os, sys
here = os.path.dirname(os.path.abspath(__file__))
with open(os.environ["MADE_FROM_LOG"], "a") as f:
    f.write(" ".join([os.path.relpath(os.getcwd(), os.environ["HEAD_DIR"])] + sys.argv) + "\\n")
with open(os.path.join(here, "rc")) as f:
    rc = int(f.read())
print("%s: %s" % (sys.argv[-1], "only data and the call" if rc == 0 else "a statement that is not data"))
sys.exit(rc)
"""
# The runner's command files, each named by a variable of a step's environment: a line that a program writes to
# GITHUB_PATH or GITHUB_ENV reaches each later step of the job.
COMMAND_FILES = ("GITHUB_OUTPUT", "GITHUB_ENV", "GITHUB_PATH", "GITHUB_STATE", "GITHUB_STEP_SUMMARY")
WORKFLOW_PATH = ".github/workflows/pr.yml"


def licence_test(body):
    """A test module of dev/licence/ that logs, to MADE_FROM_LOG, that it was imported, with one test of `body`."""
    return ("import os, unittest\nwith open(os.environ['MADE_FROM_LOG'], 'a') as f:\n"
            "    f.write('imported ' + __name__ + '\\n')\n"
            "class T(unittest.TestCase):\n    def test_it(self):\n        %s\n" % body)


def sees_command_files(who):
    """A program of the change, `who`, that logs to MADE_FROM_LOG the command files its environment names ("<who>
    sees none" when it names none), and writes a line into each file that it names."""
    return ("import os\n"
            "seen = [name for name in %r if name in os.environ]\n"
            "with open(os.environ['MADE_FROM_LOG'], 'a') as log:\n"
            "    log.write('%s sees ' + (','.join(seen) or 'none') + '\\n')\n"
            "for name in seen:\n"
            "    with open(os.environ[name], 'a') as f:\n"
            "        f.write('forged by %s\\n')\n" % (COMMAND_FILES, who, who))


def stop_command_blocks(test, out):
    """The ::stop-commands:: blocks of a step's output, [(token, text)], and the output outside them."""
    blocks, outside, rest = [], [], out
    while True:
        m = re.search(r"::stop-commands::([0-9a-f]{32})\n", rest)
        if m is None:
            outside.append(rest)
            return blocks, "".join(outside)
        outside.append(rest[:m.start()])
        body, end, rest = rest[m.end():].partition("::%s::\n" % m.group(1))
        test.assertTrue(end, "a block with no end: %s" % out)
        blocks.append((m.group(1), body))


def write_files(root, files):
    """Each {path: text or bytes} under root; a value of None deletes the path."""
    for rel, text in files.items():
        path = os.path.join(root, rel)
        if text is None:
            os.remove(path)
            continue
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "wb") as f:
            f.write(text if isinstance(text, bytes) else text.encode())


class HeadRepoTest(StandIn):
    """A git repository head/ in ws/, as the lint job checks it out, and the ways a test changes it."""

    def setUp(self):
        super().setUp()
        self.ws = os.path.join(self.dir, "ws")
        self.head = os.path.join(self.ws, "head")
        os.makedirs(self.head)
        git(self.head, "init", "-q")

    def write(self, files):
        write_files(self.head, files)

    def commit(self, message):
        git(self.head, "add", "-A")
        git(self.head, "commit", "-qm", message)
        return git(self.head, "rev-parse", "HEAD")

    def sparse(self):
        """head/ as the lint job checks it out when the plan says lint_files_left_out: every file but the proof
        libraries."""
        git(self.head, "sparse-checkout", "set", "--no-cone", "/*", "!/proofs/*/*/lib/*",
            "!/projects/*/*/proofs/lib/*")

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

    def fetches(self, trace):
        """(git fetch processes, of them those a git process started, a lazy fetch), from GIT_TRACE2_EVENT: each git
        process writes one start event, and a git process that starts another writes a child_start event."""
        started = lazy = 0
        if os.path.exists(trace):
            with open(trace) as f:
                for line in f:
                    event = json.loads(line)
                    if "fetch" in event.get("argv", []):
                        started += event["event"] == "start"
                        lazy += event["event"] == "child_start"
        return started, lazy


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
@unittest.skipUnless(shutil.which("git"), "git is not installed")
class MadeFromRepo(HeadRepoTest):
    """HeadRepoTest's head/, as the made_from job checks it out, with a first commit, and a `python` on PATH that runs
    this test's own Python, as setup-python gives the plan job one."""

    EVIDENCE = "proofs/provenance/evidence/licence/made_from.py"

    def setUp(self):
        super().setUp()
        self.temp = os.path.join(self.ws, "tmp")
        os.mkdir(self.temp)
        self.log = os.path.join(self.dir, "made-from.log")
        with open(os.path.join(self.dir, "bin", "python"), "w") as f:
            f.write('#!/bin/sh\nexec %s "$@"\n' % shlex.quote(sys.executable))
        os.chmod(os.path.join(self.dir, "bin", "python"), 0o755)
        self.write({"README": "r\n"})
        self.base = self.commit("base")

    def generator(self, unit, rc):
        """Unit <unit>/ with the stand-in made_from.py exiting rc, and no record beside it."""
        d = "%s/%s" % (unit, os.path.dirname(self.EVIDENCE))
        return {d + "/made_from.py": FAKE_MADE_FROM, d + "/rc": "%d\n" % rc}

    def record(self, unit):
        """The path of the made-from record of unit <unit>/, beside the made_from.py of generator()."""
        return "%s/%s/made-from.tsv" % (unit, os.path.dirname(self.EVIDENCE))

    def unit(self, unit, rc):
        """Unit <unit>/ with the stand-in made_from.py exiting rc, and a record beside it."""
        return dict(self.generator(unit, rc), **{self.record(unit): "row\n"})

    def calls(self):
        if not os.path.exists(self.log):
            return []
        with open(self.log) as f:
            return f.read().splitlines()

    def clear_log(self):
        if os.path.exists(self.log):
            os.remove(self.log)

    def reach(self, routed="true"):
        """The reach step's made-from block, run as the step runs it over the change from self.base to head/'s HEAD:
        changed.txt as the plan's base step lists it (every path of the tree, and BASE the commit itself, when the
        run is not routed).  (its exit, its output, the outputs it wrote)."""
        reach = next(s for s in load("pr.yml")["jobs"]["plan"]["steps"] if s.get("id") == "reach")
        block = re.search(r"\n *# made-from records\n(.*?\n) *# end of made-from records\n", reach["run"], re.S)
        self.assertIsNotNone(block, "no made-from block in the reach step")
        if routed == "true":
            base = self.base
            listed = git(self.head, "-c", "core.quotePath=false", "diff", "--no-renames", "--name-only", base, "HEAD")
        else:
            base = git(self.head, "rev-parse", "HEAD")
            listed = git(self.head, "-c", "core.quotePath=false", "ls-tree", "-r", "--name-only", "HEAD")
        with open(os.path.join(self.temp, "changed.txt"), "w") as f:
            f.write(listed + "\n" if listed else "")
        if os.path.exists(self.output):
            os.remove(self.output)
        rc, out, _summary = self.run_step('changed="$RUNNER_TEMP/changed.txt"\n' + block.group(1),
                                          {"BASE": base, "ROUTED": routed, "RUNNER_TEMP": self.temp}, cwd=self.ws)
        return rc, out, self.outputs()


class MadeFromJobTest(MadeFromRepo):
    """pr.yml's made_from job.  Its records step runs, for each unit the plan named, the head's made_from.py --check:
    exit 0 passes, 1 fails with the rows it printed, 2 warns and passes, 4 (a refusal), 5 (a defect of the generator's
    own code), 124 (the 1,800 s time-out) and any other exit fail, for every unit.  A unit is strict (UNITS,
    made_from_units) or proofs-only (PROOFS, made_from_proofs, and not UNITS): exit 3
    (the record names no path twice, and every row that differs is one a run gives again, for a file that the record
    holds in no row of another kind) fails a strict unit and gives a proofs-only unit one warning.  The step runs the
    strict units, then the proofs-only units, each in sorted order, and a proofs-only unit only when the plan's hold is
    none.  Before any of that, for every unit it checks, a unit fails when it holds a made_from.py or a made-from.tsv
    under proofs/provenance/ anywhere but evidence/licence/, or one of the two there without the other.  A unit with
    neither file passes with a line.  When the shared generator dev/licence/made_from.py is there, its --unit-file first
    checks each made_from.py, and a file it refuses fails the job and is not run.  The tests step runs the tests of
    dev/licence/ when the plan named every unit.  Nothing of the change runs while head/.git/config holds a credential,
    nothing at all for KIND=contributor, and what the change's code writes is printed between ::stop-commands:: and that
    block's token.  The change's code runs with no command file of the runner in its environment."""

    # the reason the records step's time line gives for each kind of unit
    STRICT = "strict: its provenance tree or its images/dune changed, or the change can move every record"
    PROOFS_ONLY = "proofs only: its proofs changed outside proofs/provenance/"

    def job(self):
        return load("pr.yml")["jobs"]["made_from"]

    def step(self, units, kind="maintainer", env=None, proofs=(), hold="none"):
        """The records step, for the strict units `units` and the units `proofs` whose proofs changed, under the plan's
        hold `hold`, with `env` added to its environment: (its exit, its output, the calls logged).  The job summary
        it wrote is left in self.summary."""
        s = step(self.job(), MADE_FROM_STEP)
        self.assertEqual(s["env"], {"UNITS": "${{ needs.plan.outputs.made_from_units }}",
                                    "PROOFS": "${{ needs.plan.outputs.made_from_proofs }}",
                                    "HOLD": "${{ needs.plan.outputs.hold }}"})  # KIND is the workflow's
        self.assertNotIn("if", s)
        rc, out, self.summary = self.run_step(s["run"], {"UNITS": json.dumps(units),
                                                         "PROOFS": json.dumps(list(proofs)), "HOLD": hold,
                                                         "RUNNER_TEMP": self.temp, "KIND": kind,
                                                         "MADE_FROM_LOG": self.log, "HEAD_DIR": self.head,
                                                         **(env or {})}, cwd=self.ws)
        return rc, out, self.calls()

    def licence_step(self, every="true", kind="maintainer", env=None):
        """The tests step, as step() runs the records step."""
        s = step(self.job(), MADE_FROM_TESTS)
        self.assertEqual(s["env"], {"EVERY": "${{ needs.plan.outputs.made_from_every }}"})
        self.assertEqual(s["if"], "${{ !cancelled() }}")   # whatever the records step concluded
        rc, out, self.summary = self.run_step(s["run"], {"EVERY": every, "RUNNER_TEMP": self.temp, "KIND": kind,
                                                         "MADE_FROM_LOG": self.log, "HEAD_DIR": self.head,
                                                         **(env or {})}, cwd=self.ws)
        return rc, out, self.calls()

    def shared(self, rc):
        """The shared generator in head/dev/licence/, exiting rc for each file it is given."""
        self.write({"dev/licence/made_from.py": FAKE_SHARED_MADE_FROM, "dev/licence/rc": "%d\n" % rc})

    def licence_tests(self):
        d = os.path.join(self.head, "dev", "licence")
        return [os.path.join(d, n) for n in os.listdir(d) if n.startswith("test_")] if os.path.isdir(d) else []

    def check_call(self, unit):
        return ". %s/%s --check" % (unit, self.EVIDENCE)

    def unit_file_call(self, unit):
        return ". dev/licence/made_from.py --unit-file %s/%s" % (unit, self.EVIDENCE)

    def no_record(self, unit):
        """The start of the error for unit <unit>/ when it holds a made_from.py at EVIDENCE and no made-from.tsv
        beside it."""
        return "::error::%s holds %s, a made_from.py with no made-from.tsv beside it" % (unit, self.EVIDENCE)

    def no_generator(self, unit):
        """The start of the error for unit <unit>/ when it holds a made-from.tsv beside EVIDENCE and no made_from.py
        there."""
        return "::error::%s holds %s/made-from.tsv, a made-from record with no made_from.py beside it" % (
            unit, os.path.dirname(self.EVIDENCE))

    def no_outside(self, unit, path):
        """The start of the error for unit <unit>/ when it holds `path` (a path below the unit, as escape() gives it),
        a made_from.py or a made-from.tsv, outside proofs/provenance/evidence/licence/."""
        what = "a made_from.py" if path.endswith("/made_from.py") else "a made-from record"
        return "::error::%s holds %s, %s outside proofs/provenance/evidence/licence/." % (unit, path, what)

    def assert_refused_outside(self, out, unit, directory):
        """The step's errors are exactly two: one for the made_from.py and one for the made-from.tsv in `directory`
        (below the unit), each outside evidence/licence/.  No warning."""
        errors = [line for line in out.splitlines() if line.startswith("::error::")]
        self.assertEqual(len(errors), 2, out)
        for name in ("made_from.py", "made-from.tsv"):
            want = self.no_outside(unit, "%s/%s" % (directory, name))
            self.assertEqual(len([e for e in errors if e.startswith(want)]), 1, out)
        self.assertNotIn("::warning::", out)

    def test_exit_0_passes(self):
        self.write(self.unit("projects/curl/fuzz_bufq", 0))
        self.commit("a record")
        rc, out, calls = self.step(["projects/curl/fuzz_bufq"])
        self.assertEqual((rc, calls), (0, [self.check_call("projects/curl/fuzz_bufq")]), out)
        self.assertIn("the record matches its generator", out)
        self.assertNotIn("::error::", out)
        self.assertNotIn("::warning::", out)

    def test_exit_1_fails_shows_the_rows_and_names_the_shared_generator_s_docstring(self):
        """A record that differs from its generator is the unit owner's question, not a file to regenerate: the error
        says not to clear it with --apply, and names the place that says what a record reports and what it does not,
        the module docstring of dev/licence/made_from.py."""
        self.write(self.unit("projects/curl/fuzz_bufq", 1))
        self.commit("a stale record")
        rc, out, _calls = self.step(["projects/curl/fuzz_bufq"])
        self.assertEqual(rc, 1, out)
        self.assertIn("+ row added\n- row removed\n", out)
        [error] = [line for line in out.splitlines() if line.startswith("::error::")]
        self.assertTrue(error.startswith("::error::projects/curl/fuzz_bufq/%s --check exited 1:" % self.EVIDENCE), out)
        self.assertIn("Do not run made_from.py --apply to clear this", error)
        self.assertIn("module docstring of dev/licence/made_from.py", error)
        # nothing anywhere in the step tells a reader to regenerate the record and commit it
        self.assertNotIn("commit what it writes", step(self.job(), MADE_FROM_STEP)["run"])

    def test_exit_2_warns_with_the_output_and_passes(self):
        self.write(self.unit("projects/curl/fuzz_bufq", 2))
        self.commit("an undecided record")
        rc, out, _calls = self.step(["projects/curl/fuzz_bufq"])
        self.assertEqual(rc, 0, out)
        self.assertIn("::warning::projects/curl/fuzz_bufq/%s --check exited 2" % self.EVIDENCE, out)
        self.assertIn("%0A+ row added%0A- row removed", out)
        self.assertNotIn("::error::", out)

    def test_exit_4_fails_and_says_the_generator_refused_the_unit(self):
        """The shared generator of OSSV-400 (#2615) exits 4 when it refuses a unit: an input is missing, it cannot
        read an input, or the unit file is bad.  The error says that the generator refused the unit, and not that the
        check did not finish."""
        unit = "projects/curl/fuzz_bufq"
        self.write(self.unit(unit, 4))
        self.commit("a unit that the generator refuses")
        rc, out, calls = self.step([unit])
        self.assertEqual((rc, calls), (1, [self.check_call(unit)]), out)
        [error] = [line for line in out.splitlines() if line.startswith("::error::")]
        self.assertTrue(error.startswith("::error::%s/%s --check exited 4: the generator refused this unit"
                                         % (unit, self.EVIDENCE)), out)
        self.assertNotIn("did not finish", out)

    def test_exit_5_a_defect_of_the_generator_fails_every_unit_and_never_warns(self):
        """Exit 5 is DEFECT of dev/licence/made_from.py: a defect of the generator's own code (a run or the check
        stopped on a fault or an uncaught exception, a run wrote no OUT or one that is not UTF-8, or the two runs
        differ).  It fails a strict unit and a proofs-only unit alike, with one error that names the generator, and
        gives no warning: exit 3, drift, is the exit that warns for a proofs-only unit, so a defect is not 3."""
        unit = "projects/curl/fuzz_bufq"
        self.write(self.unit(unit, 5))
        self.commit("a generator with a defect")
        for units, proofs in (([unit], []), ([], [unit])):
            with self.subTest(strict=bool(units)):
                self.clear_log()
                rc, out, calls = self.step(units, proofs=proofs)
                self.assertEqual((rc, calls), (1, [self.check_call(unit)]), out)
                self.assertIn("::error::%s/%s --check exited 5: the shared generator dev/licence/made_from.py stopped "
                              "on a defect of its own code" % (unit, self.EVIDENCE), out)
                self.assertNotIn("::warning::", out)

    def test_any_other_exit_fails(self):
        """Exit 6, which no generator gives, for a strict unit and for a proofs-only unit alike."""
        unit = "projects/curl/fuzz_bufq"
        self.write(self.unit(unit, 6))
        self.commit("a broken generator")
        for units, proofs in (([unit], []), ([], [unit])):
            with self.subTest(strict=bool(units)):
                self.clear_log()
                rc, out, calls = self.step(units, proofs=proofs)
                self.assertEqual((rc, calls), (1, [self.check_call(unit)]), out)
                self.assertIn("::error::%s/%s --check exited 6: the check did not finish" % (unit, self.EVIDENCE), out)
                self.assertNotIn("::warning::", out)

    def test_each_exit_means_the_same_for_both_kinds_of_unit_but_exit_3(self):
        """For a strict unit (UNITS) and a proofs-only unit (PROOFS alone), each exit of --check: 0 passes, 1 fails, 2
        warns and passes, 4, 5 (a defect of the generator), 124 and 6 fail.  Exit 3 fails a strict unit, with an error
        that names made_from.py --record, and gives a proofs-only unit one warning that names the unit, gives the number
        of rows that differ (the stand-in prints two) and the rows, and passes.  The time line gives the unit's reason."""
        unit = "projects/curl/fuzz_bufq"
        rel = "%s/%s" % (unit, self.EVIDENCE)
        for strict in (True, False):
            for code, failed, said in (
                    (0, False, "%s --check: the record matches its generator" % rel),
                    (1, True, "::error::%s --check exited 1: the record differs from what its generator gives" % rel),
                    (2, False, "::warning::%s --check exited 2, so the check could not decide" % rel),
                    (3, strict, "::error::%s --check exited 3: the rows that a run gives again differ from the record "
                                "(the rows + and - above). made_from.py --record brings the record up to date." % rel
                     if strict else
                     "::warning::%s: its made-from record is not up to date in rows that a run gives again (%s "
                     "--check exited 3). Rows that differ: 2. The unit is %s, so the job does not fail for this. "
                     "made_from.py --record brings the record up to date. The first 20 rows that differ:%%0A+ row "
                     "added%%0A- row removed" % (unit, rel, self.PROOFS_ONLY)),
                    (4, True, "::error::%s --check exited 4: the generator refused this unit" % rel),
                    (124, True, "::error::%s --check did not finish within 1,800 s" % rel),
                    (5, True, "::error::%s --check exited 5: the shared generator dev/licence/made_from.py stopped on a "
                              "defect of its own code" % rel),
                    (6, True, "::error::%s --check exited 6: the check did not finish" % rel)):
                with self.subTest(strict=strict, exit=code):
                    self.write(self.unit(unit, code))
                    self.clear_log()
                    rc, out, calls = self.step([unit] if strict else [], proofs=[unit] if not strict else [])
                    self.assertEqual((rc, calls), (int(failed), [self.check_call(unit)]), out)
                    lines = out.splitlines()
                    commands = [line for line in lines if line.startswith(("::error::", "::warning::"))]
                    self.assertEqual(len(commands), 0 if code == 0 else 1, out)
                    self.assertEqual(len([line for line in lines if line.startswith(said)]), 1, out)
                    if code == 3 and not strict:
                        # the warning is that whole line, rows and all
                        self.assertEqual(commands, [said], out)
                    self.assertRegex(out, r"(?m)^%s: %s --check exited %d in [0-9]+ s \(%s\)$"
                                     % (re.escape(unit), re.escape(rel), code,
                                        re.escape(self.STRICT if strict else self.PROOFS_ONLY)))

    def test_a_proofs_only_warning_holds_the_number_of_rows_and_the_first_20(self):
        """With 25 rows that differ (the lines of the output that start with "- " or "+ ") among lines that do not
        count, the warning says 25 and holds exactly the first 20 of them, in order, through escape(): each row holds
        a %, which escape() writes as %25."""
        unit = "projects/curl/fuzz_bufq"
        rows = ["%s row %d%%s" % ("-+"[i % 2], i) for i in range(1, 26)]
        text = (["made_from.py --check: the record is not what this generator gives; the rows that differ:"]
                + rows[:10] + ["+not a row", "-nor this", " + nor this"] + rows[10:]
                + ["made_from.py --check: every row that differs is one a run gives again"])
        d = "%s/%s" % (unit, os.path.dirname(self.EVIDENCE))
        self.write({d + "/made_from.py": "import sys\nprint(%r)\nsys.exit(3)\n" % "\n".join(text),
                    d + "/made-from.tsv": "row\n"})
        self.commit("a generator that prints 25 rows that differ")
        rc, out, calls = self.step([], proofs=[unit])
        self.assertEqual((rc, calls), (0, []), out)
        self.assertNotIn("::error::", out)
        [warning] = [line for line in out.splitlines() if line.startswith("::warning::")]
        self.assertIn(" Rows that differ: 25. ", warning)
        _before, cut, shown = warning.partition("The first 20 rows that differ:%0A")
        self.assertTrue(cut, warning)
        self.assertEqual(shown, "%0A".join(row.replace("%", "%25") for row in rows[:20]))

    def test_a_unit_in_both_lists_is_strict(self):
        """It runs once, as a strict unit, and its exit 3 fails."""
        unit = "projects/curl/fuzz_bufq"
        self.write(self.unit(unit, 3))
        self.commit("a record whose rows a run gives again differ")
        rc, out, calls = self.step([unit], proofs=[unit])
        self.assertEqual((rc, calls), (1, [self.check_call(unit)]), out)
        [error] = [line for line in out.splitlines() if line.startswith("::error::")]
        self.assertTrue(error.startswith("::error::%s/%s --check exited 3:" % (unit, self.EVIDENCE)), out)
        self.assertNotIn("::warning::", out)
        self.assertIn("(%s)\n" % self.STRICT, out)

    def test_a_held_proofs_only_unit_runs_nothing_and_a_strict_unit_still_runs(self):
        """With the plan's hold label or draft, a proofs-only unit gets one line that says why it is not checked, and
        nothing of it runs: no --unit-file and no --check.  A strict unit in the same run is checked.  With the hold
        none, the proofs-only unit runs after the strict unit."""
        strict, only = "projects/curl/fuzz_fnmatch", "projects/curl/fuzz_bufq"
        self.shared(0)
        self.write(self.unit(strict, 0))
        self.write(self.unit(only, 3))
        self.commit("a strict unit and a proofs-only unit")
        for hold in ("label", "draft"):
            with self.subTest(hold=hold):
                self.clear_log()
                rc, out, calls = self.step([strict], proofs=[only], hold=hold)
                self.assertEqual((rc, calls), (0, [self.unit_file_call(strict), self.check_call(strict)]), out)
                said = [line for line in out.splitlines() if line.startswith(only)]
                self.assertEqual(said, ["%s: not checked: its proofs changed outside proofs/provenance/, and the "
                                        "plan's hold is %s, not none" % (only, hold)], out)
                self.assertNotIn("::warning::", out)
        self.clear_log()
        rc, out, calls = self.step([strict], proofs=[only])
        self.assertEqual((rc, calls), (0, [self.unit_file_call(strict), self.check_call(strict),
                                           self.unit_file_call(only), self.check_call(only)]), out)
        self.assertEqual(len([line for line in out.splitlines() if line.startswith("::warning::%s: " % only)]), 1,
                         out)

    def test_strict_units_run_first_then_proofs_only_units_each_in_sorted_order(self):
        bufq, fnmatch, scene, zlib = ("projects/curl/fuzz_bufq", "projects/curl/fuzz_fnmatch",
                                      "projects/libreac/fuzz_scene", "projects/zlib/fuzz_inflate")
        for unit in (bufq, fnmatch, scene, zlib):
            self.write(self.unit(unit, 0))
        self.commit("four units with a record")
        rc, out, calls = self.step([scene, fnmatch], proofs=[zlib, scene, bufq])
        self.assertEqual((rc, calls), (0, [self.check_call(fnmatch), self.check_call(scene), self.check_call(bufq),
                                           self.check_call(zlib)]), out)
        for unit, why in ((fnmatch, self.STRICT), (scene, self.STRICT), (bufq, self.PROOFS_ONLY),
                          (zlib, self.PROOFS_ONLY)):
            with self.subTest(unit=unit):
                self.assertRegex(out, r"(?m)^%s: .* --check exited 0 in [0-9]+ s \(%s\)$"
                                 % (re.escape(unit), re.escape(why)))

    def test_a_contributor_s_change_runs_no_code_of_either_kind(self):
        strict, only = "projects/curl/fuzz_fnmatch", "projects/curl/fuzz_bufq"
        self.shared(0)
        self.write(self.unit(strict, 1))
        self.write(self.unit(only, 3))
        self.commit("a contributor's strict unit and proofs-only unit")
        rc, out, calls = self.step([strict], kind="contributor", proofs=[only])
        self.assertEqual((rc, calls), (0, []), out)
        self.assertIn("KIND=contributor: this job runs no code of the change", out)
        self.assertNotIn("::error::", out)
        self.assertNotIn("::warning::", out)

    def test_a_proofs_list_or_a_hold_it_cannot_read_fails_before_any_code_of_the_change(self):
        """PROOFS must be a JSON list of projects/<p>/<h>, as UNITS must, and HOLD one of none, draft and label.  Any
        other value fails the step, and no --unit-file and no --check runs."""
        unit = "projects/curl/fuzz_bufq"
        self.shared(0)
        self.write(self.unit(unit, 0))
        self.commit("a unit with a record")
        not_a_list = "::error::the plan named the units '%s' in PROOFS, which is not a JSON list of units"
        for name, env, said in (
                ("PROOFS empty", {"PROOFS": ""}, not_a_list % ""),
                ("PROOFS a unit, not a list", {"PROOFS": unit}, not_a_list % unit),
                ("PROOFS a JSON object", {"PROOFS": '{"%s": 1}' % unit}, not_a_list % ('{"%s": 1}' % unit)),
                ("PROOFS a list of numbers", {"PROOFS": "[1]"}, not_a_list % "[1]"),
                ("PROOFS a name that is not a unit", {"PROOFS": '["projects/curl"]'},
                 "::error::the plan named the unit projects/curl, which is not projects/<p>/<h>"),
                ("HOLD empty", {"HOLD": ""}, "::error::the plan answered hold '', none of none, draft and label"),
                ("HOLD another word", {"HOLD": "false"},
                 "::error::the plan answered hold 'false', none of none, draft and label")):
            with self.subTest(case=name):
                self.clear_log()
                rc, out, calls = self.step([unit], proofs=[unit], env=env)
                self.assertEqual((rc, calls), (1, []), out)
                self.assertIn(said, out.splitlines())

    def test_a_proofs_only_unit_whose_record_has_no_generator_fails_as_a_strict_one_does(self):
        unit = "projects/curl/fuzz_bufq"
        self.shared(0)
        self.write({self.record(unit): "row\n"})
        self.commit("a record with no generator")
        for units, proofs in (([unit], []), ([], [unit])):
            with self.subTest(strict=bool(units)):
                self.clear_log()
                rc, out, calls = self.step(units, proofs=proofs)
                self.assertEqual((rc, calls), (1, []), out)
                [error] = [line for line in out.splitlines() if line.startswith("::error::")]
                self.assertTrue(error.startswith(self.no_generator(unit)), out)

    def test_a_listed_unit_with_neither_a_generator_nor_a_record_passes_with_a_line(self):
        self.write({"projects/curl/fuzz_x/proofs/provenance/notes.txt": "n\n"})
        self.commit("provenance with no generator")
        rc, out, calls = self.step(["projects/curl/fuzz_x"])
        self.assertEqual((rc, calls), (0, []), out)
        self.assertIn("projects/curl/fuzz_x: no made_from.py and no made-from.tsv", out)

    def test_a_record_whose_generator_is_gone_fails_and_runs_nothing(self):
        """Deleting made_from.py must not turn the check off: the record is still there and nothing can check it."""
        self.shared(0)
        self.write({"projects/curl/fuzz_bufq/proofs/provenance/evidence/licence/made-from.tsv": "forged\n"})
        self.commit("a record with no generator")
        rc, out, calls = self.step(["projects/curl/fuzz_bufq"])
        self.assertEqual((rc, calls), (1, []), out)
        [error] = [line for line in out.splitlines() if line.startswith("::error::")]
        self.assertTrue(error.startswith(self.no_generator("projects/curl/fuzz_bufq")), out)

    def test_a_generator_whose_record_is_gone_fails_and_runs_nothing(self):
        """Deleting made-from.tsv must not stop the check, whatever the generator's --check gives with no record to
        compare: the stand-in gives exit 2, which the job only warns on (dev/licence/made_from.py refuses a missing
        record with exit 4).  With its record the unit passes.  Without it the unit fails, and no code of the change
        runs: no --check, and no --unit-file of the shared generator."""
        unit = "projects/curl/fuzz_bufq"
        for shared in (False, True):
            with self.subTest(shared_generator=shared):
                self.write(self.unit(unit, 0))
                if shared:
                    self.shared(0)
                self.commit("a record and its generator")
                self.clear_log()
                rc, out, calls = self.step([unit])
                self.assertEqual((rc, calls), (0, ([self.unit_file_call(unit)] if shared else [])
                                               + [self.check_call(unit)]), out)
                self.write(dict(self.generator(unit, 2), **{self.record(unit): None}))
                self.commit("the record deleted, its generator kept")
                self.clear_log()
                rc, out, calls = self.step([unit])
                self.assertEqual((rc, calls), (1, []), out)
                [error] = [line for line in out.splitlines() if line.startswith("::error::")]
                self.assertTrue(error.startswith(self.no_record(unit)), out)

    def test_a_generator_and_a_record_in_two_directories_fail_and_run_nothing(self):
        """A made_from.py finds its unit's top from its own place and reads the record at evidence/licence/made-from.tsv
        below it (Layout.record of dev/licence/made_from.py), so a made-from.tsv in another directory of
        proofs/provenance/ is no record that a made_from.py reads.  A change that moves the record to another directory,
        or moves the generator away from it, leaves --check no record to compare.  A generator whose --check gave exit
        2 for that would only warn, and the stand-in gives exit 2 here, as curl/fuzz_fnmatch's own made_from.py did
        (record or generator moved to proofs/provenance/old/: `cannot decide: missing ...made-from.tsv`, exit 2, step
        exit 0, measured in OSSV-604).  dev/licence/made_from.py refuses a missing record with exit 4, and a unit file
        outside evidence/licence/ with exit 4 too.  That is the deleted record of the test above, and the unit fails as
        it does there, with an error that names the unit, and no code of the change runs."""
        unit = "projects/curl/fuzz_bufq"
        licence = "%s/%s" % (unit, os.path.dirname(self.EVIDENCE))
        other = "%s/proofs/provenance/old" % unit
        for name, change in (
                ("the record moved", {self.record(unit): None, other + "/made-from.tsv": "row\n"}),
                ("the generator moved", {licence + "/made_from.py": None, licence + "/rc": None,
                                         other + "/made_from.py": FAKE_MADE_FROM, other + "/rc": "2\n"})):
            with self.subTest(case=name):
                self.write(self.unit(unit, 2))
                for path in (other + "/made-from.tsv", other + "/made_from.py", other + "/rc"):
                    if os.path.exists(os.path.join(self.head, path)):
                        self.write({path: None})
                self.commit("a record and its generator in one directory")
                self.write(change)
                self.commit(name)
                self.clear_log()
                rc, out, calls = self.step([unit])
                self.assertEqual((rc, calls), (1, []), out)
                self.assertIn("::error::%s " % unit, out)
                self.assertNotIn("::warning::", out)

    def test_a_pair_moved_together_out_of_evidence_licence_fails_and_runs_nothing(self):
        """A made_from.py and its made-from.tsv that a change moves together still sit in one directory.  But the moved
        made_from.py reads no record there: measured on the real surface (OSSV-604), a unit's own made_from.py said
        `cannot decide: missing ...made-from.tsv` and exited 2 (which the stand-in gives here), so the step would warn
        and pass; dev/licence/made_from.py refuses a unit file at any path but evidence/licence/made_from.py with exit
        4.  The whole pair at evidence/licence/ passes first.  After the move the unit fails, each error names the unit
        and a moved file, and no code of the change runs: no --check, and no --unit-file of the shared generator
        either."""
        unit = "projects/curl/fuzz_bufq"
        licence = "%s/%s" % (unit, os.path.dirname(self.EVIDENCE))
        for shared in (False, True):
            for to in ("proofs/provenance/old", "proofs/provenance/evidence/other"):
                with self.subTest(shared_generator=shared, moved_to=to):
                    shutil.rmtree(os.path.join(self.head, unit), ignore_errors=True)
                    if shared:
                        self.shared(0)
                    self.write(self.unit(unit, 0))
                    self.commit("a record and its generator at evidence/licence/")
                    self.clear_log()
                    rc, out, calls = self.step([unit])
                    self.assertEqual((rc, calls), (0, ([self.unit_file_call(unit)] if shared else [])
                                                   + [self.check_call(unit)]), out)
                    moved = "%s/%s" % (unit, to)
                    self.write({licence + "/made_from.py": None, licence + "/rc": None, self.record(unit): None,
                                moved + "/made_from.py": FAKE_MADE_FROM, moved + "/rc": "2\n",
                                moved + "/made-from.tsv": "row\n"})
                    self.commit("the record and its generator moved together to " + to)
                    self.clear_log()
                    rc, out, calls = self.step([unit])
                    self.assertEqual((rc, calls), (1, []), out)
                    self.assert_refused_outside(out, unit, to)

    def test_a_second_pair_in_another_directory_fails_and_runs_nothing(self):
        """A unit has one place for its pair, evidence/licence/.  A second made_from.py and made-from.tsv in
        proofs/provenance/old/, beside the whole pair at evidence/licence/, fail the unit.  The errors name both files
        of old/, and no code of the change runs: no --unit-file and no --check, also not for the whole pair."""
        unit = "projects/curl/fuzz_bufq"
        other = "proofs/provenance/old"
        self.shared(0)
        self.write(dict(self.unit(unit, 0), **{"%s/%s/%s" % (unit, other, name): text for name, text in
                                               (("made_from.py", FAKE_MADE_FROM), ("rc", "0\n"),
                                                ("made-from.tsv", "row\n"))}))
        self.commit("a record and its generator at evidence/licence/, and a second pair in old/")
        rc, out, calls = self.step([unit])
        self.assertEqual((rc, calls), (1, []), out)
        self.assert_refused_outside(out, unit, other)

    def test_a_whole_pair_and_a_lone_record_in_another_directory_fail_and_run_nothing(self):
        """One made-from.tsv outside evidence/licence/ refuses the whole unit.  The error names that file, and no code
        of the change runs: no --unit-file and no --check, also not for the unit's whole pair."""
        unit = "projects/curl/fuzz_bufq"
        lone = "proofs/provenance/old/made-from.tsv"
        self.shared(0)
        self.write(dict(self.unit(unit, 0), **{"%s/%s" % (unit, lone): "row\n"}))
        self.commit("a record and its generator, and a record with no generator in another directory")
        rc, out, calls = self.step([unit])
        self.assertEqual((rc, calls), (1, []), out)
        [error] = [line for line in out.splitlines() if line.startswith("::error::")]
        self.assertTrue(error.startswith(self.no_outside(unit, lone)), out)
        self.assertNotIn("::warning::", out)

    def test_the_name_of_a_refused_file_cannot_start_a_line_of_its_own(self):
        """The error names the file through escape(): a new line in the name becomes %0A, and a % becomes %25.  So the
        name cannot write a workflow command of its own.  Lint refuses such a name, but this error line is outside the
        output guard."""
        unit = "projects/curl/fuzz_bufq"
        self.write(dict(self.unit(unit, 0),
                        **{unit + "/proofs/provenance/x%0A\n::error::forged/made-from.tsv": "row\n"}))
        self.commit("a record outside evidence/licence/, in a directory whose name holds a new line")
        rc, out, calls = self.step([unit])
        self.assertEqual((rc, calls), (1, []), out)
        [error] = [line for line in out.splitlines() if line.startswith("::error::")]
        self.assertTrue(error.startswith(self.no_outside(
            unit, "proofs/provenance/x%250A%0A::error::forged/made-from.tsv")), out)

    def test_every_refusal_comes_before_any_check_and_a_whole_unit_is_still_checked(self):
        """The step decides both refusals for every listed unit before it runs any code of the change.  So the
        refusal of the second unit is in the log before the --check of the first, that --check still runs, and the
        step fails."""
        whole, refused = "projects/curl/fuzz_bufq", "projects/curl/fuzz_fnmatch"
        self.write(self.unit(whole, 0))
        self.write(self.generator(refused, 2))
        self.commit("a unit with both files, and a unit with a generator and no record")
        rc, out, calls = self.step([whole, refused])
        self.assertEqual((rc, calls), (1, [self.check_call(whole)]), out)
        self.assertIn(self.no_record(refused), out)
        self.assertLess(out.index(self.no_record(refused)), out.index("checking %s/%s\n" % (whole, self.EVIDENCE)),
                        out)
        self.assertIn("%s/%s --check: the record matches its generator" % (whole, self.EVIDENCE), out)

    def test_a_listed_unit_that_is_gone_passes(self):
        """A unit deleted whole has neither file, so nothing is left to check."""
        rc, out, calls = self.step(["projects/curl/fuzz_gone"])
        self.assertEqual((rc, calls), (0, []), out)

    def test_the_generator_runs_under_an_1800_s_time_out_and_a_time_out_fails(self):
        """`timeout 1800` fails closed: its 124 has a message of its own, and the step fails on it."""
        self.assertIn('timeout 1800 python3 "$rel" --check', step(self.job(), MADE_FROM_STEP)["run"])
        self.write(self.unit("projects/curl/fuzz_bufq", 124))
        self.commit("a generator that does not finish")
        rc, out, _calls = self.step(["projects/curl/fuzz_bufq"])
        self.assertEqual(rc, 1, out)
        self.assertIn("::error::projects/curl/fuzz_bufq/%s --check did not finish within 1,800 s" % self.EVIDENCE, out)

    def test_a_contributor_s_change_runs_no_code_of_it(self):
        """No --unit-file, no --check and no tests for an outside contributor's change, whose code runs only in the
        tests job; the record is left unchecked.  A maintainer's change and a release run them."""
        self.shared(0)
        self.write(self.unit("projects/curl/fuzz_bufq", 1))
        self.write({"dev/licence/test_licence.py": licence_test("pass")})
        self.commit("a contributor's record")
        rc, out, calls = self.step(["projects/curl/fuzz_bufq"], kind="contributor")
        self.assertEqual((rc, calls), (0, []), out)
        self.assertIn("KIND=contributor: this job runs no code of the change", out)
        self.assertNotIn("::error::", out)
        rc, out, calls = self.licence_step(kind="contributor")
        self.assertEqual((rc, calls), (0, []), out)
        for kind in ("maintainer", "release"):
            with self.subTest(kind=kind):
                self.clear_log()
                rc, out, calls = self.step(["projects/curl/fuzz_bufq"], kind=kind)
                self.assertEqual((rc, calls), (1, [self.unit_file_call("projects/curl/fuzz_bufq"),
                                                   self.check_call("projects/curl/fuzz_bufq")]), out)
                self.clear_log()
                rc, out, calls = self.licence_step(kind=kind)
                self.assertEqual((rc, calls), (0, ["imported test_licence"]), out)

    def test_a_contributor_s_record_still_needs_its_generator(self):
        self.write({"projects/curl/fuzz_bufq/proofs/provenance/evidence/licence/made-from.tsv": "row\n"})
        self.commit("a record with no generator")
        rc, out, calls = self.step(["projects/curl/fuzz_bufq"], kind="contributor")
        self.assertEqual((rc, calls), (1, []), out)
        self.assertIn(self.no_generator("projects/curl/fuzz_bufq"), out)

    def test_a_contributor_s_generator_still_needs_its_record(self):
        """The refusal opens no file of the change, so it holds for an outside contributor too, and nothing of the
        change runs."""
        self.shared(0)
        self.write(self.generator("projects/curl/fuzz_bufq", 2))
        self.write({"dev/licence/test_licence.py": licence_test("pass")})
        self.commit("a contributor's generator with no record")
        rc, out, calls = self.step(["projects/curl/fuzz_bufq"], kind="contributor")
        self.assertEqual((rc, calls), (1, []), out)
        self.assertIn(self.no_record("projects/curl/fuzz_bufq"), out)
        rc, out, calls = self.licence_step(kind="contributor")
        self.assertEqual((rc, calls), (0, []), out)

    def test_a_contributor_s_pair_outside_evidence_licence_still_fails(self):
        """The rule compares paths alone, so it holds for an outside contributor too, and nothing of the change
        runs."""
        unit = "projects/curl/fuzz_bufq"
        other = "proofs/provenance/old"
        self.write({"%s/%s/%s" % (unit, other, name): text for name, text in
                    (("made_from.py", FAKE_MADE_FROM), ("rc", "2\n"), ("made-from.tsv", "row\n"))})
        self.commit("a contributor's record and generator in old/")
        rc, out, calls = self.step([unit], kind="contributor")
        self.assertEqual((rc, calls), (1, []), out)
        self.assert_refused_outside(out, unit, other)

    def test_what_the_change_s_code_writes_cannot_emit_a_workflow_command(self):
        """What --unit-file, --check and the tests write, on stdout and stderr alike, is printed between
        ::stop-commands:: and a token of that block's own, so the runner acts on no workflow command of theirs."""
        d = "projects/curl/fuzz_bufq/" + os.path.dirname(self.EVIDENCE)
        forge = ("import sys\nprint('::error::forged on stdout by %s')\n"
                 "sys.stderr.write('::set-output name=x::forged on stderr by %s\\n')\n")
        self.write({d + "/made_from.py": forge % ("--check", "--check"), d + "/made-from.tsv": "row\n",
                    "dev/licence/made_from.py": forge % ("--unit-file", "--unit-file"),
                    "dev/licence/test_forged.py": "import unittest\n" + forge % ("a test", "a test")
                                                  + "class T(unittest.TestCase):\n    def test_it(self):\n"
                                                    "        pass\n"})
        self.commit("generators and a test that print workflow commands")
        rc, out, _calls = self.step(["projects/curl/fuzz_bufq"])
        self.assertEqual(rc, 0, out)
        rc, tests_out, _calls = self.licence_step()
        self.assertEqual(rc, 0, tests_out)
        blocks, outside = stop_command_blocks(self, out + tests_out)
        for who in ("--unit-file", "--check", "a test"):
            with self.subTest(who=who):
                # python's stdout is a buffered pipe here and its stderr is not, so the two reach a block in either
                # order
                self.assertEqual(len([text for _token, text in blocks
                                      if "::error::forged on stdout by %s\n" % who in text
                                      and "::set-output name=x::forged on stderr by %s\n" % who in text]), 1,
                                 out + tests_out)
        self.assertNotIn("forged", outside)
        # each block, and each run, picks a token of its own
        again, _outside = stop_command_blocks(self, self.step(["projects/curl/fuzz_bufq"])[1])
        tokens = [token for token, _text in blocks + again]
        self.assertEqual(len(set(tokens)), len(tokens), tokens)

    def test_the_change_s_code_runs_with_no_command_file_of_the_runner(self):
        """--unit-file, --check and the tests run with none of the five command files in their environment, as the
        plan job runs the change's code.  The steps' own environment names all five, each an empty file under the
        scratch directory, and each file stays empty."""
        d = "projects/curl/fuzz_bufq/" + os.path.dirname(self.EVIDENCE)
        self.write({d + "/made_from.py": sees_command_files("--check"), d + "/made-from.tsv": "row\n",
                    "dev/licence/made_from.py": sees_command_files("--unit-file"),
                    "dev/licence/test_sees.py": sees_command_files("a test") + "import unittest\n"
                                                "class T(unittest.TestCase):\n    def test_it(self):\n        pass\n"})
        self.commit("generators and a test that look for the runner's command files")
        # run_step names GITHUB_OUTPUT and GITHUB_STEP_SUMMARY itself, and gives back and deletes the summary
        files = {"GITHUB_OUTPUT": self.output, "GITHUB_STEP_SUMMARY": os.path.join(self.dir, "summary")}
        env = {name: os.path.join(self.dir, name.lower()) for name in ("GITHUB_ENV", "GITHUB_PATH", "GITHUB_STATE")}
        files.update(env)
        self.assertEqual(sorted(files), sorted(COMMAND_FILES))
        for name, run, want in (
                ("the records step", lambda: self.step(["projects/curl/fuzz_bufq"], env=env),
                 ["--unit-file sees none", "--check sees none"]),
                ("the tests step", lambda: self.licence_step(env=env), ["a test sees none"])):
            with self.subTest(step=name):
                for path in files.values():
                    open(path, "w").close()
                self.clear_log()
                rc, out, calls = run()
                self.assertEqual((rc, calls), (0, want), out)
                written = {"GITHUB_STEP_SUMMARY": self.summary}
                for var in ("GITHUB_OUTPUT",) + tuple(env):
                    with open(files[var]) as f:
                        written[var] = f.read()
                self.assertEqual(written, dict.fromkeys(COMMAND_FILES, ""), out)

    def test_two_units_each_run_in_order_and_one_failure_fails(self):
        self.write(self.unit("projects/curl/fuzz_bufq", 0))
        self.write(self.unit("projects/curl/fuzz_fnmatch", 1))
        self.commit("two records")
        rc, out, calls = self.step(["projects/curl/fuzz_bufq", "projects/curl/fuzz_fnmatch"])
        self.assertEqual(rc, 1, out)
        self.assertEqual(calls, [self.check_call("projects/curl/fuzz_bufq"),
                                 self.check_call("projects/curl/fuzz_fnmatch")])
        self.assertIn("::error::projects/curl/fuzz_fnmatch/", out)
        self.assertNotIn("::error::projects/curl/fuzz_bufq/", out)

    def test_the_log_names_each_unit_with_its_exit_and_seconds(self):
        for unit in ("projects/curl/fuzz_bufq", "projects/libreac/fuzz_scene"):
            self.write(self.unit(unit, 0))
        self.commit("two records")
        rc, out, _calls = self.step(["projects/curl/fuzz_bufq", "projects/libreac/fuzz_scene"])
        self.assertEqual(rc, 0, out)
        for unit in ("projects/curl/fuzz_bufq", "projects/libreac/fuzz_scene"):
            with self.subTest(unit=unit):
                self.assertRegex(out, r"(?m)^%s: %s/%s --check exited 0 in [0-9]+ s \(%s\)$"
                                 % (re.escape(unit), re.escape(unit), re.escape(self.EVIDENCE),
                                    re.escape(self.STRICT)))

    def test_a_change_to_a_unit_s_record_alone_runs_its_generator(self):
        """The plan names the unit from its record alone, and the job finds the generator in the unit's tree."""
        self.write(self.unit("projects/curl/fuzz_bufq", 0))
        self.base = self.commit("the generator")
        self.write({"projects/curl/fuzz_bufq/proofs/provenance/evidence/licence/made-from.tsv": "edited\n"})
        self.commit("an edit to the record")
        rc, out, outputs = self.reach()
        self.assertEqual((rc, outputs["made_from"], outputs["made_from_proofs"]), (0, "true", "[]"), out)
        rc, out, calls = self.step(json.loads(outputs["made_from_units"]),
                                   proofs=json.loads(outputs["made_from_proofs"]))
        self.assertEqual((rc, calls), (0, [self.check_call("projects/curl/fuzz_bufq")]), out)

    def test_from_the_plan_s_answer_exit_3_warns_for_a_unit_s_proofs_alone_and_fails_otherwise(self):
        """Through the reach step's block and then the records step, with each unit's --check giving exit 3.  A change
        to a unit's proofs/lib/ alone runs that unit's --check and no other unit's, and only warns.  The same change
        with the unit's proofs/provenance/ changed too fails.  So do a change to dev/licence/, which runs every unit
        with a record, and a change to the unit's images/dune alone."""
        bufq, fnmatch = "projects/curl/fuzz_bufq", "projects/curl/fuzz_fnmatch"
        for unit in (bufq, fnmatch):
            self.write(dict(self.unit(unit, 3), **{unit + "/proofs/lib/Proof.v": "(* a proof *)\n"}))
        fixture = self.commit("two units whose --check gives exit 3")
        lib = {bufq + "/proofs/lib/Proof.v": "(* another *)\n"}
        for name, change, failed, units in (
                ("its proofs/lib/ alone", lib, False, [bufq]),
                ("its proofs/lib/ and its proofs/provenance/", dict(lib, **{self.record(bufq): "edited\n"}), True,
                 [bufq]),
                ("dev/licence/", {"dev/licence/README": "r\n"}, True, [bufq, fnmatch]),
                ("its images/dune alone", {bufq + "/images/dune": "(rule)\n"}, True, [bufq])):
            with self.subTest(change=name):
                git(self.head, "reset", "-q", "--hard", fixture)
                git(self.head, "clean", "-qfdx")
                self.base = fixture
                self.write(change)
                self.commit(name)
                rc, out, outputs = self.reach()
                self.assertEqual(rc, 0, out)
                self.clear_log()
                rc, out, calls = self.step(json.loads(outputs["made_from_units"]),
                                           proofs=json.loads(outputs["made_from_proofs"]))
                self.assertEqual((rc, calls), (int(failed), [self.check_call(unit) for unit in units]), out)
                lines = out.splitlines()
                errors = [line for line in lines if line.startswith("::error::")]
                warnings = [line for line in lines if line.startswith("::warning::")]
                if failed:
                    self.assertEqual((len(errors), warnings), (len(units), []), out)
                    for unit in units:
                        self.assertIn("::error::%s/%s --check exited 3: the rows that a run gives again differ from "
                                      "the record" % (unit, self.EVIDENCE), out)
                else:
                    self.assertEqual((errors, len(warnings)), ([], 1), out)
                    self.assertTrue(warnings[0].startswith("::warning::%s: its made-from record is not up to date"
                                                           % bufq), out)

    def test_the_shared_generator_s_unit_file_check_runs_first_and_a_refused_file_is_not_run(self):
        """dev/licence/made_from.py --unit-file, from the top of the checkout with the path from that top, on each
        made_from.py before its --check.  Any exit but 0 fails the job and leaves that file's --check uncalled.  Exit 4
        (a refused file) and exit 2 (an argparse error) show the reason: a refused file is not data alone.  Exit 124,
        from `timeout 60`, says that the call did not finish within 60 s."""
        self.assertIn('timeout 60 python3 dev/licence/made_from.py --unit-file "$rel"',
                      step(self.job(), MADE_FROM_STEP)["run"])
        units = ["projects/curl/fuzz_bufq", "projects/curl/fuzz_fnmatch"]
        for unit in units:
            self.write(self.unit(unit, 0))
        self.shared(0)
        self.commit("two units and the shared generator")
        rc, out, calls = self.step(units)
        self.assertEqual((rc, calls), (0, [self.unit_file_call(units[0]), self.check_call(units[0]),
                                           self.unit_file_call(units[1]), self.check_call(units[1])]), out)
        for code in (4, 2, 124):
            with self.subTest(exit=code):
                self.clear_log()
                self.shared(code)
                rc, out, calls = self.step(units)
                self.assertEqual((rc, calls), (1, [self.unit_file_call(units[0]), self.unit_file_call(units[1])]),
                                 out)
                self.assertIn("%s/%s: a statement that is not data" % (units[0], self.EVIDENCE), out)
                if code == 124:
                    self.assertIn("::error::dev/licence/made_from.py --unit-file %s/%s did not finish within 60 s"
                                  % (units[0], self.EVIDENCE), out)
                    self.assertNotIn("does not accept", out)
                else:
                    self.assertIn("::error::dev/licence/made_from.py --unit-file %s/%s exited %d"
                                  % (units[0], self.EVIDENCE, code), out)

    def test_with_no_shared_generator_no_unit_file_check_runs(self):
        self.write(self.unit("projects/curl/fuzz_bufq", 0))
        self.commit("a unit, and no dev/licence/")
        rc, out, calls = self.step(["projects/curl/fuzz_bufq"])
        self.assertEqual((rc, calls), (0, [self.check_call("projects/curl/fuzz_bufq")]), out)
        self.assertNotIn("--unit-file", out)

    def test_a_credential_in_the_checkout_fails_the_job_before_any_of_the_change_s_code(self):
        """actions/checkout leaves the token in head/.git/config as an http extraheader unless told not to: with one
        there, neither step runs a file of the change, and neither prints the header."""
        self.shared(0)
        self.write(self.unit("projects/curl/fuzz_bufq", 0))
        self.write({"dev/licence/test_licence.py": licence_test("pass")})
        self.commit("a record")
        git(self.head, "config", "http.https://github.com/.extraheader", "AUTHORIZATION: basic s3cret")
        rc, out, calls = self.step(["projects/curl/fuzz_bufq"])
        self.assertEqual((rc, calls), (1, []), out)
        self.assertIn("::error::head/.git/config holds an http extraheader", out)
        self.assertNotIn("s3cret", out)
        rc, out, calls = self.licence_step()
        self.assertEqual((rc, calls), (1, []), out)
        self.assertIn("::error::head/.git/config holds an http extraheader", out)

    def test_the_tests_of_dev_licence_run_when_every_unit_is_checked_and_any_exit_but_0_fails(self):
        """A passing module passes; a failing one, an empty test set (exit 5: no test ran) and one that ends the
        process with 124 (what `timeout 900` gives) fail, the last with the time-out's own message."""
        self.shared(0)
        for name, files, want, said in (
                ("a passing test", {"test_ok.py": licence_test("pass")}, 0, "the tests of dev/licence/ passed"),
                ("a failing test", {"test_bad.py": licence_test("self.fail('no')")}, 1,
                 "::error::the tests of dev/licence/ exited 1"),
                ("no test", {}, 1, "::error::the tests of dev/licence/ exited 5: no test ran"),
                ("a time-out", {"test_slow.py": "import os\nos._exit(124)\n"}, 1,
                 "::error::the tests of dev/licence/ did not finish within 900 s")):
            with self.subTest(case=name):
                for old in self.licence_tests():
                    os.remove(old)
                self.write({"dev/licence/" + rel: text for rel, text in files.items()})
                rc, out, _calls = self.licence_step()
                self.assertEqual(rc, want, out)
                self.assertIn(said, out)

    def test_the_tests_of_dev_licence_run_nothing_otherwise_and_say_so_in_one_line(self):
        """Not when the plan named only the units whose records changed, not for an outside contributor, and not on a
        tree with no dev/licence/made_from.py."""
        self.write({"dev/licence/test_licence.py": licence_test("pass")})
        self.commit("tests of dev/licence/ and no generator")
        for name, every, kind in (("only some units", "false", "maintainer"), ("no generator", "true", "maintainer")):
            with self.subTest(case=name):
                rc, out, calls = self.licence_step(every=every, kind=kind)
                self.assertEqual((rc, calls, len(out.splitlines())), (0, [], 1), out)
        self.shared(0)
        for name, every, kind in (("only some units", "false", "maintainer"), ("a contributor", "true", "contributor")):
            with self.subTest(case=name, generator=True):
                rc, out, calls = self.licence_step(every=every, kind=kind)
                self.assertEqual((rc, calls, len(out.splitlines())), (0, [], 1), out)

    def test_the_job_runs_on_16_cores_with_the_whole_tree_after_lint(self):
        """The whole tree, as the tests job's whole-tree arm takes it: one checkout of head/ that keeps no token,
        with no sparse set and no filter, so no proof is left out.  No step's failure can be ignored."""
        job = self.job()
        self.assertEqual((job["runs-on"], job["timeout-minutes"], job["needs"]),
                         ("ubuntu-24.04-16core", 120, ["plan", "lint"]))
        checkouts = [s for s in job["steps"] if s.get("uses", "").startswith("actions/checkout@")]
        self.assertEqual(len(checkouts), 1, checkouts)
        self.assertEqual(checkouts[0]["with"], {"path": "head", "persist-credentials": False})
        pythons = [s for s in job["steps"] if s.get("uses", "").startswith("actions/setup-python@")]
        self.assertEqual([s["with"] for s in pythons], [{"python-version": "3.12"}])
        self.assertEqual([s for s in job["steps"] if "continue-on-error" in s], [])

    def test_the_job_runs_only_when_the_plan_named_a_unit_and_lint_passed(self):
        """Its `if:` as GitHub evaluates it, after lint passed: on made_from `true`, or on a made_from_proofs that is
        not [] when the plan's hold is none, and on nothing else.  checked_elsewhere changes nothing.  A draft and a
        push the merge queue checked skip lint, and so skip this job."""
        from oft.tests.test_facts_review_gate import evaluate

        def runs(plan="success", lint="success", answer="true", proofs="[]", hold="none", elsewhere="false",
                 cancelled=False):
            outputs = {"made_from": answer, "made_from_proofs": proofs, "hold": hold, "checked_elsewhere": elsewhere}
            needs = {"plan": {"result": plan, "outputs": outputs if plan == "success" else {}},
                     "lint": {"result": lint, "outputs": {}}}
            return evaluate(self.job().get("if", "success()"), needs, cancelled)
        for answer in ("true", "false"):
            for proofs in ("[]", '["projects/curl/fuzz_bufq"]'):
                for hold in ("none", "label", "draft"):
                    want = answer == "true" or (proofs != "[]" and hold == "none")
                    for elsewhere in ("true", "false"):
                        with self.subTest(made_from=answer, made_from_proofs=proofs, hold=hold, elsewhere=elsewhere):
                            self.assertEqual(runs(answer=answer, proofs=proofs, hold=hold, elsewhere=elsewhere), want)
        for name, kw in (("the answer false", dict(answer="false")), ("lint skipped", dict(lint="skipped")),
                         ("lint failed", dict(lint="failure")),
                         ("the plan failed", dict(plan="failure", lint="skipped")),
                         ("cancelled", dict(cancelled=True)),
                         ("a list of proofs, lint skipped", dict(answer="false", proofs='["x/y/z"]', lint="skipped"))):
            with self.subTest(case=name):
                self.assertFalse(runs(**kw))

    def test_lint_runs_no_made_from_check(self):
        """No step of lint names made_from.py or made-from.tsv, but the strip check.  That step writes the rules of a
        made_from.py again and asks git whether a unit has a made-from.tsv.  It runs no file of the change:
        StripStepTest runs it on units that have no made_from.py."""
        for s in load("pr.yml")["jobs"]["lint"]["steps"]:
            if s.get("name") == STRIP_STEP:
                continue
            with self.subTest(step=s.get("name", s.get("uses"))):
                self.assertNotIn("made_from.py", s.get("run", ""))
                self.assertNotIn("made-from.tsv", s.get("run", ""))

    def test_required_needs_every_job_whose_result_or_outputs_it_reads(self):
        """GitHub gives a job needs.<job> of its direct needs alone, so a step of required that reads another job's
        result or outputs fails in every run."""
        job = load("pr.yml")["jobs"]["required"]
        read = set()
        for s in job["steps"]:
            text = json.dumps([s.get("if", ""), s.get("env") or {}, s.get("run", "")])
            read |= set(re.findall(r"\bneeds\.([A-Za-z0-9_-]+)\.", text))
        self.assertIn("made_from", read)
        self.assertEqual(sorted(read - set(job["needs"])), [])


class MadeFromReachTest(MadeFromRepo):
    """The reach step's made-from block, the plan's answers for the made_from job.  made_from_units: the units under
    whose proofs/provenance/ the change touches a path, or whose images/dune it changes, and that hold a made_from.py
    or a made-from.tsv under proofs/provenance/, or every unit with a made-from.tsv when the change can move every
    record (a path of MADE_FROM_READS, the made_from job, the MADE_FROM_READS line, a path git quotes, a
    .gitattributes, or a run with no base).  made_from_proofs: the units with a made-from.tsv under proofs/provenance/
    under whose proofs/ the change touches a path outside proofs/provenance/.  MADE_FROM_READS is read from pr.yml's
    text, never written here."""

    UNITS = ("projects/curl/fuzz_bufq", "projects/curl/fuzz_fnmatch", "projects/libreac/fuzz_scene")
    # a unit whose provenance tree holds neither file
    BARE = "projects/curl/fuzz_bare"
    NONE = ("false", [], "false", [])
    # the block's one line when it names no unit
    NO_UNIT = ("made_from: no changed path is under the proofs/ of a unit with a made-from record, or under the "
               "proofs/provenance/ of a unit with a generator, or is the images/dune of such a unit, and nothing in "
               "the change can move every record: the job does not run")
    # the start of the line when it names a unit for its proofs alone
    NO_STRICT = ("made_from: no changed path is under the proofs/provenance/ of a unit with a made-from record or "
                 "generator, or is the images/dune of such a unit, and nothing in the change can move every record.")
    # the end of the line when it names a unit for its proofs: the job checks such a unit only when the hold is none
    HELD = "the job checks such a unit that no other reason names only when the plan's hold is none"

    def setUp(self):
        super().setUp()
        files = {WORKFLOW_PATH: self.workflow()}
        for unit in self.UNITS + (self.BARE,):
            files[unit + "/proofs/lib/Proof.v"] = "(* a proof *)\n"
            files.update(self.unit(unit, 0) if unit != self.BARE else
                         {unit + "/proofs/provenance/PROVENANCE.yaml": "p\n"})
        self.write(files)
        self.fixture = self.commit("three units with a record, and one with neither file")

    def words(self):
        """The words of pr.yml's one MADE_FROM_READS line."""
        with open(os.path.join(WORKFLOWS, "pr.yml"), encoding="utf-8") as f:
            lines = re.findall(r"^ +MADE_FROM_READS='([^']*)'$", f.read(), re.M)
        self.assertEqual(len(lines), 1, lines)
        self.assertTrue(lines[0].split(), lines)
        return lines[0]

    def workflow(self, job="ubuntu-24.04-16core", other="ubuntu-24.04", words=None, comment="# the workflow",
                 made_from=True):
        """A pr.yml with a made_from job, another job and the reach step's MADE_FROM_READS line."""
        made_from = "  made_from:\n    runs-on: %s\n" % job if made_from else ""
        return ("%s\njobs:\n%s  other:\n    runs-on: %s\n  plan:\n    steps:\n      - id: reach\n        run: |\n"
                "          MADE_FROM_READS='%s'\n" % (comment, made_from, other,
                                                      self.words() if words is None else words))

    def case(self, files=(), delete=(), base_files=None, routed="true", chmod=()):
        """The block's answer for a change from the fixture: base_files first, as a base of its own (a value None
        deletes that path), then the change writes files, deletes the paths in delete and makes the files in chmod
        executable.  (made_from, made_from_units, made_from_every, made_from_proofs); the block's output is in
        self.said and its one line in self.line.  That line names each unit of both lists, and ends with HELD exactly
        when made_from_proofs names a unit."""
        git(self.head, "reset", "-q", "--hard", self.fixture)
        git(self.head, "clean", "-qfdx")
        self.base = self.fixture
        if base_files is not None:
            for rel, text in base_files.items():
                if text is None:
                    os.remove(os.path.join(self.head, rel))
                else:
                    self.write({rel: text})
            self.base = self.commit("another base")
        self.write(dict(files))
        for rel in delete:
            os.remove(os.path.join(self.head, rel))
        for rel in chmod:
            os.chmod(os.path.join(self.head, rel), 0o755)
        self.commit("the change")
        rc, self.said, outputs = self.reach(routed)
        self.assertEqual(rc, 0, self.said)
        got = (outputs["made_from"], json.loads(outputs["made_from_units"]), outputs["made_from_every"],
               json.loads(outputs["made_from_proofs"]))
        lines = [line for line in self.said.splitlines() if line.startswith("made_from: ")]
        self.assertEqual(len(lines), 1, self.said)
        self.line = lines[0]
        for unit in got[1] + got[3]:
            self.assertIn(unit, self.line)
        self.assertEqual(self.line.endswith(self.HELD), got[3] != [], self.line)
        return got

    def every(self, proofs=()):
        """The answer when the change can move every record, with these units named for their proofs."""
        return ("true", list(self.UNITS), "true", list(proofs))

    def proofs(self, *units):
        """The answer when the change names these units for their proofs alone."""
        return ("false", [], "false", sorted(units))

    def lib(self, unit, name="Proof.v"):
        return "%s/proofs/lib/%s" % (unit, name)

    def test_a_path_of_made_from_reads_runs_every_record_and_a_path_beside_it_none(self):
        """Each word, read from pr.yml: one that ends in / is a directory, and a path under it counts; any other is
        one file, and only that path counts.  A path that only starts like a word counts for nothing.  No unit's
        proofs change, so made_from_proofs is empty."""
        for word in self.words().split():
            at = word + "made_from.py" if word.endswith("/") else word
            beside = word.rstrip("/") + "x" if word.endswith("/") else word + "c"
            with self.subTest(path=at):
                self.assertEqual(self.case({at: "x\n"}), self.every(), self.said)
            with self.subTest(path=beside):
                self.assertEqual(self.case({beside: "x\n"}), self.NONE, self.said)
                self.assertEqual(self.line, self.NO_UNIT)

    def test_a_change_to_the_made_from_job_or_its_line_runs_every_record_and_another_change_to_pr_yml_none(self):
        """The parsed made_from job and the MADE_FROM_READS line of the head's pr.yml against the base's: a change to
        either, a base without the job and a base git cannot show run every record; another job's change and a
        comment's run none."""
        for name, files, base_files, want in (
                ("the job", {WORKFLOW_PATH: self.workflow(job="ubuntu-24.04")}, None, self.every()),
                ("the line", {WORKFLOW_PATH: self.workflow(words=self.words() + " docs/")}, None, self.every()),
                ("a base without the job", {WORKFLOW_PATH: self.workflow()},
                 {WORKFLOW_PATH: self.workflow(made_from=False)}, self.every()),
                ("a base without pr.yml", {WORKFLOW_PATH: self.workflow()}, {WORKFLOW_PATH: None}, self.every()),
                ("another job", {WORKFLOW_PATH: self.workflow(other="ubuntu-24.04-4core")}, None, self.NONE),
                ("a comment", {WORKFLOW_PATH: self.workflow(comment="# the workflow, again")}, None, self.NONE)):
            with self.subTest(case=name):
                self.assertEqual(self.case(files, base_files=base_files), want, self.said)

    def test_a_change_to_a_script_a_job_calls_reaches_what_the_same_change_in_the_job_s_text_reaches(self):
        """pr.yml runs the long run texts of some steps from .github/scripts/pr/ (Dispatch issue OSSV-841): a step's
        whole run: is helpers.SCRIPT_CALL.  For each such script, from this repository's pr.yml and its scripts as the
        base: a change to the script alone gives the answer that the same change made in the job's own text gives
        (the script's text, edited, written in place of each call of it), which is every record for a script of the
        made_from job and none for any other.  The script written back in place of its calls, unchanged, is no change
        to any job, so it runs none."""
        with open(os.path.join(WORKFLOWS, "pr.yml"), encoding="utf-8") as f:
            workflow = f.read()
        scripts = {}
        for match in helpers.SCRIPT_CALL.finditer(workflow):
            with open(os.path.join(REPO, match.group(1)), encoding="utf-8") as f:
                scripts[match.group(1)] = f.read()
        self.assertTrue(scripts, "no step of pr.yml calls a script")
        made_from = {helpers.SCRIPT_CALL.fullmatch(s["run"]).group(1)
                     for s in yamlio.load_file(os.path.join(WORKFLOWS, "pr.yml"))["jobs"]["made_from"]["steps"]
                     if helpers.SCRIPT_CALL.fullmatch(str(s.get("run", "")))}
        self.assertTrue(made_from, "no step of the made_from job calls a script")

        def inline(path, text):
            """pr.yml with each call of the script at path replaced by text, as the `run: |` block it was."""
            def block(m):
                body = "".join(m.group(1) + "  " + line if line.strip() else line
                               for line in text.splitlines(keepends=True))
                return m.group(1) + "run: |\n" + body.removesuffix("\n")
            call = re.compile(r'^( *)run: exec bash --noprofile --norc -eo pipefail "\$GITHUB_WORKSPACE/head/%s"$'
                              % re.escape(path), re.M)
            out, n = call.subn(block, workflow)
            self.assertGreater(n, 0, path)
            return out

        base = dict(scripts, **{WORKFLOW_PATH: workflow})
        for path, text in sorted(scripts.items()):
            edited = text + "# a change\n"
            want = self.every() if path in made_from else self.NONE
            with self.subTest(script=path):
                self.assertEqual(self.case({path: edited}, base_files=base), want, self.said)
                self.assertEqual(self.case({WORKFLOW_PATH: inline(path, edited)}, base_files=base), want, self.said)
                self.assertEqual(self.case({WORKFLOW_PATH: inline(path, text)}, base_files=base), self.NONE, self.said)
                self.assertEqual(self.line, self.NO_UNIT)

    def test_what_can_change_any_file_runs_every_record(self):
        """A path git quotes, which no pattern can read; a .gitattributes, at the top or below it, which changes how
        git checks out any file; and a run with no base to compare with, whose every path counts as changed, so every
        unit with a record is in made_from_proofs too.  A path git quotes names no unit for its proofs, also one under
        a unit's proofs/lib/: only the change's other paths do."""
        quoted = self.lib(self.UNITS[1], 'a"b.v')
        for name, files, routed, proofs in (
                ("a path git quotes", {'docs/a"b.md': "q\n"}, "true", ()),
                ("a path git quotes under a unit's proofs/lib/", {quoted: "q\n"}, "true", ()),
                ("a path git quotes, and a unit's proofs/lib/",
                 {quoted: "q\n", self.lib(self.UNITS[0]): "(* another *)\n"}, "true", self.UNITS[:1]),
                ("a .gitattributes", {".gitattributes": "* text=auto\n"}, "true", ()),
                ("a .gitattributes below the top", {"docs/.gitattributes": "* -text\n"}, "true", ()),
                ("no base to compare with", {"docs/x.md": "x\n"}, "false", self.UNITS)):
            with self.subTest(case=name):
                self.assertEqual(self.case(files, routed=routed), self.every(proofs), self.said)
        self.assertEqual(self.line, "made_from: every unit with a made-from record (no base to route): %s. Proofs "
                                    "outside proofs/provenance/ changed in %s: %s"
                         % (" ".join(self.UNITS), " ".join(self.UNITS), self.HELD))

    def test_a_change_to_one_unit_s_provenance_runs_that_unit_alone(self):
        """A change that deletes one of the two files names the unit too, so the made_from job runs and refuses it
        (MadeFromJobTest).  So does a change that moves both files to another directory under proofs/provenance/.
        No unit's proofs outside proofs/provenance/ change, so made_from_proofs is empty."""
        record = self.UNITS[1] + "/proofs/provenance/evidence/licence/made-from.tsv"
        generator = self.UNITS[1] + "/" + self.EVIDENCE
        old = self.UNITS[1] + "/proofs/provenance/old/"
        named = ("true", [self.UNITS[1]], "false", [])
        for name, files, delete, want in (
                ("its record", {record: "edited\n"}, (), named),
                ("its generator deleted beside its record", {}, (generator,), named),
                ("its record deleted beside its generator", {}, (record,), named),
                ("its generator and its record moved to proofs/provenance/old/",
                 {old + "made_from.py": FAKE_MADE_FROM, old + "made-from.tsv": "row\n"}, (generator, record), named),
                ("a unit with neither file", {self.BARE + "/proofs/provenance/PROVENANCE.yaml": "q\n"}, (),
                 self.NONE)):
            with self.subTest(case=name):
                self.assertEqual(self.case(files, delete), want, self.said)
                if want == named:
                    self.assertEqual(self.line, "made_from: projects/curl/fuzz_fnmatch (a path under its "
                                                "proofs/provenance/ or its images/dune changed)")

    def test_a_change_to_a_unit_s_proofs_outside_provenance_names_it_for_its_proofs(self):
        """Any path under the unit's proofs/ and not under its proofs/provenance/: a file of proofs/lib/ added,
        changed, deleted or changed in mode, a file at the top of proofs/, one in another folder of proofs/, and one
        in a folder whose name starts with provenance.  The unit has a made-from.tsv, so made_from_proofs names it,
        and made_from_units does not."""
        unit = self.UNITS[0]
        for name, files, delete, chmod in (
                ("a file of proofs/lib/ added", {self.lib(unit, "New.v"): "(* new *)\n"}, (), ()),
                ("a file of proofs/lib/ changed", {self.lib(unit): "(* another *)\n"}, (), ()),
                ("a file of proofs/lib/ deleted", {}, (self.lib(unit),), ()),
                ("a file of proofs/lib/ changed in mode", {}, (), (self.lib(unit),)),
                ("a file at the top of proofs/", {unit + "/proofs/Statements.v": "(* s *)\n"}, (), ()),
                ("a file in another folder of proofs/", {unit + "/proofs/extra/Lemma.v": "(* l *)\n"}, (), ()),
                ("a file under proofs/provenance2/", {unit + "/proofs/provenance2/notes.txt": "n\n"}, (), ())):
            with self.subTest(case=name):
                self.assertEqual(self.case(files, delete, chmod=chmod), self.proofs(unit), self.said)
                self.assertEqual(self.line, "%s Proofs outside proofs/provenance/ changed in %s: %s"
                                 % (self.NO_STRICT, unit, self.HELD))

    def test_a_move_names_each_side_that_has_a_record(self):
        """changed.txt lists both sides of a move (the base step's diff has --no-renames).  A move inside one unit
        names it.  A move from one unit with a record to another names both.  A move between a unit with a record
        and one without names the one with a record, from either side."""
        bufq, fnmatch = self.UNITS[:2]
        for name, files, delete, want in (
                ("inside one unit", {self.lib(bufq, "Moved.v"): "(* a proof *)\n"}, (self.lib(bufq),), (bufq,)),
                ("from a unit with a record to another", {self.lib(fnmatch, "Moved.v"): "(* a proof *)\n"},
                 (self.lib(bufq),), (bufq, fnmatch)),
                ("from a unit with a record to one without", {self.lib(self.BARE, "Moved.v"): "(* a proof *)\n"},
                 (self.lib(bufq),), (bufq,)),
                ("from a unit without a record to one with", {self.lib(bufq, "Moved.v"): "(* a proof *)\n"},
                 (self.lib(self.BARE),), (bufq,))):
            with self.subTest(case=name):
                self.assertEqual(self.case(files, delete), self.proofs(*want), self.said)
                self.assertIn("changed in %s: " % " ".join(want), self.line)

    def test_a_change_to_a_unit_s_provenance_and_its_proofs_names_it_in_both_lists(self):
        unit = self.UNITS[1]
        self.assertEqual(self.case({self.record(unit): "edited\n", self.lib(unit): "(* another *)\n"}),
                         ("true", [unit], "false", [unit]), self.said)
        self.assertEqual(self.line, "made_from: %s (a path under its proofs/provenance/ or its images/dune changed). "
                                    "Proofs outside proofs/provenance/ changed in %s: %s" % (unit, unit, self.HELD))

    def test_a_unit_without_a_made_from_tsv_at_the_head_is_not_named_for_its_proofs(self):
        """made_from_proofs needs a made-from.tsv under the unit's proofs/provenance/ in the head tree: not a unit that
        holds only a made_from.py there, not a unit with neither file, and not a unit whose made-from.tsv the change
        deletes.  The last is in made_from_units by the rule for a change under proofs/provenance/, so the made_from
        job refuses it (MadeFromJobTest)."""
        unit = self.UNITS[0]
        changed = {self.lib(unit): "(* another *)\n"}
        for name, files, delete, base_files, want in (
                ("a made_from.py and no made-from.tsv", changed, (), {self.record(unit): None}, self.NONE),
                ("neither file", {self.lib(self.BARE): "(* another *)\n"}, (), None, self.NONE),
                ("its made-from.tsv deleted by the change", changed, (self.record(unit),), None,
                 ("true", [unit], "false", []))):
            with self.subTest(case=name):
                self.assertEqual(self.case(files, delete, base_files=base_files), want, self.said)
                if want == self.NONE:
                    self.assertEqual(self.line, self.NO_UNIT)

    def test_a_unit_s_counterexamples_or_harness_yaml_names_it_in_no_list(self):
        unit = self.UNITS[0]
        for path in (unit + "/counterexamples/c1/Cex.v", unit + "/harness.yaml"):
            with self.subTest(path=path):
                self.assertEqual(self.case({path: "x\n"}), self.NONE, self.said)
                self.assertEqual(self.line, self.NO_UNIT)

    def test_two_units_proofs_in_one_change_are_both_named_in_order(self):
        scene, bufq = self.UNITS[2], self.UNITS[0]
        self.assertEqual(self.case({self.lib(scene): "(* another *)\n", self.lib(bufq): "(* another *)\n"}),
                         self.proofs(bufq, scene), self.said)
        self.assertEqual(self.line, "%s Proofs outside proofs/provenance/ changed in %s %s: %s"
                         % (self.NO_STRICT, bufq, scene, self.HELD))

    def test_a_unit_s_images_dune_names_it_strictly_and_no_other_file_of_images_does(self):
        """The generator reads a unit's images/dune (dev/licence/made_from.py's check() lists it among its inputs), so
        a change to it names the unit in made_from_units, as a change under its proofs/provenance/ does, when the unit
        holds a made_from.py or a made-from.tsv there, and not in made_from_proofs.  A unit with neither file is not
        named.  Another file of images/, and a dune file below images/, name no unit."""
        unit = self.UNITS[0]
        dune = unit + "/images/dune"
        named = ("true", [unit], "false", [])
        for name, files, delete, base_files, want in (
                ("its images/dune added", {dune: "(rule)\n"}, (), None, named),
                ("its images/dune changed", {dune: "(rule 2)\n"}, (), {dune: "(rule)\n"}, named),
                ("its images/dune deleted", {}, (dune,), {dune: "(rule)\n"}, named),
                ("the images/dune of a unit with neither file", {self.BARE + "/images/dune": "(rule)\n"}, (), None,
                 self.NONE),
                ("another file of images/", {unit + "/images/README.md": "r\n"}, (), None, self.NONE),
                ("a dune file below images/", {unit + "/images/elf/dune": "(rule)\n"}, (), None, self.NONE)):
            with self.subTest(case=name):
                self.assertEqual(self.case(files, delete, base_files=base_files), want, self.said)
                self.assertEqual(self.line, "made_from: %s (a path under its proofs/provenance/ or its images/dune "
                                            "changed)" % unit if want == named else self.NO_UNIT)

    def test_the_plan_job_gives_the_four_answers_and_its_summary_names_them(self):
        plan = load("pr.yml")["jobs"]["plan"]
        names = {"made_from", "made_from_units", "made_from_every", "made_from_proofs"}
        for name in sorted(names):
            with self.subTest(output=name):
                self.assertEqual(plan["outputs"][name], "${{ steps.reach.outputs.%s }}" % name)
        reach = next(s for s in plan["steps"] if s.get("id") == "reach")
        [summary] = re.findall(r"grep -E '\^\(([^)]*)\)='", reach["run"])
        self.assertLessEqual(names, set(summary.split("|")))


RECORD_PATH = "tools/publish/public-before-hold.tsv"


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class PublicRowsJobTest(unittest.TestCase):
    """pr.yml's public_rows job, which checks each row of tools/publish/public-before-hold.tsv against the public
    repository's release and the hold's merge (tools/oft/tests/public_before_hold_rows.py), and the reach step's block
    that answers whether it runs: when the change touches that file and the head tree holds it, and only then."""

    def job(self):
        return load("pr.yml")["jobs"]["public_rows"]

    def block(self):
        """The reach step's public-before-hold rows block, from pr.yml's text."""
        reach = next(s for s in load("pr.yml")["jobs"]["plan"]["steps"] if s.get("id") == "reach")
        found = re.findall(r"\n *# public-before-hold rows\n(.*?)\n *# end of public-before-hold rows\n",
                           reach["run"], re.S)
        self.assertEqual(len(found), 1, "the block's two marks, once each")
        return found[0]

    def answer(self, changed, record=True):
        """(the block's public_rows answer, its output) for a change whose changed.txt lists changed, in a head tree
        that holds the record when record."""
        with tempfile.TemporaryDirectory(prefix="oft-test-") as d:
            if record:
                os.makedirs(os.path.join(d, "head", "tools", "publish"))
                with open(os.path.join(d, "head", RECORD_PATH), "w") as f:
                    f.write("# rows\n")
            with open(os.path.join(d, "changed.txt"), "w") as f:
                f.write("".join(p + "\n" for p in changed))
            out = os.path.join(d, "output")
            open(out, "w").close()
            r = subprocess.run(["bash", "-c", 'set -euo pipefail\nchanged="$1"\n' + self.block(), "block",
                                os.path.join(d, "changed.txt")], cwd=d, capture_output=True, text=True,
                               env=dict(os.environ, GITHUB_OUTPUT=out))
            self.assertEqual(r.returncode, 0, r.stderr)
            with open(out) as f:
                return dict(line.split("=", 1) for line in f.read().splitlines()).get("public_rows"), r.stdout

    def test_the_block_answers_true_only_for_a_change_to_the_record_the_head_tree_holds(self):
        for name, changed, record, want in (
                ("the record", [RECORD_PATH], True, "true"),
                ("the record and other files", ["README.md", RECORD_PATH, "tools/oft/disclosure.py"], True, "true"),
                ("the record deleted", [RECORD_PATH], False, "false"),
                ("other files", ["tools/publish/withheld.yaml", "tools/oft/disclosure.py"], True, "false"),
                ("a path that only begins like the record", [RECORD_PATH + ".old"], True, "false"),
                ("nothing", [], True, "false")):
            with self.subTest(case=name):
                got, said = self.answer(changed, record)
                self.assertEqual(got, want, said)
                self.assertIn("public_rows: ", said)

    def test_the_plan_job_gives_the_answer_and_its_summary_names_it(self):
        plan = load("pr.yml")["jobs"]["plan"]
        self.assertEqual(plan["outputs"]["public_rows"], "${{ steps.reach.outputs.public_rows }}")
        reach = next(s for s in plan["steps"] if s.get("id") == "reach")
        [summary] = re.findall(r"grep -E '\^\(([^)]*)\)='", reach["run"])
        self.assertIn("public_rows", summary.split("|"))

    def test_the_job_runs_only_when_the_plan_answered_true_and_lint_passed(self):
        from oft.tests.test_facts_review_gate import evaluate

        def runs(plan="success", lint="success", answer="true", cancelled=False):
            needs = {"plan": {"result": plan, "outputs": {"public_rows": answer} if plan == "success" else {}},
                     "lint": {"result": lint, "outputs": {}}}
            return evaluate(self.job().get("if", "success()"), needs, cancelled)
        self.assertTrue(runs())
        for name, kw in (("the answer false", dict(answer="false")), ("lint skipped", dict(lint="skipped")),
                         ("lint failed", dict(lint="failure")),
                         ("the plan failed", dict(plan="failure", lint="skipped")),
                         ("cancelled", dict(cancelled=True))):
            with self.subTest(case=name):
                self.assertFalse(runs(**kw))

    def test_the_job_reads_this_commit_s_history_and_runs_the_rows_with_the_job_s_token(self):
        """One blobless commit of tools/oft and tools/publish with the token persisted, deepened to this commit's
        whole history as the stream_tools job does; then the row test with GH_TOKEN and this pull request's number;
        contents: read and nothing more; no step that may fail and pass."""
        job, stream = self.job(), load("pr.yml")["jobs"]["stream_tools"]
        self.assertEqual(job["needs"], ["plan", "lint"])
        self.assertEqual(job["permissions"], {"contents": "read"})
        self.assertEqual(job["env"], {"GIT_TERMINAL_PROMPT": "0"})
        [checkout] = [s for s in job["steps"] if s.get("uses", "").startswith("actions/checkout@")]
        self.assertEqual(checkout["with"], {"path": "head", "persist-credentials": True, "fetch-depth": 1,
                                            "filter": "blob:none", "sparse-checkout": "tools/oft\ntools/publish\n"})
        history = step(job, "this commit's whole history, and no other branch's")
        fetch = 'git fetch --filter=blob:none --no-tags --unshallow origin "$(git rev-parse HEAD)"'
        self.assertIn(fetch, history["run"])
        self.assertIn(fetch, step(stream, "this commit's whole history, and no other branch's")["run"])
        self.assertEqual(history["working-directory"], "head")
        rows = step(job, "each row of tools/publish/public-before-hold.tsv against its release and its hold's merge")
        self.assertEqual(rows["working-directory"], "head/tools")
        self.assertEqual(rows["env"], {"GH_TOKEN": "${{ github.token }}",
                                       "OFT_CHANGE_PULL_REQUEST": "${{ github.event.pull_request.number }}"})
        self.assertEqual(rows["run"], "python -B -m unittest -v oft.tests.public_before_hold_rows")
        self.assertEqual([s for s in job["steps"] if "continue-on-error" in s], [])
        self.assertIn("public_rows", load("pr.yml")["jobs"]["required"]["needs"])


LEFT_OUT_STEP = "the left-out files lint reads"


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
@unittest.skipUnless(shutil.which("git"), "git is not installed")
class LeftOutStepTest(HeadRepoTest):
    """pr.yml's lint, in the checkout without the proof libraries (the plan's lint_files_left_out), checks out each
    left-out file that differs from the commit lint compares with.  head/ is a blob:none clone: the step fetches the
    missing blobs of those files in one request, then checks them out with no lazy fetch, and a blob it cannot fetch
    fails the step."""

    LIB = "projects/curl/fuzz_bufq/proofs/lib/"

    def setUp(self):
        super().setUp()
        # a `python` on PATH that runs this test's own Python, as setup-python gives the lint job one
        with open(os.path.join(self.dir, "bin", "python"), "w") as f:
            f.write('#!/bin/sh\nexec %s "$@"\n' % shlex.quote(sys.executable))
        os.chmod(os.path.join(self.dir, "bin", "python"), 0o755)
        self.changed = [self.LIB + "Changed%02d.v" % n for n in range(30)]
        self.write(dict({f: "(* base %d *)\n" % n for n, f in enumerate(self.changed)},
                        **{self.LIB + "Kept.v": "(* kept *)\n", "README": "r\n"}))
        self.base = self.commit("base")

    def step(self, env=None):
        full = {"BASE": self.base, "SINCE": "", "RECORD_KEY": ""}
        full.update(env or {})
        rc, out, _summary = self.run_step(step(load("pr.yml")["jobs"]["lint"], LEFT_OUT_STEP)["run"], full,
                                          cwd=self.ws)
        return rc, out

    def change(self):
        """30 changed proof library files, an added one, a symbolic link added beside them, and a changed README,
        which the checkout holds."""
        self.write(dict({f: "(* head %d *)\n" % n for n, f in enumerate(self.changed)},
                        **{self.LIB + "Added.v": "(* added *)\n", "README": "changed\n"}))
        os.symlink("Kept.v", os.path.join(self.head, self.LIB + "Link.v"))
        self.commit("change them")

    def test_the_changed_left_out_files_are_fetched_in_one_request_and_checked_out(self):
        self.change()
        self.partial()
        self.assertFalse(os.path.lexists(os.path.join(self.head, self.LIB + "Link.v")))
        trace = os.path.join(self.dir, "trace2.json")
        rc, out = self.step(env={"GIT_TRACE2_EVENT": trace})
        self.assertEqual(rc, 0, out)
        self.assertNotIn("::error::", out)
        self.assertIn("32 file(s) that differ from %s are left out of the checkout" % self.base, out)
        self.assertIn("left-out files: 32 file(s), 32 blob(s), 32 missing here, 32 fetched in 1 request(s)", out)
        self.assertEqual(self.fetches(trace), (1, 0))
        for n, f in enumerate(self.changed):
            with open(os.path.join(self.head, f)) as text:
                self.assertEqual(text.read(), "(* head %d *)\n" % n)
        with open(os.path.join(self.head, self.LIB + "Added.v")) as text:
            self.assertEqual(text.read(), "(* added *)\n")
        self.assertEqual(os.readlink(os.path.join(self.head, self.LIB + "Link.v")), "Kept.v")
        self.assertFalse(os.path.exists(os.path.join(self.head, self.LIB + "Kept.v")), "an unchanged file stays out")

    def test_a_gitlink_has_no_blob_to_fetch(self):
        """A gitlink among the left-out files names a commit of another repository, which origin does not have."""
        self.write({self.changed[0]: "(* head *)\n"})
        git(self.head, "add", "-A")
        git(self.head, "update-index", "--add", "--cacheinfo", "160000,%s,%s" % ("1" * 40, self.LIB + "Sub"))
        git(self.head, "commit", "-qm", "a changed file and a gitlink")
        self.partial()
        rc, out = self.step()
        self.assertEqual(rc, 0, out)
        self.assertIn("left-out files: 2 file(s), 1 blob(s), 1 missing here, 1 fetched in 1 request(s)", out)

    def test_a_deleted_file_and_a_renamed_one_check_out_the_new_path_alone(self):
        """The change deletes one left-out file and renames another into a new folder of the library.  The diff lists
        the three paths, of which the head's index holds the new one alone, so it alone is fetched and checked out."""
        moved = self.LIB + "Rt/Changed01.v"
        self.write({self.changed[0]: None, self.changed[1]: None, moved: "(* base 1 *)\n"})
        self.commit("delete one, rename another")
        self.partial()
        rc, out = self.step()
        self.assertEqual(rc, 0, out)
        self.assertNotIn("::error::", out)
        self.assertIn("1 file(s) that differ from %s are left out of the checkout" % self.base, out)
        self.assertIn("left-out files: 1 file(s), 1 blob(s), 1 missing here, 1 fetched in 1 request(s)", out)
        with open(os.path.join(self.head, moved)) as text:
            self.assertEqual(text.read(), "(* base 1 *)\n")
        for gone in self.changed[:2]:
            self.assertFalse(os.path.lexists(os.path.join(self.head, gone)), gone)

    def test_no_changed_left_out_file_fetches_nothing(self):
        self.write({"README": "changed\n"})
        self.commit("README alone")
        self.partial()
        trace = os.path.join(self.dir, "trace2.json")
        rc, out = self.step(env={"GIT_TRACE2_EVENT": trace})
        self.assertEqual(rc, 0, out)
        self.assertIn("0 file(s) that differ from %s are left out of the checkout" % self.base, out)
        self.assertEqual(self.fetches(trace), (0, 0))

    def test_blobs_that_cannot_be_fetched_fail_the_step(self):
        self.change()
        shutil.rmtree(self.partial())
        rc, out = self.step()
        self.assertEqual(rc, 1, out)
        errors = [line for line in out.split("\n") if line.startswith("::error::")]
        self.assertEqual(errors, ["::error::32 blob(s) of the left-out files that lint reads could not be fetched "
                                  "from origin, so lint cannot read them"], out)
        self.assertIn("left-out files: 32 file(s), 32 blob(s), 32 missing here, 0 fetched in 3 request(s)", out)
        self.assertEqual([c for c in self.calls() if c.startswith("sleep")], ["sleep 30", "sleep 90"])
        self.assertFalse(os.path.exists(os.path.join(self.head, self.changed[0])), "nothing is checked out")

    def test_the_step_has_a_time_limit_of_its_own(self):
        self.assertEqual(step(load("pr.yml")["jobs"]["lint"], LEFT_OUT_STEP)["timeout-minutes"], 30)


STRIP_STEP = "a proof file of a unit with a licence record keeps Anthropic's copyright line (the strip check)"
COPYRIGHT = "(* Copyright 2026 Anthropic PBC *)\n(* SPDX-License-Identifier: Apache-2.0 OR MIT *)\n"


def stripped_proof(name):
    """A proof's text after its licence lines: long enough that git's rename detection still pairs the file with the
    file it was (more than half of its bytes)."""
    return ("Require Import Arith.\n\n"
            "Lemma %s_adds_zero : forall n : nat, n + 0 = n.\n"
            "Proof.\n  intros n. induction n as [| n IH]; simpl; [reflexivity | rewrite IH; reflexivity].\nQed.\n\n"
            "Lemma %s_zero_adds : forall n : nat, 0 + n = n.\nProof.\n  reflexivity.\nQed.\n") % (name, name)


def licensed_proof(name):
    return COPYRIGHT + stripped_proof(name)


def escaped(name):
    """A name as the strip step prints it in a workflow command's data (as escape() of the made_from job's records
    step does)."""
    return name.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


# The generator whose rules the strip step writes again: the shared dev/licence/made_from.py, which every unit's
# made_from.py calls.  tools/oft alone (the runner image's copy) has no dev/.
MADE_FROM = os.path.join(REPO, "dev", "licence", "made_from.py")
NO_MADE_FROM = "no dev/licence/made_from.py: tools/oft alone"
# a unit file at this path under a checkout gives the generator curl/fuzz_bufq's layout (its left-bare.tsv)
BUFQ_UNIT_FILE = "projects/curl/fuzz_bufq/proofs/provenance/evidence/licence/made_from.py"


def load_made_from():
    """dev/licence/made_from.py as a module: it runs its command line only as __main__."""
    spec = importlib.util.spec_from_file_location("licence_made_from", MADE_FROM)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
@unittest.skipUnless(shutil.which("git"), "git is not installed")
class StripStepTest(HeadRepoTest):
    """pr.yml's lint fails a change in which a .v file under proofs/ (outside proofs/provenance/) of a unit with a
    licence record (proofs/provenance/evidence/licence/made-from.tsv, at the base or at HEAD) carries Anthropic's
    copyright line in its first 10 lines at the base and not at HEAD, unless the left-bare.tsv at HEAD of the head
    path's unit declares the file.  It pairs a file by its path, by git's rename detection, and a deleted with an added
    file by their text.  The unit of the base path decides.  In a unit with no record it prints a ::notice:: line.  It
    reads git objects only, fetches missing blobs in bulk, and prints file names only escaped, inside the data of its
    own ::error:: and ::notice:: lines."""

    BUFQ = "projects/curl/fuzz_bufq"        # a unit with a licence record
    FNMATCH = "projects/curl/fuzz_fnmatch"  # another, where a test gives it one
    OTHER = "projects/acme/fuzz_other"      # a unit with no licence record
    LICENCE = "proofs/provenance/evidence/licence"
    PROOF = "projects/curl/fuzz_bufq/proofs/lib/Proof.v"
    MOVED = 1100  # files moved in one change: past git's rename limit (diff.renameLimit, 1000 by default)
    _moved = None
    _run = None

    def setUp(self):
        super().setUp()
        os.mkdir(os.path.join(self.dir, "tmp"))
        self.write({self.record(self.BUFQ): "row\n", self.PROOF: licensed_proof("proof"), "README": "r\n"})
        self.base = self.commit("base")

    @classmethod
    def tearDownClass(cls):
        if cls._moved is not None:
            cls._moved[0].cleanup()
            cls._moved = None
        super().tearDownClass()

    @classmethod
    def record(cls, unit):
        return "%s/%s/made-from.tsv" % (unit, cls.LICENCE)

    @classmethod
    def left_bare(cls, unit):
        return "%s/%s/left-bare.tsv" % (unit, cls.LICENCE)

    @staticmethod
    def lib(unit, name):
        return "%s/proofs/lib/%s.v" % (unit, name)

    def status(self, head=None, base=None):
        """git's own name-status of the change, with renames: the rows the step reads."""
        return git(head or self.head, "diff", "--name-status", "-M", base or self.base, "HEAD").splitlines()

    @classmethod
    def run_text(cls):
        if cls._run is None:
            cls._run = step(load("pr.yml")["jobs"]["lint"], STRIP_STEP)["run"]
        return cls._run

    def step(self, kind="maintainer", base=None, env=None, ws=None):
        full = {"BASE": base or self.base, "RUNNER_TEMP": os.path.join(self.dir, "tmp"), "KIND": kind}
        full.update(env or {})
        rc, out, _summary = self.run_step(self.run_text(), full, cwd=ws or self.ws)
        return rc, out

    def error(self, rc, out):
        """The one ::error:: line of a run that failed."""
        self.assertEqual(rc, 1, out)
        errors = [line for line in out.split("\n") if line.startswith("::error::")]
        self.assertEqual(len(errors), 1, out)
        return errors[0]

    def fails_naming(self, rc, out, *files):
        """The run failed, and its one ::error:: line names each file of files, a head path or (head path, base
        path), escaped, on a line of its own inside the line's data."""
        line = self.error(rc, out)
        for f in files:
            head, base = f if isinstance(f, tuple) else (f, None)
            item = "%0A  " + escaped(head) + (" (at the base: %s)" % escaped(base) if base else "") + "%0A"
            self.assertIn(item, line)
        self.assertIn("left-bare.tsv of the unit that its path is in", line)
        return line

    def passes(self, rc, out):
        self.assertEqual(rc, 0, out)
        self.assertNotIn("::error::", out)

    def strip_and_declare(self, row):
        """lib/Proof.v of curl/fuzz_bufq loses its licence lines and the unit's left-bare.tsv at HEAD holds row."""
        self.write({self.PROOF: stripped_proof("proof"), self.left_bare(self.BUFQ): row})
        self.commit("strip lib/Proof.v and declare it")

    @classmethod
    def moved(cls):
        """One repository, made once for the class, in which one change moves MOVED files of curl/fuzz_bufq to new
        names and takes their licence lines off, so git's rename detection pairs none of them.  Two more files move
        with them: one that starts with a `(* Relocated from ... *)` line, and one whose `(* Modified by ...` comment
        runs over two lines; every licence comment of the two is taken off.  (the directory holding head/, the
        base)."""
        if cls._moved is None:
            tmp = tempfile.TemporaryDirectory(prefix="oft-strip-")
            head = os.path.join(tmp.name, "head")
            os.makedirs(head)
            git(head, "init", "-q")
            files = {cls.record(cls.BUFQ): "row\n",
                     cls.lib(cls.BUFQ, "Relocated"): "(* Relocated from proofs/curl/fuzz_bufq/lib/Old.v *)\n"
                                                     + COPYRIGHT + stripped_proof("relocated"),
                     cls.lib(cls.BUFQ, "Modified"): "(* Modified by Theorem Labs, 2026-11: the induction\n"
                                                    "   is written again *)\n" + COPYRIGHT
                                                    + stripped_proof("modified")}
            files.update({cls.lib(cls.BUFQ, "Many%04d" % n): licensed_proof("many%04d" % n) for n in range(cls.MOVED)})
            write_files(head, files)
            git(head, "add", "-A")
            git(head, "commit", "-qm", "base")
            base = git(head, "rev-parse", "HEAD")
            git(head, "rm", "-rq", cls.BUFQ + "/proofs/lib")
            files = {cls.lib(cls.BUFQ, "moved/RelocatedHere"): stripped_proof("relocated"),
                     cls.lib(cls.BUFQ, "moved/ModifiedHere"): stripped_proof("modified")}
            files.update({cls.lib(cls.BUFQ, "moved/Moved%04d" % n): stripped_proof("many%04d" % n)
                          for n in range(cls.MOVED)})
            write_files(head, files)
            git(head, "add", "-A")
            git(head, "commit", "-qm", "move and strip")
            cls._moved = (tmp, base)
        return cls._moved[0].name, cls._moved[1]

    def test_a_file_that_loses_its_copyright_line_at_its_path_fails(self):
        self.write({self.PROOF: stripped_proof("proof")})
        self.commit("strip lib/Proof.v")
        rc, out = self.step()
        line = self.fails_naming(rc, out, self.PROOF)
        self.assertIn("::error::1 proof file(s) lost Anthropic's copyright line", line)
        # it never tells anyone to write the lines back with the generator
        self.assertNotIn("--apply", self.run_text())

    def test_a_renamed_file_that_loses_its_line_fails_by_its_new_path(self):
        new = self.lib(self.BUFQ, "Renamed")
        self.write({self.PROOF: None, new: stripped_proof("proof")})
        self.commit("rename and strip lib/Proof.v")
        self.assertEqual([row.split("\t")[0][:1] for row in self.status()], ["R"])
        rc, out = self.step()
        self.fails_naming(rc, out, (new, self.PROOF))

    def test_files_moved_past_git_s_rename_limit_are_paired_by_their_text(self):
        ws, base = self.moved()
        # git paired none of them: the change has only D and A rows, no R row
        rows = self.status(head=os.path.join(ws, "head"), base=base)
        self.assertEqual([row for row in rows if not row.startswith(("A\t", "D\t"))], [])
        rc, out = self.step(base=base, ws=ws)
        line = self.fails_naming(rc, out, *[(self.lib(self.BUFQ, "moved/Moved%04d" % n),
                                             self.lib(self.BUFQ, "Many%04d" % n)) for n in (0, 1, self.MOVED - 1)])
        self.assertIn("::error::%d proof file(s) lost" % (self.MOVED + 2), line)

    def test_a_file_renamed_into_a_unit_with_no_record_is_judged_by_its_base_unit(self):
        new = self.lib(self.OTHER, "Proof")
        self.write({self.PROOF: None, new: stripped_proof("proof")})
        self.commit("move lib/Proof.v to a unit with no record and strip it")
        self.assertEqual([row.split("\t")[0][:1] for row in self.status()], ["R"])
        rc, out = self.step()
        self.fails_naming(rc, out, (new, self.PROOF))
        self.assertNotIn("::notice::", out)

    def test_a_file_moved_into_a_unit_whose_left_bare_tsv_declares_it_passes(self):
        """The head path's unit holds the declaration, by the path relative to that unit's proofs/: the same row in
        the base unit's left-bare.tsv declares nothing."""
        self.write({self.record(self.FNMATCH): "row\n"})
        self.base = self.commit("a second unit with a record")
        new = self.lib(self.FNMATCH, "Moved")
        self.write({self.PROOF: None, new: stripped_proof("proof"),
                    self.left_bare(self.BUFQ): "lib/Moved.v\tour own proof, written in this repository\n"})
        self.commit("move lib/Proof.v to curl/fuzz_fnmatch, strip it, declare it in the wrong unit")
        self.fails_naming(*self.step(), (new, self.PROOF))
        self.write({self.left_bare(self.BUFQ): None,
                    self.left_bare(self.FNMATCH): "lib/Moved.v\tour own proof, written in this repository\n"})
        self.commit("declare it in curl/fuzz_fnmatch")
        rc, out = self.step()
        self.passes(rc, out)
        self.assertIn("1 declared in left-bare.tsv", out)

    def test_a_left_bare_row_declares_only_with_two_columns_and_a_reason(self):
        self.strip_and_declare("path\treason\nlib/Proof.v\tour own proof, written in this repository\n")
        self.passes(*self.step())
        for row in ("lib/Proof.v\t \n", "lib/Proof.v\tour own proof\tand a third column\n"):
            with self.subTest(row=row):
                self.strip_and_declare("path\treason\n" + row)
                self.fails_naming(*self.step(), self.PROOF)

    def test_a_left_bare_tsv_with_no_header_row_takes_its_first_row(self):
        self.strip_and_declare("lib/Proof.v\tour own proof, written in this repository\n")
        rc, out = self.step()
        self.passes(rc, out)
        # the row declared the strip; a step that read no row would not count it
        self.assertIn("1 declared in left-bare.tsv", out)

    def test_a_deleted_file_passes(self):
        self.write({self.PROOF: None})
        self.commit("delete lib/Proof.v")
        rc, out = self.step()
        self.passes(rc, out)
        self.assertIn("no proof file lost Anthropic's copyright line", out)

    def test_a_copyright_line_moved_to_line_11_fails(self):
        self.write({self.PROOF: "(* a note *)\n" * 10 + licensed_proof("proof")})
        self.commit("push the copyright line to line 11")
        self.fails_naming(*self.step(), self.PROOF)

    def test_a_file_the_checkout_leaves_out_still_fails(self):
        self.write({self.PROOF: stripped_proof("proof")})
        self.commit("strip lib/Proof.v")
        self.sparse()
        self.assertFalse(os.path.exists(os.path.join(self.head, self.PROOF)))
        self.fails_naming(*self.step(), self.PROOF)

    def test_a_change_that_touches_no_proof_passes(self):
        self.write({"README": "a new readme\n"})
        self.commit("no proof")
        rc, out = self.step()
        self.passes(rc, out)
        self.assertIn("no proof file lost Anthropic's copyright line", out)
        self.assertIn("strip check: compared 0 pair(s)", out)

    def test_a_unit_with_no_record_gets_a_notice_and_passes(self):
        other = self.lib(self.OTHER, "Other")
        self.write({other: licensed_proof("other")})
        self.base = self.commit("a unit with no record")
        self.write({other: stripped_proof("other")})
        self.commit("strip lib/Other.v")
        rc, out = self.step()
        self.passes(rc, out)
        notices = [line for line in out.split("\n") if line.startswith("::notice::")]
        self.assertEqual(notices, ["::notice::%s lost Anthropic's copyright line. Its unit at the base has no licence "
                                   "record (proofs/provenance/evidence/licence/made-from.tsv), so the strip check "
                                   "does not fail on it." % escaped(other)], out)

    def test_every_kind_of_change_gets_the_same_verdicts(self):
        """No code of the head runs, so KIND changes nothing: a strip fails and a declared strip passes."""
        self.write({self.PROOF: stripped_proof("proof")})
        self.commit("strip lib/Proof.v")
        for kind in ("contributor", "maintainer", "release"):
            with self.subTest(kind=kind, case="strip"):
                self.fails_naming(*self.step(kind=kind), self.PROOF)
        self.strip_and_declare("lib/Proof.v\tour own proof, written in this repository\n")
        for kind in ("contributor", "maintainer", "release"):
            with self.subTest(kind=kind, case="declared"):
                self.passes(*self.step(kind=kind))

    def test_a_file_name_cannot_start_a_workflow_command(self):
        """A name with a new line, %0A and the old ##[ form: only the step's own ::error:: line starts with :: or
        holds ##[, and the name is in it escaped.  The commits are made with update-index, so no file system has to
        hold the name."""
        name = self.BUFQ + "/proofs/lib/X\n::error::forged %0A ##[error]forged.v"
        blobs = {}
        for label, text in (("base", licensed_proof("x")), ("head", stripped_proof("x"))):
            write_files(self.dir, {"blob-" + label: text})
            blobs[label] = git(self.head, "hash-object", "-w", os.path.join(self.dir, "blob-" + label))
        git(self.head, "update-index", "--add", "--cacheinfo", "100644,%s,%s" % (blobs["base"], name))
        git(self.head, "commit", "-qm", "a file with a forged name")
        self.base = git(self.head, "rev-parse", "HEAD")
        git(self.head, "update-index", "--cacheinfo", "100644,%s,%s" % (blobs["head"], name))
        git(self.head, "commit", "-qm", "strip it")
        rc, out = self.step()
        line = self.fails_naming(rc, out, name)
        self.assertIn("X%0A::error::forged %250A ##[error]forged.v", line)
        for other in out.split("\n"):
            if other != line:
                self.assertFalse(other.startswith("::") or "##[" in other, other)

    def test_the_step_runs_on_every_run_of_the_lint_job(self):
        s = step(load("pr.yml")["jobs"]["lint"], STRIP_STEP)
        self.assertNotIn("if", s)
        self.assertEqual(s["env"], {"BASE": "${{ steps.base.outputs.base }}"})  # KIND is the workflow's own env
        self.assertEqual(s["timeout-minutes"], 30)

    def test_the_step_runs_before_any_code_of_the_head_with_the_token_its_fetches_need(self):
        """Its fetches from origin need the token that lint's checkout of head/ keeps in head/.git/config: no such
        checkout sets persist-credentials to false, and no step before the strip check unsets the header."""
        steps = load("pr.yml")["jobs"]["lint"]["steps"]
        names = [s.get("name") for s in steps]
        at = names.index(STRIP_STEP)
        self.assertLess(names.index("the left-out files lint reads"), at)
        self.assertLess(at, names.index("lint, by the base's rules"))
        checkouts = [s for s in steps
                     if s.get("uses", "").startswith("actions/checkout@") and s["with"].get("path") == "head"]
        self.assertEqual(len(checkouts), 2, checkouts)
        for s in checkouts:
            self.assertIn(s["with"].get("persist-credentials", True), (True, "true"), s)
        for s in steps[:at]:
            self.assertNotRegex(s.get("run", ""), r"--unset\S*\s+\S*extraheader", s.get("name", s.get("uses")))

    def test_missing_blobs_are_fetched_in_bulk(self):
        """30 files stripped at their paths, in a blob:none clone that holds none of their blobs: one fetch for the
        30 head blobs and one for the 30 base blobs, and no lazy fetch of one blob."""
        files = [self.lib(self.BUFQ, "Bulk%02d" % n) for n in range(30)]
        self.write({f: licensed_proof("bulk%02d" % n) for n, f in enumerate(files)})
        self.base = self.commit("30 proofs")
        self.write({f: stripped_proof("bulk%02d" % n) for n, f in enumerate(files)})
        self.commit("strip them")
        self.partial()
        trace = os.path.join(self.dir, "trace2.json")
        rc, out = self.step(env={"GIT_TRACE2_EVENT": trace})
        self.fails_naming(rc, out, *files)
        self.assertIn("::error::30 proof file(s) lost", out)
        self.assertIn("fetched 60 blob(s) in 2 request(s)", out)
        started, lazy = self.fetches(trace)
        self.assertEqual(lazy, 0)
        self.assertTrue(1 <= started <= 3, started)

    def test_a_pair_with_one_blob_id_reads_no_blob(self):
        """A file renamed with no change: its blob is in neither the clone nor the promisor, and the step passes
        without a fetch."""
        same, renamed = self.lib(self.BUFQ, "Same"), self.lib(self.BUFQ, "Renamed")
        self.write({same: licensed_proof("same")})
        self.base = self.commit("lib/Same.v")
        git(self.head, "mv", same, renamed)
        self.commit("rename it, with no change")
        oid = git(self.head, "rev-parse", "HEAD:" + renamed)
        bare = self.partial()
        os.remove(os.path.join(bare, "objects", oid[:2], oid[2:]))
        self.assertFalse(stored(bare, oid))
        self.assertFalse(stored(self.head, oid))
        trace = os.path.join(self.dir, "trace2.json")
        rc, out = self.step(env={"GIT_TRACE2_EVENT": trace})
        self.passes(rc, out)
        self.assertIn("fetched 0 blob(s) in 0 request(s)", out)
        self.assertEqual(self.fetches(trace), (0, 0))

    def test_blobs_that_cannot_be_fetched_fail_the_step(self):
        self.write({self.PROOF: stripped_proof("proof")})
        self.commit("strip lib/Proof.v")
        shutil.rmtree(self.partial())
        rc, out = self.step()
        line = self.error(rc, out)
        self.assertIn("could not be fetched from origin, so nothing is passed", line)
        self.assertEqual([c for c in self.calls() if c.startswith("sleep")], ["sleep 30", "sleep 90"])

    def test_files_whose_licence_lines_licence_lines_does_not_take_are_paired_too(self):
        """A file that starts with `(* Relocated from ... *)`, and one whose `(* Modified by ...` comment runs over
        two lines: their text after licence_lines() still holds the copyright line, and the text after their leading
        comments pairs them."""
        ws, base = self.moved()
        self.fails_naming(*self.step(base=base, ws=ws),
                          (self.lib(self.BUFQ, "moved/RelocatedHere"), self.lib(self.BUFQ, "Relocated")),
                          (self.lib(self.BUFQ, "moved/ModifiedHere"), self.lib(self.BUFQ, "Modified")))

    def test_a_move_out_of_the_proof_files_still_fails(self):
        """Into proofs/provenance/, and to a name that does not end .v: the diff is of the whole tree."""
        into_provenance, to_txt = self.lib(self.BUFQ, "ToProvenance"), self.lib(self.BUFQ, "ToText")
        self.write({into_provenance: licensed_proof("provenance"), to_txt: licensed_proof("text")})
        self.base = self.commit("two more proofs")
        new_provenance = self.BUFQ + "/proofs/provenance/ToProvenance.v"
        new_txt = self.BUFQ + "/proofs/lib/ToText.txt"
        self.write({into_provenance: None, to_txt: None, new_provenance: stripped_proof("provenance"),
                    new_txt: stripped_proof("text")})
        self.commit("move them out of the proof files and strip them")
        self.fails_naming(*self.step(), (new_provenance, into_provenance), (new_txt, to_txt))

    def test_a_strip_with_the_record_deleted_in_the_same_change_fails(self):
        self.write({self.PROOF: stripped_proof("proof"), self.record(self.BUFQ): None})
        self.commit("strip lib/Proof.v and delete the record")
        self.fails_naming(*self.step(), self.PROOF)

    def test_a_file_replaced_by_a_symbolic_link_fails(self):
        """A T row: the head's blob is the link's target, which carries no line."""
        self.write({self.BUFQ + "/proofs/lib/Proof.txt": stripped_proof("proof"), self.PROOF: None})
        os.symlink("Proof.txt", os.path.join(self.head, self.PROOF))
        self.commit("lib/Proof.v becomes a link")
        self.assertIn("T\t" + self.PROOF, self.status())
        self.fails_naming(*self.step(), self.PROOF)

    def test_a_file_replaced_by_a_link_whose_target_names_the_line_fails(self):
        """A link's blob is its target's path, not the text a checkout of lib/Proof.v reads.  A target path that
        holds the words of the copyright line must not pass for the line: lib/Proof.v reads the stripped text."""
        target = self.BUFQ + "/proofs/lib/Copyright 2026 Anthropic PBC/Proof.v"
        self.write({target: stripped_proof("proof"), self.PROOF: None})
        os.symlink("Copyright 2026 Anthropic PBC/Proof.v", os.path.join(self.head, self.PROOF))
        self.commit("lib/Proof.v becomes a link to a stripped copy")
        self.assertIn("T\t" + self.PROOF, self.status())
        self.fails_naming(*self.step(), self.PROOF)

    def test_a_link_at_the_base_carries_no_line_whatever_its_target(self):
        """A base that is a link whose target path holds the words of the line: the stripped file that replaces it
        is no strip of it."""
        name = "Copyright 2026 Anthropic PBC/Proof.v"
        self.write({self.BUFQ + "/proofs/lib/" + name: stripped_proof("proof"), self.PROOF: None})
        os.symlink(name, os.path.join(self.head, self.PROOF))
        self.base = self.commit("lib/Proof.v is a link")
        self.write({self.PROOF: None})
        self.write({self.PROOF: stripped_proof("proof")})
        self.commit("lib/Proof.v becomes a stripped file")
        self.assertIn("T\t" + self.PROOF, self.status())
        rc, out = self.step()
        self.passes(rc, out)
        # the pair was compared and judged no strip; a step that compared nothing would print no such line
        self.assertIn("compared 1 pair(s) at one path or a rename", out)
        self.assertIn("no proof file lost Anthropic's copyright line", out)

    def test_a_file_that_becomes_a_link_with_its_own_bytes_fails(self):
        """A file whose text, which carries the line, is the path the link names: one blob id on both sides."""
        name = "Copyright 2026 Anthropic PBC/Proof.v"
        self.write({self.BUFQ + "/proofs/lib/" + name: stripped_proof("proof"), self.PROOF: name})
        self.base = self.commit("lib/Proof.v holds a path")
        self.write({self.PROOF: None})
        os.symlink(name, os.path.join(self.head, self.PROOF))
        self.commit("lib/Proof.v becomes a link to that path")
        self.assertIn("T\t" + self.PROOF, self.status())
        self.fails_naming(*self.step(), self.PROOF)

    def test_left_bare_rows_that_declare_nothing(self):
        """A path named on two rows, and a row that is not UTF-8, declare nothing; a row that ends \\r\\n
        declares."""
        for row in (b"lib/Proof.v\tours\nlib/Proof.v\tours again\n", b"lib/Proof.v\tour own \xff proof\n"):
            with self.subTest(row=row):
                self.strip_and_declare(row)
                self.fails_naming(*self.step(), self.PROOF)
        self.strip_and_declare(b"lib/Proof.v\tour own proof\r\n")
        self.passes(*self.step())

    @unittest.skipUnless(os.path.isfile(MADE_FROM), NO_MADE_FROM)
    def test_the_step_s_rules_are_made_from_py_s(self):
        """The step writes made_from.py's HEADER_LINES, ANTHROPIC, LICENCE and PROGRAM again, since it runs no file
        of the change: each one, as the step's program assigns it, equals made_from.py's."""
        made_from = load_made_from()
        run = self.run_text()
        program = run[run.index("<<'EOF'\n") + len("<<'EOF'\n"):run.rindex("\nEOF")]
        names = ("HEADER_LINES", "ANTHROPIC", "LICENCE", "PROGRAM")
        found = collections.defaultdict(list)
        for node in ast.parse(program).body:
            if (isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)
                    and node.targets[0].id in names):
                found[node.targets[0].id].append(
                    eval(compile(ast.Expression(node.value), STRIP_STEP, "eval"), {"re": re}))
        self.assertEqual(sorted(found), sorted(names))
        for name in names:
            with self.subTest(name=name):
                [value] = found[name]
                want = getattr(made_from, name)
                if name == "HEADER_LINES":
                    self.assertEqual(value, want)
                else:
                    self.assertEqual((value.pattern, value.flags), (want.pattern, want.flags))

    @unittest.skipUnless(os.path.isfile(MADE_FROM), NO_MADE_FROM)
    def test_a_left_bare_tsv_declares_as_made_from_py_s_left_bare_does(self):
        """Each set of left-bare.tsv rows of the tests above: the step passes the strip of lib/Proof.v exactly when
        made_from.py's left_bare() declares lib/Proof.v, read from the same rows."""
        made_from = load_made_from()
        top = os.path.join(self.dir, "made-from-top")
        layout = made_from.Layout(os.path.join(top, BUFQ_UNIT_FILE), (), None)
        tsv = os.path.join(top, layout.left_bare_tsv)
        os.makedirs(os.path.dirname(tsv))
        files = {"lib/Proof.v": stripped_proof("proof")}
        verdicts = set()
        for rows in (b"path\treason\nlib/Proof.v\tour own proof, written in this repository\n",
                     b"path\treason\nlib/Proof.v\t \n",
                     b"path\treason\nlib/Proof.v\tour own proof\tand a third column\n",
                     b"lib/Proof.v\tour own proof, written in this repository\n",
                     b"lib/Proof.v\tours\nlib/Proof.v\tours again\n",
                     b"lib/Proof.v\tour own \xff proof\n",
                     b"lib/Proof.v\tour own proof\r\n"):
            with self.subTest(rows=rows):
                with open(tsv, "wb") as f:
                    f.write(rows)
                with contextlib.redirect_stderr(io.StringIO()):
                    declares = "lib/Proof.v" in made_from.left_bare(top, files, layout)
                verdicts.add(declares)
                self.strip_and_declare(rows)
                rc, out = self.step()
                self.assertIn(rc, (0, 1), out)
                self.assertEqual(rc == 0, declares, out)
        # both verdicts are among the rows, so a step that declared all or none would fail
        self.assertEqual(verdicts, {False, True})

    def test_a_declared_file_that_keeps_a_licence_tag_is_not_declared(self):
        """made_from.py's headerless(): a file left bare carries no licence line, and the MIT tag is one."""
        self.write({self.PROOF: "(* SPDX-License-Identifier: MIT *)\n" + stripped_proof("proof"),
                    self.left_bare(self.BUFQ): "lib/Proof.v\tour own proof, written in this repository\n"})
        self.commit("strip the copyright line, keep the MIT tag, declare it")
        self.fails_naming(*self.step(), self.PROOF)

    def test_an_added_file_that_matches_twins_fails_when_one_twin_has_a_record(self):
        """Two deleted files with one text, one in a unit with a record and one in a unit with none, and an added file
        with that text stripped.  The texts are short, so git's rename detection pairs none of them."""
        twin_text = COPYRIGHT + "Lemma twin : True.\nProof. exact I. Qed.\n"
        twin_cf, twin_cfw = self.lib(self.BUFQ, "Twin_cf"), self.lib(self.OTHER, "Twin_cfw")
        self.write({twin_cf: twin_text, twin_cfw: twin_text})
        self.base = self.commit("twins")
        added = self.lib(self.OTHER, "Twin")
        self.write({twin_cf: None, twin_cfw: None, added: "Lemma twin : True.\nProof. exact I. Qed.\n"})
        self.commit("one stripped copy of the twins")
        self.assertEqual(sorted(row.split("\t")[0] for row in self.status()), ["A", "D", "D"])
        self.fails_naming(*self.step(), (added, "%s, %s" % (twin_cfw, twin_cf)))

    def test_a_text_that_is_empty_or_only_white_space_pairs_no_file(self):
        """A deleted file that is only its licence lines: both of its texts are empty.  The added files elsewhere,
        one empty, one of blanks and one of a comment, have an empty text too, and the step pairs none of them."""
        bare = self.lib(self.BUFQ, "OnlyLicence")
        self.write({bare: COPYRIGHT})
        self.base = self.commit("a file that is only its licence lines")
        empty, blank, note = self.lib(self.OTHER, "Empty"), self.lib(self.OTHER, "Blank"), self.lib(self.BUFQ, "Note")
        self.write({bare: None, empty: "", blank: "\n \t\n", note: "(* a note *)\n"})
        self.commit("delete it, add an empty file, a file of blanks and a file of a comment")
        self.assertEqual(sorted(row.split("\t")[0] for row in self.status()), ["A", "A", "A", "D"])
        rc, out = self.step()
        self.passes(rc, out)
        self.assertIn("no proof file lost Anthropic's copyright line", out)

    def test_a_file_git_takes_as_the_rename_of_a_twin_with_no_record_fails(self):
        """Two deleted files with one text, one in a unit with a record and one in a unit with none, and a stripped
        copy that git's rename detection pairs, as an R row, with the twin in the unit with none.  The step pairs the
        R row's head with the other twin by its text too, so the twin with a record decides."""
        twin_cf, twin_cfw = self.lib(self.BUFQ, "Twin_cf"), self.lib(self.OTHER, "Twin_cfw")
        self.write({twin_cf: licensed_proof("twin"), twin_cfw: licensed_proof("twin")})
        self.base = self.commit("twins")
        moved = self.lib(self.OTHER, "moved/Twin_cfw")
        self.write({twin_cf: None, twin_cfw: None, moved: stripped_proof("twin")})
        self.commit("one stripped copy of the twins, which git takes as the rename of the twin with no record")
        self.assertEqual(sorted((row.split("\t")[0][:1], row.split("\t")[-1]) for row in self.status()),
                         [("D", twin_cf), ("R", moved)])
        self.assertIn(twin_cfw, [row.split("\t")[1] for row in self.status() if row.startswith("R")])
        self.fails_naming(*self.step(), (moved, "%s, %s" % (twin_cfw, twin_cf)))

    @staticmethod
    def body():
        """A proof's text after its licence lines, of 40 lines."""
        return stripped_proof("proof") + "".join("\nLemma proof_%02d : True.\nProof. exact I. Qed.\n" % n
                                                 for n in range(10))

    def test_a_deleted_file_s_text_written_over_a_file_that_is_no_proof_file_fails(self):
        """git takes no file that a change rewrites as a rename's target: lib/Proof.v deleted, and its text without
        the licence lines written over the unit's NOTES.md, are a D row and an M row whose base path is no proof
        file.  The step pairs the M row's head with the deleted file by its text."""
        notes = self.BUFQ + "/NOTES.md"
        self.write({self.PROOF: COPYRIGHT + self.body(), notes: "# Notes\n\nNothing yet.\n"})
        self.base = self.commit("lib/Proof.v of 40 lines, and NOTES.md")
        self.write({self.PROOF: None, notes: self.body()})
        self.commit("delete lib/Proof.v and write its text without the licence lines over NOTES.md")
        self.assertEqual(sorted(row.split("\t") for row in self.status()), [["D", self.PROOF], ["M", notes]])
        self.fails_naming(*self.step(), (notes, self.PROOF))

    def test_a_rename_from_a_path_that_is_no_proof_file_to_a_deleted_file_s_text_fails(self):
        """lib/Proof.v.orig, an older copy of lib/Proof.v's text without its licence lines, is closer to the new
        lib/Moved.v than lib/Proof.v is, so git takes lib/Moved.v as its rename and lib/Proof.v as deleted: the R row's
        base path is no proof file.  The step pairs the R row's head with lib/Proof.v by its text."""
        orig, moved = self.PROOF + ".orig", self.lib(self.BUFQ, "Moved")
        self.write({self.PROOF: COPYRIGHT + self.body(), orig: self.body() + "(* the older copy *)\n"})
        self.base = self.commit("lib/Proof.v of 40 lines, and an older copy of its text")
        self.write({self.PROOF: None, orig: None, moved: self.body()})
        self.commit("delete lib/Proof.v and move the older copy to lib/Moved.v with lib/Proof.v's text")
        rows = [row.split("\t") for row in self.status()]
        self.assertEqual(sorted((row[0][:1],) + tuple(row[1:]) for row in rows), [("D", self.PROOF), ("R", orig, moved)])
        self.fails_naming(*self.step(), (moved, self.PROOF))

    def test_a_file_that_is_no_proof_file_moved_unchanged_with_a_deleted_file_s_text_fails(self):
        """The base already holds lib/Proof.v's text without its licence lines in NOTES.md, and the change deletes
        lib/Proof.v and moves NOTES.md unchanged to lib/Moved.v: an exact rename (R100, one blob id on both sides)
        whose base path is no proof file.  The step pairs its head with lib/Proof.v by its text all the same."""
        notes, moved = self.BUFQ + "/NOTES.md", self.lib(self.BUFQ, "Moved")
        self.write({self.PROOF: COPYRIGHT + self.body(), notes: self.body()})
        self.base = self.commit("lib/Proof.v of 40 lines, and its text without the licence lines in NOTES.md")
        self.write({self.PROOF: None})
        git(self.head, "mv", notes, moved)
        self.commit("delete lib/Proof.v and move NOTES.md unchanged to lib/Moved.v")
        self.assertEqual(sorted(row.split("\t") for row in self.status()),
                         [["D", self.PROOF], ["R100", notes, moved]])
        self.fails_naming(*self.step(), (moved, self.PROOF))

    def test_a_proof_file_of_a_unit_with_no_record_moved_unchanged_with_a_deleted_file_s_text_fails(self):
        """The base already holds lib/Proof.v's text without its licence lines in lib/S.v of a unit with no record,
        and the change deletes lib/Proof.v and moves lib/S.v unchanged to curl/fuzz_bufq's lib/Q.v: an exact rename
        (R100, one blob id on both sides) whose base path is a proof file.  The step pairs its head with lib/Proof.v by
        its text all the same."""
        source, moved = self.lib(self.OTHER, "S"), self.lib(self.BUFQ, "Q")
        self.write({self.PROOF: COPYRIGHT + self.body(), source: self.body()})
        self.base = self.commit("lib/Proof.v of 40 lines, and its text without the licence lines in another unit")
        self.write({self.PROOF: None})
        git(self.head, "mv", source, moved)
        self.commit("delete lib/Proof.v and move the other unit's lib/S.v unchanged to lib/Q.v")
        self.assertEqual(sorted(row.split("\t") for row in self.status()),
                         [["D", self.PROOF], ["R100", source, moved]])
        self.fails_naming(*self.step(), (moved, self.PROOF))

    def test_no_change_compares_nothing_and_passes(self):
        """A run the plan did not route has BASE at HEAD."""
        rc, out = self.step(base=git(self.head, "rev-parse", "HEAD"))
        self.passes(rc, out)
        self.assertIn("nothing was compared", out)


# git as pr.yml's lps_pin step calls it: `git init -q DIR`, `git -C DIR fetch -q --depth=1 REPO COMMIT`, and
# `git -C DIR archive COMMIT -- <pathspecs>`, which hands back the model fixture in FAKE_LPS as a tar on stdout.
FAKE_GIT = r"""#!/usr/bin/env bash
if [ "$1" = init ]; then mkdir -p "${@: -1}"; exit 0; fi
[ "$1" = -C ] || exit 9
shift 2
case "$1" in
  fetch) exit 0 ;;
  archive) tar -c -C "$FAKE_LPS" . ;;
  *) exit 9 ;;
esac
"""
# docker as that step calls it, with every call written to FAKE_DOCKER_CALLS: the pull passes, the run that reads
# the model's files out of the image answers FAKE_IMAGE_PIN, the run of opam's list answers the lines of
# FAKE_OPAM_LIST, and the build exits as FAKE_DOCKER_RC says.  `docker buildx imagetools inspect` answers
# FAKE_IMAGE_LABELS (by default `null`, an image with no labels), or fails as FAKE_IMAGETOOLS_RC says.
FAKE_DOCKER = r"""#!/usr/bin/env bash
all=$*
printf '%s\n' "${all//$'\n'/ }" >> "$FAKE_DOCKER_CALLS"
case "$*" in 'buildx imagetools inspect '*)
  [ "${FAKE_IMAGETOOLS_RC:-0}" = 0 ] || exit "$FAKE_IMAGETOOLS_RC"
  printf '%s\n' "${FAKE_IMAGE_LABELS-null}"; exit 0 ;; esac
[ "$1" = run ] || exit 0
case "$*" in *'~opam/lps'*) printf '%s\n' "$FAKE_IMAGE_PIN"; exit 0 ;; esac
case "$*" in *' opam list '*) cat "$FAKE_OPAM_LIST"; exit 0 ;; esac
exit "${FAKE_DOCKER_RC:-0}"
"""
# gh as the lps_pin job's attestation steps call it, each call written to <FAKE_GH>/calls: `gh --version` answers
# FAKE_GH_VERSION, and `gh attestation verify ... --format json` answers <FAKE_GH>/attestation.json, or, when there
# is none, refuses as gh refuses a digest with no attestation.  With <FAKE_GH>/signed-by, "IDENTITY REF", the
# attestation was signed by that workflow identity on that ref, and gh refuses it as gh does unless the call asks
# for exactly that identity (--cert-identity) and that ref (--source-ref).
FAKE_ATTESTATION_GH = r"""#!/usr/bin/env bash
echo "gh $*" >> "$FAKE_GH/calls"
case $1 in
  --version) printf 'gh version %s (2026-10-01)\nhttps://github.com/cli/cli/releases/tag/v%s\n' \
               "$FAKE_GH_VERSION" "$FAKE_GH_VERSION" ;;
  attestation)
    [ "$2" = verify ] || exit 9
    [ -f "$FAKE_GH/attestation.json" ] || { echo "Error: no attestations found for ${3#oci://}" >&2; exit 1; }
    if [ -f "$FAKE_GH/signed-by" ]; then
      read -r identity ref < "$FAKE_GH/signed-by"
      case " $* " in *" --cert-identity $identity "*) ;; *)
        echo "Error: verifying with issuer \"sigstore\": expected SAN value to match the certificate's $identity" >&2
        exit 1 ;; esac
      case " $* " in *" --source-ref $ref "*) ;; *)
        echo "Error: expected SourceRepositoryRef to match the certificate's $ref" >&2; exit 1 ;; esac
    fi
    cat "$FAKE_GH/attestation.json" ;;
  *) exit 9 ;;
esac
"""


def attestation(*commits):
    """What `gh attestation verify --format json` prints on stdout for a digest with one attestation per commit: a
    JSON array of {attestation, verificationResult}, the latter sigstore-go's VerificationResult, whose
    signature.certificate is the certificate summary with its Fulcio extensions inline, sourceRepositoryDigest the
    commit images.yml built at (cli/cli v2.103.3, pkg/cmd/attestation/verification/sigstore.go:28-31; sigstore-go
    v1.3.0, pkg/verify/signed_entity.go:253-264, pkg/fulcio/certificate/summarize.go:26-30, extensions.go:111)."""
    signer = "https://github.com/acme/proofs/.github/workflows/images.yml@refs/heads/main"
    return json.dumps([{"attestation": {"bundle": {}},
                        "verificationResult": {
                            "mediaType": "application/vnd.dev.sigstore.verificationresult+json;version=0.1",
                            "statement": {"predicateType": "https://slsa.dev/provenance/v1"},
                            "signature": {"certificate": {
                                "certificateIssuer": "CN=sigstore-intermediate,O=sigstore.dev",
                                "subjectAlternativeName": signer, "buildSignerURI": signer,
                                "sourceRepositoryURI": "https://github.com/acme/proofs",
                                "sourceRepositoryDigest": c, "sourceRepositoryRef": "refs/heads/main"}},
                            "verifiedTimestamps": []}}
                       for c in commits])


def lps_tree_sha256(files):
    """The hash toolchain/checker.Dockerfile holds the model's files to: the SHA-256 of `sha256sum` over every file
    of the cut, by path in C order.  Written out here, not run as the step runs it, so that the step is checked
    against the rule and not against itself."""
    lines = "".join("%s  %s\n" % (hashlib.sha256(text.encode()).hexdigest(), path)
                    for path, text in sorted(files.items()))
    return hashlib.sha256(lines.encode()).hexdigest()


def write_wheel(path, name, extra=None):
    """A wheel of `name` 1.0 at path, holding one empty module, as pip installs one: its METADATA, WHEEL and RECORD."""
    import base64
    import zipfile
    info = "%s-1.0.dist-info" % name
    files = {"%s/__init__.py" % name: "", info + "/METADATA": "Metadata-Version: 2.1\nName: %s\nVersion: 1.0\n" % name,
             info + "/WHEEL": "Wheel-Version: 1.0\nGenerator: oft-tests\nRoot-Is-Purelib: true\nTag: py3-none-any\n"}
    files.update(extra or {})
    record = ""
    for rel, text in files.items():
        digest = base64.urlsafe_b64encode(hashlib.sha256(text.encode()).digest()).rstrip(b"=").decode()
        record += "%s,sha256=%s,%d\n" % (rel, digest, len(text.encode()))
    files[info + "/RECORD"] = record + info + "/RECORD,,\n"
    with zipfile.ZipFile(path, "w") as z:
        for rel, text in files.items():
            z.writestr(rel, text)


# A source distribution whose build backend is its own (pyproject.toml's backend-path), so pip builds it with nothing
# from an index: importing the backend writes a line to $MARKER, which is code of whoever wrote the package running on
# the runner, and its wheel then installs as any other.
PLANTED_BACKEND = textwrap.dedent("""\
    import base64, hashlib, os, zipfile
    with open(os.environ["MARKER"], "a") as f:
        f.write("the planted package's build hook ran\\n")
    INFO = "planted-1.0.dist-info"
    METADATA = "Metadata-Version: 2.1\\nName: planted\\nVersion: 1.0\\n"
    def get_requires_for_build_wheel(config_settings=None):
        return []
    def prepare_metadata_for_build_wheel(directory, config_settings=None):
        os.makedirs(os.path.join(directory, INFO))
        with open(os.path.join(directory, INFO, "METADATA"), "w") as f:
            f.write(METADATA)
        return INFO
    def build_wheel(directory, config_settings=None, metadata_directory=None):
        files = {"planted/__init__.py": "", INFO + "/METADATA": METADATA,
                 INFO + "/WHEEL": "Wheel-Version: 1.0\\nGenerator: t\\nRoot-Is-Purelib: true\\nTag: py3-none-any\\n"}
        record = ""
        for k, v in files.items():
            digest = base64.urlsafe_b64encode(hashlib.sha256(v.encode()).digest()).rstrip(b"=").decode()
            record += "%s,sha256=%s,%d\\n" % (k, digest, len(v))
        files[INFO + "/RECORD"] = record + INFO + "/RECORD,,\\n"
        name = "planted-1.0-py3-none-any.whl"
        with zipfile.ZipFile(os.path.join(directory, name), "w") as z:
            for k, v in files.items():
                z.writestr(k, v)
        return name
    """)


def write_sdist(path):
    """planted-1.0.tar.gz at path: PLANTED_BACKEND as its own build backend."""
    import tarfile
    stage = tempfile.mkdtemp(dir=os.path.dirname(path))
    top = os.path.join(stage, "planted-1.0")
    os.mkdir(top)
    pyproject = ('[build-system]\nrequires = []\nbuild-backend = "backend"\nbackend-path = ["."]\n'
                 '[project]\nname = "planted"\nversion = "1.0"\n')
    for rel, text in (("pyproject.toml", pyproject),
                      ("backend.py", PLANTED_BACKEND),
                      ("PKG-INFO", "Metadata-Version: 2.1\nName: planted\nVersion: 1.0\n")):
        with open(os.path.join(top, rel), "w") as f:
            f.write(text)
    with tarfile.open(path, "w:gz") as t:
        t.add(top, arcname="planted-1.0")


def sha256_of(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def pip_runs():
    return subprocess.run([sys.executable, "-m", "pip", "--version"], capture_output=True).returncode == 0


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class LpsPinVerifierTest(StandIn):
    """lps_pin reads release.yaml with PyYAML, which it installs before it judges anything.  That install runs no code
    of the change: the requirements are the base's (the plan's `base`, checked out on their own), never the
    change's tools/oft/requirements.txt, whose hashes the change writes itself, and which may name a source
    distribution whose build runs as the runner's user and can replace what the steps after it run (gh, jq, docker,
    the Python they import).  --only-binary :all: keeps the base's own named pins to wheels, which run nothing as
    they install.  release-check.yml's copy of the job is the same job
    (LpsPinTest.test_the_push_path_runs_the_same_job)."""

    def setUp(self):
        super().setUp()
        with open(os.path.join(self.dir, "bin", "python"), "w") as f:
            f.write('#!/bin/sh\nexec "%s" "$@"\n' % sys.executable)
        os.chmod(os.path.join(self.dir, "bin", "python"), 0o755)
        self.job = load("pr.yml")["jobs"]["lps_pin"]
        [self.install] = [s for s in self.job["steps"] if "pip install" in s.get("run", "")]
        self.files = os.path.join(self.dir, "files")
        os.mkdir(self.files)
        self.sdist = os.path.join(self.files, "planted-1.0.tar.gz")
        write_sdist(self.sdist)
        self.wheel = os.path.join(self.files, "honest-1.0-py3-none-any.whl")
        write_wheel(self.wheel, "honest")
        self.marker = os.path.join(self.dir, "marker")
        self.site = os.path.join(self.dir, "site")

    def requirements(self, side, text):
        path = os.path.join(self.dir, side, "tools", "oft", "requirements.txt")
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as f:
            f.write(text)

    def by_url(self, path):
        name = "planted" if path == self.sdist else "honest"
        return "%s @ file://%s --hash=sha256:%s\n" % (name, path, sha256_of(path))

    def run_install(self, **env):
        """The install step in the job's workspace, with pip installing into a directory of its own and reading no
        index: (its exit, its output, whether the planted build hook ran, the packages installed)."""
        env = dict({"MARKER": self.marker, "PIP_TARGET": self.site, "PIP_NO_INDEX": "1", "PIP_NO_CACHE_DIR": "1",
                    "PIP_DISABLE_PIP_VERSION_CHECK": "1"}, **env)
        code, out, _ = self.run_step(self.install["run"], env, cwd=self.dir)
        installed = sorted(n for n in os.listdir(self.site) if not n.endswith(".dist-info")) \
            if os.path.isdir(self.site) else []
        return code, out, os.path.exists(self.marker), installed

    @unittest.skipUnless(pip_runs(), "no pip beside this interpreter")
    def test_the_change_s_requirements_run_nothing(self):
        """A change whose requirements.txt names a source distribution, by URL and with its own hash: its build
        hook does not run, since the step reads the base's requirements."""
        self.requirements("head", self.by_url(self.sdist))
        self.requirements("verifier", self.by_url(self.wheel))
        code, out, ran, installed = self.run_install()
        self.assertEqual((code, ran, installed), (0, False, ["honest"]), out)

    @unittest.skipUnless(pip_runs(), "no pip beside this interpreter")
    def test_a_named_pin_of_the_base_installs_a_wheel_or_nothing(self):
        """The base's requirements name each package by version and every file of it by hash, a source
        distribution's among them: pip takes a wheel, and with none, fails rather than build one."""
        links = os.path.join(self.dir, "links")
        os.mkdir(links)
        shutil.copy(self.sdist, links)
        self.requirements("head", self.by_url(self.wheel))
        self.requirements("verifier", "planted==1.0 --hash=sha256:%s\n" % sha256_of(self.sdist))
        code, out, ran, installed = self.run_install(PIP_FIND_LINKS=links)
        self.assertNotEqual(code, 0, out)
        self.assertEqual((ran, installed), (False, []), out)

    def test_the_job_checks_out_the_base_s_requirements_alone_and_no_tools_of_the_change(self):
        checkouts = [s for s in self.job["steps"] if s.get("uses", "").startswith("actions/checkout@")]
        head = next(s for s in checkouts if s["with"]["path"] == "head")
        self.assertNotIn("tools", head["with"]["sparse-checkout"])
        verifier = next(s for s in checkouts if s["with"]["path"] == "verifier")
        self.assertEqual(verifier["with"], {"path": "verifier", "ref": "${{ needs.plan.outputs.base }}",
                                            "persist-credentials": False, "sparse-checkout-cone-mode": False,
                                            "sparse-checkout": "/tools/oft/requirements.txt\n"})
        self.assertEqual(self.install["run"],
                         "python -m pip install --quiet --require-hashes --only-binary ':all:' "
                         "-r verifier/tools/oft/requirements.txt")
        for s in self.job["steps"]:
            self.assertNotIn("head/tools", str(s))
        # the base each plan job hands it: pr.yml's the router's, release-check.yml's main before the push
        self.assertEqual(load("pr.yml")["jobs"]["plan"]["outputs"]["base"], "${{ steps.base.outputs.base }}")
        self.assertEqual(load("release-check.yml")["jobs"]["plan"]["outputs"]["base"],
                         "${{ steps.lps_pin.outputs.base }}")

    BASE_STEP = "the plan named a commit before this change to take the verifier's requirements from (fail closed)"

    def test_with_no_commit_before_the_change_the_job_fails_before_it_checks_anything_out(self):
        """No base, a base that is no commit id, and a base that is this run's own commit (pr.yml's plan names the
        pushed commit itself for a push with no base to compare with) fail the job's first step after the change's
        checkout, before the verifier's checkout, which given no ref would check out this run's own commit."""
        head = os.path.join(self.dir, "head")
        os.mkdir(head)
        git(head, "init", "-q")
        git(head, "commit", "-q", "--allow-empty", "-m", "the commit before")
        before = git(head, "rev-parse", "HEAD")
        git(head, "commit", "-q", "--allow-empty", "-m", "this change")
        here = git(head, "rev-parse", "HEAD")
        for workflow in ("pr.yml", "release-check.yml"):
            job = load(workflow)["jobs"]["lps_pin"]
            s = step(job, self.BASE_STEP)
            self.assertEqual(s["env"], {"BASE": "${{ needs.plan.outputs.base }}"})
            for base, code, said in (("", 1, "the plan named no commit before this change"),
                                     ("main", 1, "the plan named no commit before this change"),
                                     (here, 1, "the plan's base is this run's own commit %s" % here),
                                     (before, 0, "the verifier's requirements come from %s" % before)):
                with self.subTest(workflow=workflow, base=base):
                    rc, out, _ = self.run_step(s["run"], {"BASE": base}, cwd=self.dir)
                    self.assertEqual(rc, code, out)
                    self.assertIn(said, out)
            names = [x.get("name") or x.get("with", {}).get("path") for x in job["steps"]]
            self.assertEqual(names[names.index("head") + 1:names.index("head") + 3], [self.BASE_STEP, "verifier"])


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class LpsPinTest(StandIn):
    """pr.yml's lps_pin job, the one job that holds a change to release.yaml, toolchain/ or theories/ to the model and
    the checker and runner images this repository pins: the two pins are one hash of the model's files; the checker
    image release.yaml names carries images.yml's attestation from main; on a repin, the commit that attestation
    names has this change's toolchain/checker.Dockerfile and toolchain/lps-core.paths, and the image holds the opam
    packages that Dockerfile pins; when theories/ changes or the image moves, the change's theories/ compiles in that
    image; and the runner image carries images.yml's attestation from main and, on a runner repin, was built at a
    commit holding this change's toolchain/runner.Dockerfile.
    Before it, a theories/ change the controls did not reach was compiled by nothing: #2360, a draft whose one change
    was theories/Premises.v written against LPS 727298f3, planned 0 units, skipped every build job and passed
    required and main-gate (run 42509915684, 2026-11-08; Dispatch issue OSSV-440); and a change could repin
    images.checker, or change toolchain/, with no check that compared the image with the Dockerfile at all.  And a
    release pull request could repin images.runner, the image every counterexample and finding runs in, to any image
    (in which a fake counterexample passes) with no check before the merge at all: only images.yml's daily
    verify-pins read its attestation, after the fact."""

    MODEL = {"dune-project": "(lang dune 3.23)\n", "theories/Spec.v": "Definition a := 1.\n"}
    COMMIT = "f" * 40
    REPOSITORY_URL = "https://github.com/theorem-labs/rocq-linux-process-semantics"
    IMAGE = "ghcr.io/theorem-labs/oss-fuzz-theorems-checker@sha256:" + "0a" * 32
    # the Dockerfile's OPAM_PACKAGES, and what the image's opam lists: those, at the same versions, with the compiler,
    # the dependencies opam chose and the model the build pinned
    OPAM = "conf-g++.1.0 dune.3.23.0 rocq-core.9.2.0 rocq-stdpp.1.13.0 rocq-stdpp-bitvector.1.13.0"
    INSTALLED = ["base-threads.base", "conf-g++.1.0", "dune.3.23.0", "ocaml.4.14.2", "rocq-core.9.2.0",
                 "rocq-linux-process-semantics-core.dev", "rocq-stdpp.1.13.0", "rocq-stdpp-bitvector.1.13.0",
                 "zarith.1.14"]
    TOOLCHAIN = ("toolchain/checker.Dockerfile", "toolchain/lps-core.paths")
    RUNNER = "ghcr.io/theorem-labs/oss-fuzz-theorems-runner@sha256:" + "2b" * 32
    RUNNER_DOCKERFILE = "toolchain/runner.Dockerfile"
    # tests/toy/, the runner's self-test, as the change holds it: the script the build runs and a hash it checks
    TOY = {"tests/toy/make_elf.py": "import sys\nopen(sys.argv[2], 'wb').write(b'ELF')\n",
           "tests/toy/exit0/exit0.plain.sha256": "0" * 64 + "  exit0.plain\n"}
    # each image's attestation step: its name, and what its IMAGE and REPIN read
    ATTESTATION_STEPS = {
        "checker": ("images.yml built and attested the pinned checker image on main, from this change's toolchain/ on "
                    "a repin", "${{ steps.image.outputs.image }}", "${{ needs.plan.outputs.checker_repin }}"),
        "runner": ("images.yml built and attested the pinned runner image on main, from this change's "
                   "toolchain/runner.Dockerfile and tests/toy/ on a repin", "${{ steps.runner_image.outputs.image }}",
                   "${{ needs.plan.outputs.runner_repin }}")}
    RUNNER_IMAGE_STEP = "the runner image release.yaml pins, by digest (fail closed)"
    RUNNER_LABEL_STEP = "on a runner repin, the runner image names the git tree of the tools/oft it carries"
    MAIN = "https://github.com/acme/proofs/.github/workflows/images.yml@refs/heads/main"

    def setUp(self):
        super().setUp()
        self.head = os.path.join(self.dir, "head")
        self.lps = os.path.join(self.dir, "model")
        for path, text in self.MODEL.items():
            full = os.path.join(self.lps, path)
            os.makedirs(os.path.dirname(full), exist_ok=True)
            with open(full, "w") as f:
                f.write(text)
        # `python` is the setup-python step's on the runner; here it is the interpreter running these tests, and
        # git and docker are the stand-ins above.  The steps that read git repositories run with real git instead,
        # from real-git-bin, which holds the same python and docker, and the stand-in gh and sleep.
        python = '#!/bin/sh\nexec "%s" "$@"\n' % sys.executable
        self.real_git_bin = os.path.join(self.dir, "real-git-bin")
        os.mkdir(self.real_git_bin)
        for where, text in ((os.path.join(self.dir, "bin", "git"), FAKE_GIT),
                            (os.path.join(self.dir, "bin", "docker"), FAKE_DOCKER),
                            (os.path.join(self.dir, "bin", "python"), python),
                            (os.path.join(self.real_git_bin, "docker"), FAKE_DOCKER),
                            (os.path.join(self.real_git_bin, "python"), python),
                            (os.path.join(self.real_git_bin, "gh"), FAKE_ATTESTATION_GH),
                            (os.path.join(self.real_git_bin, "sleep"), FAKE_SLEEP)):
            with open(where, "w") as f:
                f.write(text)
            os.chmod(where, 0o755)
        self.calls_file = os.path.join(self.dir, "docker-calls")
        self.job = load("pr.yml")["jobs"]["lps_pin"]

    def run_with_real_git(self, text, env, cwd=None):
        """run_step with real git on PATH in place of the stand-in."""
        standing, self.path = self.path, self.real_git_bin + os.pathsep + os.environ["PATH"]
        try:
            return self.run_step(text, env, cwd=cwd)
        finally:
            self.path = standing

    def write_head(self, pin, commit=None, repository=None, opam=None, dockerfile_tail="", runner=None, toy=True):
        """head/'s release.yaml, toolchain/ files and, unless toy is False, tests/toy/ (which False removes)."""
        for path, text in (
                ("release.yaml", "semantics:\n  repository: %s\n  commit: %s\nimages:\n  checker: %s\n  runner: %s\n"
                 % (repository or self.REPOSITORY_URL, commit or self.COMMIT, self.IMAGE,
                    self.RUNNER if runner is None else runner)),
                ("toolchain/checker.Dockerfile", 'FROM scratch\nARG OPAM_PACKAGES="%s"\n%sARG LPS_TREE_SHA256=%s\n'
                 % (self.OPAM if opam is None else opam, dockerfile_tail, pin)),
                ("toolchain/lps-core.paths", "# the model's files\ntheories\ndune-project\n"),
                (self.RUNNER_DOCKERFILE,
                 "FROM scratch AS runner\nCOPY --from=oft-tools / /opt/oss-fuzz-theorems/tools/oft/\n"),
                *(self.TOY.items() if toy else ())):
            full = os.path.join(self.head, path)
            os.makedirs(os.path.dirname(full), exist_ok=True)
            with open(full, "w") as f:
                f.write(text)
        if not toy:
            shutil.rmtree(os.path.join(self.head, "tests", "toy"), ignore_errors=True)

    def pin_step(self, pin, **given):
        self.write_head(pin, **given)
        text = step(self.job, "release.yaml's model and toolchain/checker.Dockerfile's LPS_TREE_SHA256 are one pin")
        rc, out, summary = self.run_step(text["run"], {"RUNNER_TEMP": tempfile.mkdtemp(dir=self.dir),
                                                       "FAKE_LPS": self.lps}, cwd=self.head)
        return rc, out + summary

    def compile_step(self, rc_of_build, pin=None, image_pin=None, theories="true", repin="false"):
        """The compile step with the pin the step before it gave and the hash the image's own model files answer
        (by default the same), a build that exits as rc_of_build says, and the plan's answers: by default a
        theories/ change that leaves images.checker as the base's."""
        pin = lps_tree_sha256(self.MODEL) if pin is None else pin
        text = step(self.job, "this change's theories/ compiles against the model the pin names")
        self.assertEqual((text["env"]["THEORIES"], text["env"]["REPIN"]),
                         ("${{ needs.plan.outputs.theories }}", "${{ needs.plan.outputs.checker_repin }}"))
        if os.path.exists(self.calls_file):
            os.remove(self.calls_file)
        rc, out, summary = self.run_step(text["run"], {"IMAGE": self.IMAGE, "GITHUB_WORKSPACE": self.dir,
                                                       "PIN": pin, "THEORIES": theories, "REPIN": repin,
                                                       "FAKE_IMAGE_PIN": pin if image_pin is None else image_pin,
                                                       "FAKE_DOCKER_RC": str(rc_of_build),
                                                       "FAKE_DOCKER_CALLS": self.calls_file})
        return rc, out + summary, self.docker_calls()

    def docker_calls(self):
        if not os.path.exists(self.calls_file):
            return []
        with open(self.calls_file) as f:
            return f.read().splitlines()

    def opam_step(self, installed=None, repin="true", **given):
        """The step that reads the image's opam packages, on a head written by write_head(**given), with the image's
        opam listing `installed` (by default INSTALLED)."""
        self.write_head(lps_tree_sha256(self.MODEL), **given)
        listing = os.path.join(self.dir, "opam-list")
        with open(listing, "w") as f:
            f.write("".join(line + "\n" for line in (self.INSTALLED if installed is None else installed)))
        text = step(self.job, "on a repin, the checker image holds each opam package toolchain/checker.Dockerfile "
                              "pins, at its version")
        self.assertEqual((text["env"]["IMAGE"], text["env"]["REPIN"]),
                         ("${{ steps.image.outputs.image }}", "${{ needs.plan.outputs.checker_repin }}"))
        self.assertEqual(text["working-directory"], "head")
        if os.path.exists(self.calls_file):
            os.remove(self.calls_file)
        rc, out, summary = self.run_step(text["run"], {"IMAGE": self.IMAGE, "REPIN": repin,
                                                       "FAKE_OPAM_LIST": listing,
                                                       "FAKE_DOCKER_CALLS": self.calls_file}, cwd=self.head)
        return rc, out + summary, self.docker_calls()

    def attestation_step(self, repin, built=None, attested=True, gh_version="2.83.0",
                         repository="acme/proofs", key="checker", signed_by=None, toy=True):
        """The attestation step of the image `key` (checker or runner), as it runs on the runner: in head/, a git
        checkout of one commit holding write_head's files (tests/toy/ among them unless toy is False); against this
        repository, a git repository served over file:// whose main has one commit, images.yml's build, holding
        head's toolchain/checker.Dockerfile, toolchain/lps-core.paths, toolchain/runner.Dockerfile and tests/toy/
        files unless `built` gives other text for them or names more files (None: no such file); with real git and
        the stand-in gh, which verifies the image with that commit as its attestation's when `attested` is True,
        answers `attested` itself when it is text, and refuses the image when it is False; with signed_by, (identity,
        ref), the attestation was signed by that workflow identity on that ref, and gh refuses it unless the step asks
        for both.  (its exit, its output and summary, that commit)."""
        self.write_head(lps_tree_sha256(self.MODEL), toy=toy)
        git(self.head, "init", "-q")
        git(self.head, "add", "-A")
        git(self.head, "commit", "-q", "--allow-empty", "-m", "the change")
        work = tempfile.mkdtemp(dir=self.dir)
        for path in dict.fromkeys(self.TOOLCHAIN + (self.RUNNER_DOCKERFILE,) + tuple(self.TOY) + tuple(built or ())):
            text = None
            if os.path.exists(os.path.join(self.head, path)):
                with open(os.path.join(self.head, path)) as src:
                    text = src.read()
            text = (built or {}).get(path, text)
            if text is None:
                continue
            full = os.path.join(work, path)
            os.makedirs(os.path.dirname(full), exist_ok=True)
            with open(full, "w") as f:
                f.write(text)
        git(work, "init", "-q")
        git(work, "add", "-A")
        git(work, "commit", "-qm", "main, where images.yml built the image")
        commit = git(work, "rev-parse", "HEAD")
        server = tempfile.mkdtemp(dir=self.dir)
        git(self.dir, "clone", "-q", "--bare", work, os.path.join(server, "acme", "proofs.git"))
        answer = os.path.join(self.api, "attestation.json")
        for name in ("attestation.json", "calls", "signed-by"):
            if os.path.exists(os.path.join(self.api, name)):
                os.remove(os.path.join(self.api, name))
        if attested is not False:
            with open(answer, "w") as f:
                f.write(attestation(commit) if attested is True else attested)
        if signed_by is not None:
            with open(os.path.join(self.api, "signed-by"), "w") as f:
                f.write("%s %s\n" % signed_by)
        self.runner_temp = tempfile.mkdtemp(dir=self.dir)
        name, image, repin_of = self.ATTESTATION_STEPS[key]
        text = step(self.job, name)
        self.assertEqual(text["env"], {"GH_TOKEN": "${{ github.token }}", "IMAGE": image, "REPIN": repin_of})
        self.assertEqual(text["working-directory"], "head")
        rc, out, summary = self.run_with_real_git(text["run"], {
            "GH_TOKEN": "t", "IMAGE": self.IMAGE if key == "checker" else self.RUNNER, "REPIN": repin,
            "RUNNER_TEMP": self.runner_temp, "GITHUB_SERVER_URL": "file://" + server, "GITHUB_REPOSITORY": repository,
            "FAKE_GH_VERSION": gh_version}, cwd=self.head)
        return rc, out + summary, commit

    def test_the_job_waits_for_the_plan_alone_and_runs_on_a_change_to_the_pins_or_theories(self):
        """Not for lint: a draft skips lint and with it the controls, the one other job that compiles theories/.
        It reads the image's attestation, which needs the permission to."""
        self.assertEqual(self.job["needs"], ["plan"])
        self.assertEqual(" ".join(self.job["if"].split()),
                         "${{ !cancelled() && needs.plan.result == 'success' "
                         "&& needs.plan.outputs.lps_pin == 'true' }}")
        self.assertEqual(self.job["permissions"], {"contents": "read", "packages": "read", "attestations": "read"})

    def test_the_two_pins_of_one_model_pass_and_both_values_are_said(self):
        want = lps_tree_sha256(self.MODEL)
        rc, out = self.pin_step(want)
        self.assertEqual(rc, 0, out)
        self.assertIn(want, out)
        self.assertIn(self.COMMIT, out)
        self.assertIn("the two pins are one model", out)

    def test_two_pins_of_different_models_fail_and_name_both_hashes(self):
        """A release.yaml whose semantics.commit is not the model the checker image was built from, or a
        LPS_TREE_SHA256 left behind by a re-pin: either way the pin a proof is judged against is not one model."""
        other = "7a" * 32
        rc, out = self.pin_step(other)
        self.assertEqual(rc, 1, out)
        self.assertIn(lps_tree_sha256(self.MODEL), out)
        self.assertIn(other, out)
        self.assertIn("the two pins name different models", out)

    def test_a_pin_or_a_commit_the_step_cannot_read_fails(self):
        """And a Dockerfile that declares the argument twice: the second declaration is the one the image build
        hashes against, so a check of the first would say nothing of the model the image holds."""
        good = lps_tree_sha256(self.MODEL)
        for name, given in (("no sha256 pin", {"pin": "not-a-hash"}),
                            ("a commit that is no commit", {"pin": good, "commit": "HEAD"}),
                            ("another model repository", {"pin": good,
                                                          "repository": "https://github.com/acme/model"}),
                            ("a second, empty declaration", {"pin": good + "\nARG LPS_TREE_SHA256="}),
                            ("a second declaration of another hash",
                             {"pin": good + "\nARG LPS_TREE_SHA256=" + "7a" * 32})):
            with self.subTest(case=name):
                self.assertEqual(self.pin_step(**given)[0], 1)

    def test_an_image_built_from_another_model_fails_before_anything_is_compiled(self):
        """The digest alone says nothing of the model inside the image: a change could move semantics.commit and
        LPS_TREE_SHA256 together and leave images.checker at an image built from the model before them.  The
        image's own files answer for it, and no build runs when they are another model's."""
        rc, out, calls = self.compile_step(0, image_pin="7a" * 32)
        self.assertEqual(rc, 1, out)
        self.assertIn("was built from another model", out)
        self.assertEqual([c for c in calls if "dune build" in c], [], calls)

    def test_theories_that_does_not_compile_against_the_pinned_model_fails(self):
        """#2360's shape: theories/ written against another LPS.  The build runs in the pinned image with no
        network, and its failure is the job's."""
        rc, out, calls = self.compile_step(1)
        self.assertEqual(rc, 1, out)
        self.assertIn("does not compile against the model release.yaml and toolchain/checker.Dockerfile pin", out)
        self.assertTrue(any(c.startswith("pull ") and self.IMAGE in c for c in calls), calls)
        build = next(c for c in calls if "dune build" in c)
        self.assertIn("--network none", build)
        self.assertIn(self.IMAGE, build)
        self.assertIn("dune build --root . @theories/default", build)
        # and every theory must leave its .vo: the alias passes over a theories/ no dune file builds
        self.assertIn("_build/default/${v%.v}.vo", build)

    def test_theories_that_compiles_against_the_pinned_model_passes(self):
        rc, out, _ = self.compile_step(0)
        self.assertEqual(rc, 0, out)
        self.assertIn("theories/ compiles against the pinned model", out)

    def test_the_pin_step_hands_the_hash_to_the_compile_step(self):
        """The compile step holds the image to it, and refuses to run on anything that is not a hash."""
        want = lps_tree_sha256(self.MODEL)
        self.assertEqual(self.pin_step(want)[0], 0)
        self.assertEqual(self.outputs().get("pin"), want)
        self.assertEqual(step(self.job, "this change's theories/ compiles against the model the pin names")
                         ["env"]["PIN"], "${{ steps.pin.outputs.pin }}")
        rc, out, calls = self.compile_step(0, pin="")
        self.assertEqual(rc, 1, out)
        self.assertEqual(calls, [], calls)

    def test_a_change_that_moves_neither_theories_nor_the_image_pulls_and_compiles_nothing(self):
        """A change to toolchain/ or release.yaml that leaves images.checker as the base's: the image's model and
        theories/ are as the base had them, so nothing is pulled or built.  A repin alone holds the new image's own
        model files to the pin and compiles theories/ in it.  An answer the plan did not give fails."""
        rc, out, calls = self.compile_step(0, theories="false", repin="false")
        self.assertEqual((rc, calls), (0, []), out)
        rc, out, calls = self.compile_step(0, theories="false", repin="true", image_pin="7a" * 32)
        self.assertEqual(rc, 1, out)
        self.assertIn("was built from another model", out)
        self.assertEqual([c for c in calls if "dune build" in c], [], calls)
        rc, out, calls = self.compile_step(0, theories="false", repin="true")
        self.assertEqual(rc, 0, out)
        self.assertTrue(any("dune build --root . @theories/default" in c for c in calls), calls)
        for theories, repin in (("", "false"), ("false", ""), ("yes", "true"), ("true", "no")):
            with self.subTest(theories=theories, repin=repin):
                rc, out, calls = self.compile_step(0, theories=theories, repin=repin)
                self.assertEqual((rc, calls), (1, []), out)

    def test_a_repinned_image_that_holds_each_pinned_opam_package_at_its_version_passes(self):
        """The image's opam lists more than OPAM_PACKAGES (the compiler, the dependencies opam chose, the model), and
        each package OPAM_PACKAGES names is among them at its version; the list alone passes too.  opam runs in the
        pinned image with no network."""
        for name, installed in (("with what else the build installed", self.INSTALLED),
                                ("exactly the pinned list", self.OPAM.split())):
            with self.subTest(case=name):
                rc, out, calls = self.opam_step(installed=installed)
                self.assertEqual(rc, 0, out)
                self.assertIn("holds each of the 5 opam packages toolchain/checker.Dockerfile pins", out)
                run = [c for c in calls if c.startswith("run ")]
                self.assertEqual(run, ["run --rm --network none %s opam list --installed --short --columns=package"
                                       % self.IMAGE], calls)

    def test_a_repinned_image_missing_a_pinned_opam_package_or_at_another_version_is_refused(self):
        """Each package named, with what the image holds instead: an image of another Rocq, or one whose build
        left a pinned library out, is not the image the Dockerfile defines."""
        def without(prefix):
            return [p for p in self.INSTALLED if not p.startswith(prefix)]
        older = [p.replace("rocq-core.9.2.0", "rocq-core.9.1.0") for p in self.INSTALLED]
        for name, installed, named in (
                ("rocq-core missing", without("rocq-core."),
                 "holds no opam package rocq-core, and toolchain/checker.Dockerfile pins rocq-core.9.2.0"),
                ("another rocq-core", older,
                 "holds rocq-core.9.1.0, and toolchain/checker.Dockerfile pins rocq-core.9.2.0"),
                # rocq-stdpp-bitvector's name begins with rocq-stdpp's: it does not stand for it
                ("rocq-stdpp missing beside rocq-stdpp-bitvector", without("rocq-stdpp."),
                 "holds no opam package rocq-stdpp, and toolchain/checker.Dockerfile pins rocq-stdpp.1.13.0"),
                ("nothing installed", [], "holds no opam package conf-g++, and")):
            with self.subTest(case=name):
                rc, out, _ = self.opam_step(installed=installed)
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::the checker image %s %s" % (self.IMAGE, named), out)

    def test_an_opam_package_list_the_step_cannot_read_fails_before_the_image_runs(self):
        """A second ARG OPAM_PACKAGES with a value would be the list a stage of the build installs; a check of the
        first would say nothing of it."""
        for name, given in (("a second list", {"dockerfile_tail": 'ARG OPAM_PACKAGES="rocq-core.9.1.0"\n'}),
                            ("an empty list", {"opam": ""})):
            with self.subTest(case=name):
                rc, out, calls = self.opam_step(**given)
                self.assertEqual((rc, calls), (1, []), out)
        rc, out, _ = self.opam_step(opam="rocq-core " + self.OPAM)
        self.assertEqual(rc, 1, out)
        self.assertIn("OPAM_PACKAGES names 'rocq-core', not NAME.VERSION", out)

    def test_an_image_left_as_the_base_s_has_no_package_read(self):
        rc, out, calls = self.opam_step(installed=[], repin="false")
        self.assertEqual((rc, calls), (0, []), out)
        rc, out, calls = self.opam_step(repin="")
        self.assertEqual((rc, calls), (1, []), out)

    def test_a_repin_to_an_image_built_from_this_change_s_toolchain_passes(self):
        """gh verifies the digest with images.yml's signer on main, as images.yml verifies a pin, and the commit
        the attestation names holds this change's two files."""
        rc, out, commit = self.attestation_step("true")
        self.assertEqual(rc, 0, out)
        self.assertIn("images.yml built %s on refs/heads/main at %s" % (self.IMAGE, commit), out)
        self.assertIn("built from this change's toolchain/checker.Dockerfile and toolchain/lps-core.paths", out)
        self.assertEqual([c for c in self.calls() if c.startswith("gh attestation")],
                         ["gh attestation verify oci://%s --repo acme/proofs --cert-identity "
                          "https://github.com/acme/proofs/.github/workflows/images.yml@refs/heads/main "
                          "--source-ref refs/heads/main --format json" % self.IMAGE])

    def test_a_repin_to_an_image_built_from_another_build_definition_is_refused(self):
        """Built and attested on main, but from another Dockerfile or another cut of the model: a rollback to an
        image of an older reviewed definition, such as one of stock Rocq 9.2.0, which accepts public proofs of False
        (Dispatch issue OSSV-644).  The refusal names the file and the commit the image was built at."""
        for path, text in (("toolchain/checker.Dockerfile",
                            'FROM scratch\nARG OPAM_PACKAGES="rocq-core.9.2.0"\nARG LPS_TREE_SHA256=%s\n'
                            % lps_tree_sha256(self.MODEL)),
                           ("toolchain/lps-core.paths", "# the model's files\ntheories\n")):
            with self.subTest(file=path):
                rc, out, commit = self.attestation_step("true", built={path: text})
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::%s was built from another %s than this change's: images.yml built it at %s"
                              % (self.IMAGE, path, commit), out)
                other = [p for p in self.TOOLCHAIN if p != path][0]
                self.assertNotIn("another %s" % other, out)

    def test_an_unchanged_digest_verifies_its_attestation_alone(self):
        """A toolchain/ change merged before its repin: the image release.yaml still names was built at the commit
        before, from the Dockerfile before, and that is no failure; nothing is fetched to compare.  Its attestation
        is still verified, and gh refusing it fails the step."""
        rc, out, _ = self.attestation_step("false", built={"toolchain/checker.Dockerfile": "FROM scratch\n# before\n"})
        self.assertEqual(rc, 0, out)
        self.assertIn("its attestation alone is verified here", out)
        self.assertFalse(os.path.exists(os.path.join(self.runner_temp, "built-from")))
        rc, out, _ = self.attestation_step("false", attested=False)
        self.assertEqual(rc, 1, out)

    def test_an_image_gh_refuses_is_refused_after_three_tries(self):
        """Three tries, 10 and 20 s apart, for a passing error of the API or the registry, then a refusal."""
        verify = "gh attestation verify oci://" + self.IMAGE
        for repin in ("true", "false"):
            with self.subTest(repin=repin):
                rc, out, _ = self.attestation_step(repin, attested=False)
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::gh attestation verify refused %s in 3 tries" % self.IMAGE, out)
                self.assertEqual([c.split(" --")[0] for c in self.calls() if not c.startswith("gh --version")],
                                 [verify, "sleep 10", verify, "sleep 20", verify])

    # what gh could print with exit 0 that names no commit images.yml built at
    NO_COMMIT = (("no attestation", "[]"),
                 ("no source commit", json.dumps([{"verificationResult": {"signature": {
                     "certificate": {"sourceRepositoryRef": "refs/heads/main"}}}}])),
                 ("a ref, not a commit", json.dumps([{"verificationResult": {"signature": {
                     "certificate": {"sourceRepositoryDigest": "main"}}}}])),
                 ("not JSON", "verified\n"))

    def test_a_repin_whose_attestation_names_no_commit_is_refused(self):
        for name, answer in self.NO_COMMIT:
            with self.subTest(case=name):
                rc, out, _ = self.attestation_step("true", attested=answer)
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::", out)

    def test_an_unchanged_digest_reads_nothing_gh_prints(self):
        """Where images.checker is unchanged, gh's exit status is the verdict: what it prints is never parsed, so
        a JSON shape this step did not expect cannot fail every run that merely touches release.yaml or
        toolchain/."""
        for name, answer in self.NO_COMMIT:
            with self.subTest(case=name):
                rc, out, _ = self.attestation_step("false", attested=answer)
                self.assertEqual(rc, 0, out)
                self.assertIn("its attestation alone is verified here", out)

    def test_a_gh_older_than_2_67_is_refused_before_it_verifies(self):
        """gh 2.49 to 2.66 could exit 0 for a digest with no attestation of the predicate type asked for
        (CVE-2025-25204), as images.yml's verify steps say."""
        rc, out, _ = self.attestation_step("true", gh_version="2.66.1")
        self.assertEqual(rc, 1, out)
        self.assertIn("gh 2.67 or newer is needed", out)
        self.assertEqual([c for c in self.calls() if c.startswith("gh attestation")], [])

    def test_the_public_repository_reads_no_attestation(self):
        """The attestations are kept in the repository images.yml ran in; the public repository holds none, and
        no token of it reads them."""
        rc, out, _ = self.attestation_step("true", attested=False, repository="theorem-labs/oss-verify-proofs")
        self.assertEqual(rc, 0, out)
        self.assertIn("theorem-labs/oss-verify-proofs holds no attestation of %s" % self.IMAGE, out)
        self.assertEqual(self.calls(), [])

    def test_a_repin_answer_the_plan_did_not_give_fails_before_gh_runs(self):
        for answer in ("", "yes"):
            with self.subTest(answer=answer):
                rc, out, _ = self.attestation_step(answer)
                self.assertEqual(rc, 1, out)
                self.assertEqual(self.calls(), [])

    # The runner image: release.yaml's images.runner, which tools/oft/ci/check-units.sh runs every counterexample and
    # finding in, taking the container's exit status as the verdict.
    def runner_image_step(self, runner):
        """The step that reads images.runner, on a head whose release.yaml pins `runner`: (its exit, its output, the
        image it hands to the runner's attestation step)."""
        self.write_head(lps_tree_sha256(self.MODEL), runner=runner)
        if os.path.exists(self.output):
            os.remove(self.output)
        text = step(self.job, self.RUNNER_IMAGE_STEP)
        self.assertEqual((text["id"], text["working-directory"]), ("runner_image", "head"))
        rc, out, summary = self.run_step(text["run"], {}, cwd=self.head)
        return rc, out + summary, self.outputs().get("image")

    def test_the_runner_s_steps_run_on_every_run_of_the_job_after_the_checker_s_attestation(self):
        """The job runs on every change to release.yaml, the one file that pins images.runner; the runner's three
        steps carry no `if` and no continue-on-error, so no run of the job passes with the runner unread.  Its value
        and attestation steps come after the checker's attestation step and before the job signs in to ghcr.io, and
        its label step right after the sign-in.  Each plan job hands the job its runner_repin."""
        names = [s.get("name") for s in self.job["steps"]]
        at = names.index(self.ATTESTATION_STEPS["checker"][0])
        self.assertEqual(names[at + 1:at + 5], [self.RUNNER_IMAGE_STEP, self.ATTESTATION_STEPS["runner"][0],
                                                "sign in to ghcr.io, where the pinned images are",
                                                self.RUNNER_LABEL_STEP])
        for name in (self.RUNNER_IMAGE_STEP, self.ATTESTATION_STEPS["runner"][0], self.RUNNER_LABEL_STEP):
            self.assertEqual({"if", "continue-on-error"} & set(step(self.job, name)), set())
        self.assertNotIn("continue-on-error", self.job)
        self.assertEqual(load("pr.yml")["jobs"]["plan"]["outputs"]["runner_repin"],
                         "${{ steps.reach.outputs.runner_repin }}")
        self.assertEqual(load("release-check.yml")["jobs"]["plan"]["outputs"]["runner_repin"],
                         "${{ steps.lps_pin.outputs.runner_repin }}")

    def test_the_runner_image_step_takes_the_runner_s_own_name_by_digest_alone(self):
        """images.runner as images.yml pushes it, by digest.  Another image of this organisation (the checker, a
        builder, a name that begins as the runner's), another owner, a tag, a short digest or no value is refused,
        and nothing is handed to the attestation step."""
        rc, out, handed = self.runner_image_step(self.RUNNER)
        self.assertEqual((rc, handed), (0, self.RUNNER), out)
        digest = "@sha256:" + "2b" * 32
        for name, value in (("the checker image", self.IMAGE),
                            ("a builder image", "ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain" + digest),
                            ("a name that begins as the runner's",
                             "ghcr.io/theorem-labs/oss-fuzz-theorems-runner-next" + digest),
                            ("another owner", "ghcr.io/acme/oss-fuzz-theorems-runner" + digest),
                            ("a tag", "ghcr.io/theorem-labs/oss-fuzz-theorems-runner:latest"),
                            ("a short digest", "ghcr.io/theorem-labs/oss-fuzz-theorems-runner@sha256:" + "2b" * 31),
                            ("no value", "")):
            with self.subTest(case=name):
                rc, out, handed = self.runner_image_step(value)
                self.assertEqual((rc, handed), (1, None), out)
                self.assertIn("::error::release.yaml must name the runner image by digest in images.runner", out)

    def test_a_runner_repin_to_an_image_built_from_this_change_s_runner_dockerfile_passes(self):
        """gh verifies the runner's digest with images.yml's signer on main, as it verifies the checker's, and the
        commit the attestation names holds this change's toolchain/runner.Dockerfile.  The checker's files at that
        commit are the checker's step to answer for, not this one's."""
        for name, built in (("this change's toolchain/", None),
                            ("another checker definition", {"toolchain/checker.Dockerfile": "FROM scratch\n# before\n",
                                                            "toolchain/lps-core.paths": None})):
            with self.subTest(case=name):
                rc, out, commit = self.attestation_step("true", built=built, key="runner")
                self.assertEqual(rc, 0, out)
                self.assertIn("images.yml built %s on refs/heads/main at %s" % (self.RUNNER, commit), out)
                for path in ("toolchain/runner.Dockerfile", "tests/toy"):
                    self.assertIn("%s: the one images.yml built %s from at %s" % (path, self.RUNNER, commit), out)
                self.assertIn("the repinned runner image was built from this change's toolchain/runner.Dockerfile "
                              "and tests/toy/", out)
                self.assertEqual([c for c in self.calls() if c.startswith("gh attestation")],
                                 ["gh attestation verify oci://%s --repo acme/proofs --cert-identity %s "
                                  "--source-ref refs/heads/main --format json" % (self.RUNNER, self.MAIN)])

    def test_a_runner_repin_to_an_image_built_from_another_runner_dockerfile_is_refused(self):
        """Built and attested on main, but from another toolchain/runner.Dockerfile, or at a commit that holds none:
        a rollback to an older runner, or an image of a definition this change is not reviewed with.  The refusal
        names the file and the commit the image was built at."""
        for name, text, there in (("another Dockerfile", "FROM scratch AS runner\n# older\n", None),
                                  ("no Dockerfile", None, "none")):
            with self.subTest(case=name):
                rc, out, commit = self.attestation_step("true", built={self.RUNNER_DOCKERFILE: text}, key="runner")
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::%s was built from another toolchain/runner.Dockerfile than this change's: "
                              "images.yml built it at %s, whose toolchain/runner.Dockerfile is %s"
                              % (self.RUNNER, commit, there or ""), out)
                self.assertNotIn("the repinned runner image was built", out)

    def test_a_runner_repin_to_an_image_built_from_another_tests_toy_is_refused(self):
        """tests/toy/ is the runner's self-test, and the build runs its make_elf.py as root in the stage the image
        ships, so a script there could rewrite qemu after its hash is checked: an image built at a commit whose
        tests/toy/ is not this change's, by any one file, or that has none where this change has one (or the other
        way round), is refused, with the same Dockerfile.  A tests/toy/ neither commit has is no difference."""
        script = "tests/toy/make_elf.py"
        for name, built, toy in (
                ("another make_elf.py", {script: self.TOY[script] + "import os; os.replace('q', '/usr/bin/q')\n"},
                 True),
                ("another recorded hash", {"tests/toy/exit0/exit0.plain.sha256": "1" * 64 + "  exit0.plain\n"}, True),
                ("a file more", {"tests/toy/exit0/extra.py": "print(1)\n"}, True),
                ("no tests/toy/ where the image was built", dict.fromkeys(self.TOY), True),
                ("no tests/toy/ in this change", dict(self.TOY), False)):
            with self.subTest(case=name):
                rc, out, commit = self.attestation_step("true", built=built, key="runner", toy=toy)
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::%s was built from another tests/toy than this change's: images.yml built it "
                              "at %s" % (self.RUNNER, commit), out)
                self.assertIn("toolchain/runner.Dockerfile: the one images.yml built", out)
                self.assertNotIn("the repinned runner image was built", out)
        rc, out, _ = self.attestation_step("true", built=dict.fromkeys(self.TOY), key="runner", toy=False)
        self.assertEqual(rc, 0, out)
        self.assertIn("tests/toy: the one images.yml built %s" % self.RUNNER, out)

    def runner_label_step(self, repin="true", labels=None, rc_of_inspect=0):
        """The runner's label step, with the stand-in docker answering `labels` (JSON text; None: no labels) for the
        image: (its exit, its output and summary, docker's calls)."""
        text = step(self.job, self.RUNNER_LABEL_STEP)
        self.assertEqual(text["env"], {"IMAGE": "${{ steps.runner_image.outputs.image }}",
                                       "REPIN": "${{ needs.plan.outputs.runner_repin }}"})
        if os.path.exists(self.calls_file):
            os.remove(self.calls_file)
        env = {"IMAGE": self.RUNNER, "REPIN": repin, "FAKE_DOCKER_CALLS": self.calls_file,
               "FAKE_IMAGETOOLS_RC": str(rc_of_inspect)}
        if labels is not None:
            env["FAKE_IMAGE_LABELS"] = labels
        rc, out, summary = self.run_step(text["run"], env, cwd=self.dir)
        return rc, out + summary, self.docker_calls()

    def test_a_repinned_runner_names_the_git_tree_of_the_tools_it_carries(self):
        """The `oft-tools` build context is the public repository's main, which this change does not hold, so it is
        not compared; images.yml labels each runner with the git tree of those tools, and a repinned runner must
        carry that label, a git tree id, read from the registry as images.yml's plan reads it."""
        tree = "e" * 40
        rc, out, calls = self.runner_label_step(labels=json.dumps({"oss-fuzz-theorems.tools.tree": tree,
                                                                   "oss-fuzz-theorems.tools.commit": "d" * 40}))
        self.assertEqual(rc, 0, out)
        self.assertIn("the runner image carries the tools/oft of git tree %s" % tree, out)
        self.assertEqual(calls, ["buildx imagetools inspect %s --format {{json .Image.Config.Labels}}" % self.RUNNER])
        for name, labels, rc_of_inspect in (
                ("no labels", None, 0),
                ("the commit label alone", json.dumps({"oss-fuzz-theorems.tools.commit": "d" * 40}), 0),
                ("a short tree", json.dumps({"oss-fuzz-theorems.tools.tree": "e" * 39}), 0),
                ("a tree id with more after it", json.dumps({"oss-fuzz-theorems.tools.tree": tree + "\nx"}), 0),
                ("not JSON", "labels", 0),
                ("the registry refuses", None, 1)):
            with self.subTest(case=name):
                rc, out, _ = self.runner_label_step(labels=labels, rc_of_inspect=rc_of_inspect)
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::", out)

    def test_an_unchanged_runner_has_no_label_read_and_an_unanswered_repin_fails(self):
        rc, out, calls = self.runner_label_step(repin="false")
        self.assertEqual((rc, calls), (0, []), out)
        for answer in ("", "yes"):
            with self.subTest(answer=answer):
                rc, out, calls = self.runner_label_step(repin=answer,
                                                        labels=json.dumps({"oss-fuzz-theorems.tools.tree": "e" * 40}))
                self.assertEqual((rc, calls), (1, []), out)

    def test_a_runner_digest_gh_refuses_is_refused_whether_or_not_the_change_moves_it(self):
        """No attestation: an image images.yml did not build, or one pushed by hand.  Three tries, then a refusal; a
        change that leaves the pin as its base's still verifies it, so a pin made before this step existed fails the
        next change to release.yaml, toolchain/ or theories/ rather than stand unread."""
        verify = "gh attestation verify oci://" + self.RUNNER
        for repin in ("true", "false"):
            with self.subTest(repin=repin):
                rc, out, _ = self.attestation_step(repin, attested=False, key="runner")
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::gh attestation verify refused %s in 3 tries: release.yaml's images.runner is "
                              "no image images.yml built and attested on main" % self.RUNNER, out)
                self.assertEqual([c.split(" --")[0] for c in self.calls() if not c.startswith("gh --version")],
                                 [verify, "sleep 10", verify, "sleep 20", verify])

    def test_a_runner_attestation_another_workflow_or_ref_signed_is_refused(self):
        """gh is asked for images.yml on refs/heads/main exactly, so an attestation made by another workflow, or by
        images.yml on another branch or a pull request's ref, is refused, whether or not the change moves the pin.
        images.yml's own on main passes."""
        other = "https://github.com/acme/proofs/.github/workflows/%s@%s"
        for repin in ("true", "false"):
            for name, signed_by, want in (
                    ("images.yml on main", (self.MAIN, "refs/heads/main"), 0),
                    ("another workflow on main", (other % ("release.yml", "refs/heads/main"), "refs/heads/main"), 1),
                    ("images.yml on another branch",
                     (other % ("images.yml", "refs/heads/runner"), "refs/heads/runner"), 1),
                    ("images.yml on a pull request's ref",
                     (other % ("images.yml", "refs/pull/7/merge"), "refs/pull/7/merge"), 1),
                    ("main's images.yml run for another ref", (self.MAIN, "refs/heads/runner"), 1)):
                with self.subTest(repin=repin, case=name):
                    rc, out, _ = self.attestation_step(repin, key="runner", signed_by=signed_by)
                    self.assertEqual(rc, want, out)
                    if want:
                        self.assertIn("::error::gh attestation verify refused %s in 3 tries" % self.RUNNER, out)

    def test_an_unchanged_runner_digest_verifies_its_attestation_alone(self):
        """A change that leaves images.runner as its base pins it, after a change to toolchain/runner.Dockerfile
        merged and before its repin: the image was built from the Dockerfile before, and that is no failure.  Its
        attestation is verified, nothing is fetched to compare, and nothing gh prints is read."""
        rc, out, _ = self.attestation_step("false", built={self.RUNNER_DOCKERFILE: "FROM scratch\n# before\n"},
                                           key="runner")
        self.assertEqual(rc, 0, out)
        self.assertIn("images.runner is unchanged by this change, and was held to its build definition when it was "
                      "pinned: its attestation alone is verified here", out)
        self.assertFalse(os.path.exists(os.path.join(self.runner_temp, "runner-built-from")))
        self.assertEqual([c for c in self.calls() if c.startswith("gh attestation")],
                         ["gh attestation verify oci://%s --repo acme/proofs --cert-identity %s "
                          "--source-ref refs/heads/main --format json" % (self.RUNNER, self.MAIN)])
        for name, answer in self.NO_COMMIT:
            with self.subTest(case=name):
                rc, out, _ = self.attestation_step("false", attested=answer, key="runner")
                self.assertEqual(rc, 0, out)

    def test_a_runner_repin_whose_attestation_names_no_commit_is_refused(self):
        for name, answer in self.NO_COMMIT:
            with self.subTest(case=name):
                rc, out, _ = self.attestation_step("true", attested=answer, key="runner")
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::", out)

    def test_the_runner_step_refuses_an_old_gh_and_an_answer_the_plan_did_not_give(self):
        rc, out, _ = self.attestation_step("true", gh_version="2.66.1", key="runner")
        self.assertEqual(rc, 1, out)
        self.assertIn("gh 2.67 or newer is needed", out)
        self.assertEqual([c for c in self.calls() if c.startswith("gh attestation")], [])
        for answer in ("", "yes"):
            with self.subTest(answer=answer):
                rc, out, _ = self.attestation_step(answer, key="runner")
                self.assertEqual(rc, 1, out)
                self.assertIn("the plan answered runner_repin '%s'" % answer, out)
                self.assertEqual(self.calls(), [])

    def test_the_public_repository_reads_no_runner_attestation(self):
        rc, out, _ = self.attestation_step("true", attested=False, repository="theorem-labs/oss-verify-proofs",
                                           key="runner")
        self.assertEqual(rc, 0, out)
        self.assertIn("theorem-labs/oss-verify-proofs holds no attestation of %s" % self.RUNNER, out)
        self.assertEqual(self.calls(), [])

    # The push path: release-check.yml is the status of main, and a commit reaches main without a pull request
    # run of this repository (a ruleset bypass, a push, the release cut), so it carries the same job.  The two
    # copies are held to one text here: a change to either is a change to both.
    def test_the_push_path_runs_the_same_job(self):
        """The whole job, key for key, not a list of keys to compare: a key added to one copy alone would be
        invisible to a list, and `continue-on-error: true` on this job is the one key that defeats the verdict,
        since a job that carries it reports success whatever it did (images.yml's verify-pins is held to the
        same rule, by name, above)."""
        self.assertEqual(load("release-check.yml")["jobs"]["lps_pin"], self.job)

    def push_path_verdict(self, **given):
        s = step(load("release-check.yml")["jobs"]["release-check"], "every job green, and every planned harness checked")
        values = {"UNITS": "0", "FULL": "false", "DEFERRED": "false", "CHECK_OF_RECORD": "", "QUEUE_RUNS": "",
                  "DRAFTS_LISTED": "false", "DRAFTS_RESULT": "skipped", "PLAN_RESULT": "success",
                  "CHECK_RESULT": "skipped", "LPS_PIN": "false", "LPS_PIN_RESULT": "skipped"}
        env = dict(values, **given)
        rc, out, summary = self.run_step(s["run"], {k: env[k] for k in s["env"]})
        return rc, out + summary

    def test_the_push_path_s_verdict_fails_a_change_to_the_pins_or_theories_the_job_did_not_pass(self):
        """release-check's collecting job reads the same pair, and a change to release.yaml, toolchain/ or theories/
        whose job did not pass is a failure there too; a commit that touches none of them leaves the job skipped."""
        wf = load("release-check.yml")
        self.assertIn("lps_pin", wf["jobs"]["release-check"]["needs"])
        s = step(wf["jobs"]["release-check"], "every job green, and every planned harness checked")
        self.assertEqual((s["env"]["LPS_PIN"], s["env"]["LPS_PIN_RESULT"]),
                         ("${{ needs.plan.outputs.lps_pin }}", "${{ needs.lps_pin.result }}"))
        for name, given, want in (
                ("no change to the pins or theories/, the job skipped", {}, 0),
                ("no change to the pins or theories/, yet the job ran", {"LPS_PIN_RESULT": "success"}, 1),
                ("the pins or theories/ changed, and the job passed", {"LPS_PIN": "true", "LPS_PIN_RESULT": "success"}, 0),
                # #2360's shape, reaching main without a pull request run
                ("theories/ changed, nothing compiled it", {"LPS_PIN": "true", "LPS_PIN_RESULT": "skipped"}, 1),
                ("the pins changed, the job failed", {"LPS_PIN": "true", "LPS_PIN_RESULT": "failure"}, 1),
                ("no lps_pin answer", {"LPS_PIN": ""}, 1)):
            with self.subTest(case=name):
                rc, out = self.push_path_verdict(**given)
                self.assertEqual(rc, want, out)

    RELEASE = "images:\n  checker: %s\n  runner: ghcr.io/theorem-labs/oss-fuzz-theorems-runner@sha256:%s\n"

    def push_path_plan_step(self, changed, parent_release=None, head_release=None, event="push", root=False,
                            parent_files=None, head_files=None, history=None, before=1, old_tip=None):
        """release-check's lps_pin plan step, as it runs after the plan step: in a checkout made as the plan job
        makes it, one commit deep and without blobs, of a commit holding head_release as release.yaml whose parent
        holds parent_release (no such file for None; with root, the commit has no parent), each with the other
        files given; or, with history, of the last of those commits, each (release.yaml, {path: text}), oldest
        first.  On a push, its `before` is the commit `before` commits back from the one checked out (all zeros
        where there is none: a push that made the branch), or the text given; with old_tip, it is a commit off the
        first one holding old_tip as release.yaml, which a force push replaced.  With the plan's changed paths
        (None: the plan wrote no list); for the event given, with the environment the workflow gives the step.
        (its exit, its output, its three answers)."""
        wf = load("release-check.yml")
        answers = ("lps_pin", "theories", "checker_repin", "runner_repin")
        self.assertEqual({k: wf["jobs"]["plan"]["outputs"][k] for k in answers},
                         {k: "${{ steps.lps_pin.outputs.%s }}" % k for k in answers})
        s = next(x for x in wf["jobs"]["plan"]["steps"] if x.get("id") == "lps_pin")
        # The step's environment is the workflow's own `env`: neither the plan job nor the step adds to it.
        self.assertNotIn("env", wf["jobs"]["plan"])
        self.assertNotIn("env", s)
        self.assertEqual(wf["env"], {"PYTHONDONTWRITEBYTECODE": "1",
                                     "EVENT_BASE": "${{ github.event_name == 'push' && github.event.before || '' }}"})
        if history is None:
            history = ([] if root else [(parent_release, parent_files or {})]) + [(head_release, head_files or {})]
        work = tempfile.mkdtemp(dir=self.dir)
        git(work, "init", "-q")

        def commit(text, files, message):
            for rel, body in dict(files, **{"release.yaml": text}).items():
                path = os.path.join(work, rel)
                if body is None:
                    if os.path.exists(path):
                        os.remove(path)
                else:
                    os.makedirs(os.path.dirname(path), exist_ok=True)
                    with open(path, "w") as f:
                        f.write(body)
            git(work, "add", "-A")
            git(work, "commit", "-q", "--allow-empty", "-m", message)
            return git(work, "rev-parse", "HEAD")
        shas = [commit(text, files, "commit %d" % i) for i, (text, files) in enumerate(history)]
        if old_tip is not None:
            git(work, "checkout", "-q", "-b", "replaced", shas[0])
            before = commit(old_tip, {}, "main before a force push")
            git(work, "checkout", "-q", "main")
        elif not isinstance(before, str):
            before = shas[-1 - before] if before < len(shas) else "0" * 40
        bare = os.path.join(tempfile.mkdtemp(dir=self.dir), "proofs.git")
        git(self.dir, "clone", "-q", "--bare", work, bare)
        git(bare, "config", "uploadpack.allowfilter", "true")
        git(bare, "config", "uploadpack.allowanysha1inwant", "true")
        # file://, so that the clone is a real fetch one commit deep and without blobs, as actions/checkout's
        checkout = os.path.join(tempfile.mkdtemp(dir=self.dir), "proofs")
        git(self.dir, "clone", "-q", "--depth", "1", "--filter=blob:none", "file://" + bare, checkout)
        self.assertEqual(git(checkout, "rev-parse", "HEAD"), shas[-1])
        if len(shas) > 1:
            self.assertEqual(git(checkout, "rev-parse", "--is-shallow-repository"), "true")
        tmp = tempfile.mkdtemp(dir=self.dir)
        if changed is not None:
            with open(os.path.join(tmp, "changed.txt"), "w") as f:
                f.write("".join(rel + "\n" for rel in changed))
        if os.path.exists(self.output):
            os.remove(self.output)
        env = {"RUNNER_TEMP": tmp, "GITHUB_EVENT_NAME": event, "PYTHONDONTWRITEBYTECODE": "1",
               "EVENT_BASE": before if event == "push" else ""}
        rc, out, _ = self.run_with_real_git(s["run"], env, cwd=checkout)
        got = self.outputs()
        return rc, out, (got.get("lps_pin"), got.get("theories"), got.get("checker_repin"))

    def test_the_push_path_reads_a_change_to_the_pins_or_theories_from_the_plan_s_diff(self):
        """pr.yml's reach step's answers for whether the job runs and compiles theories/, over the paths the plan
        found changed; an unwritten list means every path counts as changed, so the job runs rather than being
        skipped.  The image moved when this commit's images.checker is not the one main pinned before the push
        (here a push of this one commit, so its parent), whatever the list says; on a run by hand, and on a push
        that made the branch, the parent's.  A `before` or a parent that pins none, one the repository does not
        hold, and a commit with no parent, count as a repin."""
        here = self.RELEASE % (self.IMAGE, "2b" * 32)
        other_checker = self.RELEASE % (self.IMAGE.replace("0a" * 32, "1b" * 32), "2b" * 32)
        other_runner = self.RELEASE % (self.IMAGE, "3c" * 32)
        proof = "projects/zlib/fuzz/proofs/x/Proof.v"
        cases = [
            ("a theory", ["theories/Premises.v"], here, here, ("true", "true", "false")),
            ("a quoted name", ['"theories/a\\tb.v"'], here, here, ("true", "true", "false")),
            ("the checker's Dockerfile alone", ["toolchain/checker.Dockerfile"], here, here,
             ("true", "false", "false")),
            ("release.yaml, another checker", ["release.yaml"], here, other_checker, ("true", "false", "true")),
            ("release.yaml, another runner", ["release.yaml"], here, other_runner, ("true", "false", "false")),
            ("release.yaml, where the parent has none", ["release.yaml"], None, here, ("true", "false", "true")),
            ("a proof alone", [proof], here, here, ("false", "false", "false")),
            ("a name that only starts like theories/", ["theories-notes/x.md"], here, here,
             ("false", "false", "false")),
            ("a file named release.yaml elsewhere", ["docs/release.yaml"], here, here, ("false", "false", "false"))]
        for name, changed, parent_release, head_release, want in cases:
            with self.subTest(case=name):
                rc, out, got = self.push_path_plan_step(changed, parent_release, head_release)
                self.assertEqual((rc, got), (0, want), out)
        for event in ("push", "workflow_dispatch"):
            for name, parent_release, head_release, want in (
                    ("no list, the parent pins the same image", here, here, ("true", "true", "false")),
                    ("no list, the parent pins another image", other_checker, here, ("true", "true", "true")),
                    ("no list, the parent holds no release.yaml", None, here, ("true", "true", "true"))):
                with self.subTest(case=name, event=event):
                    rc, out, got = self.push_path_plan_step(None, parent_release, head_release, event=event)
                    self.assertEqual((rc, got), (0, want), out)
            with self.subTest(case="no list, no parent", event=event):
                rc, out, got = self.push_path_plan_step(None, head_release=here, event=event, root=True)
                self.assertEqual((rc, got), (0, ("true", "true", "true")), out)
                self.assertIn("this commit has no parent", out)
        for name, before, want in (("a push that made the branch: the parent pins the same image", "0" * 40, "false"),
                                   ("a before the repository does not hold", "d" * 40, "true")):
            with self.subTest(case=name):
                rc, out, got = self.push_path_plan_step(["release.yaml"], here, here, before=before)
                self.assertEqual((rc, got), (0, ("true", "false", want)), out)

    def test_the_push_path_names_the_commit_whose_requirements_the_job_installs(self):
        """The `base` the lps_pin job takes its tools' requirements from (LpsPinVerifierTest): main before the push,
        or this commit's parent on a run by hand, fetched from the remote (the checkout is one commit deep).  Never
        this commit: with no commit before it, or one the repository does not hold, `base` is empty and the job's
        first step fails.  Nothing when the job does not run."""
        here = self.RELEASE % (self.IMAGE, "2b" * 32)
        for event in ("push", "workflow_dispatch"):
            with self.subTest(event=event):
                rc, out, _ = self.push_path_plan_step(["theories/Premises.v"], here, here, event=event)
                self.assertEqual(rc, 0, out)
                against = re.search(r"images\.checker compared with [^,]*, ([0-9a-f]{40})", out)
                self.assertIsNotNone(against, out)
                self.assertEqual(self.outputs()["base"], against.group(1), out)
                self.assertIn("the lps_pin job reads release.yaml with the requirements of %s" % against.group(1),
                              out)
        for name, kw in (("a before the repository does not hold", {"before": "d" * 40}),
                         ("a commit with no parent and no before", {"before": "0" * 40, "root": True})):
            with self.subTest(case=name):
                rc, out, _ = self.push_path_plan_step(["theories/Premises.v"], None if kw.get("root") else here,
                                                      here, **kw)
                self.assertEqual(rc, 0, out)
                self.assertEqual(self.outputs()["base"], "", out)
                self.assertIn("no commit before this one to take the lps_pin job's requirements from", out)
                self.assertNotIn("the lps_pin job reads release.yaml with the requirements of", out)
        rc, out, _ = self.push_path_plan_step(["README.md"], here, here)
        self.assertEqual((rc, self.outputs()["base"]), (0, ""), out)

    def push_of_a_repin_and_a_later_commit(self):
        """A push of two commits onto A: B repins images.checker, and C, the commit checked out, changes the README
        alone.  The plan's list is the push's whole diff, from A."""
        old = self.RELEASE % (self.IMAGE.replace("0a" * 32, "1b" * 32), "2b" * 32)
        new = self.RELEASE % (self.IMAGE, "2b" * 32)
        history = [(old, {"README.md": "a\n"}), (new, {"README.md": "a\n"}), (new, {"README.md": "c\n"})]
        return self.push_path_plan_step(["README.md", "release.yaml"], history=history, before=2)

    def test_a_push_of_a_repin_and_a_later_commit_holds_the_repin(self):
        """B reaches main by this push alone and has no run of its own, so the image C names is held as a repin:
        against main before the push, not against C's parent B, which pins the same image.  An image B pinned that
        was built from an older Dockerfile than this commit's is refused; one built from this commit's passes,
        and so does the rest of the job and release-check."""
        self.job = load("release-check.yml")["jobs"]["lps_pin"]
        rc, out, got = self.push_of_a_repin_and_a_later_commit()
        self.assertEqual((rc, got), (0, ("true", "false", "true")), out)
        self.assertIn("main before this push", out)
        rc, out, commit = self.attestation_step(got[2], built={"toolchain/checker.Dockerfile": "FROM scratch\n# older\n"})
        self.assertEqual(rc, 1, out)
        self.assertIn("was built from another toolchain/checker.Dockerfile than this change's: images.yml built it at %s"
                      % commit, out)
        rc, out, _ = self.attestation_step(got[2])
        self.assertEqual(rc, 0, out)
        self.assertIn("built from this change's toolchain/checker.Dockerfile and toolchain/lps-core.paths", out)
        rc, out, _ = self.opam_step(repin=got[2])
        self.assertEqual(rc, 0, out)
        rc, out, calls = self.compile_step(0, theories=got[1], repin=got[2])
        self.assertEqual(rc, 0, out)
        self.assertTrue(any("dune build" in c for c in calls), calls)
        rc, out = self.push_path_verdict(LPS_PIN="true", LPS_PIN_RESULT="success")
        self.assertEqual(rc, 0, out)

    def test_a_force_push_is_held_against_the_tip_it_replaced(self):
        """A force push whose new history repins in the commit before the one checked out: that commit's parent is
        new history too, so the push is held against the tip it replaced, which pinned another image."""
        old = self.RELEASE % (self.IMAGE.replace("0a" * 32, "1b" * 32), "2b" * 32)
        new = self.RELEASE % (self.IMAGE, "2b" * 32)
        rc, out, got = self.push_path_plan_step(["release.yaml"], history=[(new, {}), (new, {"README.md": "c\n"})],
                                                old_tip=old)
        self.assertEqual((rc, got), (0, ("true", "false", "true")), out)

    def test_release_check_stays_green_after_a_toolchain_only_merge_on_a_push_and_on_a_dispatch(self):
        """The commit on main that changed toolchain/checker.Dockerfile, before an image built from it can be pinned
        (images.yml builds on main alone, after the push): release.yaml still names the image built at the commit
        before, from the Dockerfile before.  Its push run, with the plan's list of changed paths, and a dispatched
        run of it, with none, agree: the parent pins the same image, so no repin; release-check's own lps_pin job
        holds the model's two pins on this commit's files, verifies that image's attestation and nothing more, and
        compiles theories/ in it where the run reads theories/ as changed; and release-check passes."""
        here = self.RELEASE % (self.IMAGE, "2b" * 32)
        before, after = "FROM scratch\n# main before\n", "FROM scratch\n# this commit\n"
        self.job = load("release-check.yml")["jobs"]["lps_pin"]
        for event, changed, theories in (("push", ["toolchain/checker.Dockerfile"], "false"),
                                         ("workflow_dispatch", None, "true")):
            with self.subTest(event=event):
                rc, out, got = self.push_path_plan_step(
                    changed, here, here, event=event, parent_files={"toolchain/checker.Dockerfile": before},
                    head_files={"toolchain/checker.Dockerfile": after})
                self.assertEqual((rc, got), (0, ("true", theories, "false")), out)
                _, theories, repin = got
                rc, out = self.pin_step(lps_tree_sha256(self.MODEL))
                self.assertEqual(rc, 0, out)
                rc, out, _ = self.attestation_step(repin, built={"toolchain/checker.Dockerfile": before})
                self.assertEqual(rc, 0, out)
                self.assertIn("its attestation alone is verified here", out)
                rc, out, calls = self.opam_step(installed=[], repin=repin)
                self.assertEqual((rc, calls), (0, []), out)
                rc, out, calls = self.compile_step(0, theories=theories, repin=repin)
                self.assertEqual(rc, 0, out)
                self.assertEqual(any("dune build" in c for c in calls), theories == "true", calls)
                rc, out = self.push_path_verdict(LPS_PIN="true", LPS_PIN_RESULT="success")
                self.assertEqual(rc, 0, out)

    def test_a_dispatched_release_check_of_a_repin_holds_the_image_to_this_commit_s_dockerfile(self):
        """The same dispatched run of a commit whose parent pins another image: a repin, so an image built from
        another Dockerfile than this commit's is refused."""
        self.job = load("release-check.yml")["jobs"]["lps_pin"]
        here = self.RELEASE % (self.IMAGE, "2b" * 32)
        parent = self.RELEASE % (self.IMAGE.replace("0a" * 32, "1b" * 32), "2b" * 32)
        rc, out, got = self.push_path_plan_step(None, parent, here, event="workflow_dispatch")
        self.assertEqual((rc, got), (0, ("true", "true", "true")), out)
        rc, out, commit = self.attestation_step(got[2], built={"toolchain/checker.Dockerfile": "FROM scratch\n# older\n"})
        self.assertEqual(rc, 1, out)
        self.assertIn("was built from another toolchain/checker.Dockerfile than this change's", out)

    def test_the_push_path_reads_a_move_of_images_runner_as_a_runner_repin(self):
        """runner_repin is read as checker_repin is: against main before the push (here the commit's parent, or two
        commits back for a push of a repin and a later commit), or the parent on a run by hand; a parent with no
        release.yaml, or no parent, is a repin; a commit the job does not run for has none.  Each image's answer is
        its own: a move of the checker is no runner repin, and the other way round."""
        here = self.RELEASE % (self.IMAGE, "2b" * 32)
        other_checker = self.RELEASE % (self.IMAGE.replace("0a" * 32, "1b" * 32), "2b" * 32)
        other_runner = self.RELEASE % (self.IMAGE, "3c" * 32)
        # (case, push_path_plan_step's arguments, (lps_pin, checker_repin, runner_repin))
        for name, given, want in (
                ("release.yaml, another runner", dict(changed=["release.yaml"], parent_release=here,
                                                      head_release=other_runner), ("true", "false", "true")),
                ("release.yaml, another checker", dict(changed=["release.yaml"], parent_release=here,
                                                       head_release=other_checker), ("true", "true", "false")),
                ("release.yaml, the same images", dict(changed=["release.yaml"], parent_release=here,
                                                       head_release=here), ("true", "false", "false")),
                ("the runner's Dockerfile alone", dict(changed=["toolchain/runner.Dockerfile"], parent_release=here,
                                                       head_release=here), ("true", "false", "false")),
                ("release.yaml, where the parent has none", dict(changed=["release.yaml"], parent_release=None,
                                                                 head_release=here), ("true", "true", "true")),
                ("a runner repin and a later commit", dict(
                    changed=["README.md", "release.yaml"], before=2,
                    history=[(here, {"README.md": "a\n"}), (other_runner, {"README.md": "a\n"}),
                             (other_runner, {"README.md": "c\n"})]), ("true", "false", "true")),
                ("by hand, the parent pins another runner", dict(changed=None, parent_release=here,
                                                                 head_release=other_runner,
                                                                 event="workflow_dispatch"), ("true", "false", "true")),
                ("by hand, no parent", dict(changed=None, head_release=here, event="workflow_dispatch", root=True),
                 ("true", "true", "true")),
                ("a proof alone", dict(changed=["projects/zlib/fuzz/proofs/x/Proof.v"], parent_release=here,
                                       head_release=here), ("false", "false", "false"))):
            with self.subTest(case=name):
                changed = given.pop("changed")
                rc, out, got = self.push_path_plan_step(changed, **given)
                self.assertEqual((rc, got[0], got[2], self.outputs().get("runner_repin")), (0,) + want, out)

    def test_release_check_holds_a_runner_repin_to_this_commit_s_runner_dockerfile(self):
        """A commit that reaches main with images.runner moved, by a push or a run by hand: release-check's own copy
        of the job refuses a runner built from another toolchain/runner.Dockerfile than this commit's, passes one
        built from it, and verifies the unchanged checker's attestation alone."""
        self.job = load("release-check.yml")["jobs"]["lps_pin"]
        here = self.RELEASE % (self.IMAGE, "2b" * 32)
        parent = self.RELEASE % (self.IMAGE, "3c" * 32)
        for event, changed in (("push", ["release.yaml"]), ("workflow_dispatch", None)):
            with self.subTest(event=event):
                rc, out, got = self.push_path_plan_step(changed, parent, here, event=event)
                repin = self.outputs().get("runner_repin")
                self.assertEqual((rc, got[0], got[2], repin), (0, "true", "false", "true"), out)
                older = {self.RUNNER_DOCKERFILE: "FROM scratch\n# older\n"}
                rc, out, commit = self.attestation_step(repin, built=older, key="runner")
                self.assertEqual(rc, 1, out)
                self.assertIn("%s was built from another toolchain/runner.Dockerfile than this change's: images.yml "
                              "built it at %s" % (self.RUNNER, commit), out)
                rc, out, _ = self.attestation_step(repin, key="runner")
                self.assertEqual(rc, 0, out)
                rc, out, _ = self.attestation_step(got[2], built={"toolchain/checker.Dockerfile": "FROM scratch\n"})
                self.assertEqual(rc, 0, out)
                self.assertIn("its attestation alone is verified here", out)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class StatementsCommittedTest(StandIn):
    """pr.yml's check job compiles a tree whose generated files the planned tools render again.  Its step
    statements_committed fails unless every .v and dune file of each statement folder, and its images/dune, is the
    committed one, byte for byte: the base's, or the change's own where the plan named the change's tools, at the
    commit the work step recorded before any tool ran (OSSV-688).  Without it, a template or a comparison that an
    earlier merge changed in tools/ has proofs checked against text no committed file holds."""

    FILES = {"projects/zlib/fz/Statements.v": "Theorem plain_halts : halts_within_budget lim Images.plain.\n",
             "projects/zlib/fz/Images.v": "Definition plain := mkImage Plain.M.loaded_segments.\n",
             "projects/zlib/fz/Distribution.v": "Definition w := 1.\n",
             "projects/zlib/fz/dune": "(rocq.theory (name OSSVerify.zlib.fz) (theories OSSVerify.Core))\n",
             "projects/zlib/fz/images/dune": "(rule (deps %{project_root}/projects/zlib/bin/fz/fz.plain))\n",
             "projects/zlib/fz/README.md": "fz: no proof yet\n",
             "projects/zlib/fz/proofs/p/Proof.v": "Lemma p : True. Proof. exact I. Qed.\n"}

    def setUp(self):
        super().setUp()
        s = next(x for x in load("pr.yml")["jobs"]["check"]["steps"] if x.get("id") == "statements_committed")
        self.assertEqual(s.get("if"), "env.KIND != 'release'")
        self.text = s["run"]
        self.ws = tempfile.mkdtemp(dir=self.dir)
        self.head = os.path.join(self.ws, "head")
        self.base = os.path.join(self.ws, "base")
        os.mkdir(self.head)
        git(self.head, "init", "-q")
        self.write(self.head, self.FILES)
        git(self.head, "add", "-A")
        git(self.head, "commit", "-q", "-m", "the base")
        git(self.head, "worktree", "add", "-q", "--detach", self.base, "HEAD")
        # the ids the work step records before the render: the base's, and the head's (the same commit until a test
        # gives the change commits of its own)
        self.shas = {"BASE_SHA": git(self.base, "rev-parse", "HEAD"), "HEAD_SHA": git(self.head, "rev-parse", "HEAD")}
        os.mkdir(os.path.join(self.ws, "runner"))
        # the `python` setup-python puts on PATH in CI: here, the interpreter running this test
        os.symlink(sys.executable, os.path.join(self.dir, "bin", "python"))

    @staticmethod
    def write(root, files):
        for rel, text in files.items():
            path = os.path.join(root, rel)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w") as f:
                f.write(text)

    def reset(self):
        """base/ as the base commits it, as before the render."""
        git(self.base, "checkout", "-q", "--", ".")
        git(self.base, "clean", "-fdq")

    def check(self, tools="base"):
        rc, out, _ = self.run_step(self.text, {"RUNNER_TEMP": os.path.join(self.ws, "runner"), "TOOLS": tools,
                                               **self.shas}, cwd=self.ws)
        return rc, out

    def test_the_committed_files_pass(self):
        rc, out = self.check()
        self.assertEqual(rc, 0, out)

    def test_a_rendering_that_differs_from_a_committed_statement_file_fails(self):
        for rel in ("Statements.v", "Images.v", "Distribution.v", "dune", "images/dune"):
            with self.subTest(file=rel):
                self.reset()
                path = "projects/zlib/fz/" + rel
                self.write(self.base, {path: "True \\/ (" + self.FILES[path] + ")"})
                rc, out = self.check()
                self.assertEqual(rc, 1, out)
                self.assertIn(path, out)

    def test_a_file_the_rendering_adds_or_deletes_fails(self):
        self.write(self.base, {"projects/zlib/fz/Symbols.v": "Definition s := 0.\n"})
        rc, out = self.check()
        self.assertEqual(rc, 1, out)
        self.assertIn("projects/zlib/fz/Symbols.v", out)
        self.reset()
        os.remove(os.path.join(self.base, "projects/zlib/fz/Images.v"))
        rc, out = self.check()
        self.assertEqual(rc, 1, out)
        self.assertIn("projects/zlib/fz/Images.v", out)

    def test_the_change_s_proofs_and_a_rendered_readme_are_not_statement_files(self):
        """The check job lays the change's proofs over the base, and the render rewrites a README; neither is a file
        of a statement folder, so a proofs folder may hold files of the same names."""
        self.write(self.base, {"projects/zlib/fz/proofs/p/Proof.v": "Lemma p : 1 = 1. Proof. reflexivity. Qed.\n",
                               "projects/zlib/fz/proofs/p/Statements.v": "Definition t := True.\n",
                               "projects/zlib/fz/proofs/p/dune": "(rocq.theory (name P))\n",
                               "projects/zlib/fz/README.md": "fz: proved\n"})
        rc, out = self.check()
        self.assertEqual(rc, 0, out)

    def test_the_change_s_own_tools_are_held_to_the_change_s_own_files(self):
        """Where the plan named the change's tools, the committed files are the change's (head's): a rendering equal
        to them passes only with tools=head, and one equal to the base's only with tools=base."""
        weaker = {"projects/zlib/fz/Statements.v": "Theorem plain_halts : True.\n"}
        self.write(self.head, weaker)
        git(self.head, "commit", "-q", "-am", "the change's own statements")
        self.shas["HEAD_SHA"] = git(self.head, "rev-parse", "HEAD")
        rc, out = self.check("base")
        self.assertEqual(rc, 0, out)
        rc, out = self.check("head")
        self.assertEqual(rc, 1, out)
        self.write(self.base, weaker)
        rc, out = self.check("head")
        self.assertEqual(rc, 0, out)
        rc, out = self.check("base")
        self.assertEqual(rc, 1, out)

    def test_tools_the_plan_did_not_name_fail(self):
        for tools in ("", "main"):
            with self.subTest(tools=tools):
                rc, out = self.check(tools)
                self.assertEqual(rc, 1, out)
                self.assertIn("neither base nor head", out)

    WEAKER = "Theorem plain_halts : True.\n"

    def assert_weaker_fails(self):
        """The render left Statements.v weaker; the step must say so, whatever it left in git beside it."""
        rc, out = self.check()
        self.assertEqual(rc, 1, out)
        self.assertIn("projects/zlib/fz/Statements.v: changed", out)

    def test_a_commit_the_render_makes_is_not_the_committed_one(self):
        """The step reads the commit the work step recorded before the render, not base/'s HEAD after it."""
        self.write(self.base, {"projects/zlib/fz/Statements.v": self.WEAKER})
        git(self.base, "commit", "-q", "-am", "the render's own commit")
        self.assert_weaker_fails()

    def test_a_replace_object_the_render_makes_changes_nothing(self):
        self.write(self.base, {"projects/zlib/fz/Statements.v": self.WEAKER})
        git(self.base, "commit", "-q", "-am", "a weaker base")
        git(self.base, "replace", self.shas["BASE_SHA"], "HEAD")
        git(self.base, "checkout", "-q", "--detach", self.shas["BASE_SHA"])
        self.assert_weaker_fails()

    def test_a_clean_filter_the_render_sets_changes_nothing(self):
        """A clean filter that hands git the committed bytes while the file holds others: the step reads the file's
        own bytes, and the blob as stored."""
        original = os.path.join(self.dir, "original.v")
        with open(original, "w") as f:
            f.write(self.FILES["projects/zlib/fz/Statements.v"])
        git(self.base, "config", "filter.keep.clean", "cat " + shlex.quote(original))
        info = os.path.join(git(self.base, "rev-parse", "--path-format=absolute", "--git-common-dir"), "info")
        os.makedirs(info, exist_ok=True)
        with open(os.path.join(info, "attributes"), "w") as f:
            f.write("/projects/zlib/fz/Statements.v filter=keep\n")
        self.write(self.base, {"projects/zlib/fz/Statements.v": self.WEAKER})
        # git hashes the weaker file as the committed blob: the filter works
        self.assertEqual(git(self.base, "hash-object", "projects/zlib/fz/Statements.v"),
                         git(self.base, "rev-parse", self.shas["BASE_SHA"] + ":projects/zlib/fz/Statements.v"))
        self.assert_weaker_fails()

    def test_a_link_in_place_of_a_statement_file_fails(self):
        """The checker reads what a link points at, which can change after this step: a statement file must be a
        regular file, even with the committed bytes."""
        path = os.path.join(self.base, "projects/zlib/fz/Images.v")
        target = os.path.join(self.dir, "Images.v")
        with open(target, "w") as f:
            f.write(self.FILES["projects/zlib/fz/Images.v"])
        os.remove(path)
        os.symlink(target, path)
        rc, out = self.check()
        self.assertEqual(rc, 1, out)
        self.assertIn("projects/zlib/fz/Images.v: not a regular file", out)


if __name__ == "__main__":
    unittest.main()
