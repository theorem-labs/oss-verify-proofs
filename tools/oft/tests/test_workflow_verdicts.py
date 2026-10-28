"""The one verdict of each workflow run: pr.yml's restate, which gives a head's own verdict or none, and the jobs
that collect a run's results in images.yml and weekly.yml, each run as GitHub runs a step, against a stand-in gh;
and the base pr.yml judges a change against, which its router reads the change from."""
import json
import os
import re
import shutil
import subprocess
import tempfile
import unittest

from oft import yamlio
from oft.tests.helpers import REPO

WORKFLOWS = os.path.join(REPO, ".github", "workflows")
REPOSITORY = "acme/proofs"
OWN_RUN = 500        # the restate's own run
HEAD = "c" * 40
# A gh that answers `gh api [--method M] <endpoint> [--jq <filter>]` from <FAKE_GH>/<endpoint>.json, the endpoint's
# slashes as underscores and its query string dropped, through --jq as gh applies it; when <endpoint>.1.json,
# <endpoint>.2.json and on are there instead, each call takes the next of them and the last one stays.  A POST is
# answered by <endpoint>.json too, and refused as GitHub refuses a token without the permission when there is none.
# An answer that is the JSON string "error" is a failed call.  Every call is logged, one line each, with its query
# string, to <FAKE_GH>/calls.  With --paginate, an answer's next page, <answer file>.page2, is read through --jq too;
# without it, only the first page is, as GitHub's per_page caps a list.
FAKE_GH = r"""#!/usr/bin/env bash
[ "$1" = api ] || exit 9; shift
filter=. endpoint= method=GET
while [ $# -gt 0 ]; do
  case $1 in
    --jq) filter=$2; shift 2 ;;
    --method|-X) method=$2; shift 2 ;;
    --paginate) paginate=1; shift ;;
    *) endpoint=$1; shift ;;
  esac
done
echo "$method $endpoint" >> "$FAKE_GH/calls"
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
jq -r "$filter" "$file" || exit 1
if [ -n "${paginate:-}" ] && [ -f "$file.page2" ]; then jq -r "$filter" "$file.page2"; fi
"""
# sleep takes no time here, and says that it was asked to
FAKE_SLEEP = '#!/usr/bin/env bash\necho "sleep $1" >> "$FAKE_GH/calls"\n'


def load(name):
    return yamlio.load_file(os.path.join(WORKFLOWS, name))


def step(job, name):
    found = [s for s in job["steps"] if s.get("name") == name]
    assert len(found) == 1, name
    return found[0]


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

    def tearDown(self):
        self._tmp.cleanup()

    def run_step(self, text, env):
        """Runs a step's script as GitHub does (bash --noprofile --norc -eo pipefail): its exit status, its output
        and its job summary."""
        script = os.path.join(self.dir, "step.sh")
        with open(script, "w") as f:
            f.write(text)
        summary = os.path.join(self.dir, "summary")
        full = dict(os.environ, PATH=self.path, FAKE_GH=self.api, GITHUB_STEP_SUMMARY=summary, **env)
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", script], env=full,
                           capture_output=True, text=True)
        text = ""
        if os.path.exists(summary):
            with open(summary) as f:
                text = f.read()
            os.remove(summary)
        return r.returncode, r.stdout + r.stderr, text

    def calls(self):
        path = os.path.join(self.api, "calls")
        if not os.path.exists(path):
            return []
        with open(path) as f:
            return f.read().splitlines()


class Restate:
    """A restate step: on an edit of the title or body, the verdict of the last run on this head whose router job ran
    (`router`), from its verdict job, or none.  Subclasses name the workflow, its words and how the step is run."""

    workflow = router = word = None

    def endpoint(self, path):
        return os.path.join(self.api, ("repos/%s/actions/%s" % (REPOSITORY, path)).replace("/", "_"))

    def serve(self, path, *answers):
        """The stand-in API's answer for repos/acme/proofs/actions/<path>: one, or one a call in turn."""
        if len(answers) == 1:
            with open(self.endpoint(path) + ".json", "w") as f:
                json.dump(answers[0], f)
            return
        for n, answer in enumerate(answers, 1):
            with open("%s.%d.json" % (self.endpoint(path), n), "w") as f:
                json.dump(answer, f)

    def listing(self, *runs):
        """The runs list for this head, and each run's jobs: (id, status, conclusion, router job's result or None for
        no job records, {verdict job: conclusion}[, the run's name]) each, newest last.  A run's name is the pull
        request's title, or `restate: <title>` for a restate, as pr.yml's run-name makes it."""
        listed = []
        for n, (run, status, conclusion, router, verdicts, *name) in enumerate(runs):
            title = name[0] if name else ("restate: the change" if router == "skipped" else "the change")
            listed.append({"id": run, "run_attempt": 1, "status": status, "conclusion": conclusion, "display_title": title,
                           "run_started_at": "2026-10-26T10:%02d:00Z" % n,
                           "pull_requests": [{"number": 7}], "head_repository": {"full_name": REPOSITORY},
                           "head_branch": "topic"})
            jobs = [] if router is None else [{"name": self.router, "conclusion": router, "status": "completed"}]
            jobs += [{"name": name, "conclusion": c, "status": "completed" if c else "in_progress"}
                     for name, c in verdicts.items()]
            self.serve("runs/%d/attempts/1/jobs" % run, {"jobs": jobs})
        return {"workflow_runs": listed}

    def runs(self, *runs):
        self.serve("workflows/%s/runs" % self.workflow, self.listing(*runs))

    def accept_cancel(self):
        self.serve("runs/%d/force-cancel" % OWN_RUN, {})

    def cancelled(self):
        return "POST repos/%s/actions/runs/%d/force-cancel" % (REPOSITORY, OWN_RUN) in self.calls()

    def polls(self):
        env = self.env()
        return int(env["WAIT_SECONDS"]) // int(env["POLL_SECONDS"])

    def assertVerdict(self, want, rc, out):
        self.assertEqual(rc, 0 if want == "success" else 1, out)
        self.assertFalse(self.cancelled(), "a run with a verdict to restate cancelled itself:\n" + out)

    def assertNone(self, rc, out, summary, why):
        """No verdict, and none will come: the step fails and says why, and cancels nothing."""
        self.assertEqual(rc, 1, out)
        self.assertFalse(self.cancelled(), "a run with no verdict to come cancelled itself:\n" + out)
        self.assertIn("no verdict to restate: " + why, out)
        self.assertIn("No verdict to restate: " + why, summary)

    def assertLater(self, rc, out, summary, why):
        """The verdict comes later, from the running run: this run says so and cancels itself."""
        self.assertTrue(self.cancelled(), "a run whose verdict comes later did not cancel itself:\n" + out)
        self.assertIn("no verdict to restate yet: " + why, out)
        self.assertIn("No verdict to restate yet: " + why, summary)
        # the stand-in cancel ends nothing: the step waits for it, then says so
        self.assertIn("sleep 60", self.calls())
        self.assertEqual(rc, 1, out)
        self.assertIn("this run, which asked to be cancelled, was not", out)

    def list_calls(self):
        return [c for c in self.calls() if "/actions/workflows/%s/runs" % self.workflow in c]

    def jobs_of(self, router, verdict):
        return {"jobs": [{"name": self.router, "conclusion": router, "status": "completed"}]
                + [{"name": n, "conclusion": c, "status": "completed"} for n, c in self.verdicts(verdict).items()]}

    def test_only_this_head_s_runs_are_asked_for(self):
        self.runs()
        self.restate()
        self.assertTrue(self.list_calls())
        for call in self.list_calls():
            self.assertIn("head_sha=" + HEAD, call)

    def test_a_finished_run_s_verdict_is_restated(self):
        for verdict in ("success", "failure"):
            with self.subTest(verdict=verdict):
                self.runs((100, "completed", verdict, "success", self.verdicts(verdict)))
                rc, out, _ = self.restate()
                self.assertVerdict(verdict, rc, out)

    def test_only_the_last_run_that_ran_its_router_is_restated(self):
        """An earlier pass on this head does not stand for a later failure, an earlier restate, whose router was
        skipped, is passed over, and so is this run itself."""
        self.runs((100, "completed", "success", "success", self.verdicts("success")),
                  (200, "completed", "failure", "success", self.verdicts("failure")),
                  (300, "completed", "success", "skipped", self.verdicts("success")),
                  (OWN_RUN, "in_progress", None, "skipped", {}))
        rc, out, _ = self.restate()
        self.assertVerdict("failure", rc, out)
        self.assertIn("run 200 on this head", out)

    def test_this_run_is_never_its_own_verdict(self):
        """This run, listed with no job records yet, is not a run still to come."""
        self.runs((OWN_RUN, "in_progress", None, None, {}))
        rc, out, summary = self.restate()
        self.assertNone(rc, out, summary, self.nothing)

    def test_a_run_created_after_this_one_counts(self):
        """A re-run of an old restate after a change of base: the run the base change started, created after this
        one, holds the head's verdict now."""
        self.runs((200, "completed", "success", "success", self.verdicts("success")),
                  (OWN_RUN, "in_progress", None, "skipped", {}),
                  (600, "completed", "failure", "success", self.verdicts("failure")))
        rc, out, _ = self.restate()
        self.assertVerdict("failure", rc, out)
        self.assertIn("run 600 on this head", out)

    def test_a_run_of_another_pull_request_on_the_same_head_is_passed_over(self):
        listed = self.listing((100, "completed", "failure", "success", self.verdicts("failure")),
                              (200, "completed", "success", "success", self.verdicts("success")))
        listed["workflow_runs"][1]["pull_requests"] = [{"number": 8}]
        self.serve("workflows/%s/runs" % self.workflow, listed)
        rc, out, _ = self.restate()
        self.assertVerdict("failure", rc, out)
        self.assertIn("run 100 on this head", out)

    def test_a_fork_s_run_is_matched_by_its_head_repository_and_branch(self):
        """A run from a fork names no pull request; one of another fork or branch is passed over."""
        listed = self.listing((100, "completed", "failure", "success", self.verdicts("failure")),
                              (200, "completed", "success", "success", self.verdicts("success")))
        for r in listed["workflow_runs"]:
            r["pull_requests"] = []
        listed["workflow_runs"][0]["head_repository"] = {"full_name": "fork/proofs"}
        listed["workflow_runs"][1]["head_repository"] = {"full_name": "other/proofs"}
        self.serve("workflows/%s/runs" % self.workflow, listed)
        rc, out, _ = self.restate(head_repo="fork/proofs")
        self.assertVerdict("failure", rc, out)
        self.assertIn("run 100 on this head", out)

    def test_a_running_run_is_waited_for_and_its_verdict_restated(self):
        """Each poll lists the runs again; a call that fails is asked again at the next poll."""
        self.serve("workflows/%s/runs" % self.workflow,
                   self.listing((100, "in_progress", None, "success", self.verdicts("success"))), "error",
                   self.listing((100, "completed", "success", "success", self.verdicts("success"))))
        rc, out, _ = self.restate()
        self.assertVerdict("success", rc, out)
        self.assertEqual(len(self.list_calls()), 3)
        self.assertIn("could not list this head's runs: asking again", out)

    def test_a_failed_jobs_call_never_makes_a_restate_the_verdict(self):
        """Run 100 failed; the newer restate 300's jobs call fails seven times: each is asked again at the next poll,
        never read as a run that checked."""
        self.runs((100, "completed", "failure", "success", self.verdicts("failure")),
                  (300, "completed", "success", "skipped", self.verdicts("success")))
        # seven, as many as the step's own tries for a missing plan record: a failed call must not be one of them
        self.serve("runs/300/attempts/1/jobs", *(["error"] * 7 + [self.jobs_of("skipped", "success")]))
        rc, out, _ = self.restate(WAIT_SECONDS="300")
        self.assertVerdict("failure", rc, out)
        self.assertIn("run 100 on this head", out)
        self.assertNotIn("run 300 on this head", out)

    def test_a_run_not_listed_yet_is_waited_for(self):
        """A push and an edit together: this run may start before the push's run is listed."""
        self.serve("workflows/%s/runs" % self.workflow, self.listing(),
                   self.listing((100, "completed", "success", "success", self.verdicts("success"))))
        rc, out, _ = self.restate()
        self.assertVerdict("success", rc, out)

    def test_a_waiting_check_is_waited_for_over_an_older_verdict(self):
        """A base change or a reopen cancels the running check and waits, with no job records yet: its verdict is the
        one to come, not the older run's."""
        self.serve("workflows/%s/runs" % self.workflow,
                   self.listing((100, "completed", "failure", "success", self.verdicts("failure")),
                                (700, "pending", None, None, {})),
                   self.listing((100, "completed", "failure", "success", self.verdicts("failure")),
                                (700, "completed", "success", "success", self.verdicts("success"))))
        self.serve("runs/700/attempts/1/jobs", {"jobs": []}, self.jobs_of("success", "success"))
        rc, out, _ = self.restate()
        self.assertVerdict("success", rc, out)
        self.assertIn("run 700 on this head", out)

    def test_a_failed_call_keeps_the_run_already_found(self):
        """The last poll's list call fails: the running run found before still gives the verdict later."""
        running = self.listing((100, "in_progress", None, "success", {}))
        self.serve("workflows/%s/runs" % self.workflow, *([running] * self.polls() + ["error"]))
        self.accept_cancel()
        rc, out, summary = self.restate()
        self.assertLater(rc, out, summary, "run 100, the last to %s this head, is still in_progress" % self.word)

    def test_a_run_that_ended_with_no_job_records_is_passed_over(self):
        """Cancelled while it waited: it never checked anything."""
        self.runs((100, "completed", "success", "success", self.verdicts("success")),
                  (700, "completed", "cancelled", None, {}))
        rc, out, _ = self.restate()
        self.assertVerdict("success", rc, out)

    def test_a_waiting_run_alone_is_a_verdict_still_to_come_and_judged_once_it_has_records(self):
        """The push's run, waiting with no job records, is waited for; once it has records it is judged by them: here
        it turns out to be a restate (its router skipped), so no run checked this head."""
        self.serve("workflows/%s/runs" % self.workflow, self.listing((700, "queued", None, None, {})),
                   self.listing((700, "completed", "success", "skipped", self.verdicts("success"))))
        self.serve("runs/700/attempts/1/jobs", {"jobs": []}, self.jobs_of("skipped", "success"))
        rc, out, summary = self.restate()
        self.assertNone(rc, out, summary, self.nothing)
        self.assertIn("run 700, the last to %s this head, is queued" % self.word, out)

    def test_a_run_still_running_after_the_wait_gives_the_verdict_later(self):
        self.runs((100, "in_progress", None, "success", {}))
        self.accept_cancel()
        rc, out, summary = self.restate()
        self.assertLater(rc, out, summary, "run 100, the last to %s this head, is still in_progress" % self.word)
        self.assertEqual(len(self.list_calls()), self.polls() + 1)

    def test_a_token_that_may_not_cancel_fails(self):
        self.runs((100, "in_progress", None, "success", {}))
        rc, out, _ = self.restate()
        self.assertEqual(rc, 1, out)
        self.assertIn("is still in_progress", out)
        self.assertIn("and this run may not cancel itself", out)
        self.assertNotIn("sleep 60", self.calls())

    def test_a_run_cancelled_during_the_wait_leaves_no_verdict(self):
        self.serve("workflows/%s/runs" % self.workflow, self.listing((100, "queued", None, "success", {})),
                   self.listing((100, "completed", "cancelled", "success", {})))
        self.accept_cancel()
        rc, out, summary = self.restate()
        self.assertNone(rc, out, summary, "run 100, the last to %s this head, was cancelled" % self.word)

    def test_a_cancelled_run_leaves_no_verdict(self):
        """Its verdict job ran, always(), over cancelled jobs, and failed: that is no verdict on the head."""
        self.runs((100, "completed", "cancelled", "success", self.verdicts("failure")))
        self.accept_cancel()
        rc, out, summary = self.restate()
        self.assertNone(rc, out, summary, "run 100, the last to %s this head, was cancelled" % self.word)
        self.assertEqual(len(self.list_calls()), 1, "a finished run is not waited for")

    def test_a_head_no_run_ran_on_has_no_verdict(self):
        for runs in ((), ((300, "completed", "success", "skipped", self.verdicts("success")),)):
            with self.subTest(runs=runs):
                self.runs(*runs)
                self.accept_cancel()
                rc, out, summary = self.restate()
                self.assertNone(rc, out, summary, self.nothing)

    def test_a_finished_run_s_records_are_read_once(self):
        """Each poll lists the runs again, but a finished run's job records do not change: a finished restate listed
        on every poll is read once, so a poll costs a list call and the running run's records."""
        self.runs((100, "in_progress", None, "success", {}),
                  (300, "completed", "success", "skipped", self.verdicts("success")),
                  (301, "completed", "success", "skipped", self.verdicts("success")))
        self.accept_cancel()
        self.restate()
        jobs = lambda run: self.calls().count("GET repos/%s/actions/runs/%d/attempts/1/jobs?per_page=100" % (REPOSITORY, run))
        self.assertEqual((jobs(300), jobs(301)), (1, 1))
        self.assertEqual(jobs(100), self.polls() + 1)

    def test_a_re_run_is_judged_afresh(self):
        """A run that ended with no job records is passed over; re-run, it is a new attempt of the same run, whose
        records are read again rather than taken from the first attempt."""
        first = self.listing((700, "completed", "cancelled", None, {}))
        again = self.listing((700, "completed", "success", "success", self.verdicts("success")))
        again["workflow_runs"][0]["run_attempt"] = 2
        self.serve("workflows/%s/runs" % self.workflow, first, again)
        self.serve("runs/700/attempts/1/jobs", {"jobs": []})
        self.serve("runs/700/attempts/2/jobs", self.jobs_of("success", "success"))
        rc, out, _ = self.restate()
        self.assertVerdict("success", rc, out)
        self.assertIn("run 700 on this head", out)

    def test_runs_that_cannot_be_listed_leave_no_verdict(self):
        self.serve("workflows/%s/runs" % self.workflow, "error")
        rc, out, summary = self.restate()
        self.assertNone(rc, out, summary, "this head's runs could not be listed")


@unittest.skipUnless(shutil.which("jq"), "jq is not installed")
class PrRestateTest(Restate, StandIn):
    """pr.yml's required job, on a new title or description."""

    workflow, router, word = "pr.yml", "plan", "check"
    nothing = "no run of this workflow checked this head"

    def setUp(self):
        super().setUp()
        self.step = step(load("pr.yml")["jobs"]["required"],
                         "a new title or description restates the last verdict on this head")

    def env(self, fork=False):
        """The step's WAIT_SECONDS and POLL_SECONDS, as GitHub evaluates them for a pull request from this
        repository or from another one."""
        got = {}
        for key in ("WAIT_SECONDS", "POLL_SECONDS"):
            m = re.fullmatch(r"\$\{\{ github\.event\.pull_request\.head\.repo\.full_name != github\.repository "
                             r"&& '(\d+)' \|\| '(\d+)' \}\}", self.step["env"][key])
            self.assertIsNotNone(m, self.step["env"][key])
            got[key] = m.group(1 if fork else 2)
        got["LIST_SECONDS"] = self.step["env"]["LIST_SECONDS"]
        return got

    def test_a_fork_s_restate_waits_long_only_for_a_listed_run(self):
        """A pull request from another repository waits up to 345 minutes for a running run, but no longer than
        LIST_SECONDS for a run to be listed (a deleted fork lists none)."""
        env = self.env(fork=True)
        self.runs()
        rc, out, summary = self.run_step(self.step["run"], dict(env, GH_TOKEN="t", GITHUB_REPOSITORY=REPOSITORY,
                                                                 GITHUB_RUN_ID=str(OWN_RUN), PR="7", HEAD=HEAD,
                                                                 HEAD_REPO="fork/proofs", HEAD_REF="topic"))
        self.assertNone(rc, out, summary, self.nothing)
        self.assertEqual(self.calls().count("sleep %s" % env["POLL_SECONDS"]),
                         int(env["LIST_SECONDS"]) // int(env["POLL_SECONDS"]))

    def test_a_fork_s_restate_waits_the_whole_check_for_a_listed_running_run(self):
        """A token that may not cancel: the restate waits WAIT_SECONDS for the running run's verdict, here in vain."""
        env = self.env(fork=True)
        self.assertGreaterEqual(int(env["WAIT_SECONDS"]), 4 * 3600, "a fork's restate waits hours, not a minute")
        self.runs((100, "in_progress", None, "success", {}))
        rc, out, _ = self.run_step(self.step["run"], dict(env, GH_TOKEN="t", GITHUB_REPOSITORY=REPOSITORY,
                                                           GITHUB_RUN_ID=str(OWN_RUN), PR="7", HEAD=HEAD,
                                                           HEAD_REPO="fork/proofs", HEAD_REF="topic"))
        self.assertEqual(rc, 1, out)
        self.assertEqual(self.calls().count("sleep %s" % env["POLL_SECONDS"]),
                         int(env["WAIT_SECONDS"]) // int(env["POLL_SECONDS"]))
        self.assertIn("and this run may not cancel itself", out)

    def test_a_title_cannot_add_a_run_to_the_list(self):
        """A pull request's title may hold a newline, and GitHub keeps it in the run's name: only whether the name
        starts with `restate: ` is read, so a title cannot make a line that reads as another run."""
        self.runs((100, "completed", "failure", "success", self.verdicts("failure")),
                  (200, "completed", "success", "skipped", self.verdicts("success"),
                   "restate: x\n999 1 completed success false"))
        self.serve("runs/999/attempts/1/jobs", self.jobs_of("success", "success"))
        rc, out, _ = self.restate()
        self.assertVerdict("failure", rc, out)
        self.assertIn("run 100 on this head", out)
        self.assertFalse([c for c in self.calls() if "/runs/999/" in c], "a line made by a title was read as a run")

    def test_the_name_the_step_reads_is_the_one_run_name_gives_a_restate(self):
        wf = load("pr.yml")
        self.assertIn("format('restate: {0}', github.event.pull_request.title)", " ".join(wf["run-name"].split()))
        self.assertIn('startswith("restate: ")', self.step["run"])

    def test_the_jobs_read_are_the_listed_attempt_s(self):
        """runs/<id>/jobs gives the latest attempt; the step reads the attempt the run list showed."""
        self.assertNotIn("/jobs?", self.step["run"].replace("/attempts/$attempt/jobs?", ""))

    def test_a_waiting_restate_is_passed_over(self):
        """A newer restate waiting behind this one in its group has no job records; it checks nothing and cannot start
        before this one ends, so the older run that checked is restated."""
        self.runs((100, "completed", "failure", "success", self.verdicts("failure")),
                  (700, "pending", None, None, {}, "restate: the change"))
        rc, out, _ = self.restate()
        self.assertVerdict("failure", rc, out)
        self.assertIn("run 100 on this head", out)

    def test_a_fork_s_restate_is_not_held_by_a_restate_waiting_behind_it(self):
        env = self.env(fork=True)
        self.runs((700, "pending", None, None, {}, "restate: the change"))
        rc, out, summary = self.run_step(self.step["run"], dict(env, GH_TOKEN="t", GITHUB_REPOSITORY=REPOSITORY,
                                                                 GITHUB_RUN_ID=str(OWN_RUN), PR="7", HEAD=HEAD,
                                                                 HEAD_REPO=REPOSITORY, HEAD_REF="topic"))
        self.assertNone(rc, out, summary, self.nothing)
        self.assertLessEqual(len(self.list_calls()), int(env["LIST_SECONDS"]) // int(env["POLL_SECONDS"]) + 1)

    def test_one_pull_request_s_restates_share_one_concurrency_group(self):
        """Each restate holds a runner while it waits: they share one group per pull request, so N edits hold one
        runner at a time (GitHub runs one run of a group and keeps at most one waiting)."""
        wf = load("pr.yml")
        group = " ".join(wf["concurrency"]["group"].split())
        self.assertIn("&& format('restate-{0}', github.event.pull_request.number)", group)
        self.assertIn("github.event.action == 'edited' && github.event.changes.base == null", group)
        self.assertIs(wf["concurrency"]["cancel-in-progress"], True)

    def verdicts(self, verdict):
        return {"required": verdict, "main-gate": verdict}

    def restate(self, base="main", head_repo=REPOSITORY, **extra):
        """The step, with the pull request's base branch as the API gives it now."""
        with open(os.path.join(self.api, "repos_%s_pulls_7.json" % REPOSITORY.replace("/", "_")), "w") as f:
            json.dump({"base": {"ref": base}}, f)
        return self.run_step(self.step["run"], dict(self.env(), GH_TOKEN="t", GITHUB_REPOSITORY=REPOSITORY,
                                                     GITHUB_RUN_ID=str(OWN_RUN), PR="7", HEAD=HEAD,
                                                     HEAD_REPO=head_repo, HEAD_REF="topic", **extra))

    def test_main_gate_is_the_verdict_into_main_and_required_into_another_base(self):
        """main-gate fails on another base, since the base is not main; required is that run's verdict there.  The
        base is the one the pull request names now (a re-run of an old restate after a base change must not use the
        base its event named); the event's base is not given to the step at all."""
        self.assertNotIn("BASE", self.step["env"])
        self.runs((100, "completed", "failure", "success", {"required": "success", "main-gate": "failure"}))
        rc, out, _ = self.restate(base="lane")
        self.assertVerdict("success", rc, out)
        self.assertIn("required passed", out)
        rc, out, _ = self.restate(base="main")
        self.assertVerdict("failure", rc, out)
        self.assertIn("main-gate failed", out)

    def test_a_verdict_job_past_the_first_page_of_jobs_is_read(self):
        """Up to 256 fetch-drafts legs and 20 checks put required and main-gate past the first 100 jobs: the step
        reads every page, both for the plan record and for the verdict, and still takes the first page's answer."""
        filler = [{"name": "fetch-drafts %d" % i, "conclusion": "success", "status": "completed"} for i in range(98)]
        for verdict in ("success", "failure"):
            with self.subTest(verdict=verdict):
                self.runs((100, "completed", verdict, "success", {}))
                page1 = self.endpoint("runs/100/attempts/1/jobs") + ".json"
                with open(page1, "w") as f:
                    json.dump({"jobs": [{"name": "plan", "conclusion": "success", "status": "completed"},
                                        {"name": "lint", "conclusion": "success", "status": "completed"}] + filler}, f)
                with open(page1 + ".page2", "w") as f:
                    json.dump({"jobs": [{"name": n, "conclusion": verdict, "status": "completed"}
                                        for n in ("check 0", "required", "main-gate")]}, f)
                rc, out, _ = self.restate()
                self.assertVerdict(verdict, rc, out)
                self.assertIn("main-gate %s" % ("passed" if verdict == "success" else "failed"), out)

    def test_a_plan_record_past_the_first_page_of_jobs_is_read(self):
        """A first page with no plan record (it lists the jobs as GitHub orders them) is not read as a run whose plan
        record is still to come: the plan record on the next page says the run checked."""
        filler = [{"name": "check %d" % i, "conclusion": "success", "status": "completed"} for i in range(100)]
        self.runs((100, "completed", "success", "success", {}))
        page1 = self.endpoint("runs/100/attempts/1/jobs") + ".json"
        with open(page1, "w") as f:
            json.dump({"jobs": filler}, f)
        with open(page1 + ".page2", "w") as f:
            json.dump({"jobs": [{"name": n, "conclusion": "success", "status": "completed"}
                                for n in ("plan", "required", "main-gate")]}, f)
        rc, out, _ = self.restate()
        self.assertVerdict("success", rc, out)
        self.assertNotIn("sleep 5", self.calls())

    def test_a_base_that_cannot_be_read_leaves_no_verdict(self):
        self.runs((100, "completed", "success", "success", {"required": "success", "main-gate": "success"}))
        # no pulls/7 answer: the stand-in gh fails that call as GitHub's 404 would
        rc, out, summary = self.run_step(self.step["run"], dict(self.env(), GH_TOKEN="t",
                                                                 GITHUB_REPOSITORY=REPOSITORY,
                                                                 GITHUB_RUN_ID=str(OWN_RUN), PR="7", HEAD=HEAD,
                                                                 HEAD_REPO=REPOSITORY, HEAD_REF="topic"))
        self.assertNone(rc, out, summary, "could not read pull request 7's base branch")

    def test_a_run_with_no_verdict_job_leaves_no_verdict(self):
        for verdicts in ({}, {"main-gate": "skipped"}, {"main-gate": "cancelled"}):
            with self.subTest(verdicts=verdicts):
                self.runs((100, "completed", "failure", "success", verdicts))
                self.accept_cancel()
                rc, out, summary = self.restate()
                self.assertNone(rc, out, summary, "run 100, the last to check this head, has no main-gate verdict")

    def test_the_wait_fits_the_job_s_limit_for_both_kinds_of_pull_request(self):
        """A pull request from another repository may not cancel: it waits up to 345 minutes instead, inside a
        limit of 360 minutes; any other waits a minute inside 5.  Up to 30 seconds go to asking for a router record
        of each listed run, a few at most."""
        job = load("pr.yml")["jobs"]["required"]
        # a job's permissions leave every scope they do not name at none: each API the step calls needs its scope
        # (the restate's read of pulls/<n> failed with 403 on GitHub before pull-requests: read was added)
        self.assertEqual(job["permissions"], {"actions": "write", "pull-requests": "read"})
        self.assertIn("/pulls/$PR", self.step["run"])
        m = re.fullmatch(r"\$\{\{ (.*) && (\d+) \|\| (\d+) \}\}", " ".join(job["timeout-minutes"].split()))
        self.assertIsNotNone(m, job["timeout-minutes"])
        # the condition is RESTATE's, for a pull request from another repository
        self.assertIn("github.event.action == 'edited' && github.event.changes.base == null", m.group(1))
        self.assertIn("github.event.pull_request.head.repo.full_name != github.repository", m.group(1))
        for fork, limit in ((True, int(m.group(2))), (False, int(m.group(3)))):
            with self.subTest(fork=fork):
                env = self.env(fork)
                self.assertLess(int(env["WAIT_SECONDS"]) + 3 * 35 + 60, limit * 60)


FACTS_REVIEW = os.path.join(WORKFLOWS, "facts-review.yml")


@unittest.skipUnless(shutil.which("jq"), "jq is not installed")
@unittest.skipUnless(os.path.exists(FACTS_REVIEW), "no .github/workflows/facts-review.yml: the internal repository "
                                                   "alone has it")
class FactsReviewRestateTest(Restate, StandIn):
    """facts-review.yml's facts-review job, on a new title or description."""

    workflow, router, word = "facts-review.yml", "gate", "review"
    nothing = "no run of this workflow reviewed this head"

    def setUp(self):
        super().setUp()
        self.step = load("facts-review.yml")["jobs"]["facts-review"]["steps"][0]

    def env(self):
        return {k: self.step["env"][k] for k in ("WAIT_SECONDS", "POLL_SECONDS", "LIST_SECONDS")}

    def verdicts(self, verdict):
        return {"facts-review": verdict}

    def restate(self, head_repo=REPOSITORY, **extra):
        return self.run_step(self.step["run"], dict(self.env(), GH_TOKEN="t", GITHUB_REPOSITORY=REPOSITORY,
                                                     GITHUB_RUN_ID=str(OWN_RUN), HEAD=HEAD, EDIT="true", PR="7",
                                                     HEAD_REPO=head_repo, HEAD_REF="topic",
                                                     GATE="skipped", ROUTE="", REVIEW="skipped", KEEP="skipped",
                                                     COMMENT="skipped", SESSION="", **extra))

    def test_a_run_from_before_the_verdict_job_is_judged_by_its_conclusion(self):
        for conclusion in ("success", "failure"):
            with self.subTest(conclusion=conclusion):
                self.runs((100, "completed", conclusion, "success", {}))
                rc, out, _ = self.restate()
                self.assertVerdict(conclusion, rc, out)

    def test_the_wait_fits_the_job_s_limit(self):
        job = load("facts-review.yml")["jobs"]["facts-review"]
        self.assertEqual(job["permissions"], {"actions": "write"})
        self.assertNotIn("/pulls/", self.step["run"], "the job has no pull-requests scope")
        self.assertLess(int(self.env()["WAIT_SECONDS"]) + 3 * 35 + 60, job["timeout-minutes"] * 60)


def results(names, **given):
    """A needs context: every job of `names` succeeded, except as `given`."""
    return {n: given.get(n.replace("-", "_"), "success") for n in names}


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
        # HERE is the plan job's own condition
        self.assertEqual(s["env"]["HERE"], "${{ %s }}" % jobs["plan"]["if"])

        def env(here="true", plan="success", images='["checker"]', image="success"):
            return {"HERE": here, "PLAN": plan, "IMAGES": images, "IMAGE": image}
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
        ])

    def test_weekly(self):
        s = self.collector("weekly.yml", "weekly")
        # WARM_ASKED is the warm job's own condition
        self.assertEqual(s["env"]["WARM_ASKED"], "${{ %s }}" % load("weekly.yml")["jobs"]["warm"]["if"])
        names = ["plan", "sweep", "assets", "determinism", "determinism-compare", "warm"]

        def env(asked="false", **given):
            r = results(names, **dict({"warm": "skipped"}, **given))
            return {"WARM_ASKED": asked, "PLAN": r["plan"], "SWEEP": r["sweep"], "ASSETS": r["assets"],
                    "DETERMINISM": r["determinism"], "COMPARE": r["determinism-compare"], "WARM": r["warm"]}
        cases = [(env(), True), (env(asked="true", warm="success"), True)]
        for job in ("plan", "sweep", "assets", "determinism", "determinism_compare"):
            for result in ("failure", "cancelled", "skipped"):
                cases.append((env(**{job: result}), False))
        cases += [(env(asked="true"), False), (env(asked="true", warm="failure"), False),
                  (env(warm="success"), False)]
        self.check(s, cases)


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
        # the tools it runs are the base's copy, made before it, outside the tree it writes; the check comes after it
        self.assertEqual(step(job, "the tools, copied out of the tree they check")["run"].strip(),
                         'cp -r -- base/tools "$RUNNER_TEMP/tools"')
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
# at FAKE_ORIGIN: identical, ahead (the branch is after the commit), behind or diverged, with their merge base.
FAKE_COMPARE_GH = r"""#!/usr/bin/env bash
[ "$1" = api ] || exit 9; shift
filter=. endpoint=
while [ $# -gt 0 ]; do case $1 in --jq) filter=$2; shift 2 ;; *) endpoint=$1; shift ;; esac; done
spec=${endpoint##*/compare/}; a=${spec%%...*}; b=$(git -C "$FAKE_ORIGIN" rev-parse --verify -q "refs/heads/${spec#*...}") ||
  { echo "gh: Not Found (HTTP 404)" >&2; exit 1; }
mb=$(git -C "$FAKE_ORIGIN" merge-base "$a" "$b")
if [ "$a" = "$b" ]; then s=identical; elif [ "$mb" = "$a" ]; then s=ahead; elif [ "$mb" = "$b" ]; then s=behind
else s=diverged; fi
jq -n --arg s "$s" --arg mb "$mb" '{status: $s, merge_base_commit: {sha: $mb}}' | jq -r "$filter"
"""


@unittest.skipUnless(shutil.which("git") and shutil.which("jq"), "git or jq is not installed")
class BaseStepTest(unittest.TestCase):
    """pr.yml's plan and lint jobs take the base of a pull request from the merge commit GitHub built for the run, not
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
                          # what the plan job's base step requires of the base: the shared actions and the cache key
                          # script the workflow runs from the base
                          (".github/actions/plan-drafts/action.yml", "a\n"),
                          (".github/actions/place-drafts/action.yml", "a\n"), ("tools/oft/ci/cache-key.sh", "k\n")):
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

    def run_base(self, job, event, event_base, ref="refs/pull/1/merge", base_ref="main"):
        """The job's base step, in a fresh workspace whose head/ is a clone one commit deep of `ref`, as
        actions/checkout leaves it: its exit status, its output, the base it chose and the paths it found changed."""
        ws = tempfile.mkdtemp(dir=self.dir)
        head = os.path.join(ws, "head")
        os.mkdir(head)
        git(head, "init", "-q")
        git(head, "remote", "add", "origin", "file://" + self.origin)
        git(head, "fetch", "-q", "--depth=1", "origin", ref)
        git(head, "checkout", "-q", "--detach", "FETCH_HEAD")
        text = step(load("pr.yml")["jobs"][job], "the base branch, whose tools judge this change")["run"]
        runner, output = os.path.join(ws, "runner"), os.path.join(ws, "output")
        os.mkdir(runner)
        env = dict(os.environ, GITHUB_WORKSPACE=ws, RUNNER_TEMP=runner, GITHUB_OUTPUT=output, GITHUB_EVENT_NAME=event,
                   EVENT_BASE=event_base, KIND="maintainer", GIT_ALLOW_PROTOCOL="file", PATH=self.path,
                   FAKE_ORIGIN=self.origin, GH_TOKEN="t", GITHUB_REPOSITORY="acme/proofs", BASE_REF=base_ref)
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", text], cwd=ws, env=env,
                           capture_output=True, text=True)
        got, changed = {}, []
        if os.path.exists(output):
            with open(output) as f:
                got = dict(line.rstrip("\n").split("=", 1) for line in f if "=" in line)
        if os.path.exists(os.path.join(runner, "changed.txt")):
            with open(os.path.join(runner, "changed.txt")) as f:
                changed = f.read().split()
        return r.returncode, r.stdout + r.stderr, got.get("base"), changed

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


if __name__ == "__main__":
    unittest.main()
