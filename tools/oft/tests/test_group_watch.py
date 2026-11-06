"""pr.yml's watch of a merge queue group: the step `cancel this run once its merge queue group is gone`, the same in
the lint job and the check job, run as GitHub runs it.  When the queue drops a group, GitHub deletes the group's branch
and nothing stops its run; the watch cancels that run once two answers in a row say the branch does not exist (git
ls-remote --exit-code's exit status 2), and never on any other answer, so a group the queue still holds is never
cancelled.  It runs only for a merge queue group, and the two jobs that run it may cancel a run (actions: write).
pr.yml's concurrency comment has the measurements."""
import base64
import os
import subprocess
import tempfile
import time
import unittest

from oft import yamlio
from oft.tests.helpers import REPO

PR_YML = os.path.join(REPO, ".github", "workflows", "pr.yml")
WATCH = "cancel this run once its merge queue group is gone"
LOG = "the merge queue group's watch, its log"
JOBS = ("lint", "check")
REPOSITORY = "acme/proofs"
REF = "refs/heads/gh-readonly-queue/main/pr-656-" + "e" * 40
TOKEN = "t0ken"
RUN_ID = "4242"

# A git that answers each call from FAKE/answers, one exit status a line, and the last line again once they run out;
# each call logs its arguments, its directory and the header git would send.
FAKE_GIT = r"""#!/usr/bin/env bash
n=$(( $(cat "$FAKE/n" 2> /dev/null || echo 0) + 1 )); echo "$n" > "$FAKE/n"
echo "git $* | $PWD | ${GIT_CONFIG_KEY_0:-}: ${GIT_CONFIG_VALUE_0:-}" >> "$FAKE/calls"
rc=$(sed -n "${n}p" "$FAKE/answers"); [ -n "$rc" ] || rc=$(tail -n 1 "$FAKE/answers")
exit "$rc"
"""
FAKE_GH = '#!/usr/bin/env bash\necho "gh $*" >> "$FAKE/calls"\n'
# sleep takes no time here (or SLEEP_FOR seconds, for the real git below), and says that it was asked to
FAKE_SLEEP = '#!/usr/bin/env bash\necho "sleep $1" >> "$FAKE/calls"\n/bin/sleep "${SLEEP_FOR:-0}"\n'


def jobs(test):
    if not os.path.exists(PR_YML):
        test.skipTest("no .github/workflows/pr.yml beside tools/oft")
    return yamlio.load_file(PR_YML)["jobs"]


def step(job, name):
    found = [s for s in job["steps"] if s.get("name") == name]
    assert len(found) == 1, name
    return found[0]


class GroupWatchShape(unittest.TestCase):
    def setUp(self):
        self.jobs = jobs(self)

    def test_lint_and_check_start_the_same_watch_first_and_print_its_log_last(self):
        """First, so that it watches the whole job, checkout included; and lint runs before every job but plan."""
        for name in JOBS:
            with self.subTest(job=name):
                self.assertEqual(self.jobs[name]["steps"][0]["name"], WATCH)
                self.assertEqual(self.jobs[name]["steps"][-1]["name"], LOG)
        for name in (WATCH, LOG):
            with self.subTest(step=name):
                self.assertEqual(step(self.jobs["lint"], name), step(self.jobs["check"], name))

    def test_only_a_merge_queue_group_is_watched(self):
        """A pull request's run and a push's are cancelled by their own concurrency group, or never."""
        job = self.jobs["check"]
        self.assertEqual(step(job, WATCH)["if"], "github.event_name == 'merge_group'")
        self.assertEqual(step(job, LOG)["if"], "always() && github.event_name == 'merge_group'")
        self.assertEqual(step(job, WATCH)["env"], {"GH_TOKEN": "${{ github.token }}", "EVERY": "120", "CONFIRM": "10"})

    def test_the_two_jobs_may_cancel_a_run_and_keep_the_workflow_s_permissions(self):
        """A job's permissions replace the workflow's: these two keep contents: read and packages: read, and add
        actions: write, which `gh run cancel` needs.  No other job may cancel a run."""
        for name, job in self.jobs.items():
            with self.subTest(job=name):
                if name in JOBS:
                    self.assertEqual(job["permissions"], {"contents": "read", "packages": "read", "actions": "write"})
                else:
                    self.assertNotEqual((job.get("permissions") or {}).get("actions"), "write")


class GroupWatchRun(unittest.TestCase):
    """The watch step's script, run as GitHub runs a step, with a stand-in gh and sleep."""

    def setUp(self):
        self.jobs = jobs(self)
        self._tmp = tempfile.TemporaryDirectory(prefix="oft-group-watch-")
        self.dir = self._tmp.name
        self.fake = os.path.join(self.dir, "fake")
        self.bin = os.path.join(self.dir, "bin")
        self.temp = os.path.join(self.dir, "runner-temp")
        for d in (self.fake, self.bin, self.temp):
            os.mkdir(d)
        self.stand_in("gh", FAKE_GH)
        self.stand_in("sleep", FAKE_SLEEP)

    def tearDown(self):
        # a watch that a failed test left running
        subprocess.run(["pkill", "-f", os.path.join(self.temp, "group-watch")], capture_output=True)
        self._tmp.cleanup()

    def stand_in(self, name, text):
        path = os.path.join(self.bin, name)
        with open(path, "w") as f:
            f.write(text)
        os.chmod(path, 0o755)

    def start(self, server="https://github.com", **env):
        """Runs the step as GitHub does (bash --noprofile --norc -eo pipefail), with the values GitHub gives it: its
        exit status and output.  The watch goes on in the background."""
        s = step(self.jobs["check"], WATCH)
        script = os.path.join(self.dir, "step.sh")
        with open(script, "w") as f:
            f.write(s["run"])
        full = dict(os.environ, PATH=self.bin + os.pathsep + os.environ["PATH"], FAKE=self.fake,
                    RUNNER_TEMP=self.temp, GITHUB_SERVER_URL=server, GITHUB_REPOSITORY=REPOSITORY,
                    GITHUB_REF=REF, GITHUB_RUN_ID=RUN_ID, GH_TOKEN=TOKEN,
                    EVERY=s["env"]["EVERY"], CONFIRM=s["env"]["CONFIRM"], **env)
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", script], env=full, cwd=self.dir,
                           capture_output=True, text=True, timeout=30)
        return r.returncode, r.stdout + r.stderr

    def calls(self):
        path = os.path.join(self.fake, "calls")
        if not os.path.exists(path):
            return []
        with open(path) as f:
            return f.read().splitlines()

    def wait_for_cancel(self, seconds=20):
        end = time.monotonic() + seconds
        while time.monotonic() < end:
            if any(c.startswith("gh ") for c in self.calls()):
                time.sleep(0.2)   # anything the watch would still do after it
                return self.calls()
            time.sleep(0.05)
        self.fail("the watch cancelled nothing in %d s: %s" % (seconds, self.calls()[-10:]))

    def test_it_cancels_the_run_only_after_two_answers_in_a_row_that_the_branch_is_gone(self):
        """2 is git ls-remote --exit-code's answer for a ref that does not exist; any other exit status (0: the branch
        is there; 128: the network or the token failed; 1) is no answer.  `gone` stands for a call answered 2."""
        self.stand_in("git", FAKE_GIT)
        cases = (
            ("gone at once", [2, 2], ["gone", "sleep 10", "gone"]),
            ("there, then gone", [0, 0, 0, 2, 2],
             ["there", "sleep 120"] * 3 + ["gone", "sleep 10", "gone"]),
            ("gone once, then there again", [2, 0, 2, 0, 2, 2],
             ["gone", "sleep 10", "there", "sleep 120"] * 2 + ["gone", "sleep 10", "gone"]),
            ("errors are no answer", [128, 1, 128, 2, 128, 2, 2],
             ["error", "sleep 120"] * 3 + ["gone", "sleep 10", "error", "sleep 120", "gone", "sleep 10", "gone"]),
        )
        header = "http.https://github.com/.extraheader: AUTHORIZATION: basic " + \
            base64.b64encode(("x-access-token:" + TOKEN).encode()).decode()
        names = {0: "there", 1: "error", 2: "gone", 128: "error"}
        for name, answers, want in cases:
            with self.subTest(case=name):
                for f in ("n", "calls"):
                    if os.path.exists(os.path.join(self.fake, f)):
                        os.remove(os.path.join(self.fake, f))
                with open(os.path.join(self.fake, "answers"), "w") as f:
                    f.write("".join("%d\n" % a for a in answers))
                rc, out = self.start()
                self.assertEqual(rc, 0, out)
                self.assertIn("watching %s every 120 s" % REF, out)
                calls = self.wait_for_cancel()
                self.assertEqual(calls[-1], "gh run cancel %s --repo %s" % (RUN_ID, REPOSITORY))
                self.assertEqual(sum(c.startswith("gh ") for c in calls), 1, calls)
                git_calls = [c for c in calls if c.startswith("git ")]
                for c in git_calls:
                    self.assertEqual(c, "git ls-remote --exit-code https://github.com/%s.git %s | %s | %s"
                                     % (REPOSITORY, REF, self.temp, header))
                    self.assertNotIn(TOKEN, c.split(" | ")[0])
                got, n = [], 0
                for c in calls[:-1]:
                    if c.startswith("git "):
                        got.append(names[answers[min(n, len(answers) - 1)]])
                        n += 1
                    else:
                        got.append(c)
                self.assertEqual(got, want)
                with open(os.path.join(self.temp, "group-watch.log")) as f:
                    log = f.read()
                self.assertIn("%s does not exist, twice 10 s apart: the queue dropped this group, so run %s is "
                              "cancelled" % (REF, RUN_ID), log)
                os.remove(os.path.join(self.temp, "group-watch.log"))

    def test_with_the_real_git_a_branch_that_exists_is_never_gone_and_a_deleted_one_is(self):
        """git itself, over a repository on disk: while the group's branch is there, and while the repository cannot be
        read at all, the watch cancels nothing; once the branch is deleted, it cancels the run."""
        remote = os.path.join(self.dir, "server", REPOSITORY + ".git")
        os.makedirs(remote)
        git = ["git", "-c", "init.defaultBranch=main"]
        subprocess.run(git + ["init", "-q", "--bare", remote], check=True)
        work = os.path.join(self.dir, "work")
        subprocess.run(git + ["init", "-q", work], check=True)
        subprocess.run(["git", "-C", work, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q",
                        "--allow-empty", "-m", "group"], check=True)
        subprocess.run(["git", "-C", work, "push", "-q", remote, "HEAD:" + REF], check=True)
        server = "file://" + os.path.join(self.dir, "server")
        # the unreadable repository first, whose watch is then stopped: both watches are the one script
        for name, url in (("no repository there", server + "/missing"), ("the branch is there", server)):
            with self.subTest(case=name):
                if os.path.exists(os.path.join(self.fake, "calls")):
                    os.remove(os.path.join(self.fake, "calls"))
                rc, out = self.start(server=url, SLEEP_FOR="0.05")
                self.assertEqual(rc, 0, out)
                time.sleep(1.5)
                calls = self.calls()
                self.assertGreater(sum(c == "sleep 120" for c in calls), 5, calls)
                self.assertFalse([c for c in calls if c.startswith("gh ")], calls)
                if url != server:
                    subprocess.run(["pkill", "-f", os.path.join(self.temp, "group-watch")], capture_output=True)
                    time.sleep(0.2)
        subprocess.run(["git", "-C", remote, "update-ref", "-d", REF], check=True)
        calls = self.wait_for_cancel()
        self.assertEqual(calls[-2:], ["sleep 10", "gh run cancel %s --repo %s" % (RUN_ID, REPOSITORY)])
        self.assertEqual(sum(c.startswith("gh ") for c in calls), 1, calls)

    def test_the_log_step_prints_what_the_watch_wrote_and_passes_without_it(self):
        s = step(self.jobs["check"], LOG)
        for text in ("2026-11-04T04:29:00Z ... so run 4242 is cancelled\n", None):
            with self.subTest(log=text is not None):
                path = os.path.join(self.temp, "group-watch.log")
                if text is None:
                    if os.path.exists(path):
                        os.remove(path)
                else:
                    with open(path, "w") as f:
                        f.write(text)
                r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", s["run"]],
                                   env=dict(os.environ, RUNNER_TEMP=self.temp), capture_output=True, text=True)
                self.assertEqual((r.returncode, r.stdout), (0, text or ""))


if __name__ == "__main__":
    unittest.main()
