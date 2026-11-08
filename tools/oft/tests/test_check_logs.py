"""The check step of pr.yml's and release-check.yml's check jobs, run as GitHub runs it, with a stand-in check-units.sh
and a stand-in docker: each container with a writable /work keeps its temporary folder, oft check's logs in it, in
CHECK_LOGS/tmp, which outlives it; and when the check fails, the job's own output holds the first `File ..., line N`
and `Error` lines of each log a failure names, at most 8,000 bytes of them, as bin/ossv-n6-pod prints them.

The workflows are in a checkout only, so these tests skip in tools/oft alone (the runner image's copy)."""
import os
import subprocess
import tempfile
import textwrap
import unittest

from oft import yamlio
from oft.tests.helpers import REPO

WORKFLOWS = os.path.join(REPO, ".github", "workflows")
HAVE_WORKFLOWS = os.path.isdir(WORKFLOWS)
NO_WORKFLOWS = "no .github/workflows: tools/oft without the checkout around it"
ERROR = 'File "proofs/zlib/checksum_fuzzer/lib/Lib.v", line 42, characters 0-10:\nError: The reference foo was not found.\n'
# 200 warnings ahead of the error, 3 lines each, in the form a proof library's dune log on the check runner holds them:
# 40 of their `File` lines with context would fill the 8,000 bytes before the error
WARNINGS = ('File "proofs/zlib/checksum_fuzzer/lib/ExN.v", line 4, characters 0-16:\n'
            'Warning: There is no flag or option with this name: "Lia Cache".\n[unknown-option,default]\n') * 200
LOG = "oft-check-abc123/zlib.checksum_fuzzer.lib.dune.log"

# Stands in for docker.  It logs each call to $FAKE_DOCKER_LOG.  A `run` given `-v <dir>:/oft-check-logs` and
# `-e TMPDIR=/oft-check-logs` does what a failed proof library build in the checker image does: oft check writes its
# dune log, with $FAKE_ERROR after 1000 lines and before 50000 more, and a compiled file beside it, into that
# temporary folder, prints the message check.py prints, and exits 1.  With $FAKE_DOCKER_LINK set it also plants, as a
# hostile build can, the symbolic links a later step must take out: one at the top, one deeper, one not named `*.log`,
# one to a *directory* and named `*.log`, and one inside a directory it chmods 500 against the runner, which the
# wrapper's own `find` cannot unlink.  Any other `run` prints a line and exits 0.
FAKE_DOCKER = textwrap.dedent(r"""    #!/bin/bash
    echo "docker $*" >> "$FAKE_DOCKER_LOG"
    [ "$1" = run ] || exit 0
    tmp= tmpdir=
    while [ $# -gt 0 ]; do
      case $1 in
        -v) [[ "$2" == *:/oft-check-logs ]] && tmp="${2%:/oft-check-logs}"; shift 2 ;;
        -e) [ "$2" = TMPDIR=/oft-check-logs ] && tmpdir=1; shift 2 ;;
        *) shift ;;
      esac
    done
    if [ -z "$tmp" ] || [ -z "$tmpdir" ]; then echo "a container with no logs folder"; exit 0; fi
    mkdir -p "$tmp/oft-check-abc123/proof-1"
    { yes noise | head -n 1000; cat "$FAKE_ERROR"; yes "more noise" | head -n 50000; } > "$tmp/@LOG@"
    : > "$tmp/oft-check-abc123/proof-1/Proof.vo"
    if [ -n "${FAKE_DOCKER_LINK:-}" ]; then
      ln -s "$FAKE_DOCKER_LINK" "$tmp/evil.log"
      ln -s "$FAKE_DOCKER_LINK" "$tmp/oft-check-abc123/deeper.log"
      ln -s "$FAKE_DOCKER_LINK" "$tmp/not-a-log"
      ln -s "$(dirname "$FAKE_DOCKER_LINK")" "$tmp/dirlink.log"
      mkdir -p "$tmp/oft-check-abc123/locked"
      ln -s "$FAKE_DOCKER_LINK" "$tmp/oft-check-abc123/locked/trap.log"
      chmod 500 "$tmp/oft-check-abc123/locked"
    fi
    echo "FAIL proofs/zlib/checksum_fuzzer/lib: does not compile (see /oft-check-logs/@LOG@)"
    exit "${FAKE_DOCKER_RC:-1}"
""").replace("@LOG@", LOG)

# Stands in for check-units.sh: the facts container (/work read-only), then one unit's build in its view (a writable
# /work), as check-units.sh runs them, and the exit status of the build.
CHECK_UNITS = textwrap.dedent(r"""    #!/bin/bash
    set -euo pipefail
    docker run --rm --network none -v "$WORK:/work:ro" -v "$WORK/facts:/facts" -w /work checker python3 -m oft.check
    status=0
    docker run --rm --network none -v "$WORK/view:/work" -v "$WORK/x:/work/x:ro" -w /work checker \
      python3 -m oft.check --root /work --facts-from /facts zlib/checksum_fuzzer --parts statements,proofs || status=$?
    exit "$status"
""")

# Stands in for docker in the step that sweeps before the upload, so that no test reaches the real daemon.  `ps -q`
# names the container $FAKE_CONTAINER, as a build that outlived the runner's cancellation leaves running, and `kill`
# writes down the links that were still there when it was called: the step must kill before it sweeps, or that line
# would be empty and a container could plant again before the upload globs.
SWEEP_DOCKER = textwrap.dedent(r"""    #!/bin/bash
    echo "docker $*" >> "$FAKE_DOCKER_LOG"
    case "$1" in
      ps) [ -z "${FAKE_CONTAINER:-}" ] || echo "$FAKE_CONTAINER" ;;
      kill) find "$RUNNER_TEMP/check-logs" -type l | sort | sed 's|^|still there: |' >> "$FAKE_DOCKER_LOG" ;;
    esac
""")


def check_job(workflow):
    return yamlio.load_file(os.path.join(WORKFLOWS, workflow))["jobs"]["check"]


def step(job, name):
    found = [s for s in job["steps"] if s.get("name") == name]
    assert len(found) == 1, name
    return found[0]


def what_upload_would_read(folder):
    """The bytes actions/upload-artifact would put in the artifact for `<folder>/**/*.log`.

    At the pinned ea165f8d65b6 its search globs with `followSymbolicLinks: true` and filters the hits with `fs.stat`,
    not `lstat`, so a link named `*.log` contributes the bytes of what it points at, and a link to a directory is
    walked into."""
    found = []
    for d, _dirs, names in os.walk(folder, followlinks=True):
        for n in sorted(names):
            if n.endswith(".log"):
                with open(os.path.join(d, n), "rb") as f:
                    found.append(f.read())
    return b"".join(found)


def links_under(folder):
    """Every symbolic link left in the folder, by its path from it."""
    out = []
    for d, dirs, names in os.walk(folder):
        for n in dirs + names:
            p = os.path.join(d, n)
            if os.path.islink(p):
                out.append(os.path.relpath(p, folder))
    return sorted(out)


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class CheckLogs(unittest.TestCase):
    def run_check(self, workflow="pr.yml", error=WARNINGS + ERROR, rc=1, link=""):
        """The check step of the workflow's check job, run as GitHub runs it: (exit status, its output, CHECK_LOGS,
        the docker calls).  LINK, where given, is the file the build leaves symbolic links to in its log folder."""
        d = tempfile.mkdtemp()
        self.addCleanup(self.remove, d)
        os.makedirs(os.path.join(d, "tools", "oft", "ci"))
        os.makedirs(os.path.join(d, "bin"))
        os.makedirs(os.path.join(d, "runner"))
        with open(os.path.join(d, "tools", "oft", "ci", "check-units.sh"), "w") as f:
            f.write(CHECK_UNITS)
        with open(os.path.join(d, "bin", "docker"), "w") as f:
            f.write(FAKE_DOCKER)
        os.chmod(os.path.join(d, "bin", "docker"), 0o755)
        with open(os.path.join(d, "error.txt"), "w") as f:
            f.write(error)
        logs = os.path.join(d, "runner", "check-logs")
        calls = os.path.join(d, "docker.log")
        env = dict(os.environ, PATH=os.path.join(d, "bin") + os.pathsep + os.environ["PATH"], WORK=d,
                   TOOLS=os.path.join(d, "tools"), RUNNER_TEMP=os.path.join(d, "runner"), CHECK_LOGS=logs,
                   FAKE_DOCKER_LOG=calls, FAKE_ERROR=os.path.join(d, "error.txt"), FAKE_DOCKER_RC=str(rc),
                   FAKE_DOCKER_LINK=link)
        script = step(check_job(workflow), "check")["run"]
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", script], env=env,
                           capture_output=True, text=True)
        with open(calls) as f:
            return r.returncode, r.stdout + r.stderr, logs, f.read().splitlines()

    def remove(self, d):
        """The stand-in build chmods a directory of its own against the runner, as a hostile one can."""
        subprocess.run(["chmod", "-R", "u+rwX", "--", d])
        subprocess.run(["rm", "-rf", "--", d])

    def run_sweep(self, workflow, runner_temp, container=""):
        """The step that takes the build's links out of the logs, run alone, as it runs before the upload.

        Docker is a stand-in of this suite's, never the box's daemon; CONTAINER is the one it reports still running.
        Gives back (exit status, its output, the docker calls)."""
        d = tempfile.mkdtemp()
        self.addCleanup(self.remove, d)
        with open(os.path.join(d, "docker"), "w") as f:
            f.write(SWEEP_DOCKER)
        os.chmod(os.path.join(d, "docker"), 0o755)
        calls = os.path.join(d, "docker.log")
        open(calls, "w").close()
        script = step(check_job(workflow), "the build's symbolic links, out of the logs this job uploads")["run"]
        r = subprocess.run(
            ["bash", "--noprofile", "--norc", "-e", "-c", script],
            env=dict(os.environ, PATH=d + os.pathsep + os.environ["PATH"], RUNNER_TEMP=runner_temp,
                     FAKE_DOCKER_LOG=calls, FAKE_CONTAINER=container),
            capture_output=True, text=True)
        with open(calls) as f:
            return r.returncode, r.stdout + r.stderr, f.read().splitlines()

    def test_a_failed_build_s_rocq_error_is_in_the_job_output(self):
        for workflow in ("pr.yml", "release-check.yml"):
            with self.subTest(workflow=workflow):
                rc, out, logs, calls = self.run_check(workflow)
                self.assertEqual(rc, 1, out)
                self.assertIn("does not compile (see /oft-check-logs/%s)" % LOG, out)
                self.assertIn("== the first errors of %s (51602 lines):" % LOG, out)
                # the error's block: its File line, 5 lines of context above it and 5 below; no other warning
                self.assertIn('1601-File "proofs/zlib/checksum_fuzzer/lib/Lib.v", line 42', out)
                self.assertIn("1602:Error: The reference foo was not found.", out)
                self.assertIn("1596-", out)
                self.assertNotIn("1595-", out)
                self.assertIn("1607-more noise", out)
                self.assertNotIn("1608-more noise", out)
                self.assertEqual(out.count("Warning: There is no flag"), 2, out)
                self.assertNotIn("cut at", out)
                # the log outlives its container; nothing else it left in its temporary folder does
                self.assertTrue(os.path.isfile(os.path.join(logs, "tmp", LOG)))
                self.assertFalse(os.path.exists(os.path.join(logs, "tmp", "oft-check-abc123", "proof-1")))
                self.assertTrue(os.path.isfile(os.path.join(logs, "check-units.log")))
                # only the container with a writable /work gets the folder; the facts container is run as it was
                self.assertEqual(len(calls), 2, calls)
                self.assertNotIn("/oft-check-logs", calls[0])
                self.assertIn("-v %s/tmp:/oft-check-logs -e TMPDIR=/oft-check-logs " % logs, calls[1])

    def test_what_it_prints_is_cut_at_8000_bytes(self):
        # 40 Error lines of 300 bytes each: grep's -m 40 alone leaves 12,000 bytes
        rc, out, _, _ = self.run_check(error=("Error: " + "x" * 293 + "\n") * 100)
        self.assertEqual(rc, 1, out)
        printed = out.split("== the first errors of the logs the failures name", 1)[1]
        self.assertIn("== cut at 8000 of ", printed)
        self.assertLess(len(printed.encode()), 8000 + 300)

    def test_a_log_with_no_error_line_gets_its_file_lines(self):
        rc, out, _, _ = self.run_check(error='File "proofs/zlib/checksum_fuzzer/lib/Lib.v", line 7, characters 0-3:\n'
                                             "Syntax error: '.' expected.\n")
        self.assertEqual(rc, 1, out)
        self.assertIn('1001:File "proofs/zlib/checksum_fuzzer/lib/Lib.v", line 7', out)
        self.assertIn("1002-Syntax error: '.' expected.", out)

    def planted_secret(self):
        """A stand-in ~/.docker/config.json, which the ghcr.io login step writes with this job's token before the
        check runs, and which is the richest thing on the runner for a build's link to point at."""
        secret = tempfile.mkdtemp()
        self.addCleanup(self.remove, secret)
        config = os.path.join(secret, "config.json")
        with open(config, "w") as f:
            f.write('{"auths":{"ghcr.io":{"auth":"ghs_THE_JOB_TOKEN"}}}\n')
        return config

    def test_the_links_a_build_leaves_are_gone_before_the_logs_are_uploaded(self):
        """/oft-check-logs is the build's own writable TMPDIR, and the step uploads check-logs/**/*.log with
        actions/upload-artifact, which follows a symbolic link, so a `*.log` link the build leaves would carry the
        bytes of what it points at into an artifact anyone who can read the pull request may download.

        The docker wrapper's `find` drops every link as each container exits, but not from a directory the build
        chmods against the runner: it owns what it writes, `find` cannot unlink there, and the wrapper's status is the
        container's.  The step before the upload makes the folder the runner's again and sweeps what is left."""
        config = self.planted_secret()
        for workflow in ("pr.yml", "release-check.yml"):
            with self.subTest(workflow=workflow):
                rc, out, logs, _ = self.run_check(workflow, link=config)
                self.assertEqual(rc, 1, out)
                tmp = os.path.join(logs, "tmp")
                # the wrapper took what it could reach; the build's locked directory kept its link
                self.assertEqual(links_under(tmp), [os.path.join("oft-check-abc123", "locked", "trap.log")])
                self.assertEqual(self.run_sweep(workflow, os.path.dirname(logs))[:2], (0, ""))
                self.assertEqual(links_under(logs), [])
                left = sorted(os.path.relpath(os.path.join(d, n), tmp)
                              for d, _dirs, names in os.walk(tmp) for n in names)
                self.assertEqual(left, [LOG])  # the build's real log, and nothing it linked to
                self.assertNotIn(b"ghs_THE_JOB_TOKEN", what_upload_would_read(logs))
                self.assertTrue(os.path.isfile(config))  # the links went, not the file they pointed at
                self.assertNotIn("ghs_THE_JOB_TOKEN", out)

    def test_the_sweep_takes_the_links_a_cancelled_check_left_behind(self):
        """GitHub cancels a job that reaches timeout-minutes, so a build that plants a link and then hangs has the
        check step killed inside its container: the wrapper never returns and its cleanup never runs.  The upload
        still runs, on `cancelled()`.  The sweep carries the upload's own condition, so it runs on that path too;
        this plants the tree such a build leaves and runs the sweep alone over it."""
        config = self.planted_secret()
        for workflow in ("pr.yml", "release-check.yml"):
            with self.subTest(workflow=workflow):
                runner = tempfile.mkdtemp()
                self.addCleanup(self.remove, runner)
                tmp = os.path.join(runner, "check-logs", "tmp")
                os.makedirs(os.path.join(tmp, "oft-check-abc123", "locked"))
                with open(os.path.join(tmp, LOG.split("/")[0], "real.log"), "w") as f:
                    f.write("Error: the build's own log\n")
                os.symlink(config, os.path.join(tmp, "evil.log"))
                os.symlink(os.path.dirname(config), os.path.join(tmp, "dirlink.log"))
                os.symlink(config, os.path.join(tmp, "oft-check-abc123", "locked", "trap.log"))
                os.chmod(os.path.join(tmp, "oft-check-abc123", "locked"), 0o500)
                # what the upload would carry out of the runner without the sweep
                self.assertIn(b"ghs_THE_JOB_TOKEN", what_upload_would_read(os.path.join(runner, "check-logs")))
                self.assertEqual(self.run_sweep(workflow, runner)[:2], (0, ""))
                self.assertEqual(links_under(os.path.join(runner, "check-logs")), [])
                self.assertNotIn(b"ghs_THE_JOB_TOKEN", what_upload_would_read(os.path.join(runner, "check-logs")))
                with open(os.path.join(tmp, "oft-check-abc123", "real.log")) as f:
                    self.assertEqual(f.read(), "Error: the build's own log\n")  # a real log is untouched
                self.assertTrue(os.path.isfile(config))

    def test_the_sweep_kills_a_container_still_writing_before_it_takes_the_links(self):
        """`docker run` is a client: the runner's cancellation kills the step's process tree, and a build that
        ignores the signals the client forwards keeps running under the daemon with /oft-check-logs still mounted,
        so it plants its link again after a sweep and before the upload globs.  The step kills what is running
        first — `docker kill` is SIGKILL from the daemon, which no build can trap — and only then sweeps."""
        config = self.planted_secret()
        for workflow in ("pr.yml", "release-check.yml"):
            with self.subTest(workflow=workflow):
                runner = tempfile.mkdtemp()
                self.addCleanup(self.remove, runner)
                tmp = os.path.join(runner, "check-logs", "tmp")
                os.makedirs(tmp)
                os.symlink(config, os.path.join(tmp, "evil.log"))
                rc, out, calls = self.run_sweep(workflow, runner, container="deadbeefcafe")
                self.assertEqual((rc, out), (0, ""))
                self.assertEqual(calls, ["docker ps -q",
                                         "docker kill deadbeefcafe",
                                         "still there: %s" % os.path.join(tmp, "evil.log")])
                self.assertEqual(links_under(os.path.join(runner, "check-logs")), [])

    def test_the_sweep_ends_at_once_when_the_check_never_made_the_folder(self):
        """A job that fails or is cancelled before the check step (checkout, pip, the drafts, the ghcr login) has no
        log folder; `find` on a missing path exits 1 and the step is `bash -e`, so without the guard every such run
        would show a second red step saying nothing about the real failure."""
        for workflow in ("pr.yml", "release-check.yml"):
            with self.subTest(workflow=workflow):
                runner = tempfile.mkdtemp()
                self.addCleanup(self.remove, runner)
                self.assertEqual(self.run_sweep(workflow, runner, container="deadbeefcafe"), (0, "", []))

    def test_a_passing_check_prints_no_errors(self):
        rc, out, _, _ = self.run_check(rc=0)
        self.assertEqual(rc, 0, out)
        self.assertNotIn("the first errors", out)
        self.assertNotIn("Error: The reference foo", out)

    def test_both_workflows_run_the_same_step_and_upload_the_logs_when_it_fails(self):
        runs = []
        sweeps = []
        for workflow in ("pr.yml", "release-check.yml"):
            job = check_job(workflow)
            check = step(job, "check")
            self.assertEqual(check["env"]["CHECK_LOGS"], "${{ runner.temp }}/check-logs")
            runs.append(check["run"])
            # the sweep is between the two, and carries the upload's own condition so that it runs when the job was
            # cancelled and the wrapper's own cleanup never did
            sweep = step(job, "the build's symbolic links, out of the logs this job uploads")
            sweeps.append(sweep["run"])
            upload = step(job, "oft check's logs, when the check failed or was stopped")
            self.assertEqual(job["steps"].index(sweep), job["steps"].index(check) + 1)
            self.assertEqual(job["steps"].index(upload), job["steps"].index(sweep) + 1)
            self.assertEqual(sweep["if"], "failure() || cancelled()")
            self.assertEqual(upload["if"], "failure() || cancelled()")
            self.assertTrue(upload["uses"].startswith("actions/upload-artifact@"))
            self.assertEqual(upload["with"]["path"].splitlines(), ["${{ runner.temp }}/check-logs/**/*.log",
                                                             "${{ runner.temp }}/check-logs/errors.txt"])
            self.assertEqual(upload["with"]["name"], "check-logs-${{ matrix.job.index }}-${{ github.run_attempt }}")
        self.assertEqual(runs[0], runs[1])
        self.assertEqual(sweeps[0], sweeps[1])


if __name__ == "__main__":
    unittest.main()
