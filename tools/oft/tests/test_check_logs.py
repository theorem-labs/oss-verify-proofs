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
# temporary folder, prints the message check.py prints, and exits 1.  Any other `run` prints a line and exits 0.
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


def check_job(workflow):
    return yamlio.load_file(os.path.join(WORKFLOWS, workflow))["jobs"]["check"]


def step(job, name):
    found = [s for s in job["steps"] if s.get("name") == name]
    assert len(found) == 1, name
    return found[0]


@unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
class CheckLogs(unittest.TestCase):
    def run_check(self, workflow="pr.yml", error=WARNINGS + ERROR, rc=1):
        """The check step of the workflow's check job, run as GitHub runs it: (exit status, its output, CHECK_LOGS,
        the docker calls)."""
        d = tempfile.mkdtemp()
        self.addCleanup(subprocess.run, ["rm", "-rf", "--", d])
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
                   FAKE_DOCKER_LOG=calls, FAKE_ERROR=os.path.join(d, "error.txt"), FAKE_DOCKER_RC=str(rc))
        script = step(check_job(workflow), "check")["run"]
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", script], env=env,
                           capture_output=True, text=True)
        with open(calls) as f:
            return r.returncode, r.stdout + r.stderr, logs, f.read().splitlines()

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

    def test_a_passing_check_prints_no_errors(self):
        rc, out, _, _ = self.run_check(rc=0)
        self.assertEqual(rc, 0, out)
        self.assertNotIn("the first errors", out)
        self.assertNotIn("Error: The reference foo", out)

    def test_both_workflows_run_the_same_step_and_upload_the_logs_when_it_fails(self):
        runs = []
        for workflow in ("pr.yml", "release-check.yml"):
            job = check_job(workflow)
            check = step(job, "check")
            self.assertEqual(check["env"]["CHECK_LOGS"], "${{ runner.temp }}/check-logs")
            runs.append(check["run"])
            upload = step(job, "oft check's logs, when the check failed or was stopped")
            self.assertEqual(job["steps"].index(upload), job["steps"].index(check) + 1)
            self.assertEqual(upload["if"], "failure() || cancelled()")
            self.assertTrue(upload["uses"].startswith("actions/upload-artifact@"))
            self.assertEqual(upload["with"]["path"].splitlines(), ["${{ runner.temp }}/check-logs/**/*.log",
                                                             "${{ runner.temp }}/check-logs/errors.txt"])
            self.assertEqual(upload["with"]["name"], "check-logs-${{ matrix.job.index }}-${{ github.run_attempt }}")
        self.assertEqual(runs[0], runs[1])


if __name__ == "__main__":
    unittest.main()
