"""The shellcheck steps of the stream_tools job of .github/workflows/pr.yml: the one place that fetches shellcheck,
which serves the pinned tarball out of the Actions cache.

Two kinds of test.  The structural ones read the workflows: that no workflow downloads shellcheck anywhere else,
that the restore and the save name one key and one path, and that the save runs only where it may.  The rehearsals
run the steps' own bash, as the tests of tools/oft/ci's scripts do, against a stand-in curl and a stand-in tarball,
over the three cases the cache has: a hit whose bytes are the pinned ones, a hit whose bytes are not, and a miss.  A
hit is not trusted because it is a hit, and both the guard and the case it must not catch are here.

The release tarball is never downloaded by these tests.  The stand-in is a tar.xz built here, under a version of its
own, and the steps read the version and the hash from their `env:`, which a rehearsal sets, so a step that read the
pin some other way would fail these."""
import hashlib
import os
import re
import shutil
import subprocess
import tempfile
import unittest

from oft import yamlio
from oft.tests import helpers
from oft.tests.helpers import NO_HOME, REPO, child_environment

WORKFLOWS = os.path.join(REPO, ".github", "workflows")
PR = os.path.join(WORKFLOWS, "pr.yml")
JOB = "stream_tools"
# The stand-in's version. Not the pinned one, so a rehearsal that read the pin instead of its env would fail.
VERSION = "9.9.9"
# A stand-in curl: it records its arguments, and copies $CURL_SERVES to the --output path, or fails with
# $CURL_EXIT when that is set, as curl does when it gives up.
CURL = '''#!/bin/bash
printf '%s\\n' "$@" > "$CURL_LOG"
if [ -n "${CURL_EXIT:-}" ]; then echo "curl: (${CURL_EXIT}) stand-in failure" >&2; exit "$CURL_EXIT"; fi
out=; prev=
for a in "$@"; do [ "$prev" = --output ] && out=$a; prev=$a; done
[ -n "$out" ] || { echo "stand-in curl: no --output" >&2; exit 2; }
cp -- "$CURL_SERVES" "$out"
'''


def steps(job=JOB):
    return helpers.with_scripts(yamlio.load_file(PR))["jobs"][job]["steps"]


def step(step_id):
    for s in steps():
        if s.get("id") == step_id:
            return s
    raise AssertionError("no step with id %r in pr.yml's %s job" % (step_id, JOB))


def cache_step(kind):
    """The restore or the save step of the shellcheck cache, found by what it uses and by its path."""
    found = [s for s in steps()
             if s.get("uses", "").startswith("actions/cache/%s@" % kind)
             and "shellcheck-cache" in str(s.get("with", {}).get("path", ""))]
    if len(found) != 1:
        raise AssertionError("%d shellcheck cache %s step(s) in pr.yml's %s job" % (len(found), kind, JOB))
    return found[0]


def render(text, values):
    """A `${{ ... }}` expression replaced by what the test says it is.  An expression the test did not name is a
    failure, never an empty string: a rehearsal that quietly dropped one would run a script the job does not."""
    def one(m):
        expression = m.group(1).strip()
        if expression not in values:
            raise AssertionError("the rehearsal does not say what %r is" % expression)
        return values[expression]
    return re.sub(r"\$\{\{(.*?)\}\}", one, text)


def tarball(directory, name, version=VERSION, body="#!/bin/sh\necho 'ShellCheck - shell script analysis tool'\n"):
    """A tar.xz holding shellcheck-v<version>/shellcheck, as the release tarball does.  Returns its path."""
    stage = os.path.join(directory, "stage-" + name)
    inner = os.path.join(stage, "shellcheck-v" + version)
    os.makedirs(inner, exist_ok=True)
    with open(os.path.join(inner, "shellcheck"), "w") as f:
        f.write(body)
    os.chmod(os.path.join(inner, "shellcheck"), 0o755)
    path = os.path.join(directory, name)
    subprocess.run(["tar", "--create", "--xz", "--file", path, "-C", stage, "shellcheck-v" + version], check=True)
    return path


def sha256(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


class Structure(unittest.TestCase):
    """What the workflows say, read as YAML."""

    def test_only_this_job_downloads_shellcheck(self):
        """One copy of the fetch, and it is this job's.  Another job that grew its own would be caught here; the
        day a second one needs shellcheck, the four steps become a composite action rather than a copy."""
        for name in sorted(os.listdir(WORKFLOWS)):
            with open(os.path.join(WORKFLOWS, name)) as f:
                text = f.read()
            with self.subTest(workflow=name):
                if name != "pr.yml":
                    self.assertNotIn("koalaman", text, "this workflow downloads shellcheck itself")
        self.assertEqual(1, sum("koalaman" in str(s.get("run", "")) for s in steps()))
        for job, body in helpers.with_scripts(yamlio.load_file(PR))["jobs"].items():
            if job != JOB:
                with self.subTest(job=job):
                    self.assertNotIn("koalaman", str(body.get("steps", "")))

    def test_the_restore_and_the_save_name_one_key_and_one_path(self):
        """A save under another key or another path is an entry no restore ever matches: actions/cache versions an
        entry by its path as well as its key."""
        restore, save = cache_step("restore"), cache_step("save")
        self.assertEqual(restore["with"]["key"], save["with"]["key"])
        self.assertEqual(restore["with"]["path"], save["with"]["path"])
        self.assertEqual("${{ steps.shellcheck_key.outputs.key }}", restore["with"]["key"])

    def test_the_restore_matches_the_key_exactly_and_a_miss_is_not_a_failure(self):
        """No restore-keys: a near match is a different file, and the only thing to do with it would be to fail on
        its hash.  No fail-on-cache-miss either: actions/cache warns and reports no hit when the cache service
        fails, and turning that into a red job is the thing these steps exist to stop."""
        with_ = cache_step("restore")["with"]
        self.assertNotIn("restore-keys", with_)
        self.assertNotIn("fail-on-cache-miss", with_)

    def test_the_save_runs_only_on_a_miss_and_never_from_a_fork(self):
        save = cache_step("save")
        self.assertIn("steps.shellcheck.outputs.cache-hit == 'false'", save["if"])
        self.assertIn("github.event.pull_request.head.repo.fork != true", save["if"])

    def test_the_entry_is_saved_before_any_code_of_the_change_runs(self):
        """The job runs the change's code from its install of dev/stream/uv.lock on, and code that runs as the job's
        user can rewrite the cache directory between the hash check and the save.  So the steps up to the save are
        the checkout, the deepen of its history, setup-python and the four shellcheck steps, and nothing of the
        change runs among them: no `run` starts a file of the checkout, uv, pip or python."""
        all_steps = steps()
        at = all_steps.index(cache_step("save"))
        before = [s.get("name") or s["uses"].split("@")[0] for s in all_steps[:at + 1]]
        self.assertEqual(before, ["actions/checkout", "this commit's whole history, and no other branch's",
                                  "actions/setup-python", "the key of the pinned shellcheck tarball",
                                  "the pinned shellcheck tarball, where a run before this one kept it",
                                  "shellcheck on PATH, hashed whichever way it came",
                                  "keep the pinned shellcheck tarball for the runs after this one"])
        for s in all_steps[:at + 1]:
            run = "\n".join(line for line in s.get("run", "").splitlines() if not line.strip().startswith("#"))
            self.assertNotRegex(run, r"\./dev/stream|head/dev/stream|\buv |\bpip |\bpython3? ", s.get("name"))
        install = next(i for i, s in enumerate(all_steps)
                       if s.get("name") == "ruff, pytest and uv, which the check and the tests need, pinned and hashed")
        self.assertEqual(install, at + 1)

    def test_the_two_steps_name_one_pin(self):
        """The key step and the install step each carry the version and the hash; two pins that drifted apart
        would key an entry by one file and check the bytes against another."""
        key, install = step("shellcheck_key"), step("shellcheck")
        self.assertEqual(str(key["env"]["VERSION"]), str(install["env"]["VERSION"]))
        self.assertEqual(str(key["env"]["SHA256"]), str(install["env"]["SHA256"]))
        self.assertEqual("0.11.0", str(key["env"]["VERSION"]))
        self.assertRegex(str(key["env"]["SHA256"]), r"^[0-9a-f]{64}$")

    def test_the_download_retries_every_transient_error_within_a_bound(self):
        """The 504s of 2026-11-09 came back as 5xx and as reset connections; --retry alone covers only the first,
        and an unbounded retry is a step that hangs instead of a step that fails."""
        run = step("shellcheck")["run"]
        for flag in ("--retry-all-errors", "--retry-max-time", "--connect-timeout", "--fail"):
            with self.subTest(flag=flag):
                self.assertIn(flag, run)


class Rehearsal(unittest.TestCase):
    """The steps' bash, run here.  Each case builds the cache directory the restore would have left, puts a
    stand-in curl in front of PATH, and reads the step's exit status, its $GITHUB_OUTPUT, its $GITHUB_PATH and
    whether curl was called at all."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="oft-shellcheck-")
        self.dir = self._tmp.name
        self.temp = os.path.join(self.dir, "runner-temp")
        self.store = os.path.join(self.temp, "shellcheck-cache")
        self.bin = os.path.join(self.temp, "tools-bin")
        self.path_dir = os.path.join(self.dir, "stand-ins")
        os.makedirs(self.temp)
        os.makedirs(self.path_dir)
        self.curl_log = os.path.join(self.dir, "curl-args")
        curl = os.path.join(self.path_dir, "curl")
        with open(curl, "w") as f:
            f.write(CURL)
        os.chmod(curl, 0o755)
        self.good = tarball(self.dir, "good.tar.xz")
        self.sha = sha256(self.good)
        self.addCleanup(self._tmp.cleanup)

    def run_step(self, step_id, restored="", serves=None, curl_exit=None, sha=None, version=VERSION):
        """One step of the job, with its `env:` rendered and the pin replaced by the stand-in's, run under bash."""
        s = step(step_id)
        sha = self.sha if sha is None else sha
        values = {"runner.temp": self.temp, "steps.shellcheck_key.outputs.key": self.key(version, sha),
                  "steps.shellcheck_restore.outputs.cache-hit": restored}
        env = {name: render(str(value), values) for name, value in s["env"].items()}
        # the pin the step carries, replaced by the stand-in's: the step reads both out of its environment
        env.update(VERSION=version, SHA256=sha)
        out, github_path = os.path.join(self.dir, "output"), os.path.join(self.dir, "github-path")
        for f in (out, github_path):
            open(f, "a").close()
        env.update(GITHUB_OUTPUT=out, GITHUB_PATH=github_path, CURL_LOG=self.curl_log,
                   CURL_SERVES=serves or os.devnull, PATH=self.path_dir + os.pathsep + os.environ["PATH"])
        if curl_exit is not None:
            env["CURL_EXIT"] = str(curl_exit)
        done = subprocess.run(["bash", "-c", s["run"]], capture_output=True, text=True,
                              env=child_environment(NO_HOME, **env), cwd=self.dir)
        with open(out) as f:
            outputs = dict(line.split("=", 1) for line in f.read().splitlines() if "=" in line)
        with open(github_path) as f:
            on_path = f.read().split()
        return done, outputs, on_path

    def key(self, version=VERSION, sha=None):
        return "shellcheck-%s-%s" % (version, self.sha if sha is None else sha)

    def place(self, source, version=VERSION):
        """What a restored cache entry leaves behind: the tarball under the store, at the name the step reads."""
        os.makedirs(self.store, exist_ok=True)
        shutil.copy(source, os.path.join(self.store, "shellcheck-v%s.linux.x86_64.tar.xz" % version))

    def curl_ran(self):
        return os.path.exists(self.curl_log)

    # ---- the key step -------------------------------------------------------------------------------------

    def test_the_key_names_the_version_and_the_hash(self):
        done, outputs, _ = self.run_step("shellcheck_key")
        self.assertEqual(0, done.returncode, done.stderr)
        self.assertEqual(self.key(), outputs["key"])

    def test_the_key_step_refuses_a_version_or_a_hash_it_cannot_read(self):
        """The guard, against what it exists to catch.  A key built out of junk would name an entry nobody
        pinned."""
        for version, sha in ((VERSION, "not-a-hash"), ("v9.9.9", self.sha), (VERSION, self.sha.upper())):
            with self.subTest(version=version, sha=sha):
                done, _, _ = self.run_step("shellcheck_key", version=version, sha=sha)
                self.assertEqual(1, done.returncode)
                self.assertIn("::error::", done.stdout)

    def test_the_real_pin_passes_that_guard(self):
        """The case it must not catch: the version and the hash the job actually carries."""
        env = step("shellcheck_key")["env"]
        done, outputs, _ = self.run_step("shellcheck_key", version=str(env["VERSION"]), sha=str(env["SHA256"]))
        self.assertEqual(0, done.returncode, done.stderr)
        self.assertEqual("shellcheck-%s-%s" % (env["VERSION"], env["SHA256"]), outputs["key"])

    # ---- the install step, over the three cases the cache has ---------------------------------------------

    def test_a_hit_whose_bytes_are_the_pinned_ones_downloads_nothing(self):
        self.place(self.good)
        done, outputs, on_path = self.run_step("shellcheck", restored="true")
        self.assertEqual(0, done.returncode, done.stderr + done.stdout)
        self.assertFalse(self.curl_ran(), "a cache hit downloaded the tarball anyway")
        self.assertEqual("true", outputs["cache-hit"])
        self.assertEqual([self.bin], on_path)
        self.assertTrue(os.access(os.path.join(self.bin, "shellcheck"), os.X_OK))
        self.assertIn("out of the cache entry " + self.key(), done.stdout)

    def test_a_hit_whose_bytes_are_not_the_pinned_ones_fails_naming_the_entry(self):
        """The case the hash exists to catch: an entry anyone with read access could have written, holding a
        tarball nobody pinned.  It fails, and it does not quietly download over it."""
        self.place(tarball(self.dir, "tampered.tar.xz", body="#!/bin/sh\nexit 0\n"))
        done, outputs, on_path = self.run_step("shellcheck", restored="true")
        self.assertEqual(1, done.returncode)
        self.assertIn("::error::the cache entry " + self.key(), done.stdout)
        self.assertIn("is not the pinned shellcheck", done.stdout)
        self.assertFalse(self.curl_ran(), "a bad cache entry was downloaded over instead of refused")
        self.assertNotIn("cache-hit", outputs)
        self.assertEqual([], on_path)
        self.assertFalse(os.path.exists(os.path.join(self.bin, "shellcheck")))

    def test_a_miss_downloads_hashes_and_leaves_the_tarball_for_the_save(self):
        done, outputs, on_path = self.run_step("shellcheck", serves=self.good)
        self.assertEqual(0, done.returncode, done.stderr + done.stdout)
        self.assertTrue(self.curl_ran(), "a miss downloaded nothing")
        with open(self.curl_log) as f:
            args = f.read().split("\n")
        self.assertIn("--retry-all-errors", args)
        self.assertIn("--retry-max-time", args)
        self.assertIn("https://github.com/koalaman/shellcheck/releases/download/v%s/"
                      "shellcheck-v%s.linux.x86_64.tar.xz" % (VERSION, VERSION), args)
        self.assertEqual("false", outputs["cache-hit"])
        self.assertEqual([self.bin], on_path)
        self.assertTrue(os.access(os.path.join(self.bin, "shellcheck"), os.X_OK))
        # what actions/cache/save then keeps, under the key the restore asked for
        self.assertTrue(os.path.exists(os.path.join(self.store, "shellcheck-v%s.linux.x86_64.tar.xz" % VERSION)))

    def test_a_download_whose_bytes_are_not_the_pinned_ones_fails_naming_the_download(self):
        """The same hash, the other side of it: a bad download is the release host, not the cache, and the two
        messages must not be confused for each other."""
        done, _, on_path = self.run_step("shellcheck", serves=tarball(self.dir, "other.tar.xz", body="#!/bin/sh\n"))
        self.assertEqual(1, done.returncode)
        self.assertIn("::error::the shellcheck %s tarball downloaded from github.com" % VERSION, done.stdout)
        self.assertNotIn("the cache entry", done.stdout)
        self.assertEqual([], on_path)

    def test_a_download_that_gives_up_fails_the_step(self):
        """curl's own exit, after its retries: the step fails and nothing is put on PATH."""
        done, _, on_path = self.run_step("shellcheck", curl_exit=22)
        self.assertNotEqual(0, done.returncode)
        self.assertEqual([], on_path)

    def test_a_restored_entry_that_holds_no_tarball_refuses_loudly(self):
        """"Not found" and "nothing to find" are different answers.  The restore said it had the entry and the
        file is not there: that is refused, not read as a miss and downloaded over."""
        done, _, _ = self.run_step("shellcheck", restored="true", serves=self.good)
        self.assertEqual(1, done.returncode)
        self.assertIn("::error::the cache entry %s was restored and holds no" % self.key(), done.stdout)
        self.assertFalse(self.curl_ran())

    def test_a_restore_that_reported_nothing_is_a_miss(self):
        """The case the refusal above must not catch: no hit reported, no file, so the step downloads."""
        done, outputs, _ = self.run_step("shellcheck", restored="false", serves=self.good)
        self.assertEqual(0, done.returncode, done.stderr + done.stdout)
        self.assertEqual("false", outputs["cache-hit"])
        self.assertTrue(self.curl_ran())


if __name__ == "__main__":
    unittest.main()
