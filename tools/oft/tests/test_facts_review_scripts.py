"""tools/oft/ci/facts-review-gather, facts-review-run and facts-review-comment, and the review job's steps that run
them, against stand-ins: a gh that serves files, a local repository that git fetches from in place of GitHub, the review
agent's command, which answers what a test wrote, and commands that fail when a test says so.

The workflow, CODEOWNERS and the skill are in the internal repository only (`oft release-tree` removes them), so the
tests that read them skip where they are not."""
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import unittest

from oft import yamlio
from oft.tests.helpers import REPO
from oft.tests.test_facts_review_gate import API, FAKE_GH, HAVE_WORKFLOW, NO_WORKFLOW, WORKFLOW

CI = os.path.join(REPO, "tools", "oft", "ci")
GATHER, RUN, COMMENT = (os.path.join(CI, "facts-review-" + name) for name in ("gather", "run", "comment"))
CODEOWNERS = os.path.join(REPO, ".github", "CODEOWNERS")
SKILL = os.path.join(REPO, *".claude/skills/review-facts/SKILL.md".split("/"))
REVIEW_MD = os.path.join(REPO, "review.md")
# Stand-ins for credentials, built here so that no file holds one: SECRET is any credential's value, TOKEN has the
# shape of an Anthropic key, which facts-review-comment refuses to post.
SECRET = "synthetic-" + "secret-" + "0123456789"
TOKEN = "sk-" + "ant-" + "x" * 16
LIMIT = 30000   # characters: review.md's limit on the comment
GIT_ID = {"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@localhost",
          "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@localhost"}


def tool(directory, name, text):
    path = os.path.join(directory, name)
    with open(path, "w") as f:
        f.write(text)
    os.chmod(path, 0o755)


def read(path, mode="r"):
    with open(path, mode) as f:
        return f.read()


# The review agent's command and the prefix of its own environment variables, as facts-review-run names them. The
# command is the one run with -p and --restricted: facts-review-run also runs `mkdir -p`.
AGENT = re.search(r"^\s+(\w+) -p .*--restricted", read(RUN), re.M).group(1)
# ANTHROPIC_* and the agent's own prefix, however facts-review-run writes the pair (a glob or a case pattern).
AGENT_PREFIX = re.search(r"ANTHROPIC_\*\"?[,|]\s*\"?(\w+_)\*", read(RUN)).group(1)
AGENT_TOKEN = AGENT_PREFIX + "OAUTH_TOKEN"
# The names of the files the agent loads as its instructions.
INSTRUCTIONS, INSTRUCTIONS_DIR = AGENT.upper() + ".md", "." + AGENT
# A record of what answered, as facts-review-served writes it, that its check passes.
SERVED_OK = ("asked anthropic/claude-opus-5-5\nendpoint api.anthropic.com\nusage firstParty/claude-opus-5-5\n"
             "firstParty/claude-opus-5-5 3\n")
# The body of a stand-in agent that answers <home>/answer.json as `--output-format stream-json` does: one JSON object
# comes after a turn of the model it was asked for, as a `result` event whose modelUsage names Anthropic's API; any
# other text is printed as it is.
STREAM_ANSWER = ('model=none prev=""\n'
                 'for a in "$@"; do [ "$prev" = --model ] && model=$a; prev=$a; done\n'
                 'if jq -se \'length == 1 and (.[0] | type) == "object"\' "$HOME/answer.json" > /dev/null 2>&1; then\n'
                 '  printf \'{"type": "assistant", "message": {"id": "msg_1", "model": "%s", "content": []}}\\n\' '
                 '"$model"\n'
                 '  jq -c --arg m "$model" \'{type: "result"} + . + (if has("modelUsage") then {} else\n'
                 '    {modelUsage: {($m): {provider: "firstParty", canonicalModel: $m}}} end)\' "$HOME/answer.json"\n'
                 'else\n'
                 '  cat "$HOME/answer.json"\n'
                 'fi\n')


def patch_name(path):
    """The name gather gives a path's diff in patches/, by the rule the skill states: % / ~ as %25 %2F %7E, and a
    name over 200 bytes as its first 150 bytes, ~ and 16 hex digits of the path's SHA-256."""
    name = path.encode().replace(b"%", b"%25").replace(b"/", b"%2F").replace(b"~", b"%7E")
    if len(name) > 200:
        name = (name[:150].decode("utf-8", "ignore") + "~" + hashlib.sha256(path.encode()).hexdigest()[:16]).encode()
    return name.decode() + ".diff"


class Scripts(unittest.TestCase):
    """A directory of stand-in commands at the front of PATH, a home directory, and an environment with no GitHub
    token and no git configuration of the person running the tests."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="oft-facts-review-")
        self.dir = self._tmp.name
        self.bin = os.path.join(self.dir, "bin")
        self.home = os.path.join(self.dir, "home")
        os.mkdir(self.bin)
        os.mkdir(self.home)
        self.env = {k: v for k, v in os.environ.items()
                    if k not in ("GH_TOKEN", "GITHUB_TOKEN")
                    and not k.startswith(("GIT_", "ANTHROPIC_", AGENT.upper() + "_"))}
        self.env.update(PATH=self.bin + os.pathsep + os.environ["PATH"], HOME=self.home, PR="7", REPO="acme/proofs")

    def tearDown(self):
        self._tmp.cleanup()

    def fail_when(self, name, condition, status, once=False):
        """Put a <name> on PATH that answers <status>, an error, when the bash test <condition> holds of its arguments
        (on its first such call only, with `once`), and runs the real <name> otherwise."""
        real = shutil.which(name, path=os.environ["PATH"])
        self.assertIsNotNone(real, f"no {name} on PATH")
        done = os.path.join(self.dir, f"{name}.failed")
        guard = f' && [ ! -e {done} ]' if once else ""
        tool(self.bin, name, "#!/usr/bin/env bash\n"
             f'if {condition}{guard}; then : > {done}; echo "{name}: injected failure" >&2; exit {status}; fi\n'
             f'exec {real} "$@"\n')

    def record_argv(self, name):
        """Put a <name> on PATH that appends its arguments to <home>/<name>.argv, then runs the real <name>."""
        real = shutil.which(name, path=os.environ["PATH"])
        self.assertIsNotNone(real, f"no {name} on PATH")
        tool(self.bin, name, "#!/usr/bin/env bash\n"
             f'printf "%s\\0" "$@" >> {os.path.join(self.home, name + ".argv")}\n'
             f'exec {real} "$@"\n')

    def recorded(self, name):
        path = os.path.join(self.home, name + ".argv")
        return read(path) if os.path.exists(path) else ""


@unittest.skipUnless(shutil.which("jq") and shutil.which("git"), "jq or git is not installed")
class GatherTest(Scripts):
    """gather, on pull request 7 of acme/proofs: a stand-in gh serves the pull request, and git fetches its commits
    from a local repository in place of https://github.com/acme/proofs."""
    DOCS = {"docs/facts.md": "main's facts doc\n"}

    def setUp(self):
        super().setUp()
        tool(self.bin, "gh", FAKE_GH)
        self.git_bin = shutil.which("git")
        self.api = os.path.join(self.dir, "api")
        self.served = os.path.join(self.dir, "served")
        self.checkout = os.path.join(self.dir, "checkout")
        runner = os.path.join(self.dir, "runner")
        for d in (self.api, runner, os.path.join(self.checkout, "docs")):
            os.makedirs(d)
        with open(os.path.join(self.checkout, "docs", "facts.md"), "w") as f:
            f.write(self.DOCS["docs/facts.md"])
        self.env.update(GIT_ID, FAKE_GH=self.api, RUNNER_TEMP=runner, GIT_CONFIG_COUNT="1",
                        GIT_CONFIG_KEY_0=f"url.file://{self.served}.insteadOf",
                        GIT_CONFIG_VALUE_0="https://github.com/acme/proofs")
        self.git("init", "-q", self.served)
        self.git("-C", self.served, "config", "uploadpack.allowFilter", "true")
        self.git("-C", self.served, "config", "uploadpack.allowAnySHA1InWant", "true")
        self.base = self.commit(dict(self.DOCS, **{"release.yaml": "release: 1\n",
                                                   "projects/old/fz/harness.yaml": "old: 1\n"}))

    def git(self, *args):
        return subprocess.run([self.git_bin, *args], env=self.env, check=True, capture_output=True,
                              text=True).stdout.strip()

    def commit(self, files, delete=()):
        """A commit on the served repository's branch with `files` (path: text) written and `delete` removed."""
        for path, text in files.items():
            full = os.path.join(self.served, path)
            os.makedirs(os.path.dirname(full), exist_ok=True)
            with open(full, "w") as f:
                f.write(text)
        for path in delete:
            os.remove(os.path.join(self.served, path))
        self.git("-C", self.served, "add", "-A")
        self.git("-C", self.served, "commit", "-q", "--allow-empty", "-m", "a commit")
        return self.git("-C", self.served, "rev-parse", "HEAD")

    def gather(self, files=None, delete=()):
        """Pull request 7 with a head commit that writes `files` and deletes `delete` on top of the base; gather's
        process, and its output directory."""
        head = self.commit(files or {}, delete)
        with open(os.path.join(self.api, API + "pulls_7.json"), "w") as f:
            json.dump({"number": 7, "title": "facts", "body": "", "draft": False,
                       "head": {"sha": head}, "base": {"sha": self.base, "ref": "main"}}, f)
        with open(os.path.join(self.api, API + f"compare_{self.base}...{head}.json"), "w") as f:
            json.dump({"merge_base_commit": {"sha": self.base}}, f)
        out = os.path.join(self.checkout, ".review")
        # A bound, so that a gather that hangs (an unbounded value, once) fails the test instead of the CI job.
        r = subprocess.run(["bash", GATHER, out], cwd=self.checkout, env=self.env, capture_output=True, text=True,
                           timeout=300)
        return r, out

    ZLIB = {"projects/zlib/project.yaml": "library:\n  repository: https://example.com/zlib\n",
            "projects/zlib/fz/harness.yaml": "fz: 1\n"}

    def assertStopped(self, r, cause):
        self.assertNotEqual(r.returncode, 0, "gather went on:\n" + r.stdout + r.stderr)
        self.assertIn(cause, r.stderr)

    def test_it_gathers_a_new_project(self):
        r, out = self.gather(self.ZLIB)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(read(os.path.join(out, "targets.txt")), "zlib/fz\n")
        self.assertEqual(sorted(os.listdir(os.path.join(out, "patches"))),
                         sorted(patch_name(p) for p in self.ZLIB))
        self.assertIn("library/zlib: the library is not a GitHub repository", read(os.path.join(out, "missing.txt")))
        self.assertEqual(read(os.path.join(out, "head", "projects", "zlib", "fz", "harness.yaml")), "fz: 1\n")

    def since_last_review(self, last):
        """A restored conversation of the review of commit `last`, for gather's since-last-review.diff."""
        session = os.path.join(self.dir, "review-session")
        os.makedirs(session, exist_ok=True)
        with open(os.path.join(session, "session"), "w") as f:
            f.write(f"id=x\nhead={last}\ndir=-x\n")
        self.env["REVIEW_SESSION"] = session

    def test_the_diff_since_the_last_review_holds_the_facts_and_the_provenance(self):
        """Checks C and E compare the facts with each reviewed fuzz target's provenance/: a push that changes only a
        manifest must reach a review that looks only at this diff. Licence texts (LICENSES) and zips stay out."""
        prov = "proofs/zlib/fz/provenance/port/"
        self.since_last_review(self.commit(dict(self.ZLIB, **{prov + "manifest.yaml": "sha256: old\n"})))
        r, out = self.gather({prov + "manifest.yaml": "sha256: new\n", prov + "LICENSES/zlib.txt": "licence\n",
                              prov + "seeds.zip": "zip\n", "release.yaml": "release: 2\n"})
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        diff = read(os.path.join(out, "since-last-review.diff"))
        self.assertEqual(re.findall(r"^diff --git a/(\S+)", diff, re.M), [prov + "manifest.yaml"])
        self.assertIn("+sha256: new", diff)

    def test_a_last_review_whose_commit_cannot_be_fetched_gives_no_diff(self):
        """No diff, not an error line in its place, and missing.txt says why."""
        self.since_last_review("f" * 40)
        r, out = self.gather(self.ZLIB)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertFalse(os.path.exists(os.path.join(out, "since-last-review.diff")))
        self.assertIn(f"since-last-review.diff: could not fetch {'f' * 40}, the commit of the last review",
                      read(os.path.join(out, "missing.txt")))

    def test_an_unchanged_head_gives_an_empty_diff(self):
        """A new base or a run by hand gathers the same head again: the diff is there, and empty."""
        r, out = self.gather(self.ZLIB)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.since_last_review(self.git("-C", self.served, "rev-parse", "HEAD"))
        shutil.rmtree(out)
        r = subprocess.run(["bash", GATHER, out], cwd=self.checkout, env=self.env, capture_output=True, text=True,
                           timeout=300)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(read(os.path.join(out, "since-last-review.diff")), "")

    def test_a_deleted_project_is_not_an_error(self):
        """A project the pull request deletes is absent at the head: that absence is an answer, not a failure."""
        r, out = self.gather(delete=["projects/old/fz/harness.yaml"])
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(read(os.path.join(out, "changed.txt")), "D\tprojects/old/fz/harness.yaml\n")
        self.assertEqual(read(os.path.join(out, "targets.txt")), "")

    def test_each_path_has_a_diff_of_its_own(self):
        """R104-03: projects/a__b/c/harness.yaml and projects/a/b__c/harness.yaml once wrote the same file, the second
        diff over the first; and a path git quotes (here, one with a " or a \\) ran into the diff before it."""
        files = {"projects/a__b/c/harness.yaml": "first: 1\n", "projects/a/b__c/harness.yaml": "second: 2\n",
                 'projects/a/b__c/source/q"x.c': "quoted\n", "projects/a/b__c/source/back\\slash.c": "escaped\n",
                 "projects/a/b__c/source/100%2Fx.c": "percent\n", "projects/a/b__c/source/x~y.c": "tilde\n",
                 "projects/a/b__c/source/x%7Ey.c": "escaped tilde\n"}
        r, out = self.gather(files)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        patches = os.path.join(out, "patches")
        self.assertEqual(sorted(os.listdir(patches)), sorted(patch_name(p) for p in files))
        for path, text in files.items():
            with self.subTest(path=path):
                diff = read(os.path.join(patches, patch_name(path)))
                self.assertEqual(diff.count("diff --git "), 1, diff)
                self.assertIn("+" + text, diff)
        self.assertIn("projects/a__b: no project.yaml at the head commit", read(os.path.join(out, "missing.txt")))

    def test_a_failed_listing_of_a_path_stops_it(self):
        """R104-04: an ls-tree that failed read as "the path is not at the head", and the project was skipped."""
        self.fail_when("git", '[[ " $* " == *" ls-tree "* && " $* " != *" -r "* ]]', 128)
        r, _ = self.gather(self.ZLIB)
        self.assertStopped(r, "git ls-tree could not list projects/zlib")

    def test_a_failed_listing_of_the_fuzz_targets_stops_it(self):
        """R104-04: the fuzz targets of a new project were listed with `|| true`, so a failure was no fuzz targets."""
        self.fail_when("git", '[[ " $* " == *" ls-tree -r "* ]]', 128)
        r, _ = self.gather(self.ZLIB)
        self.assertStopped(r, "git ls-tree could not list the fuzz targets of projects/zlib")

    def test_a_failed_sort_of_the_fuzz_targets_stops_it(self):
        """R104-04: over 60 fuzz targets, their names were sorted in a process substitution whose failure was lost."""
        files = {"projects/big/project.yaml": "library: {}\n"}
        files.update({f"projects/big/t{i:02}/harness.yaml": f"t: {i}\n" for i in range(61)})
        self.fail_when("sort", "true", 2, once=True)
        r, _ = self.gather(files)
        self.assertStopped(r, "sort: injected failure")

    def test_a_failed_rewrite_of_the_docs_list_stops_it(self):
        """R104-04: diff's status 1 (the docs differ) let a sed that failed after it through."""
        self.fail_when("sed", "true", 2)
        r, _ = self.gather(dict(self.ZLIB, **{"docs/facts.md": "the head's facts doc\n"}))
        self.assertStopped(r, "sed could not write docs-changed.txt")

    def test_a_failed_comparison_of_the_docs_stops_it(self):
        self.fail_when("diff", '[ "$1" = -rq ]', 2)
        r, _ = self.gather(self.ZLIB)
        self.assertStopped(r, "diff -rq could not compare docs/ with head/docs/ (status 2)")

    def test_a_project_yaml_the_pull_request_wrote_wrong_is_reviewed(self):
        """R104-04: every exception in reading project.yaml read as "no oss_fuzz and no library", with nothing said.
        A project.yaml the pull request wrote wrong is data: missing.txt says why nothing was fetched, and the review
        goes on, so it can say what is wrong. A value that is a tree (an alias tree of a few hundred bytes stands for
        megabytes once written out, and bash then took minutes over each cut of it), a merge key (whose copies can
        multiply the same way inside the YAML load) and a file over 64 KiB are among them."""
        tree = "a: &a [x,x,x,x,x,x,x,x,x,x]\n" + "".join(
            f"{c}: &{c} [*{p},*{p},*{p},*{p},*{p},*{p},*{p},*{p},*{p},*{p}]\n" for p, c in zip("abcdef", "bcdefg"))
        mapping = "m0: &m0 {k: x}\n" + "".join(f"m{i}: &m{i} {{a: *m{i-1}, b: *m{i-1}}}\n" for i in range(1, 8))
        not_single = "its oss_fuzz path or commit, or its library repository or commit, is not a single value"
        merge = "it is YAML that cannot be read (ValueError: a merge key (<<) is not read"
        for text, why in (("library: [\n", "it is not YAML"), ("- a list\n", "it is not a mapping"),
                          ("", "it is not a mapping"), ("library: a string\n", "library is not a mapping"),
                          ("library:\n  since: 2001-02-30\n", "it is YAML that cannot be read (ValueError"),
                          ("library:\n  commit: 0x" + "f" * 3600 + "\n", "it is YAML that cannot be read (ValueError"),
                          (tree + "library:\n  repository: *g\n", not_single),
                          (mapping + "oss_fuzz:\n  path: *m7\n", not_single),
                          ("a: &a {x: 1}\nlibrary:\n  <<: *a\n", merge),
                          ("a: &a {x: 1}\nlibrary:\n  !!merge k: *a\n", merge),
                          ("library: {}\n#" + "z" * 70000 + "\n", "it is over 64 KiB")):
            with self.subTest(project_yaml=text[-40:]):
                shutil.rmtree(os.path.join(self.checkout, ".review"), ignore_errors=True)
                r, out = self.gather(dict(self.ZLIB, **{"projects/zlib/project.yaml": text}))
                self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
                self.assertEqual(read(os.path.join(out, "targets.txt")), "zlib/fz\n")
                missing = read(os.path.join(out, "missing.txt"))
                self.assertIn("projects/zlib: project.yaml could not be used: ", missing)
                self.assertIn(why, missing)

    def test_a_nul_in_the_last_value_is_reviewed(self):
        """bash drops a NUL from a line: a NUL in the last value once left the gather 4 fields under `set -u`."""
        r, out = self.gather(dict(self.ZLIB, **{"projects/zlib/project.yaml":
                                                 'library:\n  repository: x\n  commit: "\\0"\n'}))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("library/zlib: the library is not a GitHub repository", read(os.path.join(out, "missing.txt")))

    def test_a_project_yaml_that_is_a_link_is_not_read(self):
        """A project.yaml that is a symbolic link to a file the runner cannot read once stopped the gather when the
        reader read it."""
        link = os.path.join(self.served, "projects", "zlib", "project.yaml")
        os.makedirs(os.path.dirname(link))
        os.symlink("/proc/self/mem", link)
        r, out = self.gather({"projects/zlib/fz/harness.yaml": "fz: 1\n"})
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("projects/zlib: no project.yaml at the head commit", read(os.path.join(out, "missing.txt")))

    def test_a_value_too_long_is_cut(self):
        """A value is cut at 300 characters, so that neither str() nor bash gets an unbounded one."""
        r, out = self.gather(dict(self.ZLIB, **{"projects/zlib/project.yaml": "library:\n  repository: " + "y" * 5000
                                                 + "\n"}))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("pinned to a commit (" + "y" * 300 + ")\n", read(os.path.join(out, "missing.txt")))

    def test_an_oss_fuzz_pin_is_fetched_only_when_it_is_a_commit(self):
        """A hash that names a blob fetched, then failed git ls-tree, which stopped the gather. A commit is fetched."""
        oss = os.path.join(self.dir, "oss-fuzz")
        self.git("init", "-q", oss)
        self.git("-C", oss, "config", "uploadpack.allowFilter", "true")
        self.git("-C", oss, "config", "uploadpack.allowAnySHA1InWant", "true")
        os.makedirs(os.path.join(oss, "projects", "zlib"))
        with open(os.path.join(oss, "projects", "zlib", "build.sh"), "w") as f:
            f.write("make\n")
        self.git("-C", oss, "add", "-A")
        self.git("-C", oss, "commit", "-q", "-m", "zlib")
        blob = self.git("-C", oss, "rev-parse", "HEAD:projects/zlib/build.sh")
        self.env.update(GIT_CONFIG_COUNT="2", GIT_CONFIG_KEY_1=f"url.file://{oss}.insteadOf",
                        GIT_CONFIG_VALUE_1="https://github.com/google/oss-fuzz")
        r, out = self.gather(dict(self.ZLIB, **{"projects/zlib/project.yaml":
                                                 f"oss_fuzz:\n  path: projects/zlib\n  commit: {blob}\n"}))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("oss-fuzz/zlib: OSS-Fuzz has no projects/zlib at " + blob, read(os.path.join(out, "missing.txt")))
        shutil.rmtree(out)
        commit = self.git("-C", oss, "rev-parse", "HEAD")
        r, out = self.gather({"projects/zlib/project.yaml": f"oss_fuzz:\n  path: projects/zlib\n  commit: {commit}\n"})
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(read(os.path.join(out, "oss-fuzz", "zlib", "build.sh")), "make\n")

    def test_a_value_that_cannot_be_encoded_is_written_as_an_escape(self):
        """Two halves of a surrogate pair, each alone, cannot be encoded as UTF-8: print once failed on them after
        "ok", and the gather stopped."""
        r, out = self.gather(dict(self.ZLIB, **{"projects/zlib/project.yaml":
                                                 'library:\n  repository: "\\ud83d\\ude00"\n'}))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("library/zlib: the library is not a GitHub repository pinned to a commit (\\ud83d\\ude00)",
                      read(os.path.join(out, "missing.txt")))

    def test_a_project_yaml_it_cannot_read_stops_it(self):
        """R104-04: a reader that failed is not a project without oss_fuzz or library: it stops the gather."""
        self.fail_when("python3", '[[ "${@: -1}" == */project.yaml ]]', 1)
        r, _ = self.gather(self.ZLIB)
        self.assertStopped(r, "could not read projects/zlib/project.yaml")

    def test_a_long_path_has_a_diff_name_the_disk_takes(self):
        """R104-03's names are longer than the path; one over the 255 bytes a file name may have stopped the gather
        with a traceback. Over 200 bytes the name is shortened, still one name per path."""
        deep = "projects/zlib/fz/source/" + "/".join(["a_directory_name"] * 12)
        files = dict(self.ZLIB, **{deep + "/one.c": "one\n", deep + "/two.c": "two\n"})
        r, out = self.gather(files)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        names = os.listdir(os.path.join(out, "patches"))
        self.assertEqual(sorted(names), sorted(patch_name(p) for p in files))
        for path in (deep + "/one.c", deep + "/two.c"):
            with self.subTest(path=path):
                self.assertLessEqual(len(patch_name(path).encode()), 255)
                self.assertIn("~", patch_name(path))
                diff = read(os.path.join(out, "patches", patch_name(path)))
                self.assertEqual(diff.count("diff --git "), 1, diff)
                self.assertIn(f"diff --git a/{path} b/{path}\n", diff)

    def test_a_path_whose_type_changed_has_one_diff_file(self):
        """git writes a file that became a symbolic link as two diffs of the one path in a row, the deletion and the
        addition: both go to the path's one file, and the review goes on."""
        self.base = self.commit(dict(self.ZLIB, **{"projects/zlib/fz/source/x.c": "a file\n"}))
        link = os.path.join(self.served, "projects", "zlib", "fz", "source", "x.c")
        os.remove(link)
        os.symlink("elsewhere.c", link)
        r, out = self.gather()
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        name = patch_name("projects/zlib/fz/source/x.c")
        self.assertEqual(os.listdir(os.path.join(out, "patches")), [name])
        diff = read(os.path.join(out, "patches", name))
        self.assertEqual(diff.count("diff --git a/projects/zlib/fz/source/x.c b/projects/zlib/fz/source/x.c\n"), 2)
        self.assertIn("-a file\n", diff)
        self.assertIn("+elsewhere.c\n", diff)

    def test_a_diff_the_splitter_cannot_split_stops_it(self):
        """Each refusal of the splitter, on a diff a stand-in git writes: a diff that runs into the one before it is
        never written. (Two paths with one diff name cannot be built: the names are injective, and patches/ starts
        empty; that check guards the rule.)"""
        real = shutil.which("git", path=os.environ["PATH"])
        fake = os.path.join(self.dir, "fake.diff")
        tool(self.bin, "git", "#!/usr/bin/env bash\n"
             f'if [[ " $* " == *" diff --no-renames "*" --src-prefix=a/ "* ]]; then '
             f'cat {fake}; exit 0; fi\nexec {real} "$@"\n')
        p, q = "projects/zlib/fz/harness.yaml", "projects/zlib/project.yaml"
        for text, cause in ((f"diff --git a/{p} b/{q}\n", "a diff header it cannot read"),
                            ('diff --git "a/x\\qy" "b/x\\qy"\n', "a diff header has an escape it cannot read"),
                            (f"diff --git a/{p} b/{p}\n+1\ndiff --git a/{q} b/{q}\n+2\ndiff --git a/{p} b/{p}\n+3\n",
                             "two diffs of"),
                            ("+a line before any header\n", "the diff does not start with a diff --git header")):
            with self.subTest(cause=cause):
                with open(fake, "w") as f:
                    f.write(text)
                shutil.rmtree(os.path.join(self.checkout, ".review"), ignore_errors=True)
                r, _ = self.gather(self.ZLIB)
                self.assertStopped(r, cause)

    def test_a_second_gather_into_the_same_directory_is_refused(self):
        """What a gather before left (a project the pull request has since deleted, a diff name already taken) is not
        this pull request's."""
        r, out = self.gather(self.ZLIB)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        r, out = self.gather({"projects/zlib/fz/harness.yaml": "fz: 2\n"})
        self.assertStopped(r, "is not empty")

    def test_a_persons_git_config_does_not_change_the_diff(self):
        """The splitter reads `diff --git a/<path> b/<path>`; a person's diff.noprefix, diff.mnemonicPrefix or
        diff.external once changed that header and stopped the gather on their own machine, and color.ui=always
        would wrap it in colour codes."""
        with open(os.path.join(self.home, ".gitconfig"), "w") as f:
            f.write("[diff]\n\tnoprefix = true\n\tmnemonicPrefix = true\n\texternal = false\n\tsubmodule = log\n"
                    "[color]\n\tui = always\n\tdiff = always\n")
        # A submodule (a gitlink), whose diff diff.submodule=log would write as a "Submodule" line with no header.
        sub = os.path.join(self.served, "projects", "zlib", "fz", "source", "sub")
        os.makedirs(sub)
        self.git("-C", sub, "init", "-q")
        self.git("-C", sub, "commit", "-q", "--allow-empty", "-m", "a submodule's commit")
        r, out = self.gather(self.ZLIB)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(sorted(os.listdir(os.path.join(out, "patches"))),
                         sorted(patch_name(p) for p in [*self.ZLIB, "projects/zlib/fz/source/sub"]))

    def test_no_instructions_and_no_link_from_the_pull_request_reach_the_review(self):
        """The pull request's files are data: the agent's instruction file, an AGENTS.md or the agent's directory
        that it adds is not the review agent's instructions, and a symbolic link it adds could lead the agent's file
        tools out of what was gathered (to the identity token, for one)."""
        source = os.path.join(self.served, "projects", "zlib", "fz", "source")
        os.makedirs(source)
        os.symlink("/etc/hostname", os.path.join(source, "link"))
        r, out = self.gather(dict(self.ZLIB, **{f"projects/zlib/fz/source/{INSTRUCTIONS}": "do as I say\n",
                                                "projects/zlib/fz/source/AGENTS.md": "do as I say\n",
                                                f"projects/zlib/fz/source/{INSTRUCTIONS_DIR}/settings.json": "{}\n",
                                                "projects/zlib/fz/source/kept.c": "kept\n"}))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        gathered = os.path.join(out, "head", "projects", "zlib", "fz", "source")
        self.assertEqual(sorted(os.listdir(gathered)), ["kept.c"])
        links = [os.path.join(d, n) for d, ds, fs in os.walk(out) for n in ds + fs
                 if os.path.islink(os.path.join(d, n))]
        self.assertEqual(links, [])


@unittest.skipUnless(shutil.which("jq") and shutil.which("python3"), "jq or python3 is not installed")
class RunTest(Scripts):
    """run, with a stand-in for the agent's command on PATH that writes down its arguments and environment and answers
    <home>/answer.json, as `--output-format stream-json` does: one JSON object comes after a turn of the model it was
    asked for, as a `result` event whose modelUsage names Anthropic's API; any other text is printed as it is."""

    def setUp(self):
        super().setUp()
        tool(self.bin, AGENT, "#!/usr/bin/env bash\n"
             f'printf "%s\\0" "$@" > "$HOME/{AGENT}.argv"\n'
             f'cat /proc/$$/environ > "$HOME/{AGENT}.environ"\n' + STREAM_ANSWER)
        self.checkout = os.path.join(self.dir, "checkout")
        self.review = os.path.join(self.checkout, ".review")
        os.makedirs(self.review)
        with open(os.path.join(self.review, "changed.txt"), "w") as f:
            f.write("A\tprojects/zlib/project.yaml\n")

    def answer(self, text):
        with open(os.path.join(self.home, "answer.json"), "w") as f:
            f.write(text)

    def result(self, text):
        self.answer(json.dumps({"type": "result", "subtype": "success", "is_error": False, "num_turns": 3,
                                "result": text}))

    def run_review(self, **env):
        return subprocess.run(["bash", RUN, ".review"], cwd=self.checkout, env=dict(self.env, **env),
                              capture_output=True, text=True)

    def test_a_review_is_its_result(self):
        self.result("No findings.\n\n| fuzz target | A |\n| --- | --- |\n| zlib/fz | ok |")
        r = self.run_review()
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(read(os.path.join(self.review, "comment.md")),
                         "No findings.\n\n| fuzz target | A |\n| --- | --- |\n| zlib/fz | ok |\n")

    def test_a_result_that_is_not_a_review_stops_it(self):
        """R104-05: only .is_error was checked, so these were each posted as a review (the reviewer's five first)."""
        good = {"type": "result", "subtype": "success", "is_error": False}
        answers = ["{}", '{"is_error":false,"result":null}', '{"is_error":false,"result":""}',
                   '{"is_error":false,"result":"   "}', '{"is_error":false,"result":17}',
                   json.dumps(dict(good, result=None)), json.dumps(dict(good, result="")),
                   json.dumps(dict(good, result=" \n\t ")), json.dumps(dict(good, result=17)),
                   json.dumps(dict(good, result=["No findings."])), json.dumps(dict(good, result="17 | -- |")),
                   json.dumps(dict(good, is_error=True, result="No findings.")),
                   json.dumps(dict(good, subtype="error_max_turns", result="No findings.")),
                   json.dumps(dict(good, type="assistant", result="No findings.")),
                   # The agent's tool, at 2.1.310, answers a start that failed with this shape: a success
                   # whose result is the error's text.
                   json.dumps(dict(good, result="The agent didn't start. The login has expired.",
                                   terminal_reason="turn_setup_failed")),
                   json.dumps(dict(good, result="No findings.", terminal_reason="aborted_tools")),
                   json.dumps(dict(good, result="No findings.")) * 2, "[]", "17", '"No findings."', "", "not json"]
        for text in answers:
            with self.subTest(answer=text):
                self.answer(text)
                r = self.run_review()
                self.assertNotEqual(r.returncode, 0, "posted: " + read(os.path.join(self.review, "comment.md")))

    def test_a_review_that_ran_to_its_end_is_posted(self):
        """The terminal_reason check lets a review through when the agent says it completed, or says nothing."""
        self.answer(json.dumps({"type": "result", "subtype": "success", "is_error": False, "result": "No findings.",
                                "terminal_reason": "completed"}))
        r = self.run_review()
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(read(os.path.join(self.review, "comment.md")), "No findings.\n")

    def test_the_agent_runs_with_three_read_tools_only(self):
        """The agent holds the federation credential while it reads the pull request: its restricted mode and its
        three tools are what keep it off the shell, the network and file writes."""
        self.result("No findings.")
        r = self.run_review()
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        argv = read(os.path.join(self.home, AGENT + ".argv")).split("\0")[:-1]
        self.assertEqual(argv[argv.index("--tools") + 1], "Read,Glob,Grep")
        self.assertEqual(argv[argv.index("--permission-mode") + 1], "dontAsk")
        self.assertEqual(argv[argv.index("--output-format") + 1], "stream-json")
        self.assertIn("--verbose", argv)
        for flag in ("--restricted", "--strict-mcp-config"):
            with self.subTest(flag=flag):
                self.assertIn(flag, argv)
        self.assertEqual([a for a in argv if a.startswith("--") and "tool" in a.lower()], ["--tools"],
                         "another tool option widens what the agent can do")

    def test_no_credential_is_an_argument(self):
        """R104-07: the runner passed each ANTHROPIC_* variable and each of the agent's own to env as NAME=value,
        where any process on the machine can read it. The agent still gets them, and nothing else of the caller's."""
        self.record_argv("env")
        self.record_argv("python3")
        self.result("No findings.")
        r = self.run_review(ANTHROPIC_API_KEY=SECRET, **{AGENT_TOKEN: SECRET + "-2"}, OTHER_SECRET=SECRET)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        for name in ("env", "python3", AGENT):
            with self.subTest(command=name):
                self.assertNotIn(SECRET, self.recorded(name))
        environ = dict(v.split("=", 1) for v in read(os.path.join(self.home, AGENT + ".environ")).split("\0") if v)
        self.assertEqual(environ.get("ANTHROPIC_API_KEY"), SECRET)
        self.assertEqual(environ.get(AGENT_TOKEN), SECRET + "-2")
        self.assertEqual(environ.get("LANG"), "C.UTF-8")
        self.assertEqual(environ.get("HOME"), self.home)
        self.assertEqual(set(environ) - {"PATH", "HOME", "LANG", "ANTHROPIC_API_KEY", AGENT_TOKEN},
                         set(), "the agent got more of the environment than it needs")

    def test_a_review_over_the_limit_is_cut_with_a_note(self):
        """R104-08: one limit, review.md's 30,000 characters, counted as characters, and a cut always says so."""
        for length in (LIMIT, LIMIT + 1, 3 * LIMIT):
            with self.subTest(length=length):
                text = ("é" * 99 + "\n") * (length // 100) + "é" * (length % 100)
                self.result(text)
                r = self.run_review()
                self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
                comment = read(os.path.join(self.review, "comment.md"), "rb").decode()
                if length <= LIMIT:
                    self.assertEqual(comment, text + "\n")
                else:
                    note = f"\n\n(The review was {length} characters long. It was cut at {LIMIT}"
                    self.assertTrue(comment.startswith(text[:LIMIT] + note), comment[-300:])
                    self.assertNotIn("log", comment[LIMIT:])


@unittest.skipUnless(shutil.which("grep"), "grep is not installed")
class CommentTest(Scripts):
    def comment(self, review):
        path = os.path.join(self.dir, "review.md")
        with open(path, "w") as f:
            f.write(review)
        return subprocess.run(["bash", COMMENT, path], env=dict(self.env, HEAD_SHA="a" * 40, BASE_REF="main",
                                                                SERVED=SERVED_OK), capture_output=True, text=True)

    def test_a_review_is_posted_whole(self):
        r = self.comment("No findings.\n")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("No findings.", r.stdout)

    def test_a_review_that_is_not_published_lists_how_each_try_ended(self):
        """facts-review-run's exit 4: the review job passes no review, a record of another provider, and tries.txt."""
        path = os.path.join(self.dir, "review.md")
        with open(path, "w") as f:
            f.write("")
        tries = ["try 1 of 3 (resumed from the review of 0123456789ab), not published, as the provider or model that "
                 "answered it is not the one asked for or is not shown", "try 0 of 3, a second line"]
        other = SERVED_OK.replace("firstParty", "bedrock")
        r = subprocess.run(["bash", COMMENT, path], env=dict(self.env, HEAD_SHA="a" * 40, BASE_REF="main",
                                                             SERVED=other, TRIES="\n".join(tries)),
                           capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("is not published: it asked for anthropic/claude-opus-5-5", r.stdout)
        self.assertTrue(r.stdout.endswith("\n\nHow each try of the review agent ended:\n\n"
                                          + "".join(f"- {t}\n" for t in tries)), r.stdout)

    def test_a_review_with_a_credential_is_not_posted(self):
        r = self.comment(f"No findings. {TOKEN}\n")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertNotIn(TOKEN, r.stdout)
        self.assertIn("held what looks like a credential", r.stdout)

    def test_a_failed_credential_search_posts_nothing(self):
        """R104-06: grep's status 2, an error, read as "no credential", and the text was posted."""
        self.fail_when("grep", "true", 2)
        for review in (f"No findings. {TOKEN}\n", "No findings.\n"):
            with self.subTest(review=review):
                r = self.comment(review)
                self.assertNotEqual(r.returncode, 0, r.stdout)
                self.assertEqual(r.stdout, "")
                self.assertIn("could not search the review for credentials", r.stderr)

    def test_it_does_not_cut_the_review_again(self):
        """R104-08: facts-review-run is the one place the review is cut; this script once cut it at 40,000 characters
        and said the rest was in the review job's log, which never held it."""
        review = "No findings.\n" + "x" * (LIMIT + 20000) + "\nthe last line\n"
        r = self.comment(review)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("\nthe last line\n", r.stdout)
        self.assertNotIn("log", r.stdout)

    def test_a_review_it_cannot_read_posts_nothing(self):
        """R104-04's class: the review file was read with `|| true`, so a read that failed posted "did not review"
        with no cause, and one that failed part-way posted part of the review as the whole."""
        r = subprocess.run(["bash", COMMENT, os.path.join(self.dir, "no-such-review.md")], env=self.env,
                           capture_output=True, text=True)
        self.assertNotEqual(r.returncode, 0, r.stdout)
        self.assertEqual(r.stdout, "")
        self.assertIn("could not read", r.stderr)

    def test_credentials_of_each_shape_are_not_posted(self):
        """Each shape the credential search names: an identity token (a JWT), an Anthropic key, GitHub tokens."""
        for credential in ("eyJ" + "a" * 12 + "." + "b" * 12, TOKEN, "gh" + "s_" + "c" * 24,
                           "github" + "_pat_" + "d" * 24):
            with self.subTest(credential=credential[:6]):
                r = self.comment(f"No findings. {credential}\n")
                self.assertEqual(r.returncode, 0, r.stderr)
                self.assertNotIn(credential, r.stdout)
                self.assertIn("held what looks like a credential", r.stdout)


@unittest.skipUnless(shutil.which("jq") and shutil.which("openssl"), "jq or openssl is not installed")
@unittest.skipUnless(HAVE_WORKFLOW, NO_WORKFLOW)
class ReviewJobTest(Scripts):
    """The review job's steps, run as GitHub runs them, with stand-ins for curl and the agent's command."""

    def setUp(self):
        super().setUp()
        self.steps = yamlio.load_file(WORKFLOW)["jobs"]["review"]["steps"]
        self.runner = os.path.join(self.dir, "runner")
        os.mkdir(self.runner)

    def step(self, name, env, cwd=None):
        """Runs the step named `name`, with the expressions it holds that these tests need put in."""
        step = next(s for s in self.steps if s.get("name") == name)
        script = os.path.join(self.dir, "step.sh")
        with open(script, "w") as f:
            f.write(step["run"].replace("${{ github.repository_id }}", "1425069221"))
        return subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", script], cwd=cwd or self.dir,
                              env=dict(self.env, RUNNER_TEMP=self.runner, **env), capture_output=True, text=True)

    def test_the_request_token_is_not_an_argument(self):
        """R104-07: the identity token request put its bearer token in curl's -H argument. It goes on standard
        input."""
        tool(self.bin, "curl", "#!/usr/bin/env bash\n"
             'printf "%s\\0" "$@" > "$HOME/curl.argv"\n'
             'for a in "$@"; do [ "$a" = @- ] && cat > "$HOME/curl.headers"; done\n'
             "echo '{\"value\": \"the-identity-token\"}'\n")
        r = self.step("get the GitHub identity token for Anthropic",
                      {"ACTIONS_ID_TOKEN_REQUEST_TOKEN": SECRET,
                       "ACTIONS_ID_TOKEN_REQUEST_URL": "https://token.example.invalid/?api-version=2.0"})
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertNotIn(SECRET, read(os.path.join(self.home, "curl.argv")))
        self.assertEqual(read(os.path.join(self.home, "curl.headers")), f"Authorization: Bearer {SECRET}\n")
        self.assertEqual(read(os.path.join(self.runner, "oidc", "jwt")), "the-identity-token\n")

    def test_an_answer_with_no_identity_token_stops_the_step(self):
        """jq -r .value wrote the text null for an answer with no value, and the review went on with null as its
        token."""
        tool(self.bin, "curl", "#!/usr/bin/env bash\ncat > /dev/null\necho '{}'\n")
        r = self.step("get the GitHub identity token for Anthropic",
                      {"ACTIONS_ID_TOKEN_REQUEST_TOKEN": SECRET,
                       "ACTIONS_ID_TOKEN_REQUEST_URL": "https://token.example.invalid/?api-version=2.0"})
        self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("GitHub gave no identity token", r.stdout + r.stderr)
        self.assertEqual(read(os.path.join(self.runner, "oidc", "jwt")), "")

    def test_a_review_under_the_limit_is_posted_whole(self):
        """R104-08: the review step cut the comment at 60,000 bytes, with no note, before the comment script counted
        characters: a review of 25,000 characters of three bytes each lost its end, coverage table and all."""
        checkout = os.path.join(self.dir, "checkout")
        review = os.path.join(checkout, ".review")
        os.makedirs(review)
        os.symlink(os.path.join(REPO, "tools"), os.path.join(checkout, "tools"))
        with open(os.path.join(review, "changed.txt"), "w") as f:
            f.write("A\tprojects/zlib/project.yaml\n")
        text = "1 finding, in 1 fuzz target.\n" + ("—" * 99 + "\n") * 249 + "4. Not checked: segments.\n"
        self.assertLess(len(text), LIMIT)
        with open(os.path.join(self.home, "answer.json"), "w") as f:
            json.dump({"type": "result", "subtype": "success", "is_error": False, "result": text}, f)
        tool(self.bin, AGENT, "#!/usr/bin/env bash\n" + STREAM_ANSWER)
        output = os.path.join(self.dir, "output")
        r = self.step("review", {"PR": "7", "GITHUB_OUTPUT": output,
                                 "ANTHROPIC_IDENTITY_TOKEN_FILE": os.path.join(self.runner, "jwt")}, cwd=checkout)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        written = read(output, "rb").decode(errors="replace")   # a cut in bytes can split a character
        delimiter = re.search(r"^comment<<(\S+)$", written, re.M).group(1)
        posted = written.split(f"comment<<{delimiter}\n", 1)[1].rsplit("\n" + delimiter + "\n", 1)[0]
        self.assertEqual(posted, text + "\n")
        with open(os.path.join(self.dir, "review.md"), "w") as f:
            f.write(posted)
        r = subprocess.run(["bash", COMMENT, os.path.join(self.dir, "review.md")],
                           env=dict(self.env, SERVED=read(os.path.join(review, "served"))), capture_output=True,
                           text=True)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("4. Not checked: segments.", r.stdout)

    def gather_step(self, reviewed):
        """The gather step, with a stand-in gather that writes `reviewed` as reviewed.txt and one changed file."""
        checkout = os.path.join(self.dir, "checkout")
        os.makedirs(os.path.join(checkout, "tools", "oft", "ci"))
        with open(os.path.join(self.dir, "reviewed.txt"), "w") as f:
            f.write(reviewed)
        tool(os.path.join(checkout, "tools", "oft", "ci"), "facts-review-gather", "#!/usr/bin/env bash\n"
             f'mkdir -p "$1"; cp {os.path.join(self.dir, "reviewed.txt")} "$1/reviewed.txt"\n'
             'printf "A\\tprojects/zlib/project.yaml\\n" > "$1/changed.txt"\n')
        output = os.path.join(self.dir, "output")
        r = self.step("gather what the review reads", {"GITHUB_OUTPUT": output}, cwd=checkout)
        return r, read(output) if os.path.exists(output) else ""

    def test_the_gather_step_passes_on_what_was_reviewed(self):
        head = "a" * 40
        r, output = self.gather_step(f"head={head}\nbase_ref=main\nmerge_base={'b' * 40}\n")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(output, f"has_facts=true\nhead={head}\nbase_ref=main\n")

    def test_a_failed_read_of_what_was_reviewed_stops_the_gather_step(self):
        """Its grep ended in `|| true`, so a grep that failed (2) dropped the comment's "of commit ... against ..."
        and the step went on, the shape #135 fixed in the gate."""
        self.fail_when("grep", '[[ "$*" == *reviewed.txt* ]]', 2)
        r, _ = self.gather_step(f"head={'a' * 40}\nbase_ref=main\n")
        self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("could not read .review/reviewed.txt (grep status 2)", r.stdout)


@unittest.skipUnless(HAVE_WORKFLOW, NO_WORKFLOW)
class WorkflowTest(unittest.TestCase):
    """What the workflow grants each job: the review job holds the model credential and must not be able to write to
    the pull request; the comment job writes and must get no identity token."""

    def setUp(self):
        self.jobs = yamlio.load_file(WORKFLOW)["jobs"]

    def test_each_job_has_only_the_permissions_it_needs(self):
        self.assertEqual(self.jobs["review"]["permissions"],
                         {"contents": "read", "pull-requests": "read", "id-token": "write"})
        self.assertEqual(self.jobs["comment"]["permissions"], {"contents": "read", "pull-requests": "write"})

    def test_the_identity_token_goes_to_the_repositories_with_a_federation_rule(self):
        """The ids the token step lets through are the ids the review step names a federation rule for."""
        steps = {s.get("name"): s for s in self.jobs["review"]["steps"]}
        allowed = re.search(r"^\s*([0-9|]+)\) ;;$", steps["get the GitHub identity token for Anthropic"]["run"], re.M)
        rules = re.findall(r"github\.repository_id == '(\d+)' && 'fdrl_\w+'",
                           steps["review"]["env"]["ANTHROPIC_FEDERATION_RULE_ID"])
        self.assertEqual(sorted(allowed.group(1).split("|")), sorted(rules))
        self.assertEqual(len(rules), 2)


@unittest.skipUnless(os.path.exists(CODEOWNERS) and os.path.exists(REVIEW_MD),
                     "no .github/CODEOWNERS or review.md: the internal repository alone has them")
class CodeOwnersTest(unittest.TestCase):
    def test_review_md_and_codeowners_are_the_owned_paths_and_the_last_lines(self):
        """review.md says what the facts review checks, and CODEOWNERS who may change it: only a human may change
        either, so they are owned by the two people who own the reviewer's rules, whose approval main's branch rule
        requires (no team has a grant on this repository). Their lines are the last two, since GitHub takes the last
        line that matches. The release's approvals, allowed axioms and theories keep the same two owners;
        no other path has an owner."""
        patterns = [line.split("#", 1)[0].split() for line in read(CODEOWNERS).splitlines()]
        patterns = [" ".join(p) for p in patterns if p]
        owned = [p for p in patterns if len(p.split()) > 1]
        admins = owned[-1].split(None, 1)[1]
        self.assertEqual(len(admins.split()), 2, "two owners")
        release = [f"/approvals.yaml {admins}", f"/toolchain/allowed-axioms.txt {admins}", f"/theories/ {admins}"]
        last = [f"/review.md {admins}", f"/.github/CODEOWNERS {admins}"]
        self.assertEqual(owned, release + last)
        self.assertEqual(patterns[-2:], last)

    def test_the_review_criteria_are_listed_with_the_facts(self):
        """R104-02: the docs review.md reads as main's are its criteria, so CODEOWNERS lists them as files that need
        judgement, with the same owners as the facts (none since main's #212), as it lists the skill. GitHub takes the
        last line whose pattern matches a path, so that line is checked."""
        skill = read(REVIEW_MD)
        start = skill.index("**The docs are main's**")
        docs = re.findall(r"`(docs/[^`]+)`", skill[start:skill.index(")", skill.index("running.md", start))])
        self.assertEqual(docs, ["docs/facts.md", "docs/statements.md", "docs/building.md", "docs/running.md"])
        review = [".github/workflows/facts-review.yml", "tools/oft/requirements.txt",
                  ".claude/skills/review-facts/SKILL.md", f"projects/zlib/fz/source/{INSTRUCTIONS}"]
        review += [f"tools/oft/ci/facts-review-{n}" for n in ("gather", "run", "comment", "gate")]
        codeowners = read(CODEOWNERS)
        facts_owners = owners_of(codeowners, "projects/zlib/project.yaml")
        self.assertIsNotNone(facts_owners, "CODEOWNERS does not list the facts")
        for path in docs + review:
            with self.subTest(path=path):
                self.assertEqual(owners_of(codeowners, path), facts_owners)

    def test_a_later_line_decides(self):
        """The check above reads CODEOWNERS as GitHub does: a broader line after a doc's own line takes it over."""
        text = "/docs/facts.md @a @b\n/docs/ @someone\n"
        self.assertEqual(owners_of(text, "docs/facts.md"), ["@someone"])
        self.assertEqual(owners_of("docs/*.md @a\n", "docs/facts.md"), ["@a"])
        self.assertEqual(owners_of("AGENTS*.md @a\n", "projects/x/AGENTS.md"), ["@a"])
        self.assertIsNone(owners_of("/docs/facts.md @a\n", "docs/running.md"))
        self.assertEqual(owners_of("/docs/facts.md\n", "docs/facts.md"), [])


def owners_of(text, path):
    """The owners CODEOWNERS `text` gives `path`: those of the last line whose pattern matches it (GitHub's rule), or
    None. Patterns: a leading / anchors at the root, a trailing / takes everything below, * stays inside one name."""
    owners = None
    for line in text.splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        pattern, *names = line.split()
        regex = re.escape(pattern.strip("/")).replace(r"\*", "[^/]*")
        regex = ("^" if pattern.startswith("/") or "/" in pattern.strip("/") else "(^|.*/)") + regex
        regex += "(/.*)?$" if pattern.endswith("/") or "*" not in pattern else "$"
        if re.match(regex, path):
            owners = names
    return owners


@unittest.skipUnless(os.path.exists(SKILL) and os.path.exists(REVIEW_MD),
                     "no review-facts skill: the internal repository alone has it")
class SkillTest(unittest.TestCase):
    """The two rules the skill and review.md tell the agent that the scripts carry out: they must say the same."""

    def test_the_comment_limit_is_review_mds(self):
        """R104-08: one limit, in characters. review.md gives it to the agent; facts-review-run cuts there."""
        stated = re.search(r"at most ([\d,]+) characters", read(REVIEW_MD))
        self.assertIsNotNone(stated, "review.md states no limit on the comment")
        self.assertEqual(int(stated.group(1).replace(",", "")), LIMIT)
        self.assertEqual(re.findall(r"^limit=(\d+)", read(RUN), re.M), [str(LIMIT)])

    def test_the_patch_name_in_the_skill_is_gathers(self):
        """R104-03: the skill's example of a name in patches/ is the name gather gives that path."""
        example = re.search(r"\(`(projects%2F[^`]+\.diff)`\)", read(SKILL)).group(1)
        path = example.removesuffix(".diff").replace("%2F", "/")
        self.assertEqual(patch_name(path), example)


if __name__ == "__main__":
    unittest.main()
