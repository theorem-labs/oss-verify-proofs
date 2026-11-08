"""tools/oft/tests/stale_base.py, which pr.yml's required job runs: the base a pull request run was built on against
the tip of the base branch now, over a scratch git repository with fixture commits and a stand-in gh.

The rule is read from the module; the whole of it is also run as `python3 -m oft.tests.stale_base`, the way the
workflow runs it."""
import json
import os
import re
import stat
import subprocess
import sys
import tempfile
import unittest

from oft import keys, layout, paths
from oft.tests import stale_base
from oft.tests.helpers import REPO

TOOLS = os.path.join(REPO, "tools")
REPO_NAME = "acme/proofs"
BASE_REF = "main"

GIT = ["git", "-c", "user.name=oft-tests", "-c", "user.email=oft-tests" + "@" + "example.invalid",
       "-c", "commit.gpgsign=false"]
GIT_ENV = dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")

# A gh that answers `gh api <endpoint>` from <FAKE_GH_DIR>/<endpoint>.json, with the endpoint's slashes as
# underscores and its query string dropped, and fails like gh does when GitHub answers 404.  The n-th call of one
# endpoint takes <endpoint>.<n>.json when there is one, which is how a base that moves between two reads of its ref
# is served.
FAKE_GH = r"""#!/usr/bin/env bash
[ "$1" = api ] || { echo "fake gh: it serves gh api alone, not $*" >&2; exit 64; }
endpoint="${2%%\?*}"
name="${endpoint//\//_}"
calls="$FAKE_GH_DIR/.calls_$name"
n=$(( $(cat "$calls" 2>/dev/null || echo 0) + 1 ))
echo "$n" > "$calls"
file="$FAKE_GH_DIR/$name.$n.json"
[ -f "$file" ] || file="$FAKE_GH_DIR/$name.json"
if [ ! -f "$file" ]; then
  echo "gh: Not Found (HTTP 404)" >&2
  exit 1
fi
cat "$file"
"""


def git(root, *args, when=None):
    env = GIT_ENV if when is None else dict(GIT_ENV, GIT_AUTHOR_DATE=when, GIT_COMMITTER_DATE=when)
    done = subprocess.run(GIT + ["-C", root, *args], env=env, capture_output=True, text=True)
    if done.returncode != 0:
        raise AssertionError("git %s: %s" % (" ".join(args), done.stderr))
    return done.stdout.strip()


def write(root, rel, text):
    path = os.path.join(root, rel)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


def commit(root, files, message, when=None):
    for rel, text in files.items():
        write(root, rel, text)
    git(root, "add", "-A")
    git(root, "commit", "-q", "-m", message, when=when)
    return git(root, "rev-parse", "HEAD")


# The clock the scratch repositories keep, so that their commits have an order in time: the base at :00, what the
# pull request brings at :05, the base's n-th move at :10+n, and the merge GitHub builds at :59.
def at(minute):
    return "2026-10-30T%02d:%02d:00Z" % (12 + minute // 60, minute % 60)


# What the base held when the run started: a checker, a workflow, a statement and a proof.
START = {
    "tools/oft/check.py": "check\n",
    "tools/oft/keys.py": "keys\n",
    ".github/workflows/pr.yml": "name: pr\n",
    "toolchain/allowed-axioms.txt": "none\n",
    "theories/dune": "(rocq.theory)\n",
    "projects/zlib/checksum_fuzzer/Statements.v": "Theorem t.\n",
    "proofs/zlib/checksum_fuzzer/t/Proof.v": "Proof.\n",
    "README.md": "index\n",
}


class Repo:
    """A scratch repository: HEAD is the merge commit GitHub would build for a pull request on `base`, and the branch
    BASE_REF is `base` plus one commit for each of `moves` (a dict of path -> text each).  `brings` is what the pull
    request itself carries, a proof of zlib/checksum_fuzzer unless another dict is given.  It is its own origin, so
    the runner's fetches have somewhere to go."""

    BRINGS = {"proofs/zlib/checksum_fuzzer/u/Proof.v": "Proof.\n"}

    def __init__(self, tmp, moves=(), merge=True, brings=None):
        self.root = os.path.join(tmp, "repo")
        os.makedirs(self.root)
        git(self.root, "init", "-q", "-b", "line")
        git(self.root, "config", "uploadpack.allowAnySHA1InWant", "true")
        git(self.root, "config", "uploadpack.allowFilter", "true")
        git(self.root, "remote", "add", "origin", self.root)
        self.base = commit(self.root, START, "the base", when=at(0))
        git(self.root, "checkout", "-q", "-b", "contribution")
        commit(self.root, self.BRINGS if brings is None else brings, "what this change brings", when=at(5))
        git(self.root, "checkout", "-q", "line")
        self.commits = []
        for i, files in enumerate(moves):
            self.commits.append((commit(self.root, files, "move %d" % i, when=at(10 + i)), "move %d" % i))
        self.tip = git(self.root, "rev-parse", "HEAD")
        git(self.root, "checkout", "-q", "--detach", self.base)
        if merge:
            git(self.root, "merge", "-q", "--no-ff", "--no-edit", "-m", "merge", "contribution", when=at(59))


class Case(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="oft-stale-base-")
        self.tmp = self._tmp.name
        self.addCleanup(self._tmp.cleanup)
        self.api = os.path.join(self.tmp, "api")
        self.bin = os.path.join(self.tmp, "bin")
        os.makedirs(self.api)
        os.makedirs(self.bin)
        gh = os.path.join(self.bin, "gh")
        with open(gh, "w", encoding="utf-8") as f:
            f.write(FAKE_GH)
        os.chmod(gh, os.stat(gh).st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
        self.summary = os.path.join(self.tmp, "summary.md")

    def serve(self, endpoint, body, call=None):
        """The answer to `gh api <endpoint>`, or to its `call`-th call alone."""
        name = endpoint.replace("/", "_") + ("" if call is None else ".%d" % call) + ".json"
        with open(os.path.join(self.api, name), "w", encoding="utf-8") as f:
            json.dump(body, f)

    def serve_ref(self, tip, call=None):
        self.serve("repos/%s/git/ref/heads/%s" % (REPO_NAME, BASE_REF), {"object": {"sha": tip, "type": "commit"}},
                   call=call)

    def serve_compare(self, base, tip, commits, status="ahead"):
        self.serve("repos/%s/compare/%s...%s" % (REPO_NAME, base, tip),
                   {"status": status, "total_commits": len(commits),
                    "commits": [{"sha": sha, "commit": {"message": subject + "\n\nbody"}}
                                for sha, subject in commits]})

    def make(self, moves=(), merge=True, serve=True, brings=None):
        repo = Repo(self.tmp, moves, merge=merge, brings=brings)
        if serve:
            self.serve_ref(repo.tip)
            if repo.tip != repo.base:
                self.serve_compare(repo.base, repo.tip, repo.commits)
        return repo

    def script(self, repo, base_ref=BASE_REF, whole_tree=False):
        """(exit code, what it printed, what the step summary got).  repo is a Repo or the path of a checkout."""
        root = repo if isinstance(repo, str) else repo.root
        env = dict(os.environ, PATH=self.bin + os.pathsep + os.environ["PATH"], FAKE_GH_DIR=self.api,
                   GITHUB_STEP_SUMMARY=self.summary, PYTHONPATH=TOOLS, PYTHONDONTWRITEBYTECODE="1")
        args = ["--whole-tree"] if whole_tree else []
        done = subprocess.run([sys.executable, "-m", "oft.tests.stale_base", "--root", root, "--repo", REPO_NAME,
                               "--base-ref", base_ref, *args], capture_output=True, text=True, env=env)
        summary = ""
        if os.path.exists(self.summary):
            with open(self.summary, encoding="utf-8") as f:
                summary = f.read()
        return done.returncode, done.stdout + done.stderr, summary


class BaseHasNotMoved(Case):
    def test_a_base_that_has_not_moved_passes(self):
        repo = self.make()
        rc, out, summary = self.script(repo)
        self.assertEqual(rc, 0, out)
        self.assertIn("is still at %s" % repo.base[:7], out)
        self.assertEqual(summary, "")


class BaseMovedWithoutTheChecks(Case):
    def test_a_base_moved_by_another_change_s_proofs_passes(self):
        repo = self.make([{"proofs/json/fuzzer/v/Proof.v": "Proof.\n",
                           "counterexamples/json/fuzzer/s/input.bin": "x\n",
                           "findings/json/fuzzer/1/finding.yaml": "state: open\n"}])
        rc, out, summary = self.script(repo)
        self.assertEqual(rc, 0, out)
        self.assertIn("no check of this run reads any of those paths", out)
        self.assertEqual(summary, "")

    def test_a_base_moved_by_the_shared_generated_files_passes(self):
        repo = self.make([{"README.md": "rendered\n", "index/STATUS.md": "s\n", "index/proofs.tsv": "p\n",
                           "projects/zlib/README.md": "page\n", "analyses/known-issues.md": "k\n"}])
        rc, out, _ = self.script(repo)
        self.assertEqual(rc, 0, out)
        self.assertIn("no check of this run reads any of those paths", out)

    def test_a_base_moved_by_a_changelog_or_a_note_passes(self):
        repo = self.make([{"CHANGELOG.md": "c\n", "docs/checking.md": "d\n", "notes/x.md": "n\n",
                           "approvals.yaml": "a: 1\n"}])
        rc, out, _ = self.script(repo)
        self.assertEqual(rc, 0, out)

    def test_a_base_moved_by_contributions_in_the_per_project_layout_passes(self):
        repo = self.make([{"projects/json/fuzzer/proofs/t/Proof.v": "Proof.\n",
                           "projects/json/fuzzer/proofs/t/dune": "(rule)\n",
                           "projects/json/fuzzer/counterexamples/t/input.bin": "x\n"}])
        rc, out, _ = self.script(repo)
        self.assertEqual(rc, 0, out)

    def test_a_base_moved_by_another_fuzz_target_of_this_project_passes(self):
        """This change proves zlib/checksum_fuzzer (Repo); a key of its parts holds no file of another fuzz
        target."""
        repo = self.make([{"proofs/zlib/compress_fuzzer/t/Proof.v": "Proof.\n"}])
        rc, out, _ = self.script(repo)
        self.assertEqual(rc, 0, out)


class BaseMovedUnderTheChecks(Case):
    def fails(self, moves, path, what, kind=None, brings=None, whole_tree=False):
        repo = self.make(moves, brings=brings)
        rc, out, summary = self.script(repo, whole_tree=whole_tree)
        self.assertEqual(rc, 1, out)
        self.assertIn("the base moved by a change to %s since this run started" % (kind or what), out)
        self.assertIn("push or re-run", out)
        self.assertIn("%s (%s)" % (path, what), summary)
        return repo, out, summary

    def test_a_base_moved_by_a_tools_change_fails(self):
        repo, out, summary = self.fails([{"tools/oft/keys.py": "keys, changed\n"}], "tools/oft/keys.py", "the tools")
        self.assertIn(repo.commits[0][0][:7], out)
        self.assertIn("move 0", out)
        self.assertIn(repo.tip[:7], summary)

    def test_a_base_moved_by_the_workflow_fails(self):
        self.fails([{".github/workflows/pr.yml": "name: pr\non: push\n"}], ".github/workflows/pr.yml",
                   "the workflows")

    def test_a_base_moved_by_the_toolchain_fails(self):
        self.fails([{"toolchain/allowed-axioms.txt": "classic\n"}], "toolchain/allowed-axioms.txt", "the toolchain")

    def test_a_base_moved_by_this_change_s_own_statements_fails(self):
        self.fails([{"projects/zlib/checksum_fuzzer/Statements.v": "Theorem u.\n"}],
                   "projects/zlib/checksum_fuzzer/Statements.v",
                   "this change's own fuzz target zlib/checksum_fuzzer")

    def test_another_fuzz_target_s_statements_pass_a_run_that_read_only_its_own(self):
        """The check of fuzz target X reads X's facts and its project's files, and nothing of fuzz target Y.  A
        statements pull request touches many fuzz targets at once (#427 brought five projects'), so reading them
        all would fail every open pull request's required."""
        repo = self.make([{"projects/json/fuzzer/Statements.v": "Theorem v.\n",
                           "projects/json/project.yaml": "name: json\n"}])
        rc, out, summary = self.script(repo)
        self.assertEqual(rc, 0, out)
        self.assertIn("no check of this run reads any of those paths", out)
        self.assertEqual(summary, "")

    def test_another_fuzz_target_s_statements_fail_a_run_that_read_the_whole_tree(self):
        """With the tools' tests, and the whole-tree lint with them, a change anywhere in the base's facts can
        change what this run found (pr.yml's reach step: repository_lint and tests)."""
        self.fails([{"projects/json/fuzzer/Statements.v": "Theorem v.\n"}],
                   "projects/json/fuzzer/Statements.v", "the statements", whole_tree=True)

    def test_a_sibling_fuzz_target_s_harness_yaml_fails_a_narrow_run(self):
        """keys._project digests a project's project.yaml with every fuzz target's harness.yaml, and that one id is
        a component of every part of every unit of the project: so a base that lands pupnp/FuzzIxml's harness.yaml
        moves the key of pupnp/FuzzHttp too, and an open pupnp/FuzzHttp pull request must not keep its green.
        Measured on #427: keys._project('pupnp') went from f67f79ec2872 to 25d0bb8dc8aa."""
        self.fails([{"projects/zlib/compress_fuzzer/harness.yaml": "name: compress_fuzzer\n"}],
                   "projects/zlib/compress_fuzzer/harness.yaml", "this change's own project zlib")

    def test_this_change_s_own_fuzz_target_s_source_fails_a_narrow_run(self):
        self.fails([{"projects/zlib/checksum_fuzzer/source/fuzz.c": "int main(void);\n"}],
                   "projects/zlib/checksum_fuzzer/source/fuzz.c",
                   "this change's own fuzz target zlib/checksum_fuzzer")

    def test_this_change_s_own_fuzz_target_s_source_fails_a_whole_tree_run(self):
        self.fails([{"projects/zlib/checksum_fuzzer/source/fuzz.c": "int main(void);\n"}],
                   "projects/zlib/checksum_fuzzer/source/fuzz.c",
                   "this change's own fuzz target zlib/checksum_fuzzer", whole_tree=True)

    def test_this_change_s_own_project_s_patches_fail_a_narrow_run(self):
        self.fails([{"projects/zlib/patches/fix.patch": "--- a\n"}], "projects/zlib/patches/fix.patch",
                   "this change's own project zlib")

    def test_this_change_s_own_project_s_patches_fail_a_whole_tree_run(self):
        self.fails([{"projects/zlib/patches/fix.patch": "--- a\n"}], "projects/zlib/patches/fix.patch",
                   "this change's own project zlib", whole_tree=True)

    def test_one_tools_commit_among_proof_commits_fails(self):
        repo = self.make([{"proofs/json/fuzzer/v/Proof.v": "Proof.\n"},
                          {"tools/oft/check.py": "check, changed\n"},
                          {"README.md": "rendered\n"}])
        rc, out, summary = self.script(repo)
        self.assertEqual(rc, 1, out)
        self.assertIn("3 commit(s) on %s" % BASE_REF, out)
        self.assertIn("tools/oft/check.py (the tools)", summary)
        self.assertNotIn("README.md (", summary)

    def test_a_long_base_move_counts_the_commits_the_page_left_out(self):
        """A compare answers at most 100 commits a page while it counts them all, so the message counts what it did
        not name from the total, not from the page."""
        repo = self.make([{"tools/oft/keys.py": "keys, changed\n"}], serve=False)
        self.serve_ref(repo.tip)
        self.serve("repos/%s/compare/%s...%s" % (REPO_NAME, repo.base, repo.tip),
                   {"status": "ahead", "total_commits": 608,
                    "commits": [{"sha": sha, "commit": {"message": subject}} for sha, subject in repo.commits]})
        rc, out, _ = self.script(repo)
        self.assertEqual(rc, 1, out)
        self.assertIn("608 commit(s) on %s" % BASE_REF, out)
        self.assertIn("and 607 more", out)

    def test_a_base_moved_by_this_change_s_own_fuzz_target_fails(self):
        """keys.py holds a unit's whole proofs folder in its build key, so the merged tree carries a key neither
        this run nor the other change's run checked."""
        self.fails([{"proofs/zlib/checksum_fuzzer/lib/Agree.v": "Lemma.\n"}],
                   "proofs/zlib/checksum_fuzzer/lib/Agree.v", "this change's own fuzz target zlib/checksum_fuzzer")

    def test_a_base_moved_by_this_change_s_own_project_s_unpatched_pins_fails(self):
        """The findings part of every unit of a project reads its unpatched.yaml (keys.py)."""
        self.fails([{"findings/zlib/unpatched.yaml": "zlib: pinned\n"}],
                   "findings/zlib/unpatched.yaml", "this change's own project zlib")

    def test_a_change_that_brings_only_a_fuzz_target_s_facts_owns_it(self):
        """own_units counts every path of this change, not only the ones layout.is_change names: a part's key holds
        a fuzz target's facts and its proofs together, so a change that carries only its Statements.v owns it, and
        a base that lands its proofs leaves a key neither run checked.  Restoring the layout.is_change filter in
        own_units passes every other test in this file; this one is what holds it."""
        repo = self.make([{"proofs/zlib/checksum_fuzzer/v/Proof.v": "Proof.\n"}],
                         brings={"projects/zlib/checksum_fuzzer/Statements.v": "Theorem u.\n"})
        rc, out, summary = self.script(repo)
        self.assertEqual(rc, 1, out)
        self.assertIn("proofs/zlib/checksum_fuzzer/v/Proof.v (this change's own fuzz target zlib/checksum_fuzzer)",
                      summary)


class ShallowCheckout(Case):
    """What actions/checkout leaves the step: one commit deep, with the base commit named but absent.  There
    `git rev-parse HEAD^1` answers nothing, since .git/shallow hides a shallow commit's parents, so the script reads
    the parents from the commit object and fetches what it needs."""

    def shallow(self, repo):
        """A one-commit-deep checkout of the merge commit, from repo as its origin."""
        merge = git(repo.root, "rev-parse", "HEAD")
        root = os.path.join(self.tmp, "shallow")
        os.makedirs(root)
        git(root, "init", "-q")
        git(root, "remote", "add", "origin", repo.root)
        git(root, "fetch", "-q", "--no-tags", "--depth=1", "origin", merge)
        git(root, "checkout", "-q", "--detach", "FETCH_HEAD")
        self.assertEqual(git(root, "rev-parse", "--is-shallow-repository"), "true")
        self.assertEqual(git(root, "rev-parse", "HEAD^@"), "", "a shallow commit's parents are hidden from rev-parse")
        return root

    def test_a_base_moved_by_a_tools_change_fails_in_a_shallow_checkout(self):
        repo = self.make([{"tools/oft/keys.py": "keys, changed\n"}])
        root = self.shallow(repo)
        rc, out, summary = self.script(root)
        self.assertEqual(rc, 1, out)
        self.assertIn("the base moved by a change to the tools since this run started", out)
        self.assertIn("tools/oft/keys.py (the tools)", summary)

    def test_a_base_moved_by_proofs_alone_passes_in_a_shallow_checkout(self):
        repo = self.make([{"proofs/json/fuzzer/v/Proof.v": "Proof.\n",
                           "projects/zlib/checksum_fuzzer/README.md": "page\n"}])
        root = self.shallow(repo)
        rc, out, summary = self.script(root)
        self.assertEqual(rc, 0, out)
        self.assertIn("no check of this run reads any of those paths", out)
        self.assertEqual(summary, "")


class BaseMovingWhileTheStepRuns(Case):
    """A pass must rest on a tip the base still had when the comparison ended: the base is read again after it."""

    def proofs(self, n):
        return [{"proofs/json/fuzzer/p%d/Proof.v" % i: "Proof.\n"} for i in range(n)]

    def test_a_tools_change_that_lands_during_the_comparison_fails(self):
        repo = self.make(self.proofs(1) + [{"tools/oft/keys.py": "keys, changed\n"}], serve=False)
        first, second = (sha for sha, _subject in repo.commits)
        self.serve_ref(first, call=1)          # what the base is when the comparison starts
        self.serve_ref(second, call=2)         # and what it is when the comparison ends
        self.serve_compare(repo.base, first, repo.commits[:1])
        self.serve_compare(repo.base, second, repo.commits)
        rc, out, summary = self.script(repo)
        self.assertEqual(rc, 1, out)
        self.assertIn("the base moved by a change to the tools since this run started", out)
        self.assertIn("tools/oft/keys.py (the tools)", summary)

    def test_a_base_that_moves_at_every_read_fails_loudly(self):
        repo = self.make(self.proofs(4), serve=False)
        tips = [sha for sha, _subject in repo.commits]
        for i, tip in enumerate(tips, start=1):
            self.serve_ref(tip, call=i)
            self.serve_compare(repo.base, tip, repo.commits[:i])
        rc, out, _ = self.script(repo)
        self.assertEqual(rc, 2, out)
        self.assertIn("moved again every time this step compared it", out)


class CannotTell(Case):
    def test_an_api_that_cannot_name_the_tip_fails_loudly(self):
        repo = self.make(serve=False)
        rc, out, _ = self.script(repo)
        self.assertEqual(rc, 2, out)
        self.assertIn("cannot be told", out)
        self.assertIn("the tip of %s" % BASE_REF, out)

    def test_a_tip_that_is_no_commit_fails_loudly(self):
        repo = self.make(serve=False)
        self.serve("repos/%s/git/ref/heads/%s" % (REPO_NAME, BASE_REF), {"message": "Not Found"})
        rc, out, _ = self.script(repo)
        self.assertEqual(rc, 2, out)
        self.assertIn("named no commit", out)

    def test_an_api_that_cannot_name_the_commits_fails_loudly(self):
        repo = self.make([{"tools/oft/keys.py": "keys, changed\n"}], serve=False)
        self.serve_ref(repo.tip)
        rc, out, _ = self.script(repo)
        self.assertEqual(rc, 2, out)
        self.assertIn("the commits %s took after" % REPO_NAME, out)

    def test_a_base_branch_that_dropped_the_commit_fails_loudly(self):
        repo = self.make([{"tools/oft/keys.py": "keys, changed\n"}], serve=False)
        self.serve_ref(repo.tip)
        self.serve_compare(repo.base, repo.tip, repo.commits, status="diverged")
        rc, out, _ = self.script(repo)
        self.assertEqual(rc, 2, out)
        self.assertIn("no longer holds that commit", out)

    def test_a_head_that_is_not_a_merge_commit_fails_loudly(self):
        repo = self.make(merge=False)
        rc, out, _ = self.script(repo)
        self.assertEqual(rc, 2, out)
        self.assertIn("not the merge commit GitHub builds for a pull request", out)


class TheRule(unittest.TestCase):
    """feeds_the_checks over the paths of this repository, and against what paths.py and keys.py say they are."""

    def test_what_the_checks_read_from_the_base(self):
        for path, what in (
                ("tools/oft/check.py", "the tools"),
                ("tools/oft/ci/check-units.sh", "the tools"),
                ("dev/enroll/check.sh", "the tools"),
                (".github/workflows/pr.yml", "the workflows"),
                (".github/actions/plan-drafts/action.yml", "the workflows"),
                (".claude/skills/review-facts/SKILL.md", "the tools"),
                ("toolchain/checker.Dockerfile", "the toolchain"),
                ("toolchain/allowed-axioms.txt", "the toolchain"),
                ("theories/Core.v", "the statements"),
                ("tests/check.sh", "the controls"),
                ("release.yaml", "the pinned images"),
                ("dune-project", "the statements"),
                ("theories/dune", "the statements"),
                (".gitattributes", "the checkout attributes"),
                ("proofs/.gitattributes", "the checkout attributes")):
            with self.subTest(path=path):
                self.assertEqual(stale_base.feeds_the_checks(path), what)

    # The facts of one fuzz target and the files of one project: read by that fuzz target's check alone, so a move
    # of the base in them is read only by a run that touches them itself or that read the whole tree.
    FACTS = ("projects/zlib/project.yaml", "projects/zlib/checksum_fuzzer/harness.yaml",
             "projects/zlib/checksum_fuzzer/source/fuzz.c", "projects/zlib/checksum_fuzzer/Statements.v",
             "projects/zlib/patches/fix.patch", "patches/zlib/fix.patch")

    def test_the_facts_are_read_by_a_run_that_read_the_whole_tree(self):
        for path in self.FACTS:
            with self.subTest(path=path):
                self.assertEqual(stale_base.feeds_the_checks(path, whole_tree=True), "the statements")

    def test_another_fuzz_target_s_facts_are_not_read_by_a_run_that_did_not(self):
        for path in self.FACTS:
            with self.subTest(path=path):
                self.assertIsNone(stale_base.feeds_the_checks(path))

    def test_this_change_s_own_facts_are_read_either_way(self):
        units, projects = {"zlib/checksum_fuzzer"}, {"zlib"}
        for path in self.FACTS:
            for whole_tree in (False, True):
                with self.subTest(path=path, whole_tree=whole_tree):
                    self.assertIsNotNone(stale_base.feeds_the_checks(path, units, projects, whole_tree))

    def test_what_a_run_s_verdict_does_not_rest_on(self):
        for path in ("proofs/zlib/checksum_fuzzer/t/Proof.v", "proofs/zlib/checksum_fuzzer/t/dune",
                     "proofs/zlib/checksum_fuzzer/lib/Lib.v",
                     "projects/zlib/checksum_fuzzer/proofs/t/Proof.v",
                     "projects/zlib/checksum_fuzzer/proofs/lib/dune",
                     "counterexamples/json/fuzzer/t/input.bin",
                     "projects/zlib/checksum_fuzzer/counterexamples/t/expect.yaml",
                     "findings/zlib/checksum_fuzzer/1/finding.yaml",
                     "projects/zlib/checksum_fuzzer/findings/1/finding.yaml",
                     # a project's unpatched pins: layout.is_change names them a file a change brings, in both
                     # layouts, so another change's land without failing a run
                     "findings/zlib/unpatched.yaml", "projects/zlib/unpatched.yaml",
                     "README.md", "index/STATUS.md", "index/proofs.tsv", "analyses/known-issues.md",
                     # the pages `oft generate` renders and no check opens (test_keys.Checker): every merge of a
                     # proof renders them, so a base move that brings them alone must not fail a run
                     "projects/zlib/README.md", "projects/zlib/checksum_fuzzer/README.md",
                     "CHANGELOG.md", "NOTICE", "approvals.yaml", "review.md",
                     "docs/checking.md", "notes/x.md", "LICENSE", "CONTRIBUTING.md"):
            with self.subTest(path=path):
                self.assertIsNone(stale_base.feeds_the_checks(path))

    def test_every_contribution_of_either_layout_is_passed_over(self):
        """layout.is_change names the files a change brings, and paths.py classes them `contrib`: they are what its
        own run checked, and a base that took another change's are in no key of this change's parts."""
        bound = {"project": "zlib", "harness": "checksum_fuzzer", "statement": "t"}
        passed = 0
        for cls, pattern in paths.TABLE:
            if cls != "contrib":
                continue
            rel = "/".join("x.v" if seg == "**" else ("x" if seg == "*" else
                                                      bound.get(seg[1:-1], "x") if seg.startswith("{") else seg)
                           for seg in pattern.split("/"))
            rel = rel.replace("*", "x")
            with self.subTest(pattern=pattern):
                self.assertIsNotNone(paths.match(pattern, rel), "the stand-in path %s is not one of %s" %
                                     (rel, pattern))
                self.assertIsNone(stale_base.feeds_the_checks(rel))
                passed += 1
        self.assertGreater(passed, 20)

    def test_every_shared_generated_file_is_passed_over(self):
        """paths.SHARED: .github/workflows/index.yml renders them after each merge and no key holds them
        (test_keys.test_the_shared_generated_files_are_in_no_key)."""
        for pattern in paths.SHARED:
            rel = pattern.replace("{project}", "zlib").replace("*", "x")
            with self.subTest(pattern=pattern):
                self.assertIsNotNone(paths.match(pattern, rel))
                self.assertIsNone(stale_base.feeds_the_checks(rel))

    def test_every_file_of_the_checker_is_read_from_the_base(self):
        """keys.checker hashes every file of tools/ but the files keys.NOT_THE_CHECKER names; a check
        job runs all of tools/ from the base, so every one of them is read from it."""
        for root, _dirs, files in os.walk(os.path.join(REPO, "tools")):
            for name in files:
                rel = os.path.relpath(os.path.join(root, name), REPO).replace(os.sep, "/")
                if "/__pycache__/" in rel:
                    continue
                with self.subTest(path=rel):
                    self.assertEqual(stale_base.feeds_the_checks(rel), "the tools")

    def test_this_runner_is_in_no_key(self):
        """It lives under tools/oft/tests/ because keys.NOT_THE_CHECKER names oft/tests/: a file anywhere else under
        tools/ is the checker, whose id is in every unit's key, so adding this one would re-check every fuzz
        target."""
        self.assertTrue(keys.not_the_checker("tools/oft/tests/stale_base.py"))
        self.assertTrue(re.fullmatch(r".*/tools/oft/tests/stale_base\.py", stale_base.__file__))

    def test_a_fuzz_target_this_change_also_touches_is_read_from_the_base(self):
        """keys.py holds a unit's whole proofs folder in its build key, so a base that takes another change to a
        fuzz target this change also changes leaves a key neither run checked."""
        mine = "proofs/zlib/checksum_fuzzer/t/Proof.v"
        theirs = "proofs/zlib/checksum_fuzzer/lib/Agree.v"
        other = "proofs/json/fuzzer/t/Proof.v"
        self.assertEqual(layout.unit_of(mine), "zlib/checksum_fuzzer")
        units, projects = {"zlib/checksum_fuzzer"}, {"zlib"}
        self.assertEqual(stale_base.feeds_the_checks(theirs, units, projects),
                         "this change's own fuzz target zlib/checksum_fuzzer")
        self.assertEqual(stale_base.feeds_the_checks("projects/zlib/checksum_fuzzer/proofs/lib/Agree.v", units,
                                                     projects), "this change's own fuzz target zlib/checksum_fuzzer")
        self.assertEqual(stale_base.feeds_the_checks("findings/zlib/unpatched.yaml", units, projects),
                         "this change's own project zlib")
        self.assertIsNone(stale_base.feeds_the_checks(other, units, projects))
        self.assertIsNone(stale_base.feeds_the_checks(theirs, set(), set()))

    def test_every_dune_file_name_a_key_reads_matches_the_rule(self):
        """stale_base restates the dune file names as a regular expression, which this test holds to
        layout.DUNE_FILES: a name added there must be added to the rule too."""
        for name in layout.DUNE_FILES:
            with self.subTest(name=name):
                self.assertEqual(stale_base.feeds_the_checks(name), "the statements")
                self.assertEqual(stale_base.feeds_the_checks("projects/zlib/checksum_fuzzer/" + name),
                                 "the statements")

    def test_a_fuzz_target_this_change_touches_through_its_facts_is_its_own(self):
        """A change that carries a fuzz target's statements owns it as surely as one that carries its proofs: a
        part's key holds the facts and the proofs together (keys.py), so a base that lands that fuzz target's
        proofs leaves the merged tree with a key neither run checked."""
        for mine, unit in (("projects/zlib/checksum_fuzzer/Statements.v", "zlib/checksum_fuzzer"),
                           ("projects/zlib/checksum_fuzzer/Images.v", "zlib/checksum_fuzzer"),
                           ("projects/zlib/checksum_fuzzer/source/fuzz.c", "zlib/checksum_fuzzer")):
            with self.subTest(path=mine):
                self.assertEqual(stale_base.unit_and_project(mine), (unit, "zlib"))
        units, projects = {"zlib/checksum_fuzzer"}, set()
        self.assertEqual(stale_base.feeds_the_checks("proofs/zlib/checksum_fuzzer/v/Proof.v", units, projects),
                         "this change's own fuzz target zlib/checksum_fuzzer")
        self.assertEqual(stale_base.feeds_the_checks("findings/zlib/unpatched.yaml", units, projects),
                         "this change's own project zlib")
        self.assertIsNone(stale_base.feeds_the_checks("proofs/json/fuzzer/v/Proof.v", units, projects))

    def test_a_project_this_change_touches_at_its_own_level_covers_its_fuzz_targets(self):
        """project.yaml, any fuzz target's harness.yaml, unpatched.yaml and patches/ are read by the key of every
        fuzz target of the project."""
        for mine in ("projects/zlib/project.yaml", "projects/zlib/checksum_fuzzer/harness.yaml",
                     "projects/zlib/unpatched.yaml", "findings/zlib/unpatched.yaml", "patches/zlib/fix.patch"):
            with self.subTest(path=mine):
                self.assertEqual(stale_base.unit_and_project(mine), (None, "zlib"))
        units, projects = set(), {"zlib"}
        self.assertEqual(stale_base.feeds_the_checks("proofs/zlib/compress_fuzzer/v/Proof.v", units, projects),
                         "this change's own project zlib")
        self.assertEqual(stale_base.feeds_the_checks("findings/zlib/unpatched.yaml", units, projects),
                         "this change's own project zlib")
        self.assertIsNone(stale_base.feeds_the_checks("proofs/json/fuzzer/v/Proof.v", units, projects))

    def test_no_path_of_the_tools_or_the_workflows_names_a_project(self):
        for path in ("tools/oft/keys.py", ".github/workflows/pr.yml", "theories/Core.v", "docs/checking.md"):
            with self.subTest(path=path):
                self.assertEqual(stale_base.unit_and_project(path), (None, None))

    def test_what_keys_project_digests_is_judged_by_the_project(self):
        """keys._project digests a project's project.yaml and every fuzz target's harness.yaml into one id, and
        keys.keys puts that id in every part of every unit of the project: so a sibling fuzz target's harness.yaml
        is read by them all.  Which files those are is discovered from keys itself, by changing each in a scratch
        repository and watching the digest, so stale_base.PROJECT_LEVEL cannot drift from it.  Everything else of a
        fuzz target's folder is that fuzz target's own."""
        files = {"projects/zlib/project.yaml": "name: zlib\n",
                 "projects/zlib/checksum_fuzzer/harness.yaml": "name: checksum_fuzzer\n",
                 "projects/zlib/checksum_fuzzer/Statements.v": "Theorem t.\n",
                 "projects/zlib/checksum_fuzzer/Images.v": "Definition i.\n",
                 "projects/zlib/checksum_fuzzer/source/fuzz.c": "int f;\n"}

        def digest(root, at):
            return keys._project(root, at, "zlib", keys.Attributes(root, at, ("projects",)))

        with tempfile.TemporaryDirectory(prefix="oft-project-level-") as tmp:
            root = os.path.join(tmp, "repo")
            os.makedirs(root)
            git(root, "init", "-q")
            before = digest(root, commit(root, files, "a project"))
            for rel, text in files.items():
                after = digest(root, commit(root, {rel: text + "# changed\n"}, "change %s" % rel))
                restored = digest(root, commit(root, {rel: text}, "restore %s" % rel))
                self.assertEqual(restored, before, "the scratch repository did not come back to where it was")
                with self.subTest(path=rel):
                    if after != before:
                        self.assertEqual(stale_base.unit_and_project(rel), (None, "zlib"),
                                         "keys._project digests %s, so every fuzz target of zlib is checked with "
                                         "it and a base move in it must be judged by the project" % rel)
                    else:
                        self.assertEqual(stale_base.unit_and_project(rel), ("zlib/checksum_fuzzer", "zlib"),
                                         "keys._project does not digest %s, so it is its own fuzz target's" % rel)

    # The rows of paths.TABLE the checks do not read, each with why.  Every other row must be read, so that a row
    # added later for a path a check reads cannot pass the gate in silence (the sweep below).
    NOT_READ = {
        # no job of a run opens them
        "LICENSE", "CITATION.cff", "CONTRIBUTING.md", "SECURITY.md", "REUSE.toml", "oft", "theorem", ".gitignore",
        "docs/*.md", "docs/reference/*.md", "notes/*.md", "review.md",
        # facts no job of a run opens (lint.read_by_every_verdict takes them, "wider on purpose, a margin")
        "NOTICE", "CHANGELOG.md",
        # which proofs a release publishes: read by `oft release-tree`, by no check of a pull request
        "approvals.yaml",
        # the change ledgers (oft change-ledger): no job of a run opens them, and `oft release-tree` removes changes/
        "changes/*/*",
        # the shared generated files and the pages a merge renders (paths.SHARED, and no check opens a README.md
        # under projects/: test_keys.Checker)
        "README.md", "index/STATUS.md", "index/PROOFS.md", "index/*.tsv", "analyses/harness-checks/checks.tsv",
        "analyses/known-issues.md", "analyses/harness-checks/README.md", "analyses/failure-handlers/README.md",
        "analyses/failure-handlers/failure_handlers.tsv",
        "projects/{project}/README.md", "projects/{project}/{harness}/README.md",
        # what an agent reads before it works here, and the licences a release ships: no job of a run opens either
        "AGENTS.md", "LICENSES/anthropic-proofs-LICENSE", "LICENSES/anthropic-proofs-LICENSE-MIT",
        "LICENSES/anthropic-proofs-NOTICE",
        # the OSS Verify stream's operational tools: no job reads them from the base.  Without pull request 496,
        # which adds the directory, no job of a run opens dev/stream/ at all; 496 adds a stream_tools job, and that
        # job checks out the head alone and runs the head's own checker over it, on the lines the change wrote
        # (the plan job's rows).  A move of the base under dev/stream/ is checked by the run of the change that made
        # it, as another change's proofs are by theirs.  dev/stream/ is in no unit's key either (keys.checker lists
        # tools/ alone), so no check of this run reads the base's copy.
        "dev/stream/**",
    }

    def stand_in(self, pattern):
        """A path that matches the pattern, as test_every_contribution_of_either_layout_is_passed_over builds it."""
        bound = {"project": "zlib", "harness": "checksum_fuzzer", "statement": "t"}
        rel = "/".join("x.v" if seg == "**" else ("x" if seg == "*" else
                                                  bound.get(seg[1:-1], "x") if seg.startswith("{") else seg)
                       for seg in pattern.split("/"))
        return rel.replace("*", "x")

    def test_every_row_of_the_path_table_is_read_or_named_as_unread(self):
        """paths.TABLE holds every path the repository may hold, and the `paths` lint rule makes each file match one
        row.  A row added later must be put on one side or the other here, instead of falling through
        feeds_the_checks as a path no check reads.  The sweep asks a run that read the whole tree, the widest the
        rule goes: a row that is read by no such run is read by none."""
        swept = 0
        for cls, pattern in paths.TABLE:
            rel = self.stand_in(pattern)
            # a file a change brings is judged by whether this change touches its fuzz target, which the tests
            # above cover; the sweep is about everything else
            if cls == "contrib" or layout.is_change(rel) or pattern in self.NOT_READ:
                continue
            with self.subTest(pattern=pattern):
                self.assertIsNotNone(paths.match(pattern, rel), "the stand-in path %s is not one of %s"
                                     % (rel, pattern))
                self.assertIsNotNone(stale_base.feeds_the_checks(rel, whole_tree=True),
                                     "%s matches no row of FEEDS_THE_CHECKS or THE_FACTS and is in no NOT_READ "
                                     "entry: decide which side it is on" % pattern)
                swept += 1
        self.assertGreater(swept, 30)

    def test_every_unread_row_really_is_unread(self):
        """The other direction: a row named unread that the rule does read is a stale entry."""
        patterns = {pattern for _cls, pattern in paths.TABLE}
        for pattern in sorted(self.NOT_READ):
            with self.subTest(pattern=pattern):
                self.assertIn(pattern, patterns, "no row of paths.TABLE is %s any more" % pattern)
                rel = self.stand_in(pattern)
                self.assertFalse(layout.is_change(rel), "%s is a file a change brings, not an unread row" % pattern)
                self.assertIsNone(stale_base.feeds_the_checks(rel, whole_tree=True))


if __name__ == "__main__":
    unittest.main()
