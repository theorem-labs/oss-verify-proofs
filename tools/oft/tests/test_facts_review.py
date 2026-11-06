"""The facts-review gatherer: a change to a project's public patch text brings every fuzz target of that project, with
its build record, into the review."""
import json
import os
import shutil
import stat
import subprocess
import tempfile
import unittest

from oft.tests import helpers


HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
GATHER = os.path.join(REPO, "tools", "oft", "ci", "facts-review-gather")
PATCH = "--- a/zlib.h\n+++ b/zlib.h\n"


@unittest.skipUnless(shutil.which("jq") and shutil.which("git"), "jq or git is not installed")
class FactsReviewGather(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="oft-facts-review-")
        self.addCleanup(self.tmp.cleanup)
        self.root = os.path.join(self.tmp.name, "facts")
        self.out = os.path.join(self.tmp.name, "review")
        self.git_env = helpers.child_environment(helpers.NO_HOME)

    def gather_patch_only(self, harnesses, provenance=False, others=(), patch="patches/zlib/0001-public.patch"):
        """A repository whose base has project zlib with these fuzz targets (each with a build record when
        provenance), and whose head adds only the file patch (by default patches/zlib/0001-public.patch) and, for each
        of others, a fuzz target of project json; run the gatherer on that change."""
        remote = os.path.join(self.tmp.name, "remote.git")
        bin_dir = os.path.join(self.tmp.name, "bin")
        os.makedirs(self.root)
        os.makedirs(bin_dir)
        self.git("init", "-q")
        self.git("config", "user.name", "facts test")
        # an address, which the private-data rule refuses in a file of this repository, is not needed: git takes any
        # string here, and the gatherer reads no author
        self.git("config", "user.email", "facts-test")
        self.put("docs/facts.md", "# facts\n")
        self.put("release.yaml", "schema: test\n")
        self.put("projects/zlib/project.yaml", "project: zlib\n")
        for h in harnesses:
            self.put("projects/zlib/%s/harness.yaml" % h, "harness: %s\n" % h)
            # a source file with this name is data, not another fuzz target
            self.put("projects/zlib/%s/source/harness.yaml" % h, "source: fixture\n")
            if provenance:
                self.put("proofs/zlib/%s/provenance/PROVENANCE.md" % h, "# Build record of %s\n" % h)
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "base")
        base = self.git("rev-parse", "HEAD").strip()
        self.put(patch, PATCH)
        for h in others:
            self.put("projects/json/%s/harness.yaml" % h, "harness: %s\n" % h)
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "public patch")
        head = self.git("rev-parse", "HEAD").strip()
        subprocess.run(["git", "init", "--bare", "-q", remote], check=True, env=self.git_env)
        self.git("remote", "add", "origin", remote)
        self.git("push", "-q", "origin", "HEAD:refs/heads/head")
        pr = os.path.join(self.tmp.name, "pr.json")
        with open(pr, "w", encoding="utf-8") as f:
            json.dump({"number": 1, "title": "public patch", "base": {"ref": "main", "sha": base},
                       "head": {"sha": head}, "draft": True, "body": ""}, f)
        gh = os.path.join(bin_dir, "gh")
        with open(gh, "w", encoding="utf-8") as f:
            f.write("#!/bin/sh\nif [ \"$2\" = \"repos/fake/repo/pulls/1\" ]; then cat \"$FAKE_PR\"; "
                    "else printf '%s\\n' \"$FAKE_BASE\"; fi\n")
        os.chmod(gh, stat.S_IRUSR | stat.S_IWUSR | stat.S_IXUSR)
        env = helpers.child_environment(helpers.NO_HOME, PATH=bin_dir + os.pathsep + os.environ["PATH"], PR="1",
                                        REPO="fake/repo", FAKE_PR=pr, FAKE_BASE=base, GH_TOKEN="")
        helpers.add_git_config(env, ("url.file://%s.insteadOf" % remote, "https://github.com/fake/repo"))
        r = subprocess.run(["bash", GATHER, self.out], cwd=self.root, env=env, capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)

    def git(self, *args):
        r = subprocess.run(["git", "-C", self.root] + list(args), check=True, capture_output=True, text=True,
                           env=self.git_env)
        return r.stdout

    def put(self, rel, text):
        path = os.path.join(self.root, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)

    def read(self, rel):
        with open(os.path.join(self.out, rel), encoding="utf-8") as f:
            return f.read()

    def test_a_patch_only_change_collects_its_project_and_patch_text(self):
        self.gather_patch_only(["fuzz"])
        self.assertIn("A\tpatches/zlib/0001-public.patch\n", self.read("changed.txt"))
        self.assertEqual(self.read("head/patches/zlib/0001-public.patch"), PATCH)
        self.assertTrue(os.path.isfile(os.path.join(self.out, "head", "projects", "zlib", "project.yaml")))
        self.assertEqual(self.read("targets.txt"), "zlib/fuzz\n")

    def test_a_patch_only_change_gathers_every_fuzz_target_s_build_record(self):
        self.gather_patch_only(["fuzz_a", "fuzz_b"], provenance=True)
        self.assertEqual(self.read("targets.txt"), "zlib/fuzz_a\nzlib/fuzz_b\n")
        for h in ("fuzz_a", "fuzz_b"):
            self.assertEqual(self.read("head/proofs/zlib/%s/provenance/PROVENANCE.md" % h), "# Build record of %s\n" % h)

    def test_a_per_project_patch_only_change_requires_every_fuzz_target(self):
        """The public patch text in the per-project layout, projects/<p>/patches/, is a fact as patches/<p>/ is:
        gathered, and every fuzz target of its project kept past the cap."""
        harnesses = ["fuzz_%02d" % i for i in range(61)]
        self.gather_patch_only(harnesses, patch="projects/zlib/patches/0001-public.patch")
        self.assertIn("A\tprojects/zlib/patches/0001-public.patch\n", self.read("changed.txt"))
        self.assertEqual(self.read("head/projects/zlib/patches/0001-public.patch"), PATCH)
        self.assertEqual(self.read("targets.txt"), "".join("zlib/%s\n" % h for h in harnesses))

    def test_a_source_file_named_like_a_patch_is_no_public_patch(self):
        """A fuzz target's source copy may hold a file under a patches/ folder: it is that fuzz target's source, so it
        brings that fuzz target alone, not every fuzz target of its project as public patch text does."""
        self.gather_patch_only(["fuzz_a", "fuzz_b"], patch="projects/zlib/fuzz_a/source/patches/b.patch")
        self.assertIn("A\tprojects/zlib/fuzz_a/source/patches/b.patch\n", self.read("changed.txt"))
        self.assertEqual(self.read("targets.txt"), "zlib/fuzz_a\n")

    def test_a_patch_only_change_reviews_every_fuzz_target_past_the_cap(self):
        """The cap on fuzz targets per review never drops one that a public patch's change requires, and missing.txt
        says that the review is over the cap though nothing was left out (deep review, finding 6)."""
        harnesses = ["fuzz_%02d" % i for i in range(61)]
        self.gather_patch_only(harnesses)
        self.assertEqual(self.read("targets.txt"), "".join("zlib/%s\n" % h for h in harnesses))
        self.assertEqual(self.read("missing.txt"),
                         "fuzz targets: 61 changed, over the cap of 60; this review covers the 61 fuzz targets of "
                         "projects whose public patch changed and leaves out 0 others, in name order\n"
                         "library/zlib: the library is not a GitHub repository pinned to a commit (-)\n")

    def test_the_cap_leaves_out_other_fuzz_targets_after_the_required_ones(self):
        """Past the cap, every fuzz target of a project whose public patch changed is kept, then the others in name
        order; missing.txt says how many others were left out."""
        harnesses = ["fuzz_%02d" % i for i in range(58)]
        others = ["other_%d" % i for i in range(4)]
        self.gather_patch_only(harnesses, others=others)
        self.assertEqual(self.read("targets.txt"), "".join("json/%s\n" % h for h in others[:2])
                         + "".join("zlib/%s\n" % h for h in harnesses))
        self.assertIn("fuzz targets: 62 changed, over the cap of 60; this review covers the 58 fuzz targets of projects "
                      "whose public patch changed and leaves out 2 others, in name order\n", self.read("missing.txt"))


if __name__ == "__main__":
    unittest.main()
