"""tools/oft/model.py, read with git from local repositories (no network), and lint rules `model` and `pins`, which
run with --release on what model.Public reads."""
import os
import subprocess
import tempfile
import unittest

from oft import model
from oft.tests.helpers import FIXTURE_LPS_TREE, Public, Tree, add_build_record
from oft.tests.test_records import add_proof

GIT = ["git", "-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false", "-c", "tag.gpgsign=false"]
MODEL_URL = "https://github.com/theorem-labs/rocq-linux-process-semantics"
STATIC_ASAN_URL = "https://github.com/theorem-labs/static-asan"
RECORD = "proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.yaml"


class Repo:
    """A git repository in a temporary directory, made by the test."""

    def __init__(self, d):
        self.root = d
        os.makedirs(d)
        self.git("init", "-q", "-b", "main")

    def git(self, *args):
        return subprocess.run(GIT + ["-C", self.root] + list(args), check=True, capture_output=True,
                              text=True).stdout.strip()

    def commit(self, files, message="c"):
        for rel, text in files.items():
            p = os.path.join(self.root, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, "w") as f:
                f.write(text)
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", message)
        return self.git("rev-parse", "HEAD")


def dockerfile_hash(repo, commit, pathspecs):
    """The hash as toolchain/checker.Dockerfile computes it, by the shell's own tools."""
    with tempfile.TemporaryDirectory() as d:
        ctx = os.path.join(d, "ctx")
        os.makedirs(ctx)
        if pathspecs:
            archive = "git -C %s archive %s -- %s | tar -x -C %s" % (repo.root, commit, " ".join(
                "'%s'" % p for p in pathspecs), ctx)
        else:
            archive = "git -C %s archive %s package | tar -x -C %s" % (repo.root, commit, ctx)
            ctx = os.path.join(ctx, "package")
        subprocess.run(["bash", "-c", archive], check=True)
        return subprocess.run(["bash", "-c", "cd '%s' && find . -type f -printf '%%P\\n' | LC_ALL=C sort | "
                               "xargs -d '\\n' -r sha256sum | sha256sum | cut -c1-64" % ctx],
                              check=True, capture_output=True, text=True).stdout.strip()


MODEL_FILES = {"dune-project": "(lang dune 3.0)\n", "theories/A.v": "Definition a := 1.\n",
               "theories/b c.v": "Definition b := 2.\n", "theories/Common/C.v": "Definition c := 3.\n",
               "theories/Sub/D.v": "Definition d := 4.\n", "README.md": "the model\n",
               "package/theories/A.v": "Definition a := 1.\n", "package/dune-project": "(lang dune 3.0)\n"}
CUT = ["dune-project", "theories", ":(exclude)theories/Common"]


class Model(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix="oft-model-")
        self.addCleanup(tmp.cleanup)
        self.tmp = tmp.name
        self.origin = Repo(os.path.join(self.tmp, "origin"))

    def test_the_cut_hashes_as_the_checker_dockerfile_hashes_it(self):
        c = self.origin.commit(MODEL_FILES)
        os.symlink("A.v", os.path.join(self.origin.root, "theories", "link.v"))
        c = self.origin.commit({}, "a link, which is no regular file")
        for spec in (CUT, None):
            with self.subTest(spec=spec):
                got = model.cut_sha256(self.origin.root, c, spec)
                self.assertEqual(got, dockerfile_hash(self.origin, c, spec))
        self.assertNotEqual(model.cut_sha256(self.origin.root, c, CUT), model.cut_sha256(self.origin.root, c, None))

    def test_a_model_commit_takes_the_hash_of_its_line(self):
        first = self.origin.commit(MODEL_FILES)
        tree = self.origin.git("rev-parse", first + "^{tree}")
        later = self.origin.commit({"theories/E.v": "Definition e := 5.\n"})
        self.origin.git("checkout", "-q", "--orphan", "other")
        apart = self.origin.commit({"package/X.v": "Definition x := 0.\n"})
        line = {"cut": "toolchain/lps-core.paths", "commit": "0" * 40, "tree": tree, "sha256": "1" * 64}
        data = {"lines": [line], "other": {"cut": "package/", "sha256": "2" * 64}}
        self.assertEqual(model.required_tree(self.origin.root, later, data), ("1" * 64, "toolchain/lps-core.paths"))
        self.assertEqual(model.required_tree(self.origin.root, first, data), ("1" * 64, "toolchain/lps-core.paths"))
        self.assertEqual(model.required_tree(self.origin.root, apart, data), ("2" * 64, "package/"))
        data["lines"][0].update(commit=first, tree="0" * 40)
        self.assertEqual(model.required_tree(self.origin.root, later, data), ("1" * 64, "toolchain/lps-core.paths"))
        with self.assertRaises(model.ModelError):
            model.required_tree(self.origin.root, "f" * 40, data)

    def test_the_data_names_the_public_model_and_the_hash_the_dockerfile_pins(self):
        data = model.load()
        self.assertEqual([l["cut"] for l in data["lines"]], ["toolchain/lps-core.paths"])
        self.assertEqual(data["other"]["cut"], "package/")

    def test_the_branches_and_tags_that_hold_a_commit(self):
        c1 = self.origin.commit({"a": "1\n"})
        self.origin.git("tag", "-a", "v1", "-m", "v1")
        c2 = self.origin.commit({"a": "2\n"})
        loose = self.origin.git("commit-tree", "-p", c2, "-m", "on no branch", c2 + "^{tree}")
        d = os.path.join(self.tmp, "fetched")
        os.makedirs(d)   # an empty directory, as a caller's scratch directory is
        model.fetch_history(self.origin.root, d)
        self.assertEqual(sorted(model.containing(d, c1)), ["heads/main", "tags/v1"])
        self.assertEqual(model.containing(d, c2), ["heads/main"])
        self.assertEqual(model.containing(d, loose), [])
        self.assertEqual(model.containing(d, "0" * 40), [])
        self.origin.git("tag", "-d", "v1")
        model.fetch_history(self.origin.root, d)
        self.assertEqual(model.containing(d, c1), ["heads/main"])

    def test_public_fetches_each_repository_once_and_a_failed_fetch_fails_every_read(self):
        c = self.origin.commit(MODEL_FILES)
        public = model.Public()
        self.addCleanup(public.close)
        self.assertEqual(public.containing(self.origin.root, c), ["heads/main"])
        self.assertEqual(public.cut_sha256(self.origin.root, c, CUT), dockerfile_hash(self.origin, c, CUT))
        self.assertEqual(public.required_tree(self.origin.root, c)[1], "package/")
        self.assertEqual(public.containing(self.origin.root, c), ["heads/main"])
        self.assertEqual(len(os.listdir(public._tmp.name)), 1)
        missing = os.path.join(self.tmp, "no-such-repository")
        for _ in range(2):
            with self.assertRaises(model.ModelError):
                public.containing(missing, c)
        self.assertEqual(len(os.listdir(public._tmp.name)), 2)
        public.close()
        self.assertIsNone(public._tmp)

    def test_a_commit_that_is_not_one_is_refused_before_git_reads_it(self):
        for bad in ("--all", "HEAD", "a" * 39, None):
            with self.subTest(bad=bad), self.assertRaises(model.ModelError):
                model.cut_sha256(self.origin.root, bad)


class ModelRule(unittest.TestCase):
    """`model`: the cut of the model at semantics.commit hashes to what toolchain/checker.Dockerfile pins, and
    model.yaml requires that hash of the commit."""

    def setUp(self):
        self.t = Tree()
        self.addCleanup(self.t.close)
        self.commit = self.t.yaml("release.yaml")["semantics"]["commit"]

    def model(self, public):
        return [str(f) for f in self.t.lint(release=True, public=public) if f.rule == "model"]

    def test_the_three_hashes_agree(self):
        public = Public()
        self.assertEqual([str(f) for f in self.t.lint(release=True, public=public)], [])
        self.assertIn(("cut_sha256", MODEL_URL, self.commit, ("dune-project", "theories", ":(exclude)theories/Common")),
                      public.read)
        self.assertIn(("required_tree", MODEL_URL, self.commit, None), public.read)
        self.assertEqual(self.t.lint(), [])

    def test_a_cut_that_is_not_the_pin(self):
        self.assertEqual(self.model(Public(cut="0b" * 32)), [
            "model toolchain/checker.Dockerfile: LPS_TREE_SHA256 is %s, the toolchain/lps-core.paths cut of "
            "semantics.commit %s hashes to %s, and tools/oft/model.yaml requires %s (the toolchain/lps-core.paths cut) "
            "of that commit: the three are one hash" % (FIXTURE_LPS_TREE, self.commit, "0b" * 32, FIXTURE_LPS_TREE)])

    def test_a_model_on_another_line(self):
        found = self.model(Public(required="0c" * 32, line="package/"))
        self.assertEqual(len(found), 1, found)
        self.assertIn("requires %s (the package/ cut)" % ("0c" * 32), found[0])

    def test_the_package_cut_without_lps_core_paths(self):
        os.remove(self.t.path("toolchain", "lps-core.paths"))
        public = Public()
        found = self.model(public)
        self.assertIn(("cut_sha256", MODEL_URL, self.commit, None), public.read)
        self.assertEqual(found, [])

    def test_a_dockerfile_that_pins_nothing(self):
        self.t.write("toolchain/checker.Dockerfile", "FROM scratch\n")
        self.assertEqual(self.model(Public()), [
            "model toolchain/checker.Dockerfile: no ARG LPS_TREE_SHA256=<sha256>: the checker image pins the hash of "
            "the model's files"])

    def test_a_model_that_cannot_be_read(self):
        class Unreadable(Public):
            def cut_sha256(self, url, commit, pathspecs):
                raise model.ModelError("%s: fatal: could not read from remote repository" % url)
        found = self.model(Unreadable())
        self.assertEqual(found, ["model release.yaml: could not read the model: %s: fatal: could not read from remote "
                                 "repository" % MODEL_URL])


class PinsRule(unittest.TestCase):
    """`pins`: each commit a release pins in another repository is on a branch or tag of its public repository."""

    def setUp(self):
        self.t = Tree()
        self.addCleanup(self.t.close)
        add_proof(self.t, "zlib/checksum_fuzzer/plain_halts")
        add_build_record(self.t)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.commit = self.t.yaml("release.yaml")["semantics"]["commit"]

    def pins(self, public):
        return [str(f) for f in self.t.lint(release=True, public=public) if f.rule == "pins"]

    def test_commits_on_a_branch_or_tag(self):
        public = Public(refs=("tags/v1",))
        self.assertEqual(self.pins(public), [])
        self.assertIn(("containing", MODEL_URL, self.commit, None), public.read)
        self.assertIn(("containing", STATIC_ASAN_URL, "b0" * 20, None), public.read)

    def test_commits_on_no_branch_or_tag(self):
        self.assertEqual(self.pins(Public(refs=())), [
            "pins release.yaml: semantics.commit %s is on no branch or tag of %s" % (self.commit, MODEL_URL),
            "pins %s: toolchain.static_asan.commit %s, which 1 build record(s) name, is on no branch or tag of %s"
            % (RECORD, "b0" * 20, STATIC_ASAN_URL)])

    def test_a_fallback_records_public_static_asan_commit(self):
        r = self.t.yaml(RECORD)
        r["fallback"] = {"static_asan": {"internal_commit": "f" * 40, "public_commit": "d0" * 20}}
        self.t.put_yaml(RECORD, r)
        public = Public()
        self.assertEqual(self.pins(public), [])
        self.assertIn(("containing", STATIC_ASAN_URL, "d0" * 20, None), public.read)
        self.assertNotIn(("containing", STATIC_ASAN_URL, "b0" * 20, None), public.read)

    def test_a_repository_that_cannot_be_read(self):
        class Unreadable(Public):
            def containing(self, url, commit):
                raise model.ModelError("%s: fatal: could not read from remote repository" % url)
        found = self.pins(Unreadable())
        self.assertEqual(found, [
            "pins release.yaml: could not read %s: fatal: could not read from remote repository" % MODEL_URL,
            "pins %s: could not read %s: fatal: could not read from remote repository" % (RECORD, STATIC_ASAN_URL)])

    def test_without_release_nothing_is_read(self):
        public = Public()
        self.t.lint(public=public)
        self.assertEqual(public.read, [])


if __name__ == "__main__":
    unittest.main()
