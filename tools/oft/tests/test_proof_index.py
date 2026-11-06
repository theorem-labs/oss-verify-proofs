"""The released-proof index's builder, .github/proof-index.py: what it reads of a branch's proofs in both layouts
(tools/oft/layout.py): a fuzz target's proofs in proofs/<p>/<h>/ and in projects/<p>/<h>/proofs/.

The builder is in the internal repository only (`oft release-tree` removes it), so these tests skip where it is not:
in a released tree, and in tools/oft alone (the runner image's copy, which runs these tests). They run its index_rows
over commits of a scratch git repository: nothing is fetched and nothing is pushed."""
import importlib.util
import os
import shutil
import subprocess
import tempfile
import unittest

from oft import layout
from oft.tests.helpers import REPO

BUILDER = os.path.join(REPO, ".github", "proof-index.py")
HAVE_BUILDER = os.path.exists(BUILDER)
NO_BUILDER = "no .github/proof-index.py: the internal repository alone has it"
TABLED = "a" * 64      # the sha256 of a released build with a symbol table
BARE = "b" * 64        # the sha256 of a released build with none, whose addresses come from the unit's contracts
TABLE_BLOB = "c" * 40  # the stand-in blob of TABLED's symbol table
HARNESS = "builds:\n  plain:\n    sha256: %s\n  asan:\n    sha256: %s\n" % (TABLED, BARE)
BRANCH = "main"


def load_builder():
    spec = importlib.util.spec_from_file_location("proof_index", BUILDER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def unit_files(root):
    """The files of one fuzz target's proofs under its proofs folder root: a statement's proof that uses an address of
    the tabled build, a Prog/ file, the asan tree's contract of foo with a file that uses its entry, and a ubsan file
    that holds the same number."""
    return {
        root + "/foo_holds/Proof.v": "Lemma foo_holds : True.\n(* foo starts at 0x1234 *)\nProof. Qed.\n",
        root + "/lib/Prog/bar.v": "Definition bar := 0.\n",
        root + "/lib/A/Prog/foo_c.v": "Definition FOO : Z := 0x4010.\n",
        root + "/lib/A/Use.v": "(* asan's foo is at 0x4010 *)\n",
        root + "/lib/U/Other.v": "(* a ubsan number that is not asan's foo: 0x4010 *)\n",
    }


@unittest.skipUnless(HAVE_BUILDER, NO_BUILDER)
class ProofIndexLayouts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.builder = load_builder()

    def setUp(self):
        self.root = tempfile.mkdtemp(prefix="proof-index-test-")
        self.addCleanup(shutil.rmtree, self.root, True)
        self.git("init", "-q")

    def git(self, *args, data=None, env=None):
        return subprocess.run(["git", "-C", self.root, *args], input=data, capture_output=True, check=True,
                              env=env).stdout.decode().strip()

    def commit(self, files):
        """A commit of exactly files ({path: text}), on no branch: index_rows takes each branch's commit."""
        index = os.path.join(self.root, "test.index")
        if os.path.exists(index):
            os.remove(index)
        env = dict(os.environ, GIT_INDEX_FILE=index, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="",
                   GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="")
        for path, text in sorted(files.items()):
            oid = self.git("hash-object", "-w", "--stdin", data=text.encode())
            self.git("update-index", "--add", "--cacheinfo", "100644,%s,%s" % (oid, path), env=env)
        return self.git("commit-tree", self.git("write-tree", env=env), "-m", "x", env=env)

    def index(self, heads):
        """(rows, coverage, {path: branches}) of index_rows over heads ({branch: commit}), TABLED's table holding foo
        at 0x1234."""
        tables = {TABLED: (TABLE_BLOB, {0x1234: ["foo"]})}
        rows, coverage, names, _read = self.builder.index_rows(self.root, heads, tables, None)
        return rows, coverage, dict(names)

    def blob(self, commit, path):
        return self.git("rev-parse", "%s:%s" % (commit, path))

    def assert_unit_indexed(self, commit, unit, root, branch=BRANCH, index=None):
        """unit, whose proofs folder is root, is in every table of the index: each Rocq file in names.tsv, its Prog/
        file by name, its proof by the tabled build's address, its asan tree by its contract's entry (and not the ubsan
        tree's same number), and its builds in coverage."""
        rows, coverage, names = index or self.index({branch: commit})
        for path in unit_files(root):
            self.assertEqual(names.get(path), branch, path)
        proof, prog, use = root + "/foo_holds/Proof.v", root + "/lib/Prog/bar.v", root + "/lib/A/Use.v"
        self.assertIn(("bar", "prog", unit, prog, branch, self.blob(commit, prog), ""), rows)
        self.assertIn(("foo", "by-address", unit, proof, branch, self.blob(commit, proof), "plain 0x1234"), rows)
        self.assertIn(("foo", "by-address", unit, use, branch, self.blob(commit, use), "asan 0x4010"), rows)
        self.assertNotIn(root + "/lib/U/Other.v", {r[3] for r in rows})
        own = {(b, sha, t[:len("contracts-")] if t.startswith("contracts-") else t)
               for u, br, b, sha, t in coverage if (u, br) == (unit, branch)}
        self.assertEqual(own, {("plain", TABLED, TABLE_BLOB), ("asan", BARE, "contracts-")})

    def test_a_new_layout_units_proof_files_are_in_names_and_its_tables(self):
        files = dict(unit_files("projects/acme/fuzz/proofs"), **{"projects/acme/fuzz/harness.yaml": HARNESS,
                                                                  "projects/acme/fuzz/Statements.v": "(* stated *)\n"})
        commit = self.commit(files)
        self.assert_unit_indexed(commit, "acme/fuzz", "projects/acme/fuzz/proofs")
        _rows, _coverage, names = self.index({BRANCH: commit})
        self.assertNotIn("projects/acme/fuzz/Statements.v", names)   # the statement folder holds no proof

    def test_an_old_layout_unit_is_indexed_as_before(self):
        files = dict(unit_files("proofs/acme/fuzz"), **{"projects/acme/fuzz/harness.yaml": HARNESS,
                                                         "proofs/lib/Common.v": "Definition common := 0.\n"})
        commit = self.commit(files)
        self.assert_unit_indexed(commit, "acme/fuzz", "proofs/acme/fuzz", branch="main")
        _rows, _coverage, names = self.index({"main": commit})
        self.assertEqual(names.get("proofs/lib/Common.v"), "main")   # the shared library of the old layout

    def test_a_branch_with_both_layouts_is_indexed_in_both(self):
        files = dict(unit_files("proofs/acme/old"), **unit_files("projects/acme/new/proofs"))
        files.update({"projects/acme/old/harness.yaml": HARNESS, "projects/acme/new/harness.yaml": HARNESS})
        commit = self.commit(files)
        index = self.index({BRANCH: commit})
        self.assert_unit_indexed(commit, "acme/old", "proofs/acme/old", index=index)
        self.assert_unit_indexed(commit, "acme/new", "projects/acme/new/proofs", index=index)

    def test_a_new_layout_contract_gives_its_builds_addresses(self):
        root = "projects/acme/fuzz/proofs"
        commit = self.commit({"projects/acme/fuzz/harness.yaml": HARNESS,
                              root + "/lib/A/Prog/foo_c.v": "Definition FOO : Z := 0x4010.\n",
                              root + "/lib/A/Use.v": "(* 0x4010 *)\n",
                              root + "/lib/U/Other.v": "(* 0x4010 *)\n"})
        rows, coverage, _names = self.index({BRANCH: commit})
        self.assertEqual(sorted((r[0], r[3], r[6]) for r in rows if r[1] == "by-address"),
                         [("foo", root + "/lib/A/Prog/foo_c.v", "asan 0x4010"),
                          ("foo", root + "/lib/A/Use.v", "asan 0x4010")])
        self.assertIn("contracts-", {t[:len("contracts-")] for u, _b, build, _s, t in coverage
                                     if (u, build) == ("acme/fuzz", "asan")})

    def test_a_prog_file_is_one_of_the_proof_library_whatever_the_unit_is_called(self):
        """A file's kind is read from its place in its proofs folder: a harness named lib holds no proof library above
        its proofs, so a Prog/ directory of one of its statements is not one."""
        for root in ("proofs/acme/lib", "projects/acme/lib/proofs"):
            with self.subTest(root=root):
                commit = self.commit({root + "/stmt/Prog/x.v": "Definition x := 0.\n",
                                      root + "/lib/Prog/y.v": "Definition y := 0.\n"})
                rows, _coverage, _names = self.index({BRANCH: commit})
                self.assertEqual(sorted((r[0], r[1], r[3]) for r in rows),
                                 [("y", "prog", root + "/lib/Prog/y.v")])


SHA = "f" * 64          # the sha256 of the stand-in build every fuzz target below names
ENTRY = 0x1234          # the address that build's table gives the function `foo`


def repository(d, files):
    """A git repository in d with one commit of files ({path: text}): that commit."""
    env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@x", GIT_COMMITTER_NAME="t",
               GIT_COMMITTER_EMAIL="t@x", GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")
    for rel, text in files.items():
        os.makedirs(os.path.dirname(os.path.join(d, rel)), exist_ok=True)
        with open(os.path.join(d, rel), "w") as f:
            f.write(text)
    for args in (["init", "-q"], ["add", "-A"], ["commit", "-qm", "t"]):
        subprocess.run(["git", "-C", d] + args, check=True, env=env, capture_output=True)
    return subprocess.run(["git", "-C", d, "rev-parse", "HEAD"], check=True, env=env, capture_output=True,
                          text=True).stdout.strip()


def harness_yaml():
    return "builds:\n  plain:\n    sha256: %s\n" % SHA


@unittest.skipUnless(HAVE_BUILDER, NO_BUILDER)
class ProofIndex(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.pi = load_builder()

    def contract(self, path):
        """(unit, X, fn) of the contract file at path, as index_rows reads one: CONTRACT_FILE on the file's place
        inside its unit's proofs folder (proof_place). None for a path that is no contract file."""
        place = self.pi.proof_place(path)
        m = place and self.pi.CONTRACT_FILE.fullmatch("/".join(place[1]))
        return (place[0],) + m.groups() if m else None

    def test_it_reads_the_four_branches_its_readers_pin(self):
        """The OSS Verify stream's proof-index tool pins the branches the index reads and calls the index stale when
        its heads name others, so the list changes only together with that reader.  ossv/recipes joined main
        and is not read: archive/main-before-join, main's tip before that join, takes its place, for the
        proofs no other branch has."""
        self.assertEqual(self.pi.BRANCHES,
                         ("main", "archive/main-before-join", "ossv/candidates", "release/pau-projects-recipes"))
        self.assertNotIn("ossv/recipes", self.pi.BRANCHES)

    def test_a_per_project_contract_file_is_matched(self):
        self.assertEqual(self.contract("projects/libreac/fuzz_grant/proofs/lib/A/Prog/x/foo_c.v"),
                         ("libreac/fuzz_grant", "A", "foo"))
        self.assertEqual(self.contract("projects/libreac/fuzz_grant/proofs/lib/Prog/foo_c.v"),
                         ("libreac/fuzz_grant", None, "foo"))

    def test_the_old_contract_file_form_still_matches(self):
        self.assertEqual(self.contract("proofs/libreac/fuzz_grant/lib/Prog/foo_c.v"),
                         ("libreac/fuzz_grant", None, "foo"))
        self.assertEqual(self.contract("proofs/libreac/fuzz_grant/lib/U/Prog/x/y/foo_c.v"),
                         ("libreac/fuzz_grant", "U", "foo"))

    def test_no_other_path_is_a_contract_file(self):
        for path in ("projects/libreac/fuzz_grant/lib/Prog/foo_c.v",          # the statement folder, not proofs/
                     "proofs/libreac/fuzz_grant/proofs/lib/Prog/foo_c.v",     # proofs/ twice
                     "projects/libreac/fuzz_grant/proofs/s/lib/Prog/foo_c.v",  # a statement's folder
                     "projects/libreac/proofs/lib/Prog/foo_c.v"):
            self.assertIsNone(self.contract(path), path)

    def test_the_proofs_folder_of_either_layout_is_the_one_layout_py_names(self):
        """proof_place reads a path as layout.py lays the proofs folder out, in both layouts."""
        for lay in (layout.OLD, layout.NEW):
            folder = layout.proofs_dir("zlib", "checksum_fuzzer", lay)
            self.assertEqual(self.pi.proof_place(folder + "/lib/U/A.v"), ("zlib/checksum_fuzzer", ["lib", "U", "A.v"]))
            self.assertEqual(self.pi.library_build(folder + "/lib/U/A.v", set()), "ubsan")
            self.assertEqual(self.pi.library_build(folder + "/plain_halts/Proof.v", set()), "plain")
        for path in ("proofs/lib/Common.v", "projects/zlib/checksum_fuzzer/Statements.v",
                     "projects/zlib/checksum_fuzzer/counterexamples/s/x.v", "projects/zlib/project.yaml"):
            self.assertIsNone(self.pi.proof_place(path), path)

    def test_a_per_project_proof_file_is_scanned_under_its_unit(self):
        """A tree with one fuzz target in each layout: both units' proof files are searched by address, with the
        unit's build's symbol table, and both are listed in names.tsv."""
        files = {}
        for unit, lay in (("zlib/checksum_fuzzer", layout.OLD), ("libreac/fuzz_grant", layout.NEW)):
            p, h = unit.split("/")
            files["projects/%s/%s/harness.yaml" % (p, h)] = harness_yaml()
            files[layout.proofs_dir(p, h, lay) + "/plain_halts/Proof.v"] = "Definition at := 0x%x.\n" % ENTRY
        with tempfile.TemporaryDirectory() as d:
            head = repository(d, files)
            rows, coverage, names, _read = self.pi.index_rows(d, {"main": head}, {SHA: ("table", {ENTRY: ["foo"]})},
                                                              None)
        by_address = sorted((r[2], r[3]) for r in rows if r[1] == "by-address" and r[0] == "foo")
        self.assertEqual(by_address, [("libreac/fuzz_grant", "projects/libreac/fuzz_grant/proofs/plain_halts/Proof.v"),
                                      ("zlib/checksum_fuzzer", "proofs/zlib/checksum_fuzzer/plain_halts/Proof.v")])
        self.assertEqual(sorted(c[0] for c in coverage), ["libreac/fuzz_grant", "zlib/checksum_fuzzer"])
        self.assertEqual(names, [("projects/libreac/fuzz_grant/proofs/plain_halts/Proof.v", "main"),
                                 ("proofs/zlib/checksum_fuzzer/plain_halts/Proof.v", "main")])

    def test_a_per_project_contract_gives_its_build_s_addresses(self):
        """A build with no symbol table: the unit's contracts, in the per-project layout, give the entry of each
        function, matched in the files of that build alone."""
        p, h = "libreac", "fuzz_grant"
        folder = layout.proofs_dir(p, h, layout.NEW)
        files = {"projects/%s/%s/harness.yaml" % (p, h): harness_yaml(),
                 folder + "/lib/Prog/foo_c.v": "Definition FOO : Z := 0x%x.\n" % ENTRY,
                 folder + "/plain_halts/Proof.v": "Definition at := 0x%x.\n" % ENTRY}
        with tempfile.TemporaryDirectory() as d:
            head = repository(d, files)
            rows, coverage, _names, _read = self.pi.index_rows(d, {"main": head}, {}, None)
        self.assertIn(("foo", "by-address", "%s/%s" % (p, h), folder + "/plain_halts/Proof.v", "main"),
                      {r[:5] for r in rows})
        self.assertEqual([c[4].startswith(self.pi.CONTRACTS) for c in coverage], [True])


if __name__ == "__main__":
    unittest.main()
