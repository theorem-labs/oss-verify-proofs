"""port.py: `oft port-layout` moves every file of an old-layout tree to the per-project layout, by prefix, or refuses
the tree whole and moves nothing; in commit mode it gives the tree the working tree gives.  `oft port-branch` ports an
old-layout branch onto a layout commit in a worktree, checks that its change is the same after the move, and pushes
nothing.  tools/oft/ci/port-check.sh ports, renders and lints a tree, then checks it as CI's check job does."""
import contextlib
import io
import os
import shlex
import shutil
import subprocess
import tempfile
import unittest
from unittest import mock

from oft import __main__ as oft_main
from oft import facts, generate, layout, nsrename, paths, port
from oft.tests import helpers, test_nsrename
from oft.tests.test_fetch_check import HAVE_ZSTD, make_release

OFT = os.path.dirname(os.path.abspath(port.__file__))   # tools/oft
PORT_CHECK = os.path.join(OFT, "ci", "port-check.sh")

UNIT_PROOFS = "proofs/zlib/checksum_fuzzer"

# `oft generate --help` of tools before #416, and of #416's (ci/shared-generated-files at bb23bbbb9a5)
HELP_BEFORE_416 = ("usage: oft generate [-h] [--check]\n\noptions:\n"
                   "  -h, --help  show this help message and exit\n"
                   "  --check     compare instead of writing\n")
HELP_416 = ("usage: oft generate [-h] [--check] [--skip-shared | --shared-only]\n\noptions:\n"
            "  -h, --help     show this help message and exit\n"
            "  --check        compare instead of writing\n"
            "  --skip-shared  leave the shared generated files (tools/oft/paths.py SHARED)\n"
            "                 to the line's render\n"
            "  --shared-only  render the shared generated files alone, as the line's render\n"
            "                 after a merge does\n")


def proof(t, sid, body="Theorem holds : True. Proof. exact I. Qed.\n"):
    """Write a proof of statement sid in the old layout: Proof.v and a proof.yaml with the statement's fingerprint."""
    st = next(s for s in facts.load(t.root).statements() if s.id == sid)
    t.put_yaml("proofs/%s/proof.yaml" % sid, {
        "schema": "oss-fuzz-theorems/proof/1", "proves": sid, "fingerprint": st.fingerprint})
    t.write("proofs/%s/Proof.v" % sid, body)


def old_layout(t):
    """t with an old-layout file of each kind: the fixture's counterexample, the findings laid in (a finding, its series
    and the project's unpatched.yaml), a proof, a proof library file, a build record and a patch."""
    helpers.add_findings(t)
    proof(t, "zlib/checksum_fuzzer/plain_halts")
    t.write(UNIT_PROOFS + "/lib/A.v", "Definition a := 0.\n")
    t.write(UNIT_PROOFS + "/provenance/PROVENANCE.yaml", helpers.build_record())
    t.write("patches/zlib/0001-x.patch", "a stand-in patch\n")


def port_worktree(t):
    """(the exit status of port-layout on t, what it printed)."""
    out = io.StringIO()
    rc = port.port_worktree(t.root, out=out)
    return rc, out.getvalue()


class GitTests(unittest.TestCase):
    """Every git the tools start reads no global or system configuration."""

    def setUp(self):
        env = mock.patch.dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")
        env.start()
        self.addCleanup(env.stop)


class PortLayout(GitTests):
    def test_it_moves_every_old_layout_file_and_a_second_run_does_nothing(self):
        with helpers.tree() as t:
            old_layout(t)
            before = t.files()
            rc, out = port_worktree(t)
            self.assertEqual(rc, 0, out)
            self.assertEqual(sorted(layout.canonical(f) for f in before), t.files())
            self.assertIn("projects/zlib/unpatched.yaml", t.files())
            self.assertIn("projects/zlib/patches/0001-x.patch", t.files())
            self.assertIn("projects/zlib/checksum_fuzzer/findings/stand-in-abort/input.bin", t.files())
            self.assertIn("projects/json/fuzzer-parse_bjdata/counterexamples/plain_halts/expect.yaml", t.files())
            moved = sum(1 for f in before if layout.moved(f))
            self.assertEqual(out, "oft port-layout: %d file(s) moved; now run ./oft generate\n" % moved)
            # the old folders are gone, not left empty
            self.assertEqual([top for top in layout.OLD_TOPS if os.path.lexists(t.path(top))], [])
            rc, out = port_worktree(t)
            self.assertEqual((rc, out), (0, "oft port-layout: 0 file(s) moved\n"))

    def test_lib_lean_is_refused_by_name_and_nothing_moves(self):
        with helpers.tree() as t:
            old_layout(t)
            t.write("proofs/lib-lean/A.lean", "def a := 0\n")
            # four segments and more look like proofs/<project>/<harness>/<file>: still refused by name
            t.write("proofs/lib-lean/Mcsl/Core/Defs.lean", "def b := 0\n")
            before = t.files()
            rc, out = port_worktree(t)
            self.assertEqual(rc, 1, out)
            self.assertEqual(out, "refused proofs/lib-lean/A.lean: proofs/lib-lean/ has no place in the per-project "
                                  "layout\nrefused proofs/lib-lean/Mcsl/Core/Defs.lean: proofs/lib-lean/ has no place "
                                  "in the per-project layout\noft port-layout: 2 file(s) refused; nothing moved\n")
            self.assertEqual(t.files(), before)

    def test_a_stray_file_moves_with_its_folder(self):
        with helpers.tree() as t:
            old_layout(t)
            t.write(UNIT_PROOFS + "/lib/A.v.wip", "Definition a := 1.\n")
            rc, out = port_worktree(t)
            self.assertEqual(rc, 0, out)
            self.assertIn("projects/zlib/checksum_fuzzer/proofs/lib/A.v.wip", t.files())
            self.assertIn("projects/zlib/checksum_fuzzer/proofs/lib/A.v", t.files())

    def test_a_file_directly_under_proofs_is_refused_and_nothing_moves(self):
        with helpers.tree() as t:
            old_layout(t)
            t.write("proofs/zlib/notes.md", "notes\n")
            t.write("proofs/lib/X.v", "Definition x := 0.\n")
            before = t.files()
            rc, out = port_worktree(t)
            self.assertEqual(rc, 1, out)
            why = ("it has no place in the per-project layout (only proofs/<project>/<harness>/, "
                   "counterexamples/<project>/<harness>/, findings/<project>/ and patches/<project>/ move)")
            self.assertEqual(out, "refused proofs/lib/X.v: %s\nrefused proofs/zlib/notes.md: %s\n"
                                  "oft port-layout: 2 file(s) refused; nothing moved\n" % (why, why))
            self.assertEqual(t.files(), before)

    def test_a_target_with_other_content_is_refused(self):
        with helpers.tree() as t:
            old_layout(t)
            t.write("projects/zlib/checksum_fuzzer/proofs/lib/A.v", "Definition a := 2.\n")
            # the same bytes in both places is no clash: the move leaves one
            same = t.read(UNIT_PROOFS + "/plain_halts/proof.yaml")
            t.write("projects/zlib/checksum_fuzzer/proofs/plain_halts/proof.yaml", same)
            before = t.files()
            rc, out = port_worktree(t)
            self.assertEqual(rc, 1, out)
            self.assertEqual(out, "refused %s/lib/A.v: projects/zlib/checksum_fuzzer/proofs/lib/A.v is already there "
                                  "with other content\noft port-layout: 1 file(s) refused; nothing moved\n"
                             % UNIT_PROOFS)
            self.assertEqual(t.files(), before)
            os.remove(t.path("projects/zlib/checksum_fuzzer/proofs/lib/A.v"))
            rc, out = port_worktree(t)
            self.assertEqual(rc, 0, out)
            self.assertEqual(t.read("projects/zlib/checksum_fuzzer/proofs/plain_halts/proof.yaml"), same)

    def test_a_target_in_a_folder_that_is_a_file_is_refused(self):
        with helpers.tree() as t:
            old_layout(t)
            t.write("projects/zlib/checksum_fuzzer/proofs/lib", "a file where the library folder goes\n")
            before = t.files()
            rc, out = port_worktree(t)
            self.assertEqual(rc, 1, out)
            self.assertIn("refused %s/lib/A.v: projects/zlib/checksum_fuzzer/proofs/lib is already there with other "
                          "content\n" % UNIT_PROOFS, out)
            self.assertEqual(t.files(), before)

    def test_a_symbolic_link_is_refused(self):
        with helpers.tree() as t:
            old_layout(t)
            os.symlink("A.v", t.path(UNIT_PROOFS + "/lib/B.v"))
            os.symlink("lib", t.path(UNIT_PROOFS + "/lib2"))
            before = t.files()
            rc, out = port_worktree(t)
            self.assertEqual(rc, 1, out)
            self.assertEqual(out, "refused %s/lib/B.v: a symbolic link\nrefused %s/lib2: a symbolic link\n"
                                  "oft port-layout: 2 file(s) refused; nothing moved\n" % (UNIT_PROOFS, UNIT_PROOFS))
            self.assertEqual(t.files(), before)

    def test_a_top_folder_that_is_a_symbolic_link_is_refused(self):
        """A proofs/ that links elsewhere is refused, not followed: nothing moves out of where it points."""
        with helpers.tree() as t, tempfile.TemporaryDirectory() as elsewhere:
            old_layout(t)
            shutil.move(t.path("proofs"), os.path.join(elsewhere, "proofs"))
            os.symlink(os.path.join(elsewhere, "proofs"), t.path("proofs"))
            there = sorted(os.path.relpath(os.path.join(dp, f), elsewhere)
                           for dp, _, fns in os.walk(elsewhere) for f in fns)
            rc, out = port_worktree(t)
            self.assertEqual(rc, 1, out)
            self.assertIn("refused proofs: a symbolic link\n", out)
            self.assertEqual(sorted(os.path.relpath(os.path.join(dp, f), elsewhere)
                                    for dp, _, fns in os.walk(elsewhere) for f in fns), there)

    def test_what_git_never_tracks_stays_where_it_is(self):
        """A build's _build/ and the unpatched binaries an old `oft fetch --findings` unpacked are neither judged nor
        moved."""
        with helpers.tree() as t:
            old_layout(t)
            t.write(UNIT_PROOFS + "/plain_halts/_build/default/Proof.vo", "built\n")
            t.write("findings/zlib/bin/checksum_fuzzer", "a binary\n")
            rc, out = port_worktree(t)
            self.assertEqual(rc, 0, out)
            self.assertTrue(os.path.isfile(t.path(UNIT_PROOFS + "/plain_halts/_build/default/Proof.vo")))
            self.assertTrue(os.path.isfile(t.path("findings/zlib/bin/checksum_fuzzer")))
            self.assertIn("projects/zlib/unpatched.yaml", t.files())

    def test_a_dry_run_moves_nothing(self):
        with helpers.tree() as t:
            old_layout(t)
            before = t.files()
            out = io.StringIO()
            self.assertEqual(port.port_worktree(t.root, dry_run=True, out=out), 0)
            self.assertIn("patches/zlib/0001-x.patch -> projects/zlib/patches/0001-x.patch\n", out.getvalue())
            self.assertTrue(out.getvalue().endswith(
                "oft port-layout: %d file(s) to move; nothing moved (dry run)\n"
                % sum(1 for f in before if layout.moved(f))))
            self.assertEqual(t.files(), before)

    def test_commit_mode_gives_the_tree_the_worktree_gives(self):
        with helpers.tree() as t:
            old_layout(t)
            t.write(UNIT_PROOFS + "/lib/A.v.wip", "Definition a := 1.\n")
            head = helpers.git_repo(t.root)
            ported = port.port_commit(t.root, head)
            self.assertEqual(port_worktree(t)[0], 0)
            helpers.git(t.root, "add", "-A")
            self.assertEqual(ported, helpers.git(t.root, "write-tree"))
            # the working tree, ported, and committed: nothing more moves
            self.assertEqual(port.port_commit(t.root, helpers.git_commit(t.root)), ported)

    def test_both_modes_keep_an_executable_files_mode(self):
        """ossv/recipes holds 88 executable files under proofs/ (build scripts of build records): each keeps 100755 in
        the ported tree, in commit mode and in the working tree."""
        script = UNIT_PROOFS + "/provenance/recipe/build.sh"
        with helpers.tree() as t:
            old_layout(t)
            t.write(script, "#!/bin/sh\nexit 0\n")
            os.chmod(t.path(script), 0o755)
            head = helpers.git_repo(t.root)
            ported = port.port_commit(t.root, head)
            entry = helpers.git(t.root, "ls-tree", ported, "--", layout.moved(script))
            self.assertTrue(entry.startswith("100755 blob "), entry)
            self.assertEqual(helpers.git(t.root, "ls-tree", ported, "--", layout.moved(UNIT_PROOFS + "/lib/A.v"))[:6],
                             "100644")
            self.assertEqual(port_worktree(t)[0], 0)
            self.assertTrue(os.access(t.path(layout.moved(script)), os.X_OK))
            helpers.git(t.root, "add", "-A")
            self.assertEqual(ported, helpers.git(t.root, "write-tree"))

    def test_commit_mode_refuses_a_symbolic_link_and_a_target_with_another_object_id(self):
        with helpers.tree() as t:
            old_layout(t)
            os.symlink("A.v", t.path(UNIT_PROOFS + "/lib/B.v"))
            t.write("projects/zlib/unpatched.yaml", "other\n")
            t.write("proofs/lib-lean/A.lean", "def a := 0\n")
            head = helpers.git_repo(t.root)
            with self.assertRaises(port.PortError) as e:
                port.port_commit(t.root, head)
            self.assertEqual(e.exception.refused, [
                ("findings/zlib/unpatched.yaml", "projects/zlib/unpatched.yaml is already there with other content"),
                ("proofs/lib-lean/A.lean", "proofs/lib-lean/ has no place in the per-project layout"),
                (UNIT_PROOFS + "/lib/B.v", "a symbolic link")])
            self.assertEqual(port_worktree(t)[1].splitlines()[:3], str(e.exception).splitlines())

    def test_the_command(self):
        """`./oft port-layout --commit REV` prints the ported tree; `./oft port-layout` moves the files of --root."""
        with helpers.tree() as t:
            old_layout(t)
            head = helpers.git_repo(t.root)
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertEqual(oft_main.main(["--root", t.root, "port-layout", "--commit", head]), 0)
            self.assertEqual(out.getvalue(), port.port_commit(t.root, head) + "\n")
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertEqual(oft_main.main(["--root", t.root, "port-layout"]), 0)
            self.assertIn("file(s) moved; now run ./oft generate\n", out.getvalue())
            self.assertIn("projects/zlib/patches/0001-x.patch", t.files())


class PortBranch(GitTests):
    """A repository whose base, main, is in the old layout (base0, rendered), with a branch recipes that is the layout
    commit LC's per-project base, and branches made from base0 as contributors made them.  The repository holds these
    tools (tools/oft, less their tests), as every branch does: step 4 renders with the branch's own tools."""

    def setUp(self):
        super().setUp()
        self.t = helpers.Tree()
        self.addCleanup(self.t.close)
        old_layout(self.t)
        shutil.copytree(OFT, self.t.path("tools", "oft"), ignore=shutil.ignore_patterns("tests", "__pycache__"))
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.base0 = helpers.git_repo(self.t.root)
        self.dir = os.path.join(os.path.dirname(self.t.root), "port")

    def git(self, *args, where=None, input=None):
        return helpers.git(where or self.t.root, *args, input=input)

    def commit(self, branch, start, files=None, delete=()):
        """A commit on branch, made from start with files (path: text) written and delete removed; the commit."""
        self.git("checkout", "-q", "-B", branch, start)
        for rel, text in (files or {}).items():
            self.t.write(rel, text)
        for rel in delete:
            os.remove(self.t.path(rel))
        return helpers.git_commit(self.t.root, "a change on " + branch)

    def move(self, lp):
        """The layout commit: lp's tree ported, its parent lp; branch recipes is it."""
        lc = self.git("commit-tree", port.port_commit(self.t.root, lp), "-p", lp, "-m", "oft port-layout")
        self.git("branch", "-f", "recipes", lc)
        return lc

    def port(self, branch, lc):
        """(the exit status of port-branch, what it printed), onto recipes, in self.dir."""
        out = io.StringIO()
        rc = port.port_branch(self.t.root, branch, self.dir, layout_commit=lc, onto="recipes", out=out)
        return rc, out.getvalue()

    def head(self):
        return self.git("rev-parse", "HEAD", where=self.dir)

    def changes(self, a, b):
        """The lines of `git diff --name-status a b`, as a set."""
        return set(self.git("diff", "--no-renames", "--name-status", a, b).splitlines())

    def files(self, commit):
        return self.git("ls-tree", "-r", "--name-only", commit).splitlines()

    def assert_rendered(self, onto):
        """The port's generated files are current as its own tools check them, the way a pull request's CI does: with
        --skip-shared when those tools take it (port.offers_skip_shared, as step 4 reads it).  Then step 4 gave each
        shared generated file onto's bytes (or removed it where onto has none): the line renders them after a merge,
        so here they are onto's, not their render, and a full check would report them."""
        skip = port.offers_skip_shared(self.dir)
        self.assertEqual(generate.run(self.dir, check=True, out=io.StringIO(), shared=False if skip else None), 0)
        if skip:
            final = self.head()
            self.assertTrue(paths.is_shared("README.md") and "README.md" in self.files(final))
            self.assertEqual([row for row in sorted(self.changes(onto, final))
                              if paths.is_shared(row.split("\t", 1)[1])], [])

    def test_a_branch_with_a_new_proof_ports_and_its_change_is_the_same_after_moving(self):
        lp = self.commit("main", self.base0, {"notes/zlib.md": "zlib, as the base has it now\n"})
        lc = self.move(lp)
        self.commit("recipes", lc, {"notes/json.md": "json, on the per-project base\n"})
        self.git("checkout", "-q", "-B", "proofs/new", self.base0)
        proof(self.t, "zlib/checksum_fuzzer/ubsan_halts")
        tip = self.commit("proofs/new", "HEAD", {UNIT_PROOFS + "/lib/A.v": "Definition a := 1.\n"},
                          delete=["patches/zlib/0001-x.patch"])
        rc, out = self.port("proofs/new", lc)
        self.assertEqual(rc, 0, out)
        final = self.head()
        self.assertLessEqual({"A\tprojects/zlib/checksum_fuzzer/proofs/ubsan_halts/Proof.v",
                              "A\tprojects/zlib/checksum_fuzzer/proofs/ubsan_halts/proof.yaml",
                              "M\tprojects/zlib/checksum_fuzzer/proofs/lib/A.v",
                              "D\tprojects/zlib/patches/0001-x.patch",
                              "A\tnotes/json.md"}, self.changes(lc, final))
        self.assertEqual([f for f in self.files(final) if f.split("/")[0] in layout.OLD_TOPS], [])
        # the base the branch lacked is merged, and the branch's history is kept: final is a fast-forward of it
        self.assertEqual(self.git("show", final + ":notes/zlib.md"), "zlib, as the base has it now")
        self.git("merge-base", "--is-ancestor", tip, final)
        # the port commit's parents: the branch with the base merged, and the layout commit
        c = self.git("log", "--format=%H", "--grep=^oft port-branch: proofs/new onto the per-project layout", final)
        b1, second = self.git("show", "-s", "--format=%P", c).split()
        self.assertEqual(second, lc)
        self.assertEqual(self.git("rev-parse", b1 + "^1"), tip)
        self.assertEqual(self.git("rev-parse", b1 + "^2"), lp)

    def test_a_branch_that_holds_the_layout_commit_moves_the_old_layout_paths_it_still_has(self):
        """Its owner merged the per-project base into the old-layout branch, and the branch still adds a file in the
        old layout (a folder git's rename detection did not move): port-branch moves it, and no old-layout path is
        left (pre-push review of L1)."""
        lp = self.commit("main", self.base0, {"notes/zlib.md": "zlib, as the base has it now\n"})
        lc = self.move(lp)
        self.commit("proofs/merged", lc, {UNIT_PROOFS + "/lib/B.v": "Definition b := 1.\n"})
        rc, out = self.port("proofs/merged", lc)
        self.assertEqual(rc, 0, out)
        final = self.head()
        self.assertEqual([f for f in self.files(final) if f.split("/")[0] in layout.OLD_TOPS], [])
        self.assertIn(layout.moved(UNIT_PROOFS + "/lib/B.v"), self.files(final))
        self.assert_rendered("recipes")

    def test_generated_conflicts_are_rendered_again(self):
        """A conflict in a generated file takes onto's side and is rendered again: the proof library's lib/dune (not a
        shared file) ends as its render; README.md, a shared file, ends as onto's bytes, and so does index/STATUS.md,
        a shared file only the branch changed (review of #448: each fails with the restore or the merge broken)."""
        lp = self.commit("main", self.base0, {"README.md": "the base's README\n",
                                              UNIT_PROOFS + "/lib/dune": "the base's dune\n"})
        lc = self.move(lp)
        self.commit("proofs/readme", self.base0, {"README.md": "the branch's README\n",
                                                  "index/STATUS.md": "the branch's own render\n",
                                                  UNIT_PROOFS + "/lib/dune": "the branch's dune\n",
                                                  UNIT_PROOFS + "/lib/A.v": "Definition a := 1.\n"})
        rc, out = self.port("proofs/readme", lc)
        self.assertEqual(rc, 0, out)
        self.assert_rendered("recipes")
        self.assertEqual(self.git("status", "--porcelain", where=self.dir), "")
        self.assertIn("oft generate after port-branch", self.git("log", "-1", "--format=%s", where=self.dir))

    def test_a_hand_conflict_stops_with_exit_2(self):
        lp = self.commit("main", self.base0, {"notes/zlib.md": "the base's notes\n"})
        lc = self.move(lp)
        self.commit("proofs/notes", self.base0, {"notes/zlib.md": "the branch's notes\n"})
        rc, out = self.port("proofs/notes", lc)
        self.assertEqual(rc, 2, out)
        self.assertIn("\n  notes/zlib.md\n", out)
        self.assertIn("\n  git -C %s commit --no-edit && ./oft port-branch proofs/notes --layout-commit %s --worktree %s "
                      "--onto recipes\n" % (self.dir, lc, self.dir), out)
        # its owner resolves the conflict and runs the command printed: the port goes on from there
        with open(os.path.join(self.dir, "notes/zlib.md"), "w") as f:
            f.write("both sides' notes\n")
        self.git("add", "notes/zlib.md", where=self.dir)
        self.git("commit", "-q", "--no-edit", where=self.dir)
        rc, out = self.port("proofs/notes", lc)
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.git("show", self.head() + ":notes/zlib.md"), "both sides' notes")

    def test_a_worktree_it_cannot_go_on_in_is_refused(self):
        """DIR exists: a folder that is no worktree of the repository, or one left with a conflict not committed (here
        with a bare repository as the root), is refused with 1 and nothing more happens."""
        lp = self.commit("main", self.base0, {"notes/zlib.md": "the base's notes\n"})
        lc = self.move(lp)
        self.commit("proofs/notes", self.base0, {"notes/zlib.md": "the branch's notes\n"})
        os.makedirs(self.dir)
        with open(os.path.join(self.dir, "a-file"), "w") as f:
            f.write("something\n")
        rc, out = self.port("proofs/notes", lc)
        self.assertEqual((rc, out), (1, "oft port-branch: %s exists and is not a worktree of this repository\n"
                                     % self.dir))
        bare = os.path.join(os.path.dirname(self.t.root), "bare.git")
        self.git("clone", "-q", "--bare", self.t.root, bare)
        for key, value in helpers.TEST_GIT_CONFIG:
            self.git("config", key, value, where=bare)
        self.dir = os.path.join(os.path.dirname(self.t.root), "port-of-bare")
        out = io.StringIO()
        self.assertEqual(port.port_branch(bare, "proofs/notes", self.dir, layout_commit=lc, onto="recipes", out=out), 2,
                         out.getvalue())
        out = io.StringIO()
        self.assertEqual(port.port_branch(bare, "proofs/notes", self.dir, layout_commit=lc, onto="recipes", out=out), 1,
                         out.getvalue())
        self.assertEqual(out.getvalue(), "oft port-branch: %s has changes that are not committed: commit them, then "
                                         "run this again\n" % self.dir)

    def test_a_path_with_no_place_stops_with_exit_3(self):
        lc = self.move(self.base0)
        self.commit("proofs/lean", self.base0, {"proofs/lib-lean/A.lean": "def a := 0\n"})
        rc, out = self.port("proofs/lean", lc)
        self.assertEqual(rc, 3, out)
        self.assertIn("refused proofs/lib-lean/A.lean: proofs/lib-lean/ has no place in the per-project layout\n", out)

    def test_a_stray_file_travels_with_its_folder(self):
        lc = self.move(self.base0)
        self.commit("proofs/wip", self.base0, {UNIT_PROOFS + "/lib/B.v.wip": "Definition b := 0.\n"})
        rc, out = self.port("proofs/wip", lc)
        self.assertEqual(rc, 0, out)
        self.assertIn("projects/zlib/checksum_fuzzer/proofs/lib/B.v.wip", self.files(self.head()))

    def test_a_change_to_a_file_that_does_not_move_is_the_same_after_the_port(self):
        lc = self.move(self.base0)
        self.commit("proofs/docs", self.base0, {"notes/zlib.md": "notes the branch wrote\n",
                                                "tools/oft/README.md": "a file of the tools\n",
                                                UNIT_PROOFS + "/lib/A.v": "Definition a := 1.\n"})
        rc, out = self.port("proofs/docs", lc)
        self.assertEqual(rc, 0, out)
        self.assertLessEqual({"M\tnotes/zlib.md", "M\ttools/oft/README.md",
                              "M\tprojects/zlib/checksum_fuzzer/proofs/lib/A.v"}, self.changes(lc, self.head()))

    def test_it_pushes_nothing(self):
        """The branch is only on origin; afterwards no ref of the repository or of origin has moved, DIR holds the
        port, and the commands that would push it and tell the pull request are printed.  The push turns off git's
        sparse object walk (pack.useSparse=false): with it, a push of a commit on top of the move sends every moved
        file again (measured on the real tree: a 2.41 GB pack against 462 KB; GitHub refuses a push over 2 GB).  Run
        as printed, the push is a fast-forward of the branch to the port."""
        origin = os.path.join(os.path.dirname(self.t.root), "origin.git")
        self.git("init", "-q", "--bare", origin)
        self.git("remote", "add", "origin", origin)
        lc = self.move(self.base0)
        self.git("checkout", "-q", "--detach", self.base0)
        self.t.write(UNIT_PROOFS + "/lib/A.v", "Definition a := 1.\n")
        tip = helpers.git_commit(self.t.root, "a proof library change")
        self.git("push", "-q", "origin", "main", "recipes", "HEAD:refs/heads/proofs/only-there")
        self.git("fetch", "-q", "origin")
        refs = (self.git("for-each-ref"), self.git("for-each-ref", where=origin))
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            rc = oft_main.main(["--root", self.t.root, "port-branch", "proofs/only-there", "--layout-commit", lc,
                                "--worktree", self.dir, "--onto", "recipes"])
        self.assertEqual(rc, 0, out.getvalue())
        self.assertEqual((self.git("for-each-ref"), self.git("for-each-ref", where=origin)), refs)
        final = self.head()
        self.assertNotEqual(final, tip)
        push = "git -c pack.useSparse=false push origin %s:refs/heads/proofs/only-there" % final
        self.assertIn("\n  %s\n" % push, out.getvalue())
        self.assertIn("\n  gh pr comment proofs/only-there --body 'Ported to the per-project layout by oft port-branch: "
                      "%s'\n" % final, out.getvalue())
        subprocess.run(shlex.split(push), cwd=self.dir, check=True, capture_output=True)
        self.assertEqual(self.git("rev-parse", "refs/heads/proofs/only-there", where=origin), final)

    def test_a_layout_commit_that_is_not_a_pure_port_is_refused(self):
        self.move(self.base0)
        not_a_port = self.git("commit-tree", self.base0 + "^{tree}", "-p", self.base0, "-m", "no move")
        self.commit("proofs/x", self.base0, {UNIT_PROOFS + "/lib/A.v": "Definition a := 1.\n"})
        rc, out = self.port("proofs/x", not_a_port)
        self.assertEqual(rc, 1, out)
        self.assertIn("%s is not a pure port of its first parent" % not_a_port, out)
        self.assertFalse(os.path.exists(self.dir))

    def test_a_port_that_loses_a_change_stops_with_exit_4(self):
        """Step 3: the port commit must change the layout commit as the branch changed its first parent, every path
        moved.  A port that dropped one of the branch's files (here port_commit made to lose the new library file) is
        caught, and nothing goes on to the merge."""
        lc = self.move(self.base0)
        new = UNIT_PROOFS + "/lib/B.v"
        tip = self.commit("proofs/lossy", self.base0, {new: "Definition b := 1.\n"})
        real = port.port_commit

        def lossy(repo, commit):
            tree = real(repo, commit)
            if commit != tip:
                return tree
            with tempfile.TemporaryDirectory() as d:
                env = dict(os.environ, GIT_INDEX_FILE=os.path.join(d, "index"))
                git = lambda *a: subprocess.run(["git", "-C", repo, *a], env=env, check=True, capture_output=True,
                                                text=True).stdout.strip()
                git("read-tree", tree)
                git("update-index", "--force-remove", "--", layout.moved(new))
                return git("write-tree")

        with mock.patch.object(port, "port_commit", lossy):
            rc, out = self.port("proofs/lossy", lc)
        self.assertEqual(rc, 4, out)
        self.assertIn("does not change %s as" % lc, out)
        self.assertIn("\n  only before the port: A ", out)
        self.assertIn(layout.moved(new), out)

    def test_a_branch_with_no_merge_base_stops_with_exit_5(self):
        lc = self.move(self.base0)
        empty = self.git("mktree", input="")
        self.git("branch", "unrelated", self.git("commit-tree", empty, "-m", "a history of its own"))
        rc, out = self.port("unrelated", lc)
        self.assertEqual(rc, 5, out)
        self.assertIn("unrelated has no merge base with %s^1" % lc, out)

    def fake_tools(self, help_text, files=None):
        """Replace tools/oft on main by a stand-in whose `generate --help` prints help_text, which logs each call of it
        to self.calls, and whose paths.is_shared names README.md and index/<file>; the layout commit made from that,
        with branch proofs/x made from base0 with files (path: text; a proof library change by default)."""
        self.calls = os.path.join(os.path.dirname(self.t.root), "generate-calls")
        self.git("checkout", "-q", "main")
        shutil.rmtree(self.t.path("tools", "oft"))
        self.t.write("tools/oft/__init__.py", "")
        self.t.write("tools/oft/__main__.py", "\n".join([
            "import os, sys",
            "with open(os.environ['PORT_GENERATE_CALLS'], 'a') as f:",
            "    f.write(' '.join(sys.argv[1:]) + '\\n')",
            "if '--help' in sys.argv:",
            "    sys.stdout.write(%r)" % help_text,
            ""]))
        self.t.write("tools/oft/paths.py", "def is_shared(rel):\n"
                                           "    return rel == 'README.md' or (rel.startswith('index/')\n"
                                           "                                  and rel.count('/') == 1)\n")
        lc = self.move(helpers.git_commit(self.t.root, "stand-in tools"))
        self.commit("proofs/x", self.base0, files or {UNIT_PROOFS + "/lib/A.v": "Definition a := 1.\n"})
        return lc

    def renders(self, lc):
        """port-branch's exit status, what it printed, and the generate calls step 4 made (the arguments after --root
        DIR; none when the stand-in never ran)."""
        with mock.patch.dict(os.environ, PORT_GENERATE_CALLS=self.calls):
            rc, out = self.port("proofs/x", lc)
        if not os.path.exists(self.calls):
            return rc, out, []
        with open(self.calls) as f:
            return rc, out, [line.split()[2:] for line in f.read().splitlines()]

    def test_step_4_renders_with_skip_shared_when_the_branchs_tools_take_it(self):
        """Shared generated files are rendered after each merge, never in a pull request; a branch whose
        tools (the per-project base's, merged) take --skip-shared renders the rest only.  The help is #416's."""
        rc, out, calls = self.renders(self.fake_tools(HELP_416))
        self.assertEqual(rc, 0, out)
        self.assertEqual(calls, [["generate", "--help"], ["generate", "--skip-shared"]])

    def test_step_4_renders_everything_when_the_branchs_tools_lack_skip_shared(self):
        rc, out, calls = self.renders(self.fake_tools(HELP_BEFORE_416))
        self.assertEqual(rc, 0, out)
        self.assertEqual(calls, [["generate", "--help"], ["generate"]])

    def test_step_4_takes_no_skip_shared_that_the_help_names_only_in_prose(self):
        """Review of #438, finding 1: only an option line of the help counts, not the flag named in another option's
        help (those tools would refuse --skip-shared, and port-branch would blame the render)."""
        rc, out, calls = self.renders(self.fake_tools(HELP_BEFORE_416.replace(
            "compare instead of writing", "compare instead of writing (--skip-shared is not taken here)")))
        self.assertEqual(rc, 0, out)
        self.assertEqual(calls, [["generate", "--help"], ["generate"]])

    def test_step_4_takes_no_longer_option_for_skip_shared(self):
        """Review of #438, finding 1: --skip-shared-files is another option, which argparse would run silently for an
        abbreviated --skip-shared."""
        rc, out, calls = self.renders(self.fake_tools(
            "usage: oft generate [-h] [--check] [--skip-shared-files]\n\noptions:\n"
            "  -h, --help           show this help message and exit\n"
            "  --check              compare instead of writing\n"
            "  --skip-shared-files  another option\n"))
        self.assertEqual(rc, 0, out)
        self.assertEqual(calls, [["generate", "--help"], ["generate"]])

    def test_step_4_gives_each_shared_file_the_bases_version_when_the_tools_take_skip_shared(self):
        """An old-layout branch committed its own renders of the shared generated files, which #416's lint paths rule
        refuses in a pull request: with tools that take --skip-shared (and so name the shared files, paths.is_shared),
        each shared file the branch changed ends with onto's bytes, one onto lacks is removed, and every other change
        of the branch stays."""
        lc = self.fake_tools(HELP_416, {"README.md": "the branch's own render\n",
                                        "index/statements.tsv": "the branch's own row\n",
                                        "index/extra.tsv": "only the branch has it\n",
                                        "notes/zlib.md": "the branch's note\n",
                                        UNIT_PROOFS + "/lib/A.v": "Definition a := 1.\n"})
        rc, out, calls = self.renders(lc)
        self.assertEqual(rc, 0, out)
        self.assertEqual(calls, [["generate", "--help"], ["generate", "--skip-shared"]])
        final = self.head()
        for rel in ("README.md", "index/statements.tsv"):
            self.assertEqual(self.git("show", "%s:%s" % (final, rel)), self.git("show", "%s:%s" % (lc, rel)), rel)
        self.assertNotIn("index/extra.tsv", self.files(final))
        self.assertEqual(self.git("show", final + ":notes/zlib.md"), "the branch's note")
        self.assertEqual(self.git("show", final + ":" + layout.moved(UNIT_PROOFS + "/lib/A.v")), "Definition a := 1.")
        self.assertEqual(self.changes(lc, final), {"M\tnotes/zlib.md", "M\t" + layout.moved(UNIT_PROOFS + "/lib/A.v")})
        self.assertEqual(self.git("status", "--porcelain", where=self.dir), "")

    def test_an_old_layout_branch_is_ported_through_both(self):
        """An old-layout branch ported through the layout commit LC, then the namespace commit NC, the rename of LC
        (OSSV-162)."""
        lc = self.move(self.base0)
        self.git("checkout", "-q", "-B", "renamed", lc)
        out = io.StringIO()
        self.assertEqual(nsrename.rename_tree(self.t.root, NEW, NS, out=out, jobs=1), 0, out.getvalue())
        nc = helpers.git_commit(self.t.root, "the rename")
        self.git("checkout", "-q", "-B", "proofs/both", self.base0)
        proof(self.t, "zlib/checksum_fuzzer/ubsan_halts",
              "From OssFuzzTheorems.zlib.checksum_fuzzer Require Import Statements.\nTheorem t : True. Proof. "
              "exact I. Qed.\n")
        helpers.git_commit(self.t.root, "an old-layout proof naming the old namespace")
        out = io.StringIO()
        rc = port.port_branch(self.t.root, "proofs/both", self.dir, layout_commit=lc, namespace_commit=nc,
                              onto="renamed", out=out)
        self.assertEqual(rc, 0, out.getvalue())
        final = self.head()
        self.assertEqual([f for f in self.files(final) if f.split("/")[0] in layout.OLD_TOPS], [])
        moved = layout.moved("proofs/zlib/checksum_fuzzer/ubsan_halts/Proof.v")
        self.assertEqual(self.git("show", final + ":" + moved),
                         "From OSSVerify.zlib.checksum_fuzzer Require Import Statements.\nTheorem t : True. Proof. "
                         "exact I. Qed.")
        self.assertIn("ported onto the per-project layout and the Rocq namespace OSSVerify", out.getvalue())
        buf = io.StringIO()
        self.assertEqual(generate.run(self.dir, check=True, out=buf, shared=False), 0, buf.getvalue())


NEW, NS = "OSSVerify", "oss-verify"
OLD = "OssFuzzTheorems"
PROJ_PROOFS = "projects/zlib/checksum_fuzzer/proofs"


def per_project_proof(t, statement, body):
    """Write a proof of zlib/checksum_fuzzer/<statement> in the per-project layout."""
    st = next(s for s in facts.load(t.root).statements() if s.id == "zlib/checksum_fuzzer/" + statement)
    t.put_yaml("%s/%s/proof.yaml" % (PROJ_PROOFS, statement), {
        "schema": "oss-fuzz-theorems/proof/1", "proves": st.id, "fingerprint": st.fingerprint})
    t.write("%s/%s/Proof.v" % (PROJ_PROOFS, statement), body)


NEW_PROOF = ("From OssFuzzTheorems.zlib.checksum_fuzzer Require Import Statements.\n"
             "From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib Require Import T.\n"
             "Theorem holds : True. Proof. exact I. Qed.\n")


class PortBranchNamespace(GitTests):
    """`oft port-branch --namespace-commit NC`: a repository in the per-project layout whose base0 holds a proof with a
    proof library of the stored encodings, rendered, with these tools (less their tests); main moves on to base1, and
    NC, on branch renamed, is base1 renamed by `oft rename-namespace`.  Branches are made as lanes made them."""

    def setUp(self):
        super().setUp()
        self.t = helpers.Tree()
        self.addCleanup(self.t.close)
        per_project_proof(self.t, "plain_halts", NEW_PROOF)
        self.t.write(PROJ_PROOFS + "/lib/T.v", test_nsrename.WHOLE_FILE)
        shutil.copytree(OFT, self.t.path("tools", "oft"), ignore=shutil.ignore_patterns("tests", "__pycache__"))
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.base0 = helpers.git_repo(self.t.root)
        self.base1 = self.commit("main", self.base0, {"notes/zlib.md": "zlib, as the base has it now\n"})
        self.nc = self.rename("renamed", self.base1)
        self.dir = os.path.join(os.path.dirname(self.t.root), "port")

    def git(self, *args, where=None, input=None):
        return helpers.git(where or self.t.root, *args, input=input)

    def commit(self, branch, start, files=None, delete=()):
        self.git("checkout", "-q", "-B", branch, start)
        for rel, text in (files or {}).items():
            self.t.write(rel, text)
        for rel in delete:
            os.remove(self.t.path(rel))
        return helpers.git_commit(self.t.root, "a change on " + branch)

    def rename(self, branch, start, also=None):
        """The namespace commit: start renamed (and also's files written in the same commit), on branch."""
        self.git("checkout", "-q", "-B", branch, start)
        out = io.StringIO()
        self.assertEqual(nsrename.rename_tree(self.t.root, NEW, NS, out=out, jobs=1), 0, out.getvalue())
        for rel, text in (also or {}).items():
            self.t.write(rel, text)
        return helpers.git_commit(self.t.root, "oft rename-namespace --to %s --opam-stem %s" % (NEW, NS))

    def port(self, branch, nc=None, lc=None, onto="renamed"):
        out = io.StringIO()
        rc = port.port_branch(self.t.root, branch, self.dir, layout_commit=lc, namespace_commit=nc or self.nc,
                              onto=onto, out=out)
        return rc, out.getvalue()

    def head(self):
        return self.git("rev-parse", "HEAD", where=self.dir)

    def show(self, commit, rel):
        return self.git("show", "%s:%s" % (commit, rel))

    def files(self, commit):
        return self.git("ls-tree", "-r", "--name-only", commit).splitlines()

    def old_names_left(self, commit):
        """The files of commit outside the ones the rename leaves alone and the shared ones that hold the old names."""
        r = subprocess.run(["git", "-C", self.t.root, "grep", "-l", "-e", OLD, "-e", "rocq-oss-fuzz-theorems", commit,
                            "--", "."] + nsrename.exclude_pathspecs(), capture_output=True, text=True)
        return [hit.split(":", 1)[1] for hit in r.stdout.splitlines() if not paths.is_shared(hit.split(":", 1)[1])]

    def assert_rendered(self):
        buf = io.StringIO()
        self.assertEqual(generate.run(self.dir, check=True, out=buf, shared=False), 0, buf.getvalue())
        self.assertEqual(self.git("status", "--porcelain", where=self.dir), "")

    def port_commit_of(self, final, name):
        return self.git("log", "--format=%H", "--grep=^oft port-branch: %s onto the Rocq namespace" % name, final)

    def test_a_branch_with_a_new_proof_naming_the_old_namespace_ports_to_the_new_one(self):
        self.git("checkout", "-q", "-B", "proofs/new", self.base0)
        per_project_proof(self.t, "ubsan_halts", NEW_PROOF)
        tip = helpers.git_commit(self.t.root, "a new proof")
        rc, out = self.port("proofs/new")
        self.assertEqual(rc, 0, out)
        final = self.head()
        self.assertEqual(self.show(final, PROJ_PROOFS + "/ubsan_halts/Proof.v"), NEW_PROOF.replace(OLD, NEW).strip())
        self.assertEqual(self.old_names_left(final), [])
        self.assertEqual(self.show(final, "notes/zlib.md"), "zlib, as the base has it now")
        self.assert_rendered()
        self.git("merge-base", "--is-ancestor", tip, final)
        self.git("merge-base", "--is-ancestor", self.nc, final)
        pc = self.port_commit_of(final, "proofs/new")
        b1, second = self.git("show", "-s", "--format=%P", pc).split()
        self.assertEqual((second, self.git("rev-parse", b1 + "^1"), self.git("rev-parse", b1 + "^2")),
                         (self.nc, tip, self.base1))
        self.assertIn("ported onto the Rocq namespace OSSVerify in %s: %s\n" % (self.dir, final), out)

    def test_a_port_renames_only_the_branch_s_changed_files(self):
        """Every path the branch did not change holds NC's blob in the port commit: no whole-tree rename runs."""
        tip = self.commit("proofs/new", self.base0, {PROJ_PROOFS + "/lib/A.v": "Definition a := %s.Core.x.\n" % OLD})
        rc, out = self.port("proofs/new")
        self.assertEqual(rc, 0, out)
        pc = self.port_commit_of(self.head(), "proofs/new")
        changed = set(self.git("diff", "--name-only", "--no-renames", self.nc, pc).splitlines())
        self.assertEqual(changed, {PROJ_PROOFS + "/lib/A.v"})
        self.assertEqual(self.show(pc, PROJ_PROOFS + "/lib/A.v"), "Definition a := %s.Core.x." % NEW)
        self.git("merge-base", "--is-ancestor", tip, pc)

    def test_an_encoded_table_in_a_new_proof_is_renamed_by_the_codec(self):
        self.commit("proofs/enc", self.base0, {PROJ_PROOFS + "/lib/U.v": test_nsrename.WHOLE_FILE})
        rc, out = self.port("proofs/enc")
        self.assertEqual(rc, 0, out)
        text = self.show(self.head(), PROJ_PROOFS + "/lib/U.v") + "\n"
        self.assertNotIn(OLD, text)
        lz = [text[s:e] for s, e, k in nsrename.literals(text) if k == "kr_table_lz"][0]
        plain = nsrename.lz_inflate(lz.encode("utf-8").decode("latin-1"))
        self.assertNotIn(OLD, plain)
        self.assertIn(NEW, plain)
        self.assertEqual(text, self.show(self.nc, PROJ_PROOFS + "/lib/T.v") + "\n")

    def test_a_branch_past_the_rename_gets_its_later_old_names_renamed(self):
        """A lane that kept generating files with the old name after it merged the rename (Review Focus 5)."""
        self.commit("proofs/later", self.nc, {PROJ_PROOFS + "/lib/L.v": "From %s.Core Require Import Shapes.\n" % OLD,
                                              "notes/zlib.md": "a note of its own\n"})
        rc, out = self.port("proofs/later")
        self.assertEqual(rc, 0, out)
        final = self.head()
        self.assertEqual(self.show(final, PROJ_PROOFS + "/lib/L.v"), "From %s.Core Require Import Shapes." % NEW)
        self.assertEqual(self.show(final, "notes/zlib.md"), "a note of its own")
        self.assertIn("oft port-branch: the old namespace in files added after the rename",
                      self.git("log", "--format=%s", final))
        self.assertEqual(self.old_names_left(final), [])

    def test_a_hand_conflict_stops_with_exit_2(self):
        self.commit("proofs/notes", self.base0, {"notes/zlib.md": "the branch's notes\n"})
        rc, out = self.port("proofs/notes")
        self.assertEqual(rc, 2, out)
        self.assertIn("\n  notes/zlib.md\n", out)
        self.assertIn("./oft port-branch proofs/notes --namespace-commit %s --worktree %s --onto renamed\n"
                      % (self.nc, self.dir), out)

    def test_an_unknown_encoding_holding_the_old_name_stops_with_exit_3(self):
        bad = PROJ_PROOFS + "/lib/Bad.v"
        self.commit("proofs/bad", self.base0, {bad: 'Ltac2 tbl () := "C3?%s:boost_json".\n' % OLD})
        rc, out = self.port("proofs/bad")
        self.assertEqual(rc, 3, out)
        self.assertIn("refused %s:1: a string literal holds %s" % (bad, OLD), out)
        # nothing is half renamed: the worktree holds the branch with the base merged, as the branch has the file
        self.assertEqual(self.show(self.head(), bad), 'Ltac2 tbl () := "C3?%s:boost_json".' % OLD)
        self.assertEqual(self.git("status", "--porcelain", where=self.dir), "")
        self.assertEqual(self.git("rev-parse", self.head() + "^2"), self.base1)

    def test_a_namespace_commit_that_is_not_a_pure_rename_is_refused(self):
        """NC changes notes/zlib.md by more than the rename, and the branch changes it too: the port would take the
        branch's version and drop NC's change, so it stops with 4."""
        nc = self.rename("renamed-and-more", self.base1, {"notes/zlib.md": "a change the rename does not make\n"})
        self.commit("proofs/notes", self.base1, {"notes/zlib.md": "the branch's notes\n"})
        rc, out = self.port("proofs/notes", nc=nc, onto="renamed-and-more")
        self.assertEqual(rc, 4, out)
        self.assertIn("  notes/zlib.md: %s changes it by more than the rename, and the branch changed it too" % nc, out)

    def test_a_namespace_commit_that_renames_nothing_is_refused(self):
        self.commit("proofs/x", self.base0, {"notes/zlib.md": "x\n"})
        rc, out = self.port("proofs/x", nc=self.base1, onto="main")
        self.assertEqual(rc, 1, out)
        self.assertIn("is no rename of the Rocq namespace", out)
        self.assertFalse(os.path.exists(self.dir))

    def test_the_files_the_rename_leaves_alone_keep_the_branch_s_bytes(self):
        """A branch made before the rename that changes tools/oft/facts.py (where the fingerprint's fixed name lives)
        and docs/statements.md (which states it): the port keeps both as the branch has them, and exits 0, not 4."""
        facts_py = self.t.read("tools/oft/facts.py")
        self.assertIn('FINGERPRINT_NAMESPACE = "%s"' % OLD, facts_py)
        self.commit("proofs/tools", self.base0, {
            "tools/oft/facts.py": facts_py + "# a comment the branch adds\n",
            "docs/statements.md": "The theories are hashed with the namespace read as `%s`.\n" % OLD})
        rc, out = self.port("proofs/tools")
        self.assertEqual(rc, 0, out)
        final = self.head()
        self.assertEqual(self.show(final, "tools/oft/facts.py") + "\n", facts_py + "# a comment the branch adds\n")
        self.assertIn("read as `%s`" % OLD, self.show(final, "docs/statements.md"))

    def test_a_branch_past_the_rename_keeps_the_files_the_rename_leaves_alone(self):
        """Step Q0 does not rename tools/oft/names.py (NAMESPACE_DEFAULT) or docs/versioning.md."""
        names_py = self.show(self.nc, "tools/oft/names.py") + "\n"
        self.commit("proofs/later-tools", self.nc, {
            "tools/oft/names.py": names_py + "# a comment the branch adds\n",
            "docs/versioning.md": "read as `%s` where it starts a dotted path\n" % OLD})
        rc, out = self.port("proofs/later-tools")
        self.assertEqual(rc, 0, out)
        final = self.head()
        self.assertIn('NAMESPACE_DEFAULT = "%s"' % OLD, self.show(final, "tools/oft/names.py"))
        self.assertEqual(self.show(final, "docs/versioning.md"), "read as `%s` where it starts a dotted path" % OLD)

    def test_it_pushes_nothing(self):
        origin = os.path.join(os.path.dirname(self.t.root), "origin.git")
        self.git("init", "-q", "--bare", origin)
        self.git("remote", "add", "origin", origin)
        self.git("checkout", "-q", "--detach", self.base0)
        self.t.write(PROJ_PROOFS + "/lib/A.v", "Definition a := %s.Core.x.\n" % OLD)
        helpers.git_commit(self.t.root, "a proof library change")
        self.git("push", "-q", "origin", "main", "renamed", "HEAD:refs/heads/proofs/only-there")
        self.git("fetch", "-q", "origin")
        refs = (self.git("for-each-ref"), self.git("for-each-ref", where=origin))
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            rc = oft_main.main(["--root", self.t.root, "port-branch", "proofs/only-there", "--namespace-commit",
                                self.nc, "--worktree", self.dir, "--onto", "renamed"])
        self.assertEqual(rc, 0, out.getvalue())
        self.assertEqual((self.git("for-each-ref"), self.git("for-each-ref", where=origin)), refs)
        final = self.head()
        self.assertIn("\n  git -c pack.useSparse=false push origin %s:refs/heads/proofs/only-there\n" % final,
                      out.getvalue())
        self.assertIn("\n  gh pr comment proofs/only-there --body 'Ported to the Rocq namespace OSSVerify by oft "
                      "port-branch: %s'\n" % final, out.getvalue())



# A stand-in docker: it logs each call, and a `run` with a TMPDIR writes oft check's log with two
# overriding-logical-loadpath warnings into the host folder mounted where that TMPDIR is, then exits STAND_IN_EXIT (a
# run without one, check-units.sh's facts run, exits 0).
STAND_IN_DOCKER = r"""#!/bin/bash
echo "docker $*" >> "$STAND_IN_LOG"
[ "$1" = run ] || exit 0
tmp= mounts=()
while [ "$#" -gt 0 ]; do
  if [ "$1" = -e ] && [[ "$2" == TMPDIR=* ]]; then tmp="${2#TMPDIR=}"; fi
  if [ "$1" = -v ]; then mounts+=("$2"); fi
  shift
done
[ -n "$tmp" ] || exit 0
for m in "${mounts[@]}"; do
  if [ "${m##*:}" = "$tmp" ]; then
    mkdir -p "${m%:*}/oft-check-stand-in"
    printf '%s\n' 'Warning: lib is bound twice [overriding-logical-loadpath,filesystem,default]' \
      'Warning: once more [overriding-logical-loadpath,filesystem,default]' 'Warning: another [deprecated,default]' \
      > "${m%:*}/oft-check-stand-in/dune.log"
  fi
done
exit "${STAND_IN_EXIT:-0}"
"""


class PortCheck(unittest.TestCase):
    """port-check.sh over a fixture copy, with a stand-in docker on PATH, as test_fetch_check stands in for
    check-units.sh's tools."""

    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.addCleanup(self.d.cleanup)
        self.bin = os.path.join(self.d.name, "bin")
        os.makedirs(self.bin)
        with open(os.path.join(self.bin, "docker"), "w") as f:
            f.write(STAND_IN_DOCKER)
        os.chmod(os.path.join(self.bin, "docker"), 0o755)
        self.log = os.path.join(self.d.name, "docker.log")
        open(self.log, "w").close()
        self.assets = os.path.join(self.d.name, "assets")
        os.makedirs(self.assets)

    def port_check(self, t, *args, **env):
        """(the completed port-check.sh over t, every docker call)."""
        env = dict(os.environ, WORK=t.root, TOOLS=os.path.dirname(OFT),
                   PATH=self.bin + os.pathsep + os.environ["PATH"], UNITS="zlib/checksum_fuzzer", PROOF_UNITS='""',
                   PROJECTS="zlib", ASSETS=self.assets, PYDEPS=self.d.name, CACHE=os.path.join(self.d.name, "cache"),
                   STAND_IN_LOG=self.log, PYTHONDONTWRITEBYTECODE="1", **env)
        r = subprocess.run(["bash", PORT_CHECK, *args], env=env, capture_output=True, text=True)
        with open(self.log) as f:
            return r, f.read()

    def test_port_check_refuses_a_tree_it_cannot_port(self):
        with helpers.tree() as t:
            old_layout(t)
            t.write("proofs/lib-lean/A.lean", "def a := 0\n")
            before = t.files()
            r, calls = self.port_check(t)
            self.assertNotEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("refused proofs/lib-lean/A.lean: proofs/lib-lean/ has no place in the per-project layout\n"
                          "oft port-layout: 1 file(s) refused; nothing moved\n", r.stdout)
            self.assertEqual(calls, "")
            self.assertEqual(t.files(), before)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_port_check_runs_check_units_and_counts_the_warnings_in_its_logs(self):
        """--no-port: the tree is rendered and linted, check-units.sh checks each unit in its view with oft check's
        temporary files in WORK/_build/oft-port-check, and the warning count is printed; the exit status is
        check-units.sh's."""
        with helpers.tree() as t:
            make_release(t, self.assets)
            for status in (0, 1):
                with self.subTest(check_units_exit=status):
                    open(self.log, "w").close()
                    r, calls = self.port_check(t, "--no-port", STAND_IN_EXIT=str(status))
                    self.assertEqual(r.returncode, status, r.stdout + r.stderr)
                    self.assertIn("oft lint: 0 finding(s)\n", r.stdout)
                    self.assertIn("docker run -v %s/_build/oft-port-check:/oft-port-check -e TMPDIR=/oft-port-check "
                                  "--rm --network none " % t.root, calls)
                    self.assertIn("python3 -m oft.check --root /work --facts-from /facts zlib/checksum_fuzzer "
                                  "--parts statements\n", calls)
                    # the facts run reads the whole tree read-only, and keeps no logs
                    facts_run = [c for c in calls.splitlines() if "--facts-to" in c]
                    self.assertEqual(len(facts_run), 1, calls)
                    self.assertIn("-v %s:/work:ro " % t.root, facts_run[0])
                    self.assertNotIn("TMPDIR", facts_run[0])
                    self.assertTrue(r.stdout.endswith(
                        "overriding-logical-loadpath warnings: 2 (oft check's logs in %s/_build/oft-port-check)\n"
                        % t.root), r.stdout)


if __name__ == "__main__":
    unittest.main()
