"""A sparse workspace that does not hold a proof library (INFRA-1385 R12, A11).

A Legion issue pod writes the libraries its issue names and no other (.legion/hooks/checkout).  A tool
that reads the working tree across units would read an empty place where a library is, so `oft
generate`, a local `oft check` and a local facts run each refuse and name the two commands that add the
library.  After the library is added, each runs as in a full workspace.
"""
import io
import os
import shutil
import tempfile
import unittest
from unittest import mock

from oft import check, generate, layout
from oft.tests.helpers import git, git_commit, git_repo, tree

UNIT = "zlib/checksum_fuzzer"
LIB = "proofs/zlib/checksum_fuzzer/lib"          # the old layout, which the fixture is in


class SparseWorkspace(unittest.TestCase):

    def setUp(self):
        self.ctx = tree()
        self.t = self.ctx.__enter__()
        self.addCleanup(self.ctx.__exit__, None, None, None)
        self.root = self.t.root
        self.t.write(LIB + "/Statements.v", "(* the proof library *)\n")
        # the library's dune file is generated: render it, so that the tree `oft generate --check` reads is
        # the one the facts produce and a refusal is the only thing these tests change
        self.assertEqual(generate.run(self.root, out=io.StringIO()), 0)
        git_repo(self.root)
        self.facts = tempfile.mkdtemp(prefix="oft-facts-")
        self.addCleanup(shutil.rmtree, self.facts, True)

    def make_sparse(self, hold_the_library):
        """Set git's sparse checkout to the patterns the hook writes, with or without this library.  git
        takes the files off disk and puts them back, as it does in a pod."""
        patterns = ["/*", "!/proofs/*/*/lib/"] + (["/%s/" % LIB] if hold_the_library else [])
        git(self.root, "sparse-checkout", "set", "--no-cone", "--skip-checks", *patterns)

    def generate_check(self):
        out = io.StringIO()
        return generate.run(self.root, check=True, out=out), out.getvalue()

    def facts_run(self, units=(UNIT,)):
        """A local facts run: `python3 -m oft.check --facts-to DIR`, which loads the whole tree."""
        out = io.StringIO()
        return check.run(self.root, list(units), facts_to=self.facts, out=out), out.getvalue()

    def unit_check(self):
        out = io.StringIO()
        return check.run(self.root, [UNIT], parts="findings", out=out), out.getvalue()

    # ------------------------------------------------------------------ a full workspace

    def test_a_full_workspace_is_not_refused(self):
        """Nothing changes where the whole tree is on disk: sparse() is false, so no tool asks any further."""
        self.assertFalse(layout.sparse(self.root))
        self.assertEqual(layout.unwritten_libraries(self.root, [UNIT]), [])
        rc, out = self.generate_check()
        self.assertEqual(rc, 0, out)
        rc, out = self.facts_run()
        self.assertEqual(rc, 0, out)

    def test_a_sparse_workspace_that_holds_the_library_is_not_refused(self):
        """A pod whose issue names this fuzz target holds its library: every tool runs as in a full
        workspace, which is the second half of A11."""
        self.make_sparse(hold_the_library=True)
        self.assertTrue(layout.sparse(self.root))
        self.assertEqual(layout.unwritten_libraries(self.root, [UNIT]), [])
        rc, out = self.generate_check()
        self.assertEqual(rc, 0, out)
        rc, out = self.facts_run()
        self.assertEqual(rc, 0, out)

    def test_a_library_the_commit_does_not_hold_is_not_missing(self):
        """A fuzz target with no proof library at all is not refused: there is nothing to add."""
        self.make_sparse(hold_the_library=True)
        self.assertEqual(layout.unwritten_libraries(self.root, ["zlib/api-driver"]), [])

    # ------------------------------------------------------------------ a library the workspace lacks

    def test_the_missing_library_is_named_with_both_commands(self):
        self.make_sparse(hold_the_library=False)
        self.assertEqual(layout.unwritten_libraries(self.root, [UNIT]), [(UNIT, LIB)])
        said = layout.unwritten_libraries_message("oft check", [(UNIT, LIB)], self.root)
        self.assertIn("jj sparse set --add %s" % LIB, said)
        self.assertIn("git sparse-checkout add /%s/" % LIB, said)
        self.assertIn(UNIT, said)

    def test_the_git_command_is_the_one_this_workspace_takes(self):
        """git's cone mode takes a directory and refuses a pattern (`/<lib>/` exits 128 there), and a pod's
        workspace is not in cone mode (the hook writes patterns): the message prints the command that works here."""
        self.make_sparse(hold_the_library=False)
        self.assertFalse(layout.cone(self.root))
        said = layout.unwritten_libraries_message("oft check", [(UNIT, LIB)], self.root)
        self.assertIn("  git sparse-checkout add /%s/" % LIB, said)
        git(self.root, "sparse-checkout", "set", "--cone", "--skip-checks", "tools")
        self.assertTrue(layout.cone(self.root))
        said = layout.unwritten_libraries_message("oft check", [(UNIT, LIB)], self.root)
        self.assertIn("  git sparse-checkout add %s" % LIB, said)
        self.assertNotIn("/%s/" % LIB, said)
        # a caller that names no workspace keeps the pattern, which is what a pod takes
        self.assertIn("  git sparse-checkout add /%s/" % LIB,
                      layout.unwritten_libraries_message("oft check", [(UNIT, LIB)]))

    def test_generate_refuses_instead_of_writing_partial_output(self):
        """Without the refusal the render would write this library's dune file into a directory the
        workspace does not hold, and --check would report every generated file of it as missing."""
        self.make_sparse(hold_the_library=False)
        rc, out = self.generate_check()
        self.assertEqual(rc, 1, out)
        self.assertIn("oft generate", out)
        self.assertIn("jj sparse set --add %s" % LIB, out)
        self.assertIn("git sparse-checkout add /%s/" % LIB, out)
        self.assertNotIn("differs from its rendering", out)

    def test_a_local_facts_run_refuses_and_writes_no_facts(self):
        """The facts a run writes are read by every unit's check: a run over a tree it did not read must
        write none."""
        self.make_sparse(hold_the_library=False)
        rc, out = self.facts_run()
        self.assertEqual(rc, 1, out)
        self.assertIn("jj sparse set --add %s" % LIB, out)
        self.assertEqual(os.path.exists(os.path.join(self.facts, "zlib", "checksum_fuzzer.yaml")), False)

    def test_a_local_check_of_the_unit_refuses(self):
        self.make_sparse(hold_the_library=False)
        rc, out = self.unit_check()
        self.assertEqual(rc, 1, out)
        self.assertIn("oft check", out)
        self.assertIn("git sparse-checkout add /%s/" % LIB, out)

    def test_a_check_of_another_unit_is_not_refused(self):
        """Only a unit the run needs is asked for: a workspace holding one library checks that one."""
        self.make_sparse(hold_the_library=False)
        self.assertEqual(layout.unwritten_libraries(self.root, ["zlib/api-driver"]), [])

    def test_a_multi_unit_run_names_every_library_it_lacks(self):
        self.t.write("proofs/json/fuzz_parse/lib/Statements.v", "(* another library *)\n")
        git_commit(self.root, "another proof library")
        self.make_sparse(hold_the_library=False)
        missing = layout.unwritten_libraries(self.root, [UNIT, "json/fuzz_parse"])
        self.assertEqual(missing, [(UNIT, LIB), ("json/fuzz_parse", "proofs/json/fuzz_parse/lib")])
        rc, out = self.facts_run([UNIT, "json/fuzz_parse"])
        self.assertEqual(rc, 1, out)
        self.assertIn("proofs/json/fuzz_parse/lib", out)

    def test_adding_the_library_back_lets_every_tool_run_again(self):
        """A11's second half with the commands an agent runs: after the library is on disk, the same
        commands answer as they do in a full workspace."""
        self.make_sparse(hold_the_library=False)
        self.assertEqual(self.facts_run()[0], 1)
        git(self.root, "sparse-checkout", "add", "/%s/" % LIB)
        self.assertTrue(os.path.isdir(os.path.join(self.root, LIB)))
        self.assertEqual(layout.unwritten_libraries(self.root, [UNIT]), [])
        rc, out = self.generate_check()
        self.assertEqual(rc, 0, out)
        rc, out = self.facts_run()
        self.assertEqual(rc, 0, out)
        self.assertTrue(os.path.exists(os.path.join(self.facts, "zlib", "checksum_fuzzer.yaml")))

    # ------------------------------------------------------- a library the change itself removed

    def test_a_library_the_change_removed_is_not_refused(self):
        """A workspace may be sparse and still carry a change of its own that deletes a library: `git rm -r` and a
        plain `rm -rf` both leave the index entries as they are (git tags them `H`), where a sparse workspace's are
        skip-worktree (`S`).  Refusing here would stop a run that passes in a full workspace, and would tell the
        author to add back what their own change removed."""
        self.make_sparse(hold_the_library=True)
        self.assertEqual(layout.unwritten_libraries(self.root, [UNIT]), [])
        # the change deletes the library and keeps the deletion in the index
        git(self.root, "rm", "-r", "-q", LIB)
        self.assertFalse(os.path.isdir(self.t.path(LIB)))
        self.assertEqual(layout.unwritten_libraries(self.root, [UNIT]), [])
        self.assertNotIn("sparse workspace", self.generate_check()[1])
        # and the same with the files removed on disk alone, the index untouched
        git(self.root, "reset", "-q", "HEAD", "--", LIB)
        self.assertFalse(os.path.isdir(self.t.path(LIB)))
        self.assertEqual(layout.unwritten_libraries(self.root, [UNIT]), [])
        self.assertNotIn("sparse workspace", self.generate_check()[1])

    def test_only_a_skip_worktree_library_is_refused(self):
        """The two cases side by side in one workspace: the library git left out is refused, and a second library
        that this workspace holds and the change deletes is not."""
        self.t.write("proofs/json/fuzz_parse/lib/Statements.v", "(* another library *)\n")
        self.assertEqual(generate.run(self.root, out=io.StringIO()), 0)
        git_commit(self.root, "another proof library")
        other = "proofs/json/fuzz_parse/lib"
        patterns = ["/*", "!/proofs/*/*/lib/", "/%s/" % other]
        git(self.root, "sparse-checkout", "set", "--no-cone", "--skip-checks", *patterns)
        self.assertTrue(os.path.isdir(self.t.path(other)), "the second library is in this sparse workspace")
        self.assertFalse(os.path.isdir(self.t.path(LIB)), "the first is not")
        git(self.root, "rm", "-r", "-q", other)
        self.assertEqual(layout.unwritten_libraries(self.root, [UNIT, "json/fuzz_parse"]), [(UNIT, LIB)])

    def test_a_directory_that_is_no_repository_is_never_refused(self):
        """`oft check --facts-from` reads a view holding one unit's files: it is no git repository, so
        sparse() is false and the view is never read as a sparse workspace."""
        view = tempfile.mkdtemp(prefix="oft-view-")
        self.addCleanup(shutil.rmtree, view, True)
        self.assertFalse(layout.sparse(view))
        self.assertEqual(layout.unwritten_libraries(view, [UNIT]), [])

    def test_a_machine_with_no_git_answers_instead_of_crashing(self):
        """The check images carry no git at all (toolchain/runner.Dockerfile), and a missing program
        raises rather than failing, so a question nobody can answer must read as a full workspace and
        not as a traceback in the middle of a check."""
        self.make_sparse(hold_the_library=False)
        with mock.patch.dict(os.environ, {"PATH": ""}):
            self.assertFalse(layout.sparse(self.root))
            self.assertEqual(layout.unwritten_libraries(self.root, [UNIT]), [])
            self.assertEqual(layout.sparse(tempfile.gettempdir()), False)

    def test_a_unit_view_a_check_pod_reads_is_never_refused(self):
        """`oft check --facts-from` reads a directory holding one unit's files, which is no git
        repository: that check must run as it does in CI, where every proof verdict comes from it."""
        self.make_sparse(hold_the_library=True)
        self.assertEqual(self.facts_run()[0], 0)
        view = tempfile.mkdtemp(prefix="oft-view-")
        self.addCleanup(shutil.rmtree, view, True)
        for rel in (LIB, "theories"):
            shutil.copytree(os.path.join(self.root, rel), os.path.join(view, rel), dirs_exist_ok=True)
        self.assertFalse(layout.sparse(view))
        self.assertEqual(layout.unwritten_libraries(view, [UNIT]), [])
        out = io.StringIO()
        rc = check.run(view, [UNIT], parts="findings", facts_from=self.facts, out=out)
        self.assertNotIn("sparse workspace", out.getvalue())
        self.assertIsInstance(rc, int)


if __name__ == "__main__":
    unittest.main()
