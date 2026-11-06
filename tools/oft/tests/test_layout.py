"""The two layouts of a fuzz target's proofs, counterexamples and findings (tools/oft/layout.py): every path of both,
where an old-layout path moves, and which layout a path or a tree is in; the rows of both in paths.py."""
import ast
import io
import os
import shutil
import subprocess
import tempfile
import unittest

from oft import facts, generate, layout, names, paths, port
from oft.tests import helpers
from oft.tests.helpers import REPO
from oft.tests.test_release_tree import add_proof
from oft.tests.test_workflow_verdicts import HAVE_WORKFLOWS, NO_WORKFLOWS


def canon(error):
    """A loader error with every path in it as the per-project layout spells it."""
    return " ".join(layout.canonical(w.rstrip(":")) + (":" if w.endswith(":") else "") for w in error.split(" "))


def old_layout_tree(t):
    """The fixture with a proof, a proof library, a build record, its counterexample and its findings, all in the old
    layout."""
    helpers.add_findings(t)
    add_proof(t, "zlib/checksum_fuzzer/plain_halts")
    t.write("proofs/zlib/checksum_fuzzer/lib/A.v", "Definition a := 0.\n")
    t.write("proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.yaml", helpers.build_record())
    # a fuzz target with only a build record (15 of ossv/recipes' 90 proofs folders)
    t.write("proofs/zlib/api-driver/provenance/PROVENANCE.yaml", helpers.build_record())


class Paths(unittest.TestCase):
    def test_a_unit_is_a_project_and_a_harness(self):
        """layout.split_unit, the one reading of a <project>/<harness> a command takes (oft prove, oft symbols)."""
        self.assertEqual(layout.split_unit("zlib/checksum_fuzzer"), ("zlib", "checksum_fuzzer"))
        for bad in ("zlib", "zlib/a/b", "/x", "x/", "./x", "x/..", ""):
            with self.subTest(unit=bad), self.assertRaises(ValueError) as e:
                layout.split_unit(bad)
            self.assertEqual(str(e.exception), "a unit is <project>/<harness>, not %r" % bad)

    def test_every_kind_of_path_in_both_layouts(self):
        p, h = "zlib", "checksum_fuzzer"
        self.assertEqual(layout.statement_dir(p, h), "projects/zlib/checksum_fuzzer")
        self.assertEqual(layout.proofs_dir(p, h, layout.OLD), "proofs/zlib/checksum_fuzzer")
        self.assertEqual(layout.proofs_dir(p, h, layout.NEW), "projects/zlib/checksum_fuzzer/proofs")
        self.assertEqual(layout.proof_dir(p, h, "plain_halts", layout.NEW),
                         "projects/zlib/checksum_fuzzer/proofs/plain_halts")
        self.assertEqual(layout.proof_lib_dir(p, h, layout.OLD), "proofs/zlib/checksum_fuzzer/lib")
        self.assertEqual(layout.provenance_dir(p, h, layout.NEW), "projects/zlib/checksum_fuzzer/proofs/provenance")
        self.assertEqual(layout.record_path(p, h, layout.OLD), "proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.yaml")
        self.assertEqual(layout.counterexamples_dir(p, h, layout.OLD), "counterexamples/zlib/checksum_fuzzer")
        self.assertEqual(layout.counterexample_dir(p, h, "plain_halts", layout.NEW),
                         "projects/zlib/checksum_fuzzer/counterexamples/plain_halts")
        self.assertEqual(layout.findings_dir(p, h, layout.OLD), "findings/zlib/checksum_fuzzer")
        self.assertEqual(layout.finding_dir(p, h, "stand-in-abort", layout.NEW),
                         "projects/zlib/checksum_fuzzer/findings/stand-in-abort")
        self.assertEqual(layout.series_path(p, h, layout.NEW), "projects/zlib/checksum_fuzzer/findings/series")
        self.assertEqual(layout.unpatched_path(p, layout.OLD), "findings/zlib/unpatched.yaml")
        self.assertEqual(layout.unpatched_path(p, layout.NEW), "projects/zlib/unpatched.yaml")
        self.assertEqual(layout.patches_dir(p, layout.OLD), "patches/zlib")
        self.assertEqual(layout.patches_dir(p, layout.NEW), "projects/zlib/patches")
        self.assertEqual(layout.unpatched_bin_dir(p), "projects/zlib/unpatched-bin")
        self.assertEqual(layout.barrier_dirs(p, h), ("projects/zlib/checksum_fuzzer/proofs",
                                                     "projects/zlib/checksum_fuzzer/counterexamples"))

    def test_moved_maps_each_old_row_and_nothing_else(self):
        cases = {
            "proofs/zlib/checksum_fuzzer/lib/A/B.v": "projects/zlib/checksum_fuzzer/proofs/lib/A/B.v",
            "proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.yaml":
                "projects/zlib/checksum_fuzzer/proofs/provenance/PROVENANCE.yaml",
            "counterexamples/janet/fuzz_compile/plain_halts/input.bin":
                "projects/janet/fuzz_compile/counterexamples/plain_halts/input.bin",
            "findings/zlib/unpatched.yaml": "projects/zlib/unpatched.yaml",
            "findings/zlib/checksum_fuzzer/series": "projects/zlib/checksum_fuzzer/findings/series",
            "findings/zlib/checksum_fuzzer/stand-in-abort/input.bin":
                "projects/zlib/checksum_fuzzer/findings/stand-in-abort/input.bin",
            "patches/zlib/0001-x.patch": "projects/zlib/patches/0001-x.patch",
            # by prefix, whatever the name: a stray file travels with its folder
            "proofs/zlib/checksum_fuzzer/lib/A.v.wip": "projects/zlib/checksum_fuzzer/proofs/lib/A.v.wip",
        }
        for old, new in cases.items():
            self.assertEqual(layout.moved(old), new, old)
            self.assertEqual(layout.canonical(old), new, old)
        # proofs/lib/ and proofs/lib-lean/ are no fuzz target's at any depth (209 branch tips hold proofs/lib-lean/)
        for none in ("proofs/lib/X.v", "proofs/lib-lean/A.lean", "proofs/lib/A/B/C.v", "proofs/lib-lean/A/B.lean",
                     "proofs/lib-lean/Mcsl/Core/Defs.lean", "proofs/zlib", "proofs/zlib/notes.md", "README.md",
                     "counterexamples/janet/fuzz_compile", "findings/zlib/README.md",
                     "findings/zlib/bin/checksum_fuzzer/plain.elf",
                     "projects/zlib/checksum_fuzzer/proofs/plain_halts/Proof.v"):
            self.assertIsNone(layout.moved(none), none)
        self.assertEqual(layout.canonical("projects/zlib/checksum_fuzzer/proofs/plain_halts/Proof.v"),
                         "projects/zlib/checksum_fuzzer/proofs/plain_halts/Proof.v")

    def test_is_change(self):
        for yes in ("proofs/zlib/checksum_fuzzer/plain_halts/Proof.v", "findings/zlib/unpatched.yaml",
                    "counterexamples/janet/fuzz_compile/plain_halts/input.bin",
                    "projects/zlib/checksum_fuzzer/proofs/lib/A.v", "projects/zlib/checksum_fuzzer/findings/series",
                    "projects/zlib/checksum_fuzzer/counterexamples/plain_halts/expect.yaml",
                    "projects/zlib/unpatched.yaml"):
            self.assertTrue(layout.is_change(yes), yes)
        for no in ("projects/zlib/checksum_fuzzer/Statements.v", "projects/zlib/project.yaml",
                   "projects/zlib/patches/0001-x.patch", "patches/zlib/0001-x.patch", "proofsx/a",
                   "projects/zlib/checksum_fuzzer/proofs.md", "theories/Shapes.v"):
            self.assertFalse(layout.is_change(no), no)

    def test_unit_of_reads_both_layouts(self):
        self.assertEqual(layout.unit_of("proofs/zlib/checksum_fuzzer/lib/A.v"), "zlib/checksum_fuzzer")
        self.assertEqual(layout.unit_of("projects/zlib/checksum_fuzzer/proofs/lib/A.v"), "zlib/checksum_fuzzer")
        self.assertEqual(layout.unit_of("findings/zlib/checksum_fuzzer/series"), "zlib/checksum_fuzzer")
        self.assertEqual(layout.unit_of("projects/zlib/checksum_fuzzer/findings/series"), "zlib/checksum_fuzzer")
        self.assertIsNone(layout.unit_of("proofs/lib/A.v"))
        self.assertIsNone(layout.unit_of("findings/zlib/unpatched.yaml"))
        self.assertIsNone(layout.unit_of("projects/zlib/patches/0001-x.patch"))

    def test_of_path(self):
        for old in ("proofs/zlib/checksum_fuzzer/lib/A.v", "proofs/lib/X.v", "findings/zlib/unpatched.yaml",
                    "counterexamples/j/f/s/input.bin", "patches/zlib/0001-x.patch"):
            self.assertEqual(layout.of_path(old), layout.OLD, old)
        for new in ("projects/zlib/checksum_fuzzer/proofs/lib/A.v", "projects/zlib/unpatched.yaml",
                    "projects/j/f/counterexamples/s/input.bin", "projects/zlib/checksum_fuzzer/findings/series",
                    "projects/zlib/patches/0001-x.patch"):
            self.assertEqual(layout.of_path(new), layout.NEW, new)
        for neither in ("projects/zlib/checksum_fuzzer/Statements.v", "README.md", "projects/zlib/project.yaml"):
            self.assertIsNone(layout.of_path(neither), neither)

    def test_of_tree_is_old_while_an_old_top_folder_holds_a_file(self):
        with tempfile.TemporaryDirectory() as root:
            self.assertEqual(layout.of_tree(root), layout.NEW)
            os.makedirs(os.path.join(root, "proofs", "zlib", "checksum_fuzzer"))
            os.makedirs(os.path.join(root, "findings", "zlib", "bin", "checksum_fuzzer"))
            with open(os.path.join(root, "findings", "zlib", "bin", "checksum_fuzzer", "plain.elf"), "w"):
                pass   # what `oft fetch --findings` unpacked before L1: never tracked, so no layout
            self.assertEqual(layout.of_tree(root), layout.NEW)
            with open(os.path.join(root, "proofs", "zlib", "checksum_fuzzer", "x"), "w"):
                pass
            self.assertEqual(layout.of_tree(root), layout.OLD)

    def test_the_regular_expressions_take_a_units_proofs_folder_in_both_layouts(self):
        import re
        rx = re.compile(layout.PROOF_HARNESS_RE + "/provenance/")
        for yes in ("proofs/zlib/checksum_fuzzer/provenance/", "projects/zlib/checksum_fuzzer/proofs/provenance/"):
            self.assertTrue(rx.match(yes), yes)
        for no in ("proofs/lib/x/provenance/", "proofs/lib-lean/x/provenance/", "projects/zlib/provenance/"):
            self.assertFalse(rx.match(no), no)
        same = re.compile(layout.PROOF_HARNESS_PROJECT_RE + r"/provenance/port/projects/(?:\1|\2)/")
        self.assertTrue(same.match("proofs/zlib/f/provenance/port/projects/zlib/"))
        self.assertTrue(same.match("projects/zlib/f/proofs/provenance/port/projects/zlib/"))
        self.assertFalse(same.match("proofs/zlib/f/provenance/port/projects/json/"))
        self.assertFalse(same.match("projects/zlib/f/proofs/provenance/port/projects/json/"))
        finding = re.compile(layout.FINDING_FILE_RE)
        self.assertTrue(finding.match("findings/zlib/checksum_fuzzer/stand-in-abort/finding.yaml"))
        self.assertTrue(finding.match("projects/zlib/checksum_fuzzer/findings/stand-in-abort/finding.yaml"))
        self.assertFalse(finding.match("projects/zlib/checksum_fuzzer/findings/series"))
        unpatched = re.compile(layout.UNPATCHED_FILE_RE)
        self.assertEqual(unpatched.match("findings/zlib/unpatched.yaml").group(1), "zlib")
        self.assertEqual(unpatched.match("projects/zlib/unpatched.yaml").group(2), "zlib")


class Rows(unittest.TestCase):
    def test_the_table_is_a_literal_with_each_old_row_beside_its_twin(self):
        """tools/enroll/ci/inputs.py reads TABLE as a literal, never running paths.py; each old-layout row is followed
        by its per-project twin, layout.moved of it, with the same class."""
        with open(os.path.join(REPO, "tools", "oft", "paths.py")) as f:
            node = next(n for n in ast.parse(f.read()).body
                        if isinstance(n, ast.Assign) and [getattr(t, "id", None) for t in n.targets] == ["TABLE"])
        table = ast.literal_eval(node.value)
        self.assertEqual(table, paths.TABLE)
        old = [i for i, (_, pat) in enumerate(table) if pat.split("/")[0] in layout.OLD_TOPS]
        self.assertTrue(old)
        for i in old:
            self.assertEqual(table[i + 1], (table[i][0], layout.moved(table[i][1])), table[i])

    def test_each_new_layout_path_has_the_class_of_its_old_twin(self):
        for old in ("proofs/zlib/checksum_fuzzer/plain_halts/Proof.v", "proofs/zlib/checksum_fuzzer/lib/A/B.v",
                    "proofs/zlib/checksum_fuzzer/lib/dune", "proofs/zlib/checksum_fuzzer/plain_halts/dune",
                    "proofs/zlib/checksum_fuzzer/plain_halts/proof.yaml",
                    "proofs/zlib/checksum_fuzzer/plain_halts/classifier/x.py",
                    "proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.yaml",
                    "proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.md",
                    "proofs/zlib/checksum_fuzzer/provenance/recipe/build.sh",
                    "proofs/zlib/checksum_fuzzer/provenance/port/manifest.yaml",
                    "proofs/zlib/checksum_fuzzer/provenance/port/projects/zlib/build.sh",
                    "proofs/zlib/checksum_fuzzer/provenance/LICENSES/Zlib.txt",
                    # a build record's evidence: scripts of record, per-value tables, gate records, a MANIFEST
                    "proofs/zlib/checksum_fuzzer/provenance/evidence/MANIFEST",
                    "proofs/zlib/checksum_fuzzer/provenance/evidence/scripts/run.sh",
                    "counterexamples/zlib/checksum_fuzzer/plain_halts/input.bin",
                    "counterexamples/zlib/checksum_fuzzer/plain_halts/control.bin",
                    "counterexamples/zlib/checksum_fuzzer/plain_halts/expect.yaml",
                    "findings/zlib/unpatched.yaml", "findings/zlib/checksum_fuzzer/series",
                    "findings/zlib/checksum_fuzzer/s/finding.yaml", "findings/zlib/checksum_fuzzer/s/input.bin",
                    "findings/zlib/checksum_fuzzer/s/control.bin", "findings/zlib/checksum_fuzzer/s/0001-x.patch"):
            a, b = paths.classify(old), paths.classify(layout.moved(old))
            self.assertEqual(len(a), 1, (old, a))
            self.assertEqual(len(b), 1, (layout.moved(old), b))
            self.assertEqual(a[0][0], b[0][0], old)
            self.assertEqual(a[0][2], b[0][2], old)

    def test_a_build_records_evidence_is_a_contributors_in_both_layouts(self):
        for rel in ("proofs/zlib/checksum_fuzzer/provenance/evidence/MANIFEST",
                    "projects/zlib/checksum_fuzzer/proofs/provenance/evidence/tables/values.tsv"):
            self.assertEqual([c for c, _, _ in paths.classify(rel)], ["contrib"], rel)

    def test_the_barrier_dunes_are_generated(self):
        self.assertTrue(paths.is_gen("projects/zlib/checksum_fuzzer/proofs/dune"))
        self.assertTrue(paths.is_gen("projects/zlib/checksum_fuzzer/counterexamples/dune"))

    def test_no_row_admits_a_cross_project_library(self):
        self.assertEqual(paths.classify("proofs/lib/X.v"), [])
        self.assertEqual(paths.classify("proofs/lib-lean/A.lean"), [])

    def test_a_projects_own_folders_are_no_fuzz_target(self):
        for rel in ("projects/zlib/patches/README.md", "projects/zlib/unpatched-bin/README.md",
                    "projects/zlib/patches/dune"):
            self.assertEqual(paths.classify(rel), [], rel)
        self.assertTrue(paths.ignored("projects/zlib/unpatched-bin/checksum_fuzzer/plain.elf"))
        # what `oft fetch --findings` unpacked before the per-project layout stays untracked until the old layout goes
        self.assertTrue(paths.ignored("findings/zlib/bin/checksum_fuzzer/plain.elf"))
        self.assertTrue({"patches", "unpatched-bin"} <= names.RESERVED_HARNESS_NAMES)

    @unittest.skipUnless(HAVE_WORKFLOWS, NO_WORKFLOWS)
    def test_a_moved_counterexample_keeps_its_checkout_attributes(self):
        """.gitattributes holds the new layout's twin of the counterexamples rule, so a moved input checks out as the
        same bytes: binary, text unset, in both places.  It skips where the checkout around tools/oft is not, as in
        the runner image (toolchain/runner.Dockerfile); a checkout without .gitattributes fails it."""
        with tempfile.TemporaryDirectory() as d:
            subprocess.run(["git", "init", "-q", d], check=True)
            shutil.copy(os.path.join(REPO, ".gitattributes"), d)

            def attrs(rel):
                out = subprocess.run(["git", "-C", d, "check-attr", "text", "diff", "eol", "--", rel],
                                     capture_output=True, text=True, check=True).stdout
                return {line.split(": ")[1]: line.split(": ")[2] for line in out.splitlines()}

            self.assertEqual(attrs("counterexamples/j/f/s/input.bin"), attrs("projects/j/f/counterexamples/s/input.bin"))
            self.assertEqual(attrs("projects/j/f/counterexamples/s/input.bin")["text"], "unset")
            self.assertEqual(attrs("projects/j/f/counterexamples/s/expect.yaml")["text"], "auto")



class Loader(unittest.TestCase):
    def test_the_loader_reads_each_layout_the_same(self):
        with helpers.tree() as a, helpers.tree() as b:
            for t in (a, b):
                old_layout_tree(t)
            self.assertEqual(port.port_worktree(b.root, out=io.StringIO()), 0)
            x, y = facts.load(a.root), facts.load(b.root)
            self.assertEqual(sorted(x.proofs), sorted(y.proofs))
            self.assertEqual([layout.canonical(x.proofs[s].path) for s in sorted(x.proofs)],
                             [y.proofs[s].path for s in sorted(y.proofs)])
            self.assertEqual(sorted(x.counterexamples), sorted(y.counterexamples))
            self.assertEqual({u: layout.canonical(d) for u, d in x.proof_libs.items()}, y.proof_libs)
            self.assertEqual({k: layout.canonical(r) for k, r in x.records_at.items()}, y.records_at)
            self.assertEqual(x.records, y.records)
            self.assertEqual(sorted(x.findings), sorted(y.findings))
            self.assertEqual(x.finding_series, y.finding_series)
            self.assertEqual(x.unpatched, y.unpatched)
            self.assertEqual({p: layout.canonical(r) for p, r in x.unpatched_paths.items()}, y.unpatched_paths)
            self.assertEqual(sorted(canon(e) for e in x.errors), sorted(y.errors))
            self.assertEqual((x.layout, y.layout), (layout.OLD, layout.NEW))
            self.assertEqual((x.unit_layout("zlib/checksum_fuzzer"), y.unit_layout("zlib/checksum_fuzzer")),
                             (layout.OLD, layout.NEW))
            self.assertEqual(x.unit_layout("json/no-such-target"), layout.NEW)

    def test_a_unit_in_both_layouts_is_refused(self):
        with helpers.tree() as t:
            old_layout_tree(t)
            shutil.copytree(t.path("proofs/zlib/checksum_fuzzer/plain_halts"),
                            t.path("projects/zlib/checksum_fuzzer/proofs/plain_halts"))
            tree = facts.load(t.root)
            self.assertIn("projects/zlib/checksum_fuzzer/proofs: zlib/checksum_fuzzer is in both layouts "
                          "(proofs/zlib/checksum_fuzzer and projects/zlib/checksum_fuzzer/proofs): run ./oft port-layout",
                          tree.errors)
            self.assertNotIn("zlib/checksum_fuzzer/plain_halts", tree.proofs)
            self.assertNotIn("zlib/checksum_fuzzer", tree.proof_libs)
            self.assertNotIn(("zlib", "checksum_fuzzer"), tree.records_at)
            self.assertFalse([f for f in tree.findings if f.startswith("zlib/checksum_fuzzer/")])

    def test_an_unpatched_yaml_in_both_layouts_is_refused(self):
        with helpers.tree() as t:
            helpers.add_findings(t)
            shutil.copy(t.path("findings/zlib/unpatched.yaml"), t.path("projects/zlib/unpatched.yaml"))
            tree = facts.load(t.root)
            self.assertIn("projects/zlib/unpatched.yaml: zlib is in both layouts (findings/zlib/unpatched.yaml and "
                          "projects/zlib/unpatched.yaml): run ./oft port-layout", tree.errors)
            self.assertNotIn("zlib", tree.unpatched)

    def test_a_projects_own_folders_hold_no_fuzz_target(self):
        """projects/<p>/bin/, patches/ and unpatched-bin/ are no fuzz target's folder, whatever they hold."""
        with helpers.tree() as t:
            for d in ("bin", "patches", "unpatched-bin"):
                t.write("projects/zlib/%s/counterexamples/x/expect.yaml" % d, "not a counterexample\n")
            tree = facts.load(t.root)
            self.assertFalse([u for u in tree.unit_layouts if u.split("/")[1] in ("bin", "patches", "unpatched-bin")])
            self.assertEqual(tree.errors, [])

    def test_the_same_names_hold_no_fuzz_target_in_the_old_layout(self):
        """proofs/<p>/patches/, counterexamples/<p>/bin/ and the like are no fuzz target's folder either: the loader
        skips them (lint refuses their files, which match no row) rather than failing on them."""
        with helpers.tree() as t:
            t.write("proofs/zlib/patches/provenance/PROVENANCE.yaml", helpers.build_record())
            t.write("proofs/zlib/unpatched-bin/plain_halts/proof.yaml", "proves: zlib/unpatched-bin/plain_halts\n")
            t.write("counterexamples/zlib/bin/plain_halts/expect.yaml", "not a counterexample\n")
            t.write("findings/zlib/patches/s/finding.yaml", "not a finding\n")
            tree = facts.load(t.root)
            self.assertFalse([u for u in tree.unit_layouts if u.split("/")[1] in layout.NOT_A_HARNESS])
            self.assertEqual(tree.records_at, {})
            self.assertEqual(tree.errors, [])

    def test_a_folder_holding_only_its_barrier_dune_is_no_fuzz_targets(self):
        """When a per-project proofs folder's last proof goes, only its generated dune is left: the fuzz target then has
        no proofs folder (no key component, no barrier rendered), and oft generate says to remove the stale dune."""
        with helpers.tree() as t:
            t.write("projects/zlib/api-driver/proofs/dune", generate.barrier_dune())
            tree = facts.load(t.root)
            self.assertNotIn("zlib/api-driver", tree.unit_kinds)
            self.assertNotIn("zlib/api-driver", tree.unit_layouts)
            self.assertEqual(tree.errors, [])
            self.assertNotIn("projects/zlib/api-driver/proofs/dune", generate.render_all(tree))
            self.assertEqual(t.generate(check=True), 1)
            self.assertIn("projects/zlib/api-driver/proofs/dune: generated file that the facts no longer produce; "
                          "remove it", t.last_output)

    def test_the_unpatched_binaries_go_to_the_projects_own_folder(self):
        with helpers.tree() as t:
            helpers.add_findings(t)
            h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
            self.assertEqual(h.unpatched_elf_path("asan"),
                             "projects/zlib/unpatched-bin/checksum_fuzzer/checksum_fuzzer.asan")


if __name__ == "__main__":
    unittest.main()
