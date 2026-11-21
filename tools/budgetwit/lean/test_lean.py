"""Small fixtures catch range, token, metadata and stale-source mistakes."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))


class LeanBackendTests(unittest.TestCase):
    def test_copy_is_inclusive_and_renames_whole_dotted_tokens(self):
        from tools.budgetwit.lean.emitter import twin
        self.assertEqual(twin("skip\nprivate theorem X.foo : X.fooBar := X.foo\nend\n",
                              [[2, 2]], {"X.foo": "B.bar"}, True),
                         "theorem B.bar : X.fooBar := B.bar\n")

    def test_period_and_numeric_projection_are_not_identifier_suffixes(self):
        from tools.budgetwit.lean.emitter import twin
        self.assertEqual(twin("X.foo. X.foo.1 X.fooBar X.foo.bar\n", [[1, 1]],
                              {"X.foo": "B.bar"}),
                         "B.bar. B.bar.1 X.fooBar X.foo.bar\n")

    def test_bad_range_is_not_silently_truncated(self):
        from tools.budgetwit.lean.emitter import twin
        for ranges in ([[0, 1]], [[2, 1]], [[1, 3]]):
            with self.subTest(ranges=ranges), self.assertRaises(ValueError):
                twin("a\nb\n", ranges, {}, False)

    def test_ranges_may_reorder_but_not_overlap_within_one_piece(self):
        from tools.budgetwit.lean.emitter import twin
        self.assertEqual(twin("a\nb\n", [[2, 2], [1, 1]], {}), "b\na\n")
        with self.assertRaisesRegex(ValueError, "overlap"):
            twin("a\nb\n", [[1, 2], [2, 2]], {})

    def test_manifest_assembles_template_and_refuses_source_drift(self):
        from tools.budgetwit.lean.emitter import generate
        from tools.budgetwit.units import Unit
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "source.lean").write_text("private theorem foo : True := by trivial\n")
            (root / "pre.in").write_text("discard\nnamespace {{unit_prefix}}\n")
            (root / "names.tsv").write_text("foo\tfoo_b\n")
            unit = Unit(root, "p/h", root, root, "Root.p.h.proofs.lib", {}, ())
            source = {"source": "source.lean", "ranges": [[1, 1]],
                      "sha256": hashlib.sha256((root / "source.lean").read_bytes()).hexdigest(),
                      "renames": "names.tsv", "drop_private": True}
            spec = {"family": "YK15", "files": [{"output": "Twin.lean", "pieces": [
                {"fragment": "pre.in", "ranges": [[2, 2]]}, source]}]}
            (root / "control.json").write_text(json.dumps(spec))
            generate(root / "control.json", unit, root / "out")
            self.assertEqual((root / "out/Twin.lean").read_text(),
                             "namespace Root.p.h\ntheorem foo_b : True := by trivial\n")
            (root / "source.lean").write_text("theorem other : False := by trivial\n")
            with self.assertRaisesRegex(ValueError, "source changed"):
                generate(root / "control.json", unit, root / "out")

    def test_lean_unit_reads_its_own_namespace_and_released_alias(self):
        from tools.budgetwit.lean.units import load
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            tree = repo / "lean-proofs/p/h/DifferentRoot/p/h"
            (tree / "proofs/lib").mkdir(parents=True)
            (tree / "Images.lean").write_text(
                "namespace DifferentRoot.p.h.Images\ndef plain : Image :=\n"
                "  Image.mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs\n")
            (tree / "Statements.lean").write_text(
                "def plain_halts : Prop :=\n  halts Images.plain\n")
            (tree / "proofs/lib/Theorems.lean").write_text(
                "theorem p_h_plain_halts : Statements.plain_halts := proof\n")
            unit = load("p/h", repo)
            self.assertEqual(unit.package, "DifferentRoot.p.h.proofs.lib")
            self.assertEqual(unit.image("plain"), ("plain", "DifferentRoot.p.h.images.Plain"))
            self.assertEqual(unit.statements[0].released_theorems, ("p_h_plain_halts",))
    def test_type_probe_qualifies_pairs_and_keeps_strengthening_explicit(self):
        from tools.budgetwit.lean.about_check import probe
        from tools.budgetwit.units import Unit
        unit = Unit(ROOT, "p/h", ROOT, ROOT, "Other.p.h.proofs.lib", {}, ())
        result = probe({"family": "YK15", "types": [{"original": "proofs.lib.A.old", "twin": "BudgetWit.B.new",
                                   "mode": "extra_grant"}]}, unit)
        self.assertIn("#budget_strengthened Other.p.h.proofs.lib.A.old => Other.p.h.BudgetWit.B.new\n", result)
        self.assertNotIn("{{", result)
        with self.assertRaises(ValueError):
            probe({"types": []}, unit)


    def test_profile_substitutions_do_not_assume_yk15(self):
        from dataclasses import replace
        from tools.budgetwit.carriers import PROFILES
        from tools.budgetwit.lean.emitter import values
        from tools.budgetwit.units import Unit
        profile = replace(PROFILES[0], family="Tree", relation="holds", prelude_module="Prelude",
                          support_modules=("Support",), cfg_directory="Config",
                          lean_carrier_directory="Forest", lean_carrier_module="Algebra")
        result = values(Unit(ROOT, "p/h", ROOT, ROOT, "Root.p.h.proofs.lib", {}, ()), profile)
        self.assertEqual(result["original_relation"], "Root.p.h.proofs.lib.Forest.Algebra.holds")
        self.assertEqual(result["support_modules"], "Support")
        self.assertEqual(result["cfg_module"], "Forest.Config.Cfg")

    def test_copied_tactic_body_renames_released_carrier_calls(self):
        from tools.budgetwit.lean.emitter import twin
        source = 'macro "walk" : tactic => `(tactic|\n  apply YP03.rz_run_gen\n  exact YK15.rz_msteps $h)\n'
        self.assertEqual(twin(source, [[1, 3]], {"YP03.rz_run_gen": "RunB.rzb_run_gen",
                                               "YK15.rz_msteps": "Rzb.rzb_msteps"}),
                         'macro "walk" : tactic => `(tactic|\n  apply RunB.rzb_run_gen\n  exact Rzb.rzb_msteps $h)\n')

    def test_macro_audit_rejects_old_qualified_carrier_calls(self):
        from tools.budgetwit.lean.about_check import audit_macros
        with self.assertRaisesRegex(ValueError, "macro.*rz_run_gen"):
            audit_macros('macro "walk" : tactic => `(tactic|\n  apply Root.YP03.rz_run_gen)\n',
                         {"rz_run_gen"})
        audit_macros('macro "walk" : tactic => `(tactic|\n  apply RunB.rzb_run_gen)\n', {"rz_run_gen"})

    def test_type_pair_coverage_and_original_names_are_checked_locally(self):
        from tools.budgetwit.lean.about_check import validate_pairs
        from tools.budgetwit.units import Unit
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "proofs/lib").mkdir(parents=True)
            (root / "proofs/lib/A.lean").write_text("theorem old : True := by trivial\n")
            (root / "out/BudgetWit").mkdir(parents=True)
            (root / "out/BudgetWit/B.lean").write_text("theorem new : True := by trivial\n")
            unit = Unit(root, "p/h", root, root, "Root.p.h.proofs.lib", {}, ())
            spec = {"files": [{"output": "BudgetWit/B.lean"}], "types": [
                {"original": "proofs.lib.A.old", "twin": "BudgetWit.B.new", "mode": "equal"}]}
            self.assertEqual(validate_pairs(spec, unit, root / "out"), (1, 1, 0))
            spec["fresh"] = {"BudgetWit.B.stale": "Removed theorem"}
            with self.assertRaisesRegex(ValueError, "unknown pairs/exemptions"):
                validate_pairs(spec, unit, root / "out")
            spec["fresh"] = {"BudgetWit.B.new": "Already paired"}
            with self.assertRaisesRegex(ValueError, "must not also be paired"):
                validate_pairs(spec, unit, root / "out")
            spec["fresh"] = {}
            spec["types"][0]["original"] = "proofs.lib.A.typo"
            with self.assertRaisesRegex(ValueError, "original"):
                validate_pairs(spec, unit, root / "out")
            spec["types"] = []
            with self.assertRaisesRegex(ValueError, "unpaired"):
                validate_pairs(spec, unit, root / "out")

    def test_duplicate_outputs_are_rejected_before_writing(self):
        from tools.budgetwit.lean.emitter import generate
        from tools.budgetwit.units import Unit
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            unit = Unit(root, "p/h", root, root, "Root.p.h.proofs.lib", {}, ())
            file = {"output": "Twin.lean", "pieces": []}
            (root / "spec.json").write_text(json.dumps({"family": "YK15", "files": [file, file]}))
            with self.assertRaisesRegex(ValueError, "duplicate output"):
                generate(root / "spec.json", unit, root / "out")

    def test_cli_help_describes_manifest(self):
        command = [sys.executable, "-m", "tools.budgetwit.lean", "--help"]
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("manifest", result.stdout)


if __name__ == "__main__":
    unittest.main()
