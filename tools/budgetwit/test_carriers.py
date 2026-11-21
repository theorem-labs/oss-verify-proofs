"""Regression cases for carrier soundness and generation refusal."""
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from . import __main__ as cli, carriers, control, units


REPO = Path(__file__).resolve().parents[2]


class NodeStepTests(unittest.TestCase):
    def test_parametric_carrier_soundness_is_specialized_at_mayfail(self):
        unit = units.load('libreac/fuzz_knock', repo=REPO)
        profile = carriers.detect(unit.lib_dir)
        self.assertEqual(profile.node_step.configuration, 'mcfg')
        self.assertEqual(profile.node_step.soundness_mode, 'MayFail')
        self.assertFalse(profile.node_step.requires_transparency)
        self.assertEqual(profile.node_step.evidence.declaration, 'node_ok')
        text = profile.render(unit)
        self.assertIn('@node_ok segs MayFail', text)
        self.assertIn('grant_ok segs c', text)
        self.assertNotIn('/\\ cfg_transparent segs c', text)

    def test_fixed_carrier_records_its_actual_filtered_step(self):
        unit = units.load('zlib/checksum_fuzzer', repo=REPO)
        profile = carriers.detect(unit.lib_dir)
        self.assertEqual(profile.node_step.relation, 'sstep_cfg')
        self.assertEqual(profile.node_step.configuration, 'ACFG')
        self.assertEqual(profile.node_step.soundness_mode, 'fixed')
        self.assertTrue(profile.node_step.requires_transparency)
        self.assertEqual(profile.index_arguments, ())
        self.assertEqual(profile.template_path.name, 'YK15Fixed.v.in')

    def test_fixed_template_preserves_the_transparency_conjunct(self):
        unit = units.load('zlib/checksum_fuzzer', repo=REPO)
        text = carriers.detect(unit.lib_dir).render(unit)
        self.assertIn('/\\ cfg_transparent segs c', text)
        self.assertIn('Lemma budget_ok_instr', text)
        self.assertIn('Lemma budget_ok_no', text)
        self.assertIn('Lemma budget_ok_exit', text)
        self.assertIn('(proj2 Hg e (SNext c2) Hss)', text)
        self.assertNotIn('Context {AM : AllocMode}', text)
        self.assertNotIn('{{', text)
        self.assertNotIn('OSSVerify.Proofs.libreac', text)


class GenerationTests(unittest.TestCase):
    def test_gen_refuses_stub_family_without_writing_files(self):
        unit = units.load('yajl-ruby/json_fuzzer', repo=REPO)
        with TemporaryDirectory() as directory:
            root = Path(directory)
            args = cli.arguments().parse_args([
                'gen', '--unit', unit.name, '--usage', 'R.RDrv_A.main_usage',
                '--module', 'Common.ShapeAlgCfg', '--out', str(root / 'out' / 'One.v'),
            ])
            with self.assertRaisesRegex(ValueError, 'RealizesCfg: soundness template is a carrier-prover stub'):
                cli.generate_command(unit, args)
            self.assertEqual(list(root.iterdir()), [])


class ControlScopeTests(unittest.TestCase):
    def test_a_second_witness_in_the_twin_directory_is_not_the_reference(self):
        reference = {'W.StartB', 'W.UsageB', 'W.BudgetWitness', 'W.Rzb', 'W.AW.YK18_w', 'W.AsanWitness'}
        reached = {'W.BudgetWitness', 'W.StartB', 'W.UsageB'}
        walk, skipped = control.walk_scope(reference, reached, {'W.BudgetWitness', 'W.Rzb'})
        self.assertEqual(walk, {'W.StartB', 'W.UsageB'})
        self.assertEqual(skipped, ['W.AW.YK18_w', 'W.AsanWitness'])

    def test_an_unpaired_file_the_entry_reaches_stays_in_scope(self):
        walk, skipped = control.walk_scope({'W.StartB', 'W.Other'}, {'W.StartB', 'W.Other'}, set())
        self.assertEqual(walk, {'W.StartB', 'W.Other'})
        self.assertEqual(skipped, [])


if __name__ == '__main__':
    unittest.main()
