"""Pure text cases for the common image/sibling correspondence checker."""
import json
from pathlib import Path
from types import SimpleNamespace
from tempfile import TemporaryDirectory
import unittest

from .retarget import Rewriter, checked_addresses, merge_twin, profile_adaptations, provenance_modules, render_files, reviewed_renames
from . import carriers, units


REPO = Path(__file__).resolve().parents[2]


def source(name, text):
    return SimpleNamespace(path=name, src=text)


class CorrespondenceTests(unittest.TestCase):
    def test_addresses_and_reviewed_identifier_change_share_one_checker(self):
        rewrite = Rewriter({'old_helper': 'new_helper'}, {})
        addresses, _, failures = checked_addresses([
            (source('a.v', 'Lemma x : old_helper 0x100.\n'),
             source('b.v', 'Lemma x : new_helper 0x200.\n'))], rewrite)
        self.assertEqual(failures, [])
        self.assertEqual(addresses, {'0x100': '0x200'})

    def test_an_unreviewed_proof_change_is_not_a_relocation(self):
        addresses, _, failures = checked_addresses([
            (source('a.v', 'Lemma x : True.\nProof. exact I. Qed.\n'),
             source('b.v', 'Lemma x : False.\nProof. contradiction. Qed.\n'))], Rewriter({}, {}))
        self.assertEqual(addresses, {})
        self.assertEqual(len(failures), 1)
        self.assertEqual(failures[0]['line'], 1)
        self.assertIn('False', failures[0]['diff'])

    def test_a_constant_cannot_relocate_and_stay_unchanged_elsewhere(self):
        _, _, failures = checked_addresses([
            (source('a.v', 'Check 0x10.\nCheck 0x10.\n'),
             source('b.v', 'Check 0x20.\nCheck 0x10.\n'))], Rewriter({}, {}))
        self.assertTrue(failures)
        self.assertIn('inconsistent', failures[0]['message'])

    def test_only_the_profile_requested_context_is_removed(self):
        rewrite = Rewriter({}, {}, drop_context='AllocMode')
        prepared = rewrite('Context {fx : FloatImplementations}.\n(*\nContext {AM : AllocMode}.\n*)\nContext {AM : AllocMode}.\nCheck 0x10.\n', 'a.v')
        self.assertEqual(prepared.text, 'Context {fx : FloatImplementations}.\n(*\nContext {AM : AllocMode}.\n*)\nCheck 0x10.\n')
        self.assertEqual(prepared.lines, [1, 2, 3, 4, 6])
        self.assertEqual(prepared.contexts[0]['line'], 5)

    def test_from_imports_move_with_their_corresponding_modules(self):
        rewrite = Rewriter({'P.Old': 'P.New'}, {'P.Old.A': 'P.New.A'})
        self.assertEqual(rewrite('From P.Old Require Import A.\n', 'a.v').text,
                         'From P.New Require Import A.\n')

    def test_combined_walk_provenance_keeps_every_released_owner(self):
        unit = units.load('libreac/fuzz_knock', repo=REPO)
        text = '(* made from Reusable/YP0n.v, YP03.v and YN35.v: released lemmas *)'
        self.assertEqual(provenance_modules(text, unit),
                         tuple(unit.qualify('Reusable.' + name) for name in ('YP0n', 'YP03', 'YN35')))

    def test_comments_and_strings_do_not_relocate_as_addresses(self):
        original = 'Check 0x10.\n(*\n0x10\n*)\nDefinition message := "0x10".\n'
        target = original.replace('Check 0x10', 'Check 0x20')
        rewrite = Rewriter({}, {})
        addresses, _, failures = checked_addresses([
            (source('a.v', original), source('b.v', target))], rewrite)
        self.assertEqual(failures, [])
        self.assertEqual(addresses, {'0x10': '0x20'})
        with TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / 'a.v'
            path.write_text(original, encoding='utf8')
            rendered, count, _, _ = render_files([path], root, root / 'out', rewrite, addresses)
            self.assertEqual(rendered[0][1], target)
            self.assertEqual(count, 1)

    def test_changed_hexadecimal_string_is_not_address_only(self):
        _, _, failures = checked_addresses([
            (source('a.v', 'Definition message := "0x10".\n'),
             source('b.v', 'Definition message := "0x20".\n'))], Rewriter({}, {}))
        self.assertEqual(len(failures), 1)
        self.assertEqual(failures[0]['line'], 1)


class ThreeWayTests(unittest.TestCase):
    def test_disjoint_address_and_relation_changes_merge(self):
        base = 'Definition pc := 0x10.\n\nLemma usage : realizes c.\nProof. exact walk. Qed.\n'
        ours = base.replace('realizes', 'rzb')
        theirs = base.replace('0x10', '0x20')
        merged, conflicts = merge_twin(ours, base, theirs)
        self.assertEqual(conflicts, 0)
        self.assertEqual(merged, ours.replace('0x10', '0x20'))

    def test_overlapping_changes_retain_all_three_sides(self):
        merged, conflicts = merge_twin('Check twin.\n', 'Check base.\n', 'Check target.\n')
        self.assertGreater(conflicts, 0)
        for text in ('<<<<<<<', '|||||||', '=======', '>>>>>>>', 'Check twin.', 'Check base.', 'Check target.'):
            self.assertIn(text, merged)


class ReviewedRenameTests(unittest.TestCase):
    def check_policy(self, data, derived=None):
        with TemporaryDirectory() as directory:
            path = Path(directory) / 'reviewed.json'
            path.write_text(json.dumps(data), encoding='utf8')
            return reviewed_renames(path, 'Check old_helper.', 'Check new_helper.',
                                   Rewriter(derived or {}, {}), derived or {})

    def test_reason_and_reviewer_are_required(self):
        with self.assertRaisesRegex(ValueError, 'reviewed_by'):
            self.check_policy({'renames': [{'from': 'old_helper', 'to': 'new_helper', 'reason': 'checked'}]})

    def test_a_reviewed_rename_is_preserved_in_the_report_metadata(self):
        row = {'from': 'old_helper', 'to': 'new_helper', 'reason': 'same target helper', 'reviewed_by': 'reviewer'}
        renames, metadata = self.check_policy({'renames': [row], 'manual_patches': ['manual-node.patch']})
        self.assertEqual(renames, {'old_helper': 'new_helper'})
        self.assertEqual(metadata['renames'], [row])
        self.assertEqual(metadata['manual_patches'], ['manual-node.patch'])

    def test_a_declaration_cannot_override_the_profile_budget_mapping(self):
        row = {'from': 'grant_ok', 'to': 'wrong_budget', 'reason': 'reviewed', 'reviewed_by': 'reviewer'}
        with self.assertRaisesRegex(ValueError, 'disagrees with the carrier profiles'):
            self.check_policy({'renames': [row]}, {'grant_ok': 'budget_ok'})


class ProfileAdaptationTests(unittest.TestCase):
    def test_mayfail_to_fixed_derives_grants_and_context_not_arbitrary_helpers(self):
        a = carriers.detect(units.load('libreac/fuzz_knock', repo=REPO).lib_dir)
        b = carriers.detect(units.load('zlib/checksum_fuzzer', repo=REPO).lib_dir)
        renames, context, _ = profile_adaptations(a, b)
        self.assertEqual(context, 'AllocMode')
        self.assertEqual(renames['grant_ok'], 'budget_ok')
        self.assertEqual(renames['grant_ok_no'], 'budget_ok_no')
        self.assertNotIn('mcfg_nonspurious_no', renames)


if __name__ == '__main__':
    unittest.main()
