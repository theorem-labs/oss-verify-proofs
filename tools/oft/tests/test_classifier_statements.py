"""The classifier statements in the yes / no / maybe form (kinds classifier-total, classifier-sound, classifier-maybe
and classifier-bound): their terms, names, rules, rendering, fingerprints and proofs (docs/statements.md, "Classifier
statements"; theories/ClassifierShapes.v)."""
import os
import unittest
from unittest import mock

from oft import check, claims, facts, lint, names, revisions, rules, shapes
from oft.tests import test_classifier_images as ci
from oft.tests.helpers import edit, errors, tree
from oft.tests.test_release_tree import add_proof

UNIT, HARNESS, PROJECT = ci.UNIT, ci.HARNESS, "projects/zlib/project.yaml"
SID = "zlib/checksum_fuzzer/"


def no_patches(y):
    """project.yaml of a project that applies no patch, every build published (a project with unpublished builds
    does not count its patches): originals: published is then allowed."""
    y.pop("patches", None)
    y.pop("withheld", None)
    y["library"]["patch_count"] = 0


def st(kind, role, **kw):
    """Statement fields of the asan pair, with the reading and originals only classifier-sound takes."""
    d = {"kind": kind, "builds": ["plain", "asan"], "classifier": role}
    if kind in shapes.READING_KINDS:
        d.update(reading="alloc-forced-only", originals="unpatched")
    d.update(kw)
    return {k: v for k, v in d.items() if v is not None}


class Terms(unittest.TestCase):
    WANT = {
        ("classifier-total", "a"): ("", "classifier_total3 Images.classifier_a_asan"),
        ("classifier-total", "b"): ("", "classifier_total3 Images.classifier_b_asan"),
        ("classifier-sound", "a"): ("", "classifies_good_inputs_sound Env.alloc_forced_only Images.plain_original "
                                        "Images.asan_original Images.classifier_a_asan"),
        ("classifier-sound", "b"): ("", "classifies_patch_diff_sound Env.alloc_forced_only Images.plain_original "
                                        "Images.plain Images.asan_original Images.asan Images.classifier_b_asan"),
        ("classifier-maybe", "a"): (" (b : Q)", "maybe_at_most Images.classifier_a_asan Distribution.w "
                                                "Distribution.M b"),
        ("classifier-maybe", "b"): (" (b : Q)", "maybe_at_most Images.classifier_b_asan Distribution.w "
                                                "Distribution.M b"),
        ("classifier-bound", "a"): (" (b : Q)", "classifier_rejects_at_most Images.classifier_a_asan "
                                                "Distribution.w Distribution.M b"),
        ("classifier-bound", "b"): (" (b : Q)", "classifier_rejects_at_most Images.classifier_b_asan "
                                                "Distribution.w Distribution.M b")}

    def test_the_eight_terms(self):
        for (kind, role), term in self.WANT.items():
            self.assertEqual(shapes.term(st(kind, role), distribution=True), term, (kind, role))

    def test_published_originals_and_the_reading(self):
        self.assertEqual(shapes.term(st("classifier-sound", "b", originals="published", reading="may-fail"),
                                     distribution=False)[1],
                         "classifies_patch_diff_sound Env.may_fail Images.plain Images.plain Images.asan Images.asan "
                         "Images.classifier_b_asan")
        self.assertEqual(shapes.term(st("classifier-sound", "a", originals="published"), distribution=False)[1],
                         "classifies_good_inputs_sound Env.alloc_forced_only Images.plain Images.asan "
                         "Images.classifier_a_asan")

    def test_maybe_without_a_distribution_is_the_empty_maybe_set(self):
        """A classifier-maybe statement is a bound with a distribution and the empty maybe set without one, so every
        caller of shapes.term and shapes.shape_name says which (facts.Statement reads it from the harness)."""
        self.assertEqual(shapes.term(st("classifier-maybe", "a"), distribution=False),
                         ("", "maybe_empty Images.classifier_a_asan"))
        for fn in (shapes.term, shapes.shape_name):
            with self.assertRaises(TypeError, msg=fn):
                fn(st("classifier-maybe", "a"))
        self.assertTrue(shapes.takes_bound("classifier-maybe", True))
        self.assertFalse(shapes.takes_bound("classifier-maybe", False))
        self.assertTrue(shapes.takes_bound("classifier-bound", False))
        self.assertFalse(shapes.takes_bound("classifier-sound", True))

    def test_shape_names(self):
        self.assertEqual(shapes.shape_name(st("classifier-sound", "a"), distribution=False),
                         "classifies_good_inputs_sound")
        self.assertEqual(shapes.shape_name(st("classifier-sound", "b"), distribution=False),
                         "classifies_patch_diff_sound")
        self.assertEqual(shapes.shape_name(st("classifier-total", "b"), distribution=False), "classifier_total3")
        self.assertEqual(shapes.shape_name(st("classifier-bound", "a"), distribution=False),
                         "classifier_rejects_at_most")

    def test_fields_a_kind_does_not_read_are_refused(self):
        for bad in (st("classifier-sound", None),
                    st("classifier-total", "c"),
                    st("classifier-sound", "b", originals=None),
                    st("classifier-sound", "a", reading=None),
                    st("classifier-sound", "a", reading="budget"),
                    st("classifier-sound", "a", originals="maybe"),
                    st("classifier-total", "a", reading="may-fail"),
                    st("classifier-maybe", "b", reading="alloc-forced-only"),
                    st("classifier-bound", "a", reading="may-fail"),
                    st("classifier-total", "b", originals="published"),
                    st("classifier-sound", "a", machine="rv64g"),
                    st("classifier-total", "a", machine="rv64gc"),
                    st("classifier-bound", "a", budgets="asan"),
                    st("classifier-maybe", "a", abort="signal"),
                    st("classifier-total", "a", env="forced_only"),
                    st("classifier-sound", "a", builds=["asan"]),
                    st("classifier-total", "a", exits="any"),
                    {"kind": "agreement", "builds": ["plain", "asan"], "reading": "may-fail", "budgets": "asan",
                     "classifier": "a"},
                    {"kind": "bound", "builds": ["plain", "asan"], "reading": "may-fail", "originals": "published"},
                    {"kind": "halts", "builds": ["plain"], "reading": "may-fail", "classifier": "a"},
                    {"kind": "halts", "builds": ["asan"], "reading": "budget", "originals": "unpatched"},
                    {"kind": "decidability", "builds": ["plain", "asan"]}):
            with self.assertRaises(shapes.ShapeError, msg=bad):
                shapes.term(bad, distribution=True)


class Names(unittest.TestCase):
    def test_the_eight_names(self):
        got = {(k, r): names.statement_name(k, ["plain", "asan-ubsan"], None, r)
               for k in shapes.CLASSIFIER_KINDS for r in ("a", "b")}
        self.assertEqual(got, {("classifier-total", "a"): "asan_ubsan_ca_total",
                               ("classifier-total", "b"): "asan_ubsan_cb_total",
                               ("classifier-sound", "a"): "asan_ubsan_ca_sound",
                               ("classifier-sound", "b"): "asan_ubsan_cb_sound",
                               ("classifier-maybe", "a"): "asan_ubsan_maybe_good",
                               ("classifier-maybe", "b"): "asan_ubsan_maybe_diff",
                               ("classifier-bound", "a"): "asan_ubsan_bound_good",
                               ("classifier-bound", "b"): "asan_ubsan_bound_diff"})

    def test_a_classifier_kind_without_its_classifier_has_no_name(self):
        with self.assertRaises(ValueError):
            names.statement_name("classifier-sound", ["plain", "asan"], "may-fail")


class Rendering(unittest.TestCase):
    def test_statements_and_readmes(self):
        with tree() as t:
            ci.with_images(t)
            self.assertEqual(errors(t), [])
            self.assertEqual(t.generate(), 0, t.last_output)
            sv = " ".join(t.read(UNIT + "/Statements.v").split())
            self.assertIn("From OssFuzzTheorems.Core Require Import Shapes ClassifierShapes.", sv)
            self.assertIn("Definition asan_ca_sound : Prop := classifies_good_inputs_sound Env.alloc_forced_only "
                          "Images.plain_original Images.asan_original Images.classifier_a_asan.", sv)
            self.assertIn("Definition asan_cb_total : Prop := classifier_total3 Images.classifier_b_asan.", sv)
            self.assertIn("Definition asan_maybe_good (b : Q) : Prop := maybe_at_most Images.classifier_a_asan "
                          "Distribution.w Distribution.M b.", sv)
            self.assertIn("Definition asan_bound_diff (b : Q) : Prop :=", sv)
            for title in ("Each classifier answers yes, no or maybe", "Each classifier is sound",
                          "How often each classifier answers maybe", "How much each classifier does not accept"):
                self.assertIn("(** ** %s *)" % title, sv)
            readme = t.read(UNIT + "/README.md")
            self.assertIn("classifier A, when it answers yes, is right that plain and ASan without the patches "
                          "agree", readme)
            self.assertIn("classifier B of the plain and ASan pair always answers yes, no or maybe", readme)

    def test_maybe_without_a_distribution_renders_the_empty_maybe_set(self):
        def no_distribution(y):
            y.pop("distribution")
            for n in [n for n, s in y["statements"].items() if s["kind"] in ("bound", "classifier-bound")]:
                del y["statements"][n]
        with tree() as t:
            ci.with_images(t, no_distribution)
            os.remove(t.path(UNIT + "/Distribution.v"))
            self.assertEqual(errors(t), [])
            self.assertEqual(t.generate(), 0, t.last_output)
            sv = " ".join(t.read(UNIT + "/Statements.v").split())
            self.assertIn("Definition asan_maybe_diff : Prop := maybe_empty Images.classifier_b_asan.", sv)

    # the root README's sentence of the kinds of statement: main's, and the one with the classifier statements' clause
    FOUR_KINDS = ("There are four kinds of statement: a build halts; a sanitizer build agrees with the plain build; the "
                  "two builds disagree on at most a fraction *b* of a stated input distribution; and the inputs on "
                  "which they agree are decidable ([docs/statements.md](docs/statements.md)). One example:")
    FIVE_KINDS = ("There are five kinds of statement: a build halts; a sanitizer build agrees with the plain build; the "
                  "two builds disagree on at most a fraction *b* of a stated input distribution; the inputs on which "
                  "they agree are decidable; and a classifier program of a pair always answers yes, no or maybe, is "
                  "right when it answers yes or no, and gives no firm answer, or an answer other than yes, on at most "
                  "a fraction *b* of the stated input distribution ([docs/statements.md](docs/statements.md)). One "
                  "example:")

    def test_the_root_readme_names_four_kinds_when_no_statement_is_a_classifier_statement(self):
        """Main's sentence, word for word, so that `oft generate --check` over main finds no file to change: in the
        fixture, which has no classifier statement, and where every classifier statement is withdrawn, as the README
        counts none."""
        def withdrawn(y):
            for name in ci.eight():
                y["statements"][name].update(status="withdrawn", reason="Withdrawn for this test.")
        with tree() as t:
            readme = t.read("README.md")
            self.assertIn(self.FOUR_KINDS, readme)
            ci.with_images(t, withdrawn)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(t.read("README.md"), readme)

    def test_the_root_readme_gives_the_classifier_statements_a_clause(self):
        with tree() as t:
            ci.with_images(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            readme = t.read("README.md")
            self.assertIn(self.FIVE_KINDS, readme)
            self.assertNotIn("There are four kinds of statement", readme)


class Rules(unittest.TestCase):
    def found(self, change=None):
        with tree() as t:
            ci.with_images(t, change)
            return [str(e) for e in errors(t)]

    def assert_found(self, text, change=None):
        """The findings of the fixture with change, which hold one that contains text."""
        got = self.found(change)
        self.assertTrue(any(text in e for e in got), "%r not in %r" % (text, got))
        return got

    def test_a_statement_names_a_listed_classifier(self):
        """Reported once, by the rule: the fingerprint, which cannot hash an image harness.yaml does not list, adds no
        finding of its own."""
        got = self.assert_found("which harness.yaml's classifiers does not list",
                                lambda y: y["classifiers"]["asan"].pop("b"))
        self.assertFalse([e for e in got if "cannot be stated" in e], got)

    def test_a_listed_classifier_with_no_sha256_and_not_withheld_is_the_schema_finding_alone(self):
        """A classifier harness.yaml lists with no sha256 and no withheld is a published image with a field missing, not
        a withheld one: the schema rule reports it, and the fingerprint, which cannot hash it, adds no finding of its
        own."""
        got = self.assert_found("classifiers.asan.b: a published image has bytes, sha256 and segments",
                                lambda y: y["classifiers"]["asan"]["b"].pop("sha256"))
        self.assertFalse([e for e in got if "cannot be stated" in e or "is withheld" in e], got)

    def test_every_classifier_and_original_is_named_by_a_statement(self):
        def drop_b(y):
            for name in ci.NAMES_B:
                del y["statements"][name]
        self.assert_found("classifiers.asan.b: no statement names this classifier", drop_b)

        def drop_sound(y):
            for name in ("asan_ca_sound", "asan_cb_sound"):
                del y["statements"][name]
        self.assert_found("originals.plain: no statement names this original", drop_sound)

    def test_a_planted_unused_binary_is_an_error(self):
        """An unused published binary cannot slip in: a classifier or an original that no statement names is a lint
        ERROR (rules.py, tree.err), not a warning."""
        def plant(y):
            y["classifiers"]["ubsan"] = {"a": ci.classifier("a", build="ubsan", sha256="ab" * 32)}
            y["originals"]["ubsan"] = {"file": names.original_file("checksum_fuzzer", "ubsan"), "bytes": 8192,
                                       "sha256": "cd" * 32, "segments": [1, 1, 1, 1]}
        got = self.found(plant)
        self.assertIn(ci.HARNESS + ": classifiers.ubsan.a: no statement names this classifier", got)
        self.assertIn(ci.HARNESS + ": originals.ubsan: no statement names this original", got)

    def test_unpatched_originals_must_be_listed(self):
        """Reported once, by the rule, as a classifier that is not listed is."""
        got = self.assert_found("names the original of the asan build, which harness.yaml's originals does not list",
                                lambda y: y["originals"].pop("asan"))
        self.assertFalse([e for e in got if "cannot be stated" in e], got)

    def test_a_withheld_classifier_withholds_its_statements(self):
        def held(y):
            rec = y["classifiers"]["asan"]["a"]
            for k in ("bytes", "sha256", "segments"):
                rec.pop(k)
            rec["withheld"] = "not-yet-published"
        self.assert_found("names a withheld build or image, so it is withheld too", held)

    def test_a_withheld_statement_is_withheld_for_the_reason_of_its_withheld_image(self):
        """A statement that names a withheld image is withheld for a reason that image is withheld for, as one that
        names a withheld build is: under not-yet-published, beside a classifier withheld for source-bundle, it is
        refused, and under source-bundle it passes."""
        def held(reason):
            def change(y):
                rec = y["classifiers"]["asan"]["b"]
                for k in ("bytes", "sha256", "segments"):
                    rec.pop(k)
                rec["withheld"] = "source-bundle"
                for name in ci.NAMES_B:
                    y["statements"][name].update(status="withheld", withheld=reason)
            return change
        got = self.found(held("not-yet-published"))
        for name in ci.NAMES_B:
            self.assertIn(HARNESS + ": statements.%s: withheld for not-yet-published, but its build or image is withheld "
                          "for source-bundle" % name, got)
        self.assertEqual(self.found(held("source-bundle")), [])

    def test_no_classifier_statement_on_an_rv64gc_pair(self):
        def gc(y):
            for s in y["statements"].values():
                if s["kind"] in ("agreement", "bound", "decidability") and s["builds"] == ["plain", "asan"]:
                    s["machine"] = "rv64gc"
        self.assert_found("the asan pair is stated with the machine rv64gc", gc)

    def test_a_classifier_bound_needs_the_distribution(self):
        self.assert_found("a classifier bound statement needs the harness's distribution",
                          lambda y: y.pop("distribution"))

    def test_published_originals_only_without_patches(self):
        bad = "which only a harness without patches may"

        def published(y):
            y.pop("originals")
            for name in ("asan_ca_sound", "asan_cb_sound"):
                y["statements"][name]["originals"] = "published"
        with tree() as t:
            ci.with_images(t, published)
            got = [str(e) for e in errors(t)]
            self.assertTrue(any(bad in e for e in got), got)
            edit(t, PROJECT, no_patches)
            self.assertEqual(errors(t), [])
            for change in (lambda y: y["library"].update(patch_count=1), lambda y: y["library"].pop("patch_count")):
                edit(t, PROJECT, change)
                self.assertTrue(any(bad in str(e) for e in errors(t)))
                edit(t, PROJECT, no_patches)
            edit(t, HARNESS, lambda y: y["source"].update(modified=True))
            self.assertTrue(any(bad in str(e) for e in errors(t)))

    def test_a_withheld_classifier_and_its_withheld_statements_have_no_fingerprint(self):
        def held(y):
            rec = y["classifiers"]["asan"]["b"]
            for k in ("bytes", "sha256", "segments"):
                rec.pop(k)
            rec["withheld"] = "not-yet-published"
            for name in ci.NAMES_B:
                y["statements"][name].update(status="withheld", withheld="not-yet-published")
        with tree() as t:
            ci.with_images(t, held)
            self.assertEqual(errors(t), [])
            prints = {s.name: s.fingerprint for s in facts.load(t.root).statements()}
            self.assertEqual([prints[n] for n in ci.NAMES_B], [None] * 4)
            self.assertIsNotNone(prints["asan_ca_sound"])

    def test_a_classifier_statement_takes_no_instance(self):
        """shapes.instance_type has no classifier form: lint refuses an instance on a classifier statement, and
        instance_type refuses one rather than give it the type of another kind's shape.  So a project whose
        statements must carry an instance (shapes.REQUIRED) needs none on a classifier statement
        (lint.check_instances leaves those out)."""
        inst = {"file": "in.bin", "sha256": "0" * 64, "bytes": 2, "path": "reaches-harness"}
        self.assert_found("statements.asan_ca_total: a classifier-total statement has no instance form",
                          lambda y: y["statements"]["asan_ca_total"].update(instance=inst))
        for kind in shapes.CLASSIFIER_KINDS:
            with self.assertRaisesRegex(shapes.ShapeError, "a %s statement has no instance form" % kind):
                shapes.instance_type(dict(st(kind, "a"), instance=inst))
        with tree() as t, mock.patch.object(shapes, "REQUIRED", ("zlib",)):
            ci.with_images(t)
            found = [f.msg for f in lint.check_instances(facts.load(t.root))]
        self.assertIn("statements.asan_agrees.instance: required for project zlib", found)
        self.assertFalse([m for m in found if any("statements.%s." % n in m for n in ci.eight())], found)

    def test_a_classifier_statement_takes_no_witness(self):
        """A witness is a run of one build, which shows no classifier's answer: witness_problems refuses one on a
        classifier statement, saying so, once (lint reports it once), and reads a statement with no reading."""
        wt = {"build": "asan", "input_hex": "00", "refused": {"call": "mmap", "position": 1, "bytes": 4096},
              "outcome": "abort", "runner": "qemu-riscv64 10.0.11"}
        refused = ("a classifier-total statement has no witness form, so it takes no witness: a witness is a run of "
                   "one build, which shows no classifier's answer")
        got = self.assert_found("statements.asan_ca_total: " + refused,
                                lambda y: y["statements"]["asan_ca_total"].update(status="witnessed-false", witness=wt))
        self.assertEqual([e for e in got if "statements.asan_ca_total:" in e and "witness" in e],
                         [HARNESS + ": statements.asan_ca_total: " + refused])
        self.assertEqual(rules.witness_problems(dict(st("classifier-total", "a"), witness=wt), {"builds": {}}),
                         [refused])

    def test_a_classifier_statement_with_a_twin_is_refused_for_its_twin(self):
        """A twin is for a halts or an agreement statement (names.TWIN_KIND): a classifier statement with one gets the
        name its fields give and is refused for the twin, not as one that names no classifier."""
        self.assertEqual(names.statement_name("classifier-total", ["plain", "asan"], None, "a", "any-exit"),
                         "asan_ca_total_any_exit")

        def twin(y):
            y["statements"]["asan_ca_total_any_exit"] = dict(y["statements"].pop("asan_ca_total"), twin="any-exit")
        got = self.found(twin)
        self.assertIn(HARNESS + ": statements.asan_ca_total_any_exit: twin any-exit is for halts statements", got)
        self.assertFalse(any("names its classifier" in e for e in got), got)

    def test_the_shape_field_of_a_maybe_statement_follows_the_distribution(self):
        """A classifier-maybe statement's shape is maybe_at_most in a harness with a distribution and maybe_empty in
        one without, as its term is: the redundant `shape` field is compared with that one."""
        def shape(name):
            return lambda y: y["statements"]["asan_maybe_good"].update(shape=name)
        self.assertEqual(self.found(shape("maybe_at_most")), [])
        self.assertIn(HARNESS + ": statements.asan_maybe_good: shape is maybe_empty, but its fields give maybe_at_most",
                      self.found(shape("maybe_empty")))
        self.assertEqual(shapes.shape_name(st("classifier-maybe", "a"), distribution=True), "maybe_at_most")
        self.assertEqual(shapes.shape_name(st("classifier-maybe", "a"), distribution=False), "maybe_empty")


class Fingerprints(unittest.TestCase):
    def prints(self, t):
        return {s.id: s.fingerprint for s in facts.load(t.root).statements()}

    def test_the_shapes_file_moves_the_classifier_statements_alone(self):
        with tree() as t:
            ci.with_images(t)
            a = self.prints(t)
            t.write(ci.SHAPES, t.read(ci.SHAPES) + "Definition extra := 0.\n")
            b = self.prints(t)
            self.assertEqual(sorted(k for k in a if a[k] != b[k]), sorted(SID + n for n in ci.eight()))

    def test_the_classifier_and_the_originals_are_hashed(self):
        with tree() as t:
            ci.with_images(t)
            a = self.prints(t)
            edit(t, HARNESS, lambda y: y["classifiers"]["asan"]["b"].update(sha256="ee" * 32))
            b = self.prints(t)
            self.assertEqual(sorted(k for k in a if a[k] != b[k]), sorted(SID + n for n in ci.NAMES_B))
            edit(t, HARNESS, lambda y: y["originals"]["plain"].update(sha256="ff" * 32))
            c = self.prints(t)
            self.assertEqual(sorted(k for k in b if b[k] != c[k]), [SID + "asan_ca_sound", SID + "asan_cb_sound"])

    def test_the_distribution_is_hashed_for_the_maybe_and_bound_statements(self):
        with tree() as t:
            ci.with_images(t)
            a = self.prints(t)
            t.write(UNIT + "/Distribution.v", t.read(UNIT + "/Distribution.v") + "\nDefinition extra := 0.\n")
            b = self.prints(t)
            moved = {k for k in a if a[k] != b[k] and k.startswith(SID + "asan_")}
            self.assertLessEqual({SID + n for n in ("asan_maybe_good", "asan_maybe_diff", "asan_bound_good",
                                                    "asan_bound_diff")}, moved)
            self.assertFalse({SID + n for n in ("asan_ca_sound", "asan_cb_total")} & moved)


class Proofs(unittest.TestCase):
    def test_a_maybe_or_classifier_bound_proof_names_its_bound_and_the_wrapper_applies_it(self):
        for name in ("asan_maybe_good", "asan_bound_diff"):
            with tree() as t:
                ci.with_images(t)
                add_proof(t, SID + name)
                self.assertTrue(any("a bound proof names its bound" in str(e) for e in errors(t)), name)
                edit(t, "proofs/%s%s/proof.yaml" % (SID, name), lambda y: y.update(bound="1/2"))
                got = errors(t)
                self.assertFalse(any("bound" in str(e) for e in got), got)
                s = next(x for x in facts.load(t.root).statements() if x.name == name)
                pd = mock.Mock(refutes=False, data={"bound": "1/2"})
                self.assertEqual(check.wrapper_args(s, pd), " (1 # 2)")
                self.assertEqual(check.wrapper_args(s, mock.Mock(refutes=True, data={})), "")

    def test_a_sound_proof_names_no_bound(self):
        with tree() as t:
            ci.with_images(t)
            add_proof(t, SID + "asan_ca_sound")
            edit(t, "proofs/%sasan_ca_sound/proof.yaml" % SID, lambda y: y.update(bound="1/2"))
            self.assertTrue(any("only a bound proof names a bound" in str(e) for e in errors(t)))

    def test_a_maybe_or_classifier_bound_proof_names_a_bound_below_1(self):
        """A classifier-bound statement, and a classifier-maybe statement with a distribution, at b = 1 holds of every
        program, as a bound statement does (each Statements.v says so): a proof of one at b = 1 is refused, with the
        statement's kind named; at b = 1/2 it is not."""
        for name, kind in (("asan_maybe_good", "classifier-maybe"), ("asan_bound_diff", "classifier-bound")):
            with self.subTest(name=name), tree() as t:
                ci.with_images(t)
                add_proof(t, SID + name)
                proof = "proofs/%s%s/proof.yaml" % (SID, name)
                edit(t, proof, lambda y: y.update(bound="1"))
                want = ("a %s proof names a bound below 1: %s%s at b = 1 holds of every program, as its Statements.v "
                        "says" % (kind, SID, name))
                got = [e for e in errors(t) if "bound" in e]
                self.assertEqual(len(got), 1, got)
                self.assertTrue(got[0].endswith("%s: %s" % (proof, want)), got)
                edit(t, proof, lambda y: y.update(bound="1/2"))
                got = errors(t)
                self.assertFalse(any("bound" in str(e) for e in got), got)


class Revisions(unittest.TestCase):
    def test_a_distribution_render_change_re_renders_the_maybe_and_bound_statements(self):
        with tree() as t:
            ci.with_images(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(revisions.rerendered(facts.load(t.root)), set())
            with mock.patch.object(claims, "distribution_v", return_value="Definition changed := 0.\n"):
                got = revisions.rerendered(facts.load(t.root))
            self.assertLessEqual({SID + n for n in ("asan_bound_good", "asan_bound_diff", "asan_maybe_good",
                                                    "asan_maybe_diff")}, got)
            self.assertFalse({SID + "asan_ca_sound", SID + "asan_ca_total"} & got)


if __name__ == "__main__":
    unittest.main()
