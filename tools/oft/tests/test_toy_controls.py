"""The falsifiability controls (tests/toy/ebreak/) say what the generator says, for every choice it makes.

tests/toy/ebreak/Statements.v is written by hand.  This test renders each of its statements with shapes.term and
shapes.templates, requires the file to hold exactly that text, requires every choice those functions make (each halts
reading and exit set, each agreement shape and budget pair, each bound and decidability reading and machine, each
classifier template, each classifier statement's kind, classifier, reading and originals, with and without an input
distribution) to have a statement there, and requires each control statement to have its Refutation.v under
tests/proofs/toy/ebreak/ and nothing else to be there.  So a change to shapes.py that adds or moves a choice, or a
deleted control, fails here.

A classifier-sound statement is written with its classifier a parameter [C], in the place of the classifier image the
generator names: the toy's classifiers give no answer, so they are sound for every property, and the control applies
the statement to a classifier that always answers yes (A, [_accept_all]) or always no (B, [_reject_all]).
"""
import os
import re
import unittest

from oft import names, shapes

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
STATEMENTS = os.path.join(ROOT, "tests", "toy", "ebreak", "Statements.v")
PROOFS = os.path.join(ROOT, "tests", "proofs", "toy", "ebreak")
# tests/ is beside tools/, not under it; tools/oft alone, as the runner image carries it, has no tests/toy, and this
# class says so instead of ending setUpClass in FileNotFoundError (images.yml run 42574457306, 2026-11-09).
HAVE_STATEMENTS = os.path.exists(STATEMENTS)
NO_STATEMENTS = "no tests/toy/ebreak/Statements.v: tools/oft without the checkout around it"
PAIR = ["plain", "asan"]
EXITS = {"any": "any", "ok_or_refused": [0, 2], "rejected": [0, 2, shapes.REJECTED]}
BUDGET_NAMES = {"standard": "standard", "asan": "asan"}
ENV_NAMES = {"may-fail": "may_fail", "alloc-forced-only": "alloc_forced_only"}
ORIGINALS = ("published", "unpatched")
# The classifier a classifier-sound control applies its statement to: one that answers yes on an input where the
# originals disagree (A), one that answers no on an input where each build agrees with its original (B).
SOUND_CONTROL = {"a": ("_accept_all", "Images.always_yes"), "b": ("_reject_all", "Images.always_no")}


def statements():
    """[(name, fields, control)]: every statement of Statements.v rendered by shapes.term, and the name of the
    statement that is its refuted control (None for the decidability statements, which are true for the pair)."""
    out = []
    for key, exits in EXITS.items():
        for reading, stem in (("budget", "plain_halts_"), ("may-fail", "plain_halts_may_fail_")):
            name = stem + key
            out.append((name, {"kind": "halts", "builds": ["plain"], "reading": reading, "exits": exits}, name))
    for (reading, abort, machine), shape in sorted(shapes.AGREEMENT.items()):
        for budgets in shapes.BUDGETS:
            name = "asan_%s_%s" % (shape, BUDGET_NAMES[budgets])
            fields = {"kind": "agreement", "builds": PAIR, "reading": reading, "abort": abort, "machine": machine,
                      "budgets": budgets}
            out.append((name, fields, name))
    for machine in ("rv64g", "rv64gc"):
        gc = "_rv64gc" if machine == "rv64gc" else ""
        for reading in shapes.ENV:
            name = "asan_disagrees_at_most%s_%s" % (gc, ENV_NAMES[reading])
            out.append((name, {"kind": "bound", "builds": PAIR, "reading": reading, "machine": machine},
                        name + "_below_1"))
            name = "asan_agreement_decidable%s_%s" % (gc, ENV_NAMES[reading])
            out.append((name, {"kind": "decidability", "builds": PAIR, "reading": reading, "machine": machine}, None))
    return out


def classifier_templates():
    """[(name, params, body, control)]: the classifier problem of each reading and machine, as shapes.templates
    renders it for an ASan build."""
    out = []
    for machine in ("rv64g", "rv64gc"):
        gc = "_rv64gc" if machine == "rv64gc" else ""
        for reading in shapes.ENV:
            (tname, params, body), = [t for t in shapes.templates(reading, "asan", False, machine)
                                      if t[0] == "asan_classifies"]
            name = "asan_classifies%s_%s" % (gc, ENV_NAMES[reading])
            out.append((name, params, body, name + "_accept_all"))
    return out


def below_1(name):
    return "exists b : Q, (b < 1)%%Q /\\ %s b" % name


def classifier_statements():
    """[(name, params, body, control, control_body)]: every classifier statement of Statements.v, for each kind of
    shapes.CLASSIFIER_KINDS and each classifier, rendered by shapes.term with the toy's distribution and, for
    classifier-maybe, also without one (the empty maybe set, `<name>_no_distribution`); and the statement that is its
    refuted control, with that statement's body (control is name, and control_body None, where the statement is its
    own control).  A classifier-sound statement is named after its reading and originals, and has the classifier
    image the generator names replaced by the parameter C."""
    out = []
    for kind in shapes.CLASSIFIER_KINDS:
        for role in ("a", "b"):
            name = names.statement_name(kind, PAIR, None, classifier=role)
            fields = {"kind": kind, "builds": PAIR, "classifier": role}
            if kind == "classifier-total":
                out.append((name,) + shapes.term(fields, distribution=True) + (name, None))
            elif kind == "classifier-sound":
                image = " " + shapes.classifier_image(role, PAIR[1])
                suffix, classifier = SOUND_CONTROL[role]
                for reading in shapes.ENV:
                    for originals in ORIGINALS:
                        n = "%s_%s_%s" % (name, ENV_NAMES[reading], originals)
                        params, body = shapes.term(dict(fields, reading=reading, originals=originals),
                                                   distribution=True)
                        head, sep, tail = body.rpartition(image)
                        if sep and not tail and not params:
                            params, body = " (C : Image)", head + " C"
                        out.append((n, params, body, n + suffix, "%s %s" % (n, classifier)))
            elif kind == "classifier-maybe":
                out.append((name,) + shapes.term(fields, distribution=True) + (name + "_below_1", below_1(name)))
                n = name + "_no_distribution"
                out.append((n,) + shapes.term(fields, distribution=False) + (n, None))
            elif kind == "classifier-bound":
                out.append((name,) + shapes.term(fields, distribution=True) + (name + "_below_1", below_1(name)))
            else:
                raise AssertionError("no control for the classifier kind %s" % kind)
    return out


def definition(name, params, body):
    return "Definition %s%s : Prop :=\n  %s.\n" % (name, params, body)


@unittest.skipUnless(HAVE_STATEMENTS, NO_STATEMENTS)
class ToyControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with open(STATEMENTS, encoding="utf-8") as f:
            cls.text = f.read()

    def test_each_statement_is_the_generators_rendering(self):
        for name, fields, _ in statements():
            with self.subTest(name=name):
                params, body = shapes.term(fields, distribution=True)
                self.assertIn(definition(name, params, body), self.text)
        for name, params, body, _ in classifier_templates():
            with self.subTest(name=name):
                self.assertIn(definition(name, params, body), self.text)
        for name, params, body, _, _ in classifier_statements():
            with self.subTest(name=name):
                self.assertIn(definition(name, params, body), self.text)

    def test_each_parameterised_statement_has_its_control(self):
        for name, fields, control in statements():
            if fields["kind"] == "bound":
                with self.subTest(name=name):
                    self.assertIn(definition(control, "", below_1(name)), self.text)
        for name, _, _, control in classifier_templates():
            with self.subTest(name=name):
                self.assertIn(definition(control, "", "%s Images.asan" % name), self.text)
        for name, params, _, control, control_body in classifier_statements():
            with self.subTest(name=name):
                if control_body is None:
                    self.assertEqual((control, params), (name, ""))
                else:
                    self.assertIn(definition(control, "", control_body), self.text)

    def test_every_choice_of_the_generator_has_a_statement(self):
        rendered = {shapes.term(f, distribution=True)[1].split(" Images.")[0] for _, f, _ in statements()}
        for (reading, abort, machine), shape in shapes.AGREEMENT.items():
            env = (shapes.ENV[reading] + " ") if reading == "alloc-forced-only" else ""
            for budgets in shapes.BUDGETS:
                mod = shapes.BUDGETS[budgets][0]
                self.assertIn("%s %s%s.lim_source %s.lim_target" % (shape, env, mod, mod), rendered)
        for key in shapes.EXIT_SETS:
            ex = shapes.EXIT_SETS[key]
            self.assertIn("halts_within_budget %s %s" % (shapes.HALTS_BUDGET[0], ex), rendered)
            self.assertIn("halts_may_fail %s" % ex, rendered)
        for reading in shapes.ENV:
            for gc in ("", "_rv64gc"):
                self.assertIn("disagrees_at_most%s %s Distribution.w Distribution.M" % (gc, shapes.ENV[reading]),
                              rendered)
                self.assertIn("agreement_decidable%s %s" % (gc, shapes.ENV[reading]), rendered)
        self.assertEqual(len(classifier_templates()), len(shapes.ENV) * 2)
        # every classifier term the generator writes for the pair, written here by hand as the halts and agreement
        # terms above are, with the classifier of a classifier-sound one the parameter C, is the body of a statement
        # here
        bodies = {body for _, _, body, _, _ in classifier_statements()}
        for role in ("a", "b"):
            c = "Images.classifier_%s_asan" % role
            for body in ("classifier_total3 %s" % c, "maybe_empty %s" % c,
                         "maybe_at_most %s Distribution.w Distribution.M b" % c,
                         "classifier_rejects_at_most %s Distribution.w Distribution.M b" % c):
                with self.subTest(classifier=role, body=body):
                    self.assertIn(body, bodies)
        for reading in shapes.ENV:
            env = shapes.ENV[reading]
            for body in ("classifies_good_inputs_sound %s Images.plain Images.asan C" % env,
                         "classifies_good_inputs_sound %s Images.plain_original Images.asan_original C" % env,
                         "classifies_patch_diff_sound %s Images.plain Images.plain Images.asan Images.asan C" % env,
                         "classifies_patch_diff_sound %s Images.plain_original Images.plain Images.asan_original "
                         "Images.asan C" % env):
                with self.subTest(reading=reading, body=body):
                    self.assertIn(body, bodies)

    def test_the_file_has_no_other_statement(self):
        names_here = set(re.findall(r"^Definition (\w+)", self.text, re.M))
        expected = {n for n, _, _ in statements()} | {c for _, _, c in statements() if c}
        expected |= {n for n, _, _, _ in classifier_templates()} | {c for _, _, _, c in classifier_templates()}
        expected |= {n for n, _, _, _, _ in classifier_statements()} | {c for _, _, _, c, _ in classifier_statements()}
        self.assertEqual(names_here, expected)

    def test_each_control_has_its_refutation_and_nothing_else_is_there(self):
        controls = {c for _, _, c in statements() if c} | {c for _, _, _, c in classifier_templates()}
        controls |= {c for _, _, _, c, _ in classifier_statements()}
        for c in sorted(controls):
            with self.subTest(control=c):
                self.assertTrue(os.path.isfile(os.path.join(PROOFS, c, "Refutation.v")))
        self.assertEqual(set(os.listdir(PROOFS)), controls)


if __name__ == "__main__":
    unittest.main()
