"""The falsifiability controls (tests/toy/ebreak/) say what the generator says, for every choice it makes.

tests/toy/ebreak/Statements.v is written by hand.  This test renders each of its statements with shapes.term and
shapes.templates, requires the file to hold exactly that text, requires every choice those functions make (each halts
reading and exit set, each agreement shape and budget pair, each bound and decidability reading and machine, each
classifier template) to have a statement there, and requires each control statement to have its Refutation.v under
tests/proofs/toy/ebreak/ and nothing else to be there.  So a change to shapes.py that adds or moves a choice, or a
deleted control, fails here.
"""
import os
import re
import unittest

from oft import shapes

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
STATEMENTS = os.path.join(ROOT, "tests", "toy", "ebreak", "Statements.v")
PROOFS = os.path.join(ROOT, "tests", "proofs", "toy", "ebreak")
PAIR = ["plain", "asan"]
EXITS = {"any": "any", "ok_or_refused": [0, 2], "rejected": [0, 2, shapes.REJECTED]}
BUDGET_NAMES = {"standard": "standard", "asan": "asan"}
ENV_NAMES = {"may-fail": "may_fail", "alloc-forced-only": "alloc_forced_only"}


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


def definition(name, params, body):
    return "Definition %s%s : Prop :=\n  %s.\n" % (name, params, body)


class ToyControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with open(STATEMENTS, encoding="utf-8") as f:
            cls.text = f.read()

    def test_each_statement_is_the_generators_rendering(self):
        for name, fields, _ in statements():
            with self.subTest(name=name):
                params, body = shapes.term(fields)
                self.assertIn(definition(name, params, body), self.text)
        for name, params, body, _ in classifier_templates():
            with self.subTest(name=name):
                self.assertIn(definition(name, params, body), self.text)

    def test_each_parameterised_statement_has_its_control(self):
        for name, fields, control in statements():
            if fields["kind"] == "bound":
                with self.subTest(name=name):
                    self.assertIn(definition(control, "", "exists b : Q, (b < 1)%%Q /\\ %s b" % name), self.text)
        for name, _, _, control in classifier_templates():
            with self.subTest(name=name):
                self.assertIn(definition(control, "", "%s Images.asan" % name), self.text)

    def test_every_choice_of_the_generator_has_a_statement(self):
        rendered = {shapes.term(f)[1].split(" Images.")[0] for _, f, _ in statements()}
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

    def test_the_file_has_no_other_statement(self):
        names = set(re.findall(r"^Definition (\w+)", self.text, re.M))
        expected = {n for n, _, _ in statements()} | {c for _, _, c in statements() if c}
        expected |= {n for n, _, _, _ in classifier_templates()} | {c for _, _, _, c in classifier_templates()}
        self.assertEqual(names, expected)

    def test_each_control_has_its_refutation_and_nothing_else_is_there(self):
        controls = {c for _, _, c in statements() if c} | {c for _, _, _, c in classifier_templates()}
        for c in sorted(controls):
            with self.subTest(control=c):
                self.assertTrue(os.path.isfile(os.path.join(PROOFS, c, "Refutation.v")))
        self.assertEqual(set(os.listdir(PROOFS)), controls)


if __name__ == "__main__":
    unittest.main()
