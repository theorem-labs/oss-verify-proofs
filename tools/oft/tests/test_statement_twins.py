"""Twins (harness.yaml `twin`; docs/statements.md, "Twins"): a second statement of a harness beside its first, named
for the one way it differs from it, so that a harness can carry a statement beside one with the same kind, builds and
reading without either taking the other's name."""
import re
import unittest

from oft import facts, generate, names
from oft.tests.helpers import edit, errors, tree

HARNESS = "projects/zlib/checksum_fuzzer/harness.yaml"
UNIT = "projects/zlib/checksum_fuzzer"
SID = "zlib/checksum_fuzzer/"

# beside the fixture's plain_halts (exits [0, 2]) and asan_agrees (read may-fail)
HALTS_TWIN = {"kind": "halts", "builds": ["plain"], "reading": "budget", "exits": "any", "twin": "any-exit",
              "status": "open"}
AGREES_TWIN = {"kind": "agreement", "builds": ["plain", "asan"], "reading": "alloc-forced-only", "budgets": "asan",
               "twin": "alloc-forced-only", "status": "open"}


def with_twins(y):
    y["statements"]["plain_halts_any_exit"] = dict(HALTS_TWIN)
    y["statements"]["asan_agrees_alloc_forced_only"] = dict(AGREES_TWIN)


class Names(unittest.TestCase):
    def test_a_twin_is_named_after_its_first(self):
        self.assertEqual(names.statement_name("halts", ["plain"], "budget", twin="any-exit"), "plain_halts_any_exit")
        self.assertEqual(names.statement_name("halts", ["asan-ubsan"], "budget", twin="any-exit"),
                         "asan_ubsan_halts_any_exit")
        self.assertEqual(names.statement_name("agreement", ["plain", "asan"], "alloc-forced-only",
                                              twin="alloc-forced-only"), "asan_agrees_alloc_forced_only")
        self.assertEqual(names.statement_name("agreement", ["plain", "ubsan"], "alloc-forced-only",
                                              twin="alloc-forced-only"), "ubsan_agrees_alloc_forced_only")

    def test_without_a_twin_every_name_is_the_one_it_was(self):
        """The name of every statement that has no twin is unchanged: the names before twins, by kind and reading."""
        want = {("halts", ("plain",), "budget"): "plain_halts",
                ("halts", ("ubsan",), "may-fail"): "ubsan_halts_may_fail",
                ("agreement", ("plain", "asan"), "may-fail"): "asan_agrees",
                ("agreement", ("plain", "asan"), "alloc-forced-only"): "asan_agrees",
                ("bound", ("plain", "asan-ubsan"), "alloc-forced-only"): "asan_ubsan_disagrees_at_most",
                ("decidability", ("plain", "ubsan"), "may-fail"): "ubsan_agreement_decidable"}
        for (kind, builds, reading), name in want.items():
            self.assertEqual(names.statement_name(kind, builds, reading), name)
            self.assertEqual(names.statement_name(kind, builds, reading, twin=None), name)

    def test_no_twin_takes_the_name_of_a_statement_without_one(self):
        plain = {names.statement_name(k, b, r) for k in ("halts",) for b in [(x,) for x in names.BUILD_IDENT]
                 for r in ("budget", "may-fail")}
        plain |= {names.statement_name(k, ("plain", x), r) for k in ("agreement", "bound", "decidability")
                  for x in names.BUILD_IDENT if x != "plain" for r in ("may-fail", "alloc-forced-only")}
        twins = [names.statement_name("halts", (x,), r, twin="any-exit") for x in names.BUILD_IDENT
                 for r in ("budget", "may-fail")]
        twins += [names.statement_name("agreement", ("plain", x), "alloc-forced-only", twin="alloc-forced-only")
                  for x in names.BUILD_IDENT if x != "plain"]
        self.assertEqual(len(set(twins)), len(twins))
        self.assertEqual(plain & set(twins), set())

    def test_the_builds_of_a_twin_from_its_name(self):
        self.assertEqual(names.statement_builds("plain_halts_any_exit"), ("plain",))
        self.assertEqual(names.statement_builds("asan_ubsan_halts_any_exit"), ("asan-ubsan",))
        self.assertEqual(names.statement_builds("asan_agrees_alloc_forced_only"), ("plain", "asan"))
        self.assertEqual(names.statement_builds("asan_ubsan_agrees_alloc_forced_only"), ("plain", "asan-ubsan"))
        self.assertEqual(names.statement_builds("plain_halts"), ("plain",))
        self.assertEqual(names.statement_builds("asan_agrees"), ("plain", "asan"))
        self.assertIsNone(names.statement_builds("plain_halts_any"))


class Rules(unittest.TestCase):
    def found(self, change):
        with tree() as t:
            edit(t, HARNESS, change)
            return [str(e) for e in errors(t)]

    def assert_found(self, text, change):
        got = self.found(change)
        self.assertTrue(any(text in e for e in got), "%r not in %r" % (text, got))

    def test_the_two_twins_beside_their_firsts_are_clean(self):
        self.assertEqual(self.found(with_twins), [])

    def test_a_twin_under_its_first_name_or_a_first_under_a_twin_name(self):
        def twin_named_first(y):
            with_twins(y)
            del y["statements"]["plain_halts_any_exit"]
            y["statements"]["plain_halts_two"] = dict(HALTS_TWIN)
        self.assert_found("statements.plain_halts_two: its fields give the name plain_halts_any_exit",
                          twin_named_first)

        def no_twin_field(y):
            with_twins(y)
            del y["statements"]["asan_agrees_alloc_forced_only"]["twin"]
        self.assert_found("statements.asan_agrees_alloc_forced_only: its fields give the name asan_agrees",
                          no_twin_field)

    def test_a_twin_of_the_wrong_kind(self):
        def wrong(y):
            with_twins(y)
            y["statements"]["plain_halts_any_exit"]["twin"] = "alloc-forced-only"
            y["statements"]["plain_halts_alloc_forced_only"] = y["statements"].pop("plain_halts_any_exit")
        self.assert_found("twin alloc-forced-only is for agreement statements", wrong)

        def wrong_agreement(y):
            with_twins(y)
            y["statements"]["asan_agrees_alloc_forced_only"]["twin"] = "any-exit"
            y["statements"]["asan_agrees_any_exit"] = y["statements"].pop("asan_agrees_alloc_forced_only")
        self.assert_found("twin any-exit is for halts statements", wrong_agreement)

    def test_a_twin_without_its_first(self):
        def no_first(y):
            with_twins(y)
            del y["statements"]["plain_halts"]
        self.assert_found("a twin goes with its first statement plain_halts, which harness.yaml does not list",
                          no_first)

        def no_first_agreement(y):
            with_twins(y)
            for n in ("asan_agrees", "asan_disagrees_at_most", "asan_agreement_decidable"):
                del y["statements"][n]
        self.assert_found("a twin goes with its first statement asan_agrees, which harness.yaml does not list",
                          no_first_agreement)

    def test_an_any_exit_twin_allows_any_status_beside_a_finite_set(self):
        def finite(y):
            with_twins(y)
            y["statements"]["plain_halts_any_exit"]["exits"] = [0, 2]
        self.assert_found("twin any-exit allows any exit status (exits: any), beside its first plain_halts", finite)

        def first_any(y):
            with_twins(y)
            y["statements"]["plain_halts"]["exits"] = "any"
        self.assert_found("twin any-exit allows any exit status (exits: any), beside its first plain_halts",
                          first_any)

    def test_an_alloc_forced_only_twin_is_read_so_beside_may_fail(self):
        def may_fail(y):
            with_twins(y)
            y["statements"]["asan_agrees_alloc_forced_only"]["reading"] = "may-fail"
        self.assert_found("twin alloc-forced-only is read alloc-forced-only, beside its first asan_agrees", may_fail)

        def first_alloc(y):
            with_twins(y)
            y["statements"]["asan_agrees"]["reading"] = "alloc-forced-only"
        self.assert_found("twin alloc-forced-only is read alloc-forced-only, beside its first asan_agrees",
                          first_alloc)

    def test_an_unknown_twin_is_refused(self):
        def unknown(y):
            with_twins(y)
            y["statements"]["plain_halts_any_exit"]["twin"] = "any-status"
        got = self.found(unknown)
        self.assertTrue(any("twin" in e and "any-status" in e for e in got), got)

    def test_a_halts_twin_with_no_reading_is_a_finding(self):
        """`reading` is optional in the schema: a twin without one gets the finding shapes.term gives it, and the twin
        rule reads the missing reading as none and raises nothing."""
        def halts_twin(y):
            with_twins(y)
            del y["statements"]["plain_halts_any_exit"]["reading"]
        self.assert_found("statements.plain_halts_any_exit: a halts statement has a reading", halts_twin)

    def test_an_alloc_forced_only_twin_whose_first_has_no_reading_is_a_finding(self):
        """A first without a reading gets the finding shapes.term gives it, and its alloc-forced-only twin is refused
        as one beside a first not read may-fail, with nothing raised."""
        def agreement_first(y):
            with_twins(y)
            del y["statements"]["asan_agrees"]["reading"]
        got = self.found(agreement_first)
        self.assertTrue(any(e.startswith(HARNESS + ": statements.asan_agrees: ") and e.endswith("has a reading")
                            for e in got), got)
        self.assertIn(HARNESS + ": statements.asan_agrees_alloc_forced_only: twin alloc-forced-only is read "
                      "alloc-forced-only, beside its first asan_agrees, which is read may-fail", got)


class Rendering(unittest.TestCase):
    def test_statements_v_states_each_twin_by_its_fields(self):
        """Each twin's term is its first's with the one difference its twin names, and it comes after the statements
        of its kind and reading that are not twins."""
        with tree() as t:
            edit(t, HARNESS, with_twins)
            self.assertEqual(t.generate(), 0, t.last_output)
            sv = " ".join(t.read(UNIT + "/Statements.v").split())
            first_h = ("Definition plain_halts : Prop := halts_within_budget Budgets.Standard.lim_source "
                       "Exits.ok_or_refused Images.plain.")
            twin_h = ("Definition plain_halts_any_exit : Prop := halts_within_budget Budgets.Standard.lim_source "
                      "Exits.any Images.plain.")
            first_a = ("Definition asan_agrees : Prop := agrees Budgets.Asan.lim_source Budgets.Asan.lim_target "
                       "Images.plain Images.asan.")
            twin_a = ("Definition asan_agrees_alloc_forced_only : Prop := agrees_in Env.alloc_forced_only "
                      "Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan.")
            for d in (first_h, twin_h, first_a, twin_a):
                self.assertIn(d, sv)
            order = re.findall(r"Definition (\w+)", sv)
            self.assertLess(order.index("asan_ubsan_halts"), order.index("plain_halts_any_exit"))
            self.assertLess(order.index("plain_halts_any_exit"), order.index("plain_halts_may_fail"))
            self.assertLess(order.index("asan_ubsan_agrees"), order.index("asan_agrees_alloc_forced_only"))
            self.assertIn("every execution of the plain build exits with any status", sv)
            readme = t.read(UNIT + "/README.md")
            self.assertIn("| `plain_halts_any_exit` |", readme)
            self.assertIn("| `asan_agrees_alloc_forced_only` |", readme)

    def test_without_twins_the_order_is_the_one_it_was(self):
        def old_key(s):
            b = s.data["builds"][-1]
            rank = generate.schema.BUILDS.index(b) if s.kind == "halts" else generate.PAIR_ORDER.index(b)
            return generate.KIND_ORDER[s.kind], generate.READING_ORDER[s.data["reading"]], rank
        with tree() as t:
            loaded = facts.load(t.root)
            hs = list(loaded.harnesses())
            self.assertTrue(hs)
            for h in hs:
                self.assertEqual([s.name for s in generate._order(h)],
                                 [s.name for s in sorted(h.statements.values(), key=old_key)], h.name)


class Fingerprints(unittest.TestCase):
    def test_a_twin_moves_no_other_fingerprint(self):
        with tree() as t:
            before = {s.id: s.fingerprint for s in facts.load(t.root).statements()}
            edit(t, HARNESS, with_twins)
            after = {s.id: s.fingerprint for s in facts.load(t.root).statements()}
        self.assertTrue(before[SID + "plain_halts"])
        for sid, fp in before.items():
            self.assertEqual(after[sid], fp, sid)
        self.assertEqual(set(after) - set(before), {SID + "plain_halts_any_exit", SID + "asan_agrees_alloc_forced_only"})
        self.assertNotEqual(after[SID + "plain_halts_any_exit"], after[SID + "plain_halts"])
        self.assertNotEqual(after[SID + "asan_agrees_alloc_forced_only"], after[SID + "asan_agrees"])


if __name__ == "__main__":
    unittest.main()
