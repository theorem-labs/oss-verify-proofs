"""pack.py: how oft plan deals units into check jobs, and how many CPUs a job's check gets."""
import math
import os
import random
import tempfile
import unittest

from oft import pack
from oft.tests.helpers import REPO




class Shards(unittest.TestCase):
    def test_the_longest_units_go_to_separate_jobs_and_the_rest_fill_every_job(self):
        times = {"a/1": 200, "a/2": 150, "a/3": 100, "a/4": 90}
        table = {u: (10, 30.0, 16) for u in times}
        cheap = ["c/%02d" % i for i in range(10)]
        got = pack.shards(list(times) + cheap, 3, set(times), table, times)
        # longest first, each to the least-loaded job: 200 | 150 | 100 + 90
        self.assertEqual([[u for u in s if u.startswith("a/")] for s in got], [["a/1"], ["a/2"], ["a/3", "a/4"]])
        self.assertEqual(sorted(u for s in got for u in s), sorted(list(times) + cheap))
        self.assertTrue(all(got))
        self.assertTrue(all(s == sorted(s) for s in got))

    def test_equal_times_give_no_job_more_than_its_share_of_proved_units(self):
        for p, n in ((7, 20), (20, 20), (45, 20), (61, 7)):
            with self.subTest(p=p, n=n):
                proved = ["p/%03d" % i for i in range(p)]
                got = pack.shards(proved + ["r/%04d" % i for i in range(500)], n, set(proved), {},
                                  {u: 10 for u in proved})
                self.assertLessEqual(max(sum(u in proved for u in s) for s in got), math.ceil(p / n))

    def test_the_jobs_depend_on_the_units_not_on_their_order(self):
        times = {"a/%d" % i: 10 * (i % 7) + 5 for i in range(30)}
        table = {u: (10, 30.0, 16) for u in times}
        units = list(times) + ["z/%d" % i for i in range(40)] + ["m/untimed"]
        proved = set(times) | {"m/untimed"}
        first = pack.shards(units, 6, proved, table, times)
        for seed in range(5):
            shuffled = list(units)
            random.Random(seed).shuffle(shuffled)
            self.assertEqual(pack.shards(shuffled, 6, proved, table, times), first)

    def test_a_job_per_unit_leaves_no_job_empty(self):
        got = pack.shards(["a/1", "b/1", "b/2"], 3, {"a/1"}, {"a/1": (300, 30.0, 16)}, {"a/1": 300})
        self.assertEqual(got, [["a/1"], ["b/1"], ["b/2"]])

    def test_a_unit_given_fewer_cpus_has_no_other_proved_unit_in_its_job(self):
        table = {"l/paintcmap": (53, 101.5, 8), "o/hashtable": (145, 68.1, 11), "c/rgb": (216, 83.9, 16),
                 "a/1": (60, 10.0, 16), "a/2": (50, 10.0, 16), "a/3": (40, 10.0, 16)}
        times = {"l/paintcmap": 122, "o/hashtable": 145, "c/rgb": 200, "a/1": 60, "a/2": 50, "a/3": 40}
        cheap = ["r/%d" % i for i in range(9)]
        got = pack.shards(list(table) + cheap, 4, set(table), table, times)
        proved = [[u for u in s if u in table] for s in got]
        self.assertEqual(proved, [["o/hashtable"], ["l/paintcmap"], ["c/rgb"], ["a/1", "a/2", "a/3"]])
        self.assertEqual([pack.job_cpus(s, table) for s in got], [11, 8, 0, 0])
        # with no job to spare for the others, the limited units are dealt like any other
        got = pack.shards(["l/paintcmap", "o/hashtable", "c/rgb"], 2, set(table), table, times)
        self.assertEqual(got, [["c/rgb"], ["l/paintcmap", "o/hashtable"]])


class Cap(unittest.TestCase):
    """A shard is never shorter than its longest unit, so a unit over the cap takes a job to itself and the units
    under it stay evenly spread: run 42556340137's shard 29 held a unit of 236 minutes that no table listed,
    with 58 others, and was cancelled at the 6-hour limit."""

    TIMES = {"big/one": 236, "a/1": 100, "a/2": 90, "a/3": 80, "a/4": 70, "a/5": 60, "a/6": 50}
    TABLE = {u: (10, 30.0, 16) for u in TIMES}

    def test_a_unit_over_the_cap_gets_a_job_of_its_own_and_the_rest_stay_balanced(self):
        got = pack.shards(list(self.TIMES), 4, set(self.TIMES), self.TABLE, self.TIMES, cap=210)
        self.assertEqual(got[0], ["big/one"])
        load = [sum(self.TIMES[u] for u in s) for s in got[1:]]
        self.assertEqual(sorted(load), [150, 150, 150])
        self.assertTrue(all(x <= 210 for x in load), load)

    def test_under_the_cap_a_long_unit_shares_its_job_like_any_other(self):
        """The cap is what holds a job to its planned length: with two jobs and no cap to speak of, the longest
        unit takes two of the small ones with it (356 minutes), and at 210 it does not."""
        units, n = list(self.TIMES), 2
        loose = pack.shards(units, n, set(self.TIMES), self.TABLE, self.TIMES, cap=300)
        self.assertEqual(loose, [["a/4", "a/6", "big/one"], ["a/1", "a/2", "a/3", "a/5"]])
        tight = pack.shards(units, n, set(self.TIMES), self.TABLE, self.TIMES, cap=210)
        self.assertEqual(tight, [["big/one"], ["a/1", "a/2", "a/3", "a/4", "a/5", "a/6"]])

    def test_an_untimed_proved_unit_gets_a_job_of_its_own_before_any_timed_one(self):
        times = dict(self.TIMES)
        del times["big/one"]
        got = pack.shards(list(self.TIMES), 4, set(self.TIMES), self.TABLE, times, cap=210)
        self.assertEqual(got[0], ["big/one"])
        self.assertEqual(pack.unmeasured(list(self.TIMES), set(self.TIMES), times), ["big/one"])

    def test_an_untimed_unit_counts_as_the_longest_timed_one_when_no_job_can_be_spared(self):
        """Two jobs, three proved units, one untimed: it is dealt like any other, at the longest time there is, so
        it never shares a job with another heavy unit."""
        times = {"a/1": 100, "a/2": 90}
        got = pack.shards(["a/1", "a/2", "u/untimed"], 2, {"a/1", "a/2", "u/untimed"},
                          {u: (10, 30.0, 16) for u in ("a/1", "a/2", "u/untimed")}, times, cap=50)
        self.assertEqual(got, [["a/1", "a/2"], ["u/untimed"]])

    def test_the_cap_the_sweep_plans_to(self):
        """weekly.yml's shard count is chosen against this, and the 6-hour limit is 360 minutes."""
        self.assertEqual(pack.CAP, 210)

    def test_how_many_jobs_the_timed_units_need(self):
        """One job for each unit that takes a job to itself, and `cap` of the rest in each of the others."""
        times = {"big/one": 236, "a/1": 100, "a/2": 90, "a/3": 80, "a/4": 70, "a/5": 60, "a/6": 50}
        table = {u: (10, 30.0, 16) for u in times}
        # 236 alone, then 450 at 210 a job: one job and three
        self.assertEqual(pack.jobs_needed(table, times, cap=210), 1 + 3)
        # nothing above a cap of 300, and 686 at 300 a job: three jobs, none of them one unit's own
        self.assertEqual(pack.jobs_needed(table, times, cap=300), 3)
        # a unit the table limits on CPUs takes a job to itself whatever its time: 50 out, 636 at 300 a job
        limited = dict(table, **{"a/6": (10, 30.0, 8)})
        self.assertEqual(pack.jobs_needed(limited, times, cap=300), 1 + 3)
        self.assertEqual(pack.jobs_needed({}, {}, cap=210), 0)


class Cpus(unittest.TestCase):
    def test_a_job_gets_the_fewest_cpus_the_table_gives_its_units(self):
        table = {"l/paintcmap": (53, 101.5, 8), "o/hashtable": (145, 68.1, 11), "c/rgb": (216, 83.9, 16)}
        self.assertEqual(pack.job_cpus(["c/rgb", "l/paintcmap", "x/unlisted"], table), 8)
        self.assertEqual(pack.job_cpus(["c/rgb", "o/hashtable"], table), 11)

    def test_a_job_whose_units_all_passed_at_full_width_is_not_held_to_the_table_s_most(self):
        """0 means every CPU of the runner, so a larger runner (vars.PROOF_RUNNER) is not held to 16."""
        table = {"l/paintcmap": (53, 101.5, 8), "c/rgb": (216, 83.9, 16), "z/other": (10, 1.0, 16)}
        self.assertEqual(pack.job_cpus(["c/rgb", "z/other"], table), 0)
        self.assertEqual(pack.job_cpus(["x/unlisted"], table), 0)
        self.assertEqual({pack.job_cpus([u], pack.load()) for u in pack.load()}, {0, 8, 11})


class Table(unittest.TestCase):
    def test_the_tracked_table_loads_with_the_measured_16_core_outcomes(self):
        table = pack.load()
        self.assertGreater(len(table), 0)
        for unit in table:
            self.assertEqual(unit.count("/"), 1, unit)
        # out of memory at 16 CPUs (exit 137), and swapping at 16: fewer; passed at 16: 16
        self.assertEqual(table["leptonica/paintcmap_fuzzer"][2], 8)
        self.assertEqual(table["openssl/hashtable"][2], 11)
        for unit in ("cgif/cgif_rgb_fuzzer", "leptonica/graymorph_fuzzer"):
            self.assertEqual(table[unit][2], 16, unit)

    def test_a_unit_listed_twice_or_a_value_that_is_not_positive_is_refused(self):
        for rows in (["a/b\t5\t1.0\t16", "a/b\t6\t1.0\t16"], ["a/b\t0\t1.0\t16"], ["a/b\t5\t0\t16"],
                     ["a/b\t5\tnan\t16"], ["a/b\t5\t1.0\t0"]):
            with self.subTest(rows=rows):
                with tempfile.NamedTemporaryFile("w", suffix=".tsv", delete=False) as f:
                    f.write("unit\tminutes\tpeak_gib\tcpus\n" + "\n".join(rows) + "\n")
                try:
                    with self.assertRaises(ValueError):
                        pack.load(f.name)
                finally:
                    os.unlink(f.name)


class SweepTimes(unittest.TestCase):
    def test_the_tracked_rows_are_the_sweep_s_own_minutes(self):
        """Every reading is well formed and every unit gets one row.  Which units they are is not written out
        here: tools/oft/tests ships, and a shipped file that names a fuzz target says it exists, which is what a
        hold withholds (release_tree.cut_pack_readings takes the readings themselves out of the cut)."""
        rows, measured = pack.sweep(), pack.times()
        self.assertEqual(len(rows), 90)
        self.assertEqual(len(measured), 88)
        for unit, (minutes, outcome) in rows.items():
            self.assertEqual(unit.count("/"), 1, unit)
            self.assertGreater(minutes, 0, unit)
            self.assertIn(outcome, ("finished", "cut"), unit)
        # the two whose check no run has seen end are floors and no weights, and one of them is over the hosted cap
        cut = sorted(u for u, (_m, o) in rows.items() if o == "cut")
        self.assertEqual(len(cut), 2)
        self.assertEqual([u for u in cut if u in measured], [])
        self.assertEqual(sorted(m for u, (m, _o) in rows.items() if u in cut), [152, 347])
        # the longest readings, which set what one shard cannot go below
        self.assertEqual(sorted(measured.values())[-3:], [236, 260, 302])

    def test_a_finished_reading_beats_a_longer_cut_one(self):
        """A cut job gives a floor and never a time, so it never sets a unit's minutes where some run finished
        the check, and never labels such a row `finished` with its own figure (the second review of #2477)."""
        self.assertEqual(pack.best_reading([(169, "a", True), (179, "b", False)]), (169, "a", "finished"))
        self.assertEqual(pack.best_reading([(179, "b", False), (169, "a", True)]), (169, "a", "finished"))
        # among readings of one kind the longest wins
        self.assertEqual(pack.best_reading([(169, "a", True), (174, "b", True)]), (174, "b", "finished"))
        self.assertEqual(pack.best_reading([(100, "a", False), (152, "b", False)]), (152, "b", "cut"))
        # a unit nothing read has no row at all; none is made up here
        with self.assertRaises(ValueError):
            pack.best_reading([])

    def test_a_reading_listed_twice_a_time_that_is_not_positive_or_a_bad_outcome_is_refused(self):
        for rows in ((("a/b", "1", 5, "finished"), ("a/b", "1", 6, "finished")), (("a/b", "1", 0, "finished"),),
                     (("a/b", "1", -5, "finished"),), (("a/b", "", 5, "finished"),),
                     (("a/b", "  ", 5, "finished"),), (("a/b", "1", 5, "running"),),
                     (("a/b", "1", 5.5, "finished"),)):
            with self.subTest(rows=rows):
                with self.assertRaises(ValueError):
                    pack.sweep(rows)
        self.assertEqual(pack.sweep((("a/b", "1", 5, "cut"),)), {"a/b": (5, "cut")})
        # the same unit read in two runs is one row, not a repeat
        self.assertEqual(pack.sweep((("a/b", "1", 5, "finished"), ("a/b", "2", 9, "finished"))), {"a/b": (9, "finished")})

    def test_a_longer_cut_reading_changes_no_derived_row(self):
        """sweep() derives every row through best_reading, so the rule is what the packer runs and not a comment:
        adding a cut reading longer than a unit's finished one leaves that unit's row where it was, while a
        longer finished one moves it."""
        rows = pack.sweep()
        self.assertEqual(len(rows), 90)
        longest = sorted((m, u) for u, (m, o) in rows.items() if o == "finished")[-3:]
        self.assertEqual(len(longest), 3)
        for _m, unit in longest:
            with self.subTest(minutes=_m):
                was = rows[unit]
                self.assertEqual(was[1], "finished")
                longer = pack.SWEEP_TIMES + ((unit, "a-later-run", was[0] + 500, "cut"),)
                self.assertEqual(pack.sweep(longer)[unit], was)
                finished = pack.SWEEP_TIMES + ((unit, "a-later-run", was[0] + 500, "finished"),)
                self.assertEqual(pack.sweep(finished)[unit], (was[0] + 500, "finished"))
        # and every other row is untouched either way
        other = pack.sweep(pack.SWEEP_TIMES + ((longest[0][1], "a-later-run", 9000, "cut"),))
        self.assertEqual({u: r for u, r in other.items() if u != longest[0][1]},
                         {u: r for u, r in rows.items() if u != longest[0][1]})

    def test_which_units_no_hosted_job_can_check(self):
        """A floor over the cap settles it as surely as a finished check does, and nothing else is read: no list
        of units is written by hand anywhere."""
        rows = {"a/finished-over": (300, "finished"), "a/cut-over": (300, "cut"),
                "a/finished-at": (240, "finished"), "a/cut-under": (50, "cut"), "a/small": (10, "finished")}
        self.assertEqual(pack.too_long_for_hosted(rows, cap=240), ["a/cut-over", "a/finished-over"])
        self.assertEqual(pack.too_long_for_hosted(rows, cap=400), [])
        over = pack.too_long_for_hosted(pack.sweep())
        self.assertEqual(len(over), 3)
        self.assertTrue(all(pack.sweep()[u][0] > pack.HOSTED_CAP for u in over), over)

    def test_the_farm_checks_are_farm_runs_with_a_day(self):
        checks = pack.farm_checks()
        self.assertGreater(len(checks), 0)
        for rows in ((("a/b", "farm/20261107t222300z-b2f735", "2026-11-07"),
                      ("a/b", "farm/20261107t222300z-b2f735", "2026-11-07")),
                     (("a/b", "20261107t222300z-b2f735", "2026-11-07"),),
                     (("a/b", "farm/nope", "2026-11-07"),),
                     (("a/b", "farm/20261107t222300z-b2f735", "7 Nov 2026"),)):
            with self.subTest(rows=rows):
                with self.assertRaises(ValueError):
                    pack.farm_checks(rows)

    def test_every_unit_no_hosted_job_can_check_has_a_farm_check_to_name(self):
        """The summary of a skipped unit is only useful when there is a standing check to date; a unit with none
        is reported in those words, and today none of the three is in that case."""
        checks = pack.farm_checks()
        for unit in pack.too_long_for_hosted(pack.sweep()):
            self.assertIn(unit, checks, unit)

    def test_the_copy_of_the_farm_register_matches_it(self):
        """FARM_CHECKS is a copy of the `pass` rows of dev/stream/data/corpus-checks.tsv, which does not ship to
        the public repository.  Where the register is present, the two agree; a clone without it skips."""
        register = os.path.join(REPO, "dev", "stream", "data", "corpus-checks.tsv")
        if not os.path.isfile(register):
            self.skipTest("no dev/stream/data/corpus-checks.tsv in this clone")
        want = {}
        with open(register, encoding="utf-8") as f:
            rows = [l.rstrip("\n").split("\t") for l in f if not l.startswith("#") and l.strip()]
        head, rows = rows[0], rows[1:]
        for r in rows:
            d = dict(zip(head, r))
            if d["result"] == "pass":
                want[d["unit"]] = d["job"]
        self.assertEqual({u: run for u, (run, _d) in pack.farm_checks().items()}, want)


if __name__ == "__main__":
    unittest.main()
