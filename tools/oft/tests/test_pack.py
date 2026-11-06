"""pack.py: how oft plan deals units into check jobs, and how many CPUs a job's check gets."""
import math
import os
import random
import tempfile
import unittest

from oft import pack


class Shards(unittest.TestCase):
    def test_the_longest_units_go_to_separate_jobs_and_the_rest_fill_every_job(self):
        table = {"a/1": (300, 30.0, 16), "a/2": (200, 30.0, 16), "a/3": (100, 30.0, 16), "a/4": (90, 30.0, 16)}
        cheap = ["c/%02d" % i for i in range(10)]
        got = pack.shards(list(table) + cheap, 3, set(table), table)
        # longest first, each to the least-loaded job: 300 | 200 | 100 + 90
        self.assertEqual([[u for u in s if u.startswith("a/")] for s in got], [["a/1"], ["a/2"], ["a/3", "a/4"]])
        self.assertEqual(sorted(u for s in got for u in s), sorted(list(table) + cheap))
        self.assertTrue(all(got))
        self.assertTrue(all(s == sorted(s) for s in got))

    def test_equal_times_give_no_job_more_than_its_share_of_proved_units(self):
        for p, n in ((7, 20), (20, 20), (45, 20), (61, 7)):
            with self.subTest(p=p, n=n):
                proved = ["p/%03d" % i for i in range(p)]
                got = pack.shards(proved + ["r/%04d" % i for i in range(500)], n, set(proved), {})
                self.assertLessEqual(max(sum(u in proved for u in s) for s in got), math.ceil(p / n))

    def test_the_jobs_depend_on_the_units_not_on_their_order(self):
        table = {"a/%d" % i: (10 * (i % 7) + 5, 20.0, 16) for i in range(30)}
        units = list(table) + ["z/%d" % i for i in range(40)] + ["m/unlisted"]
        proved = set(table) | {"m/unlisted"}
        first = pack.shards(units, 6, proved, table)
        for seed in range(5):
            shuffled = list(units)
            random.Random(seed).shuffle(shuffled)
            self.assertEqual(pack.shards(shuffled, 6, proved, table), first)

    def test_a_job_per_unit_leaves_no_job_empty(self):
        got = pack.shards(["a/1", "b/1", "b/2"], 3, {"a/1"}, {"a/1": (300, 30.0, 16)})
        self.assertEqual(got, [["a/1"], ["b/1"], ["b/2"]])

    def test_a_unit_given_fewer_cpus_has_no_other_proved_unit_in_its_job(self):
        table = {"l/paintcmap": (53, 101.5, 8), "o/hashtable": (145, 68.1, 11), "c/rgb": (216, 83.9, 16),
                 "a/1": (60, 10.0, 16), "a/2": (50, 10.0, 16), "a/3": (40, 10.0, 16)}
        cheap = ["r/%d" % i for i in range(9)]
        got = pack.shards(list(table) + cheap, 4, set(table), table)
        proved = [[u for u in s if u in table] for s in got]
        self.assertEqual(proved, [["o/hashtable"], ["l/paintcmap"], ["c/rgb"], ["a/1", "a/2", "a/3"]])
        self.assertEqual([pack.job_cpus(s, table) for s in got], [11, 8, 0, 0])
        # with no job to spare for the others, the limited units are dealt like any other
        got = pack.shards(["l/paintcmap", "o/hashtable", "c/rgb"], 2, set(table), table)
        self.assertEqual(got, [["c/rgb"], ["l/paintcmap", "o/hashtable"]])


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


if __name__ == "__main__":
    unittest.main()
