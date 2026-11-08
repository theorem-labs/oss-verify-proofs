"""check.RUN_TIMEOUT_SECONDS: the seconds one counterexample or finding run gets, which `oft check` takes from the
same constant as its --timeout default, so a slow runner does not fail a counterexample a fast one passes."""
import argparse
import inspect
import unittest

from oft import check


def parse(*argv):
    p = argparse.ArgumentParser()
    check.add_arguments(p)
    return p.parse_args(["zlib/checksum_fuzzer", *argv])


class Timeout(unittest.TestCase):
    def test_the_default_holds_the_slowest_measured_run_three_times_over(self):
        """535 s is the slowest counterexample step measured (ffmpeg SIPR's .asan and .asan-ubsan, public run
        42228615142); 3 x 535 s = 1605 s, rounded up to the whole minute."""
        self.assertEqual(check.RUN_TIMEOUT_SECONDS, 1620)
        self.assertGreaterEqual(check.RUN_TIMEOUT_SECONDS, 3 * 535)

    def test_the_cli_default_is_the_constant(self):
        self.assertEqual(parse().timeout, check.RUN_TIMEOUT_SECONDS)

    def test_run_s_default_is_the_constant(self):
        self.assertEqual(inspect.signature(check.run).parameters["timeout"].default, check.RUN_TIMEOUT_SECONDS)

    def test_a_caller_can_still_lower_it(self):
        self.assertEqual(parse("--timeout", "30").timeout, 30)


if __name__ == "__main__":
    unittest.main()
