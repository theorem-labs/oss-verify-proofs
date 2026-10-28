"""tools/enroll/tests, run by the tools' own test runner, so that pr.yml's tests job runs them.

tools/enroll/'s tests load their scripts by path (none of them is a package), so they run as their own unittest
discovery in a process of their own; this class fails, with their whole output, when any of them fails.
"""
import os
import subprocess
import sys
import unittest

TOOLS = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ENROLL_TESTS = os.path.join(TOOLS, "enroll", "tests")


class EnrollTools(unittest.TestCase):
    def test_tools_enroll_tests_pass(self):
        if not os.path.isdir(ENROLL_TESTS):
            self.skipTest("this tree has no tools/enroll/tests")
        run = subprocess.run([sys.executable, "-B", "-m", "unittest", "discover", "-s", ENROLL_TESTS],
                             cwd=os.path.dirname(TOOLS), capture_output=True, text=True)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertRegex(run.stderr, r"\nOK")


if __name__ == "__main__":
    unittest.main()
