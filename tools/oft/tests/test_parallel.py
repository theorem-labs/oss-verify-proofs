"""tools/oft/tests/parallel.py, the runner pr.yml's tests job uses: it never reports green while it ran less than
`unittest discover` would have."""
import io
import os
import sys
import tempfile
import textwrap
import unittest

from oft.tests import parallel

PASSING = '''
import unittest

class Passes(unittest.TestCase):
    def test_one(self):
        pass

    def test_two(self):
        pass
'''


class Runner(unittest.TestCase):
    def run_over(self, modules):
        """parallel.run over a package of its own holding modules ({file name: source}): (its exit, its output)."""
        with tempfile.TemporaryDirectory() as top:
            pkg = os.path.join(top, "parallel_probe")
            os.mkdir(pkg)
            open(os.path.join(pkg, "__init__.py"), "w").close()
            for name, source in modules.items():
                with open(os.path.join(pkg, name), "w", encoding="utf-8") as f:
                    f.write(textwrap.dedent(source))
            out = io.StringIO()
            try:
                status = parallel.run(jobs=2, out=out, progress=io.StringIO(), start=pkg, top=top)
            finally:
                # discovery imports the probe package into this process; the next test's package has the same name
                # in another directory, which unittest refuses as "incorrectly imported"
                for m in [m for m in sys.modules if m == "parallel_probe" or m.startswith("parallel_probe.")]:
                    del sys.modules[m]
            return status, out.getvalue()

    def test_every_class_passing_passes_with_discovery_s_count(self):
        status, out = self.run_over({"test_a.py": PASSING})
        self.assertEqual(status, 0, out)
        self.assertIn("ran 2 test(s) in 1 class(es)", out)

    def test_no_test_class_fails(self):
        """`unittest discover` exits 5 when no test ran; the runner fails too."""
        status, out = self.run_over({})
        self.assertEqual(status, 1, out)
        self.assertIn("no test class found", out)

    def test_a_failing_test_fails_and_is_named(self):
        status, out = self.run_over({"test_a.py": PASSING, "test_b.py": '''
            import unittest

            class Fails(unittest.TestCase):
                def test_it(self):
                    self.fail("no")
            '''})
        self.assertEqual(status, 1, out)
        self.assertIn("parallel_probe.test_b.Fails.test_it", out)

    def test_a_module_that_cannot_be_imported_fails(self):
        status, out = self.run_over({"test_a.py": PASSING, "test_b.py": "import no_such_module_anywhere\n"})
        self.assertEqual(status, 1, out)
        self.assertIn("parallel_probe.test_b", out)

    def test_a_process_that_ends_with_status_0_and_no_report_fails(self):
        """A test that calls os._exit(0) ends its process with status 0 and no report: a failure, not a pass."""
        status, out = self.run_over({"test_a.py": PASSING, "test_b.py": '''
            import os
            import unittest

            class Leaves(unittest.TestCase):
                def test_it(self):
                    os._exit(0)
            '''})
        self.assertEqual(status, 1, out)
        self.assertIn("parallel_probe.test_b.Leaves (its process exited 0 and wrote no report", out)


if __name__ == "__main__":
    unittest.main()
