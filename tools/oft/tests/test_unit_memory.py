"""check.UnitMemory: the per-unit peak memory line `oft check` prints to stderr, from which proof-times.tsv's `cpus`
column is refreshed with numbers measured on the runner that ran the check."""
import contextlib
import io
import os
import tempfile
import unittest
from unittest import mock

from oft import check


class UnitMemoryTest(unittest.TestCase):
    def sampled(self, stat_text):
        """finish()'s stderr for a unit whose cgroup memory.stat holds stat_text (None: no readable file)."""
        with tempfile.TemporaryDirectory() as d:
            stat = os.path.join(d, "memory.stat")
            if stat_text is not None:
                with open(stat, "w") as f:
                    f.write(stat_text)
            err = io.StringIO()
            with mock.patch.object(check.UnitMemory, "_run", lambda self: None), contextlib.redirect_stderr(err):
                m = check.UnitMemory("zlib/checksum_fuzzer")
                m.stat = stat
                a = m._anon()
                if a is not None:
                    m.peak = a
                m.finish()
            return err.getvalue()

    def test_the_peak_is_printed_to_stderr_with_the_cpus(self):
        out = self.sampled("file 1\nanon %d\n" % (3 << 30))
        self.assertIn("zlib/checksum_fuzzer: peak memory 3.0 GiB", out)
        self.assertIn("on %d CPUs" % check._jobs(), out)

    def test_nothing_is_printed_without_a_readable_stat(self):
        self.assertEqual(self.sampled(None), "")
        self.assertEqual(self.sampled("file 1\n"), "")


if __name__ == "__main__":
    unittest.main()
