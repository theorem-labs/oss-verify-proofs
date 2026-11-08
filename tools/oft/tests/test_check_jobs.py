"""check._jobs: dune's -j is OFT_JOBS, else the cgroup's CPU quota, at most the CPUs the process may run on."""
import os
import shutil
import tempfile
import unittest
from unittest import mock

from oft import check


class Jobs(unittest.TestCase):
    def setUp(self):
        self.root = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.root)
        for p in (mock.patch.object(check, "CGROUP_ROOT", self.root),
                  mock.patch.object(check.os, "sched_getaffinity", return_value=set(range(32))),
                  mock.patch.dict(os.environ)):
            p.start()
            self.addCleanup(p.stop)
        os.environ.pop("OFT_JOBS", None)

    def put(self, rel, text):
        path = os.path.join(self.root, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as f:
            f.write(text)

    def test_v2_quota_rounds_up(self):
        self.put("cpu.max", "150000 100000\n")
        self.assertEqual(check._jobs(), 2)

    def test_v2_one_cpu(self):
        self.put("cpu.max", "100000 100000\n")
        self.assertEqual(check._jobs(), 1)

    def test_v2_max_is_the_affinity(self):
        self.put("cpu.max", "max 100000\n")
        self.assertEqual(check._jobs(), 32)

    def test_no_cgroup_files_is_the_affinity(self):
        self.assertEqual(check._jobs(), 32)

    def test_v1_quota(self):
        self.put("cpu/cpu.cfs_quota_us", "400000\n")
        self.put("cpu/cpu.cfs_period_us", "100000\n")
        self.assertEqual(check._jobs(), 4)

    def test_v1_combined_controller_directory(self):
        self.put("cpu,cpuacct/cpu.cfs_quota_us", "250000\n")
        self.put("cpu,cpuacct/cpu.cfs_period_us", "100000\n")
        self.assertEqual(check._jobs(), 3)

    def test_v1_no_limit_is_the_affinity(self):
        self.put("cpu/cpu.cfs_quota_us", "-1\n")
        self.put("cpu/cpu.cfs_period_us", "100000\n")
        self.assertEqual(check._jobs(), 32)

    def test_malformed_files_are_the_affinity(self):
        for text in ("", "150000\n", "abc 100000\n", "150000 0\n", "1 2 3\n"):
            with self.subTest(text=text):
                self.put("cpu.max", text)
                self.assertEqual(check._jobs(), 32)

    def test_malformed_v1_is_the_affinity(self):
        self.put("cpu/cpu.cfs_quota_us", "lots\n")
        self.put("cpu/cpu.cfs_period_us", "100000\n")
        self.assertEqual(check._jobs(), 32)

    def test_oft_jobs_overrides_the_quota(self):
        self.put("cpu.max", "150000 100000\n")
        with mock.patch.dict(os.environ, {"OFT_JOBS": "6"}):
            self.assertEqual(check._jobs(), 6)

    def test_oft_jobs_not_a_positive_integer_is_ignored(self):
        self.put("cpu.max", "150000 100000\n")
        for value in ("0", "-3", "two", ""):
            with self.subTest(value=value), mock.patch.dict(os.environ, {"OFT_JOBS": value}):
                self.assertEqual(check._jobs(), 2)

    def test_clamped_to_the_affinity(self):
        self.put("cpu.max", "6400000 100000\n")
        self.assertEqual(check._jobs(), 32)
        with mock.patch.dict(os.environ, {"OFT_JOBS": "100"}):
            self.assertEqual(check._jobs(), 32)
        with mock.patch.object(check.os, "sched_getaffinity", return_value={0, 1}):
            self.put("cpu.max", "400000 100000\n")
            self.assertEqual(check._jobs(), 2)


if __name__ == "__main__":
    unittest.main()
