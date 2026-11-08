"""The tests of tools/oft.

Importing this package gives the process a TMPDIR of its own, removed when the process ends, so that a run of these
tests leaves nothing behind on a shared box (INFRA-1547; tmpdir.py says why, and what to set to keep it).
This is the one place every runner of these tests reaches before any test module: `unittest discover`, the parallel
runner the tests job uses, and pytest all import the package first.
"""
from oft.tests import tmpdir

TMPDIR = tmpdir.own_tmpdir()
