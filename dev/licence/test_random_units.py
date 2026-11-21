#!/usr/bin/env python3
"""Random units through dev/licence/made_from.py: one unit's record is the same in any order of its files, with the
index shortcut on or off and under two hash seeds, and `--check` passes right after `--apply`.

Run: python3 -B -m unittest discover -s dev/licence -t dev/licence -v   (from the top of the checkout: the first 35
cases).  The long form, 3,000 cases, from the top of the checkout:
    MADE_FROM_RANDOM_UNITS=3000 python3 -B -m unittest discover -s dev/licence -t dev/licence -p test_random_units.py -v

Each case writes, in a scratch checkout as test_made_from.Tree makes it, a unit of 6 to 11 files: blocks of code
shared between files (whole or a slice), headers of every kind (Anthropic's lines, none, Anthropic's tag alone,
Modified by alone, the MIT tag), named origins (a Relocated from line or a derive_y line, to any file, cycles
included), history rows (to any file, some never licensed), a left-bare row, and random first-added times.  Each case
holds:
- licensed_in_order on the files in path order, reversed and three shuffles, each with the shortcut on and off, gives
  one result;
- every `made from` chain of sources ends at a file with Anthropic's lines before the run, and returns to no file of
  it (test_made_from.chains);
- a `made from (named origin)` row's source is the file's named origin, and a `made from (history...)` row's source is
  its history row's source;
- `made_from.py <record> --apply` exits 0, and `--check` right after it exits 0: each row that a run on --apply's own
  output gives again is --apply's row (a file --apply gave Anthropic's lines is decided by no run after it);
- every fifth case, the command line run twice, with PYTHONHASHSEED 1 and 2, writes two OUT files equal byte for byte;
- the case ends within HANG seconds, where the platform has SIGALRM, and each command line run of it within HANG
  seconds, the two runs a --check starts among them: a case over it is a run that does not end.

The cases are deterministic: case n's unit and its three shuffles come from random.Random(n) alone, and no case reads
what the one before it left.  So on one Python a run of N cases is the first N of every longer run, and a failure's
subtest names the case, which fails the same way in every run that reaches it.
"""
import contextlib
import io
import os
import random
import shutil
import signal
import unittest

import test_made_from as t
from test_made_from import ANTHROPIC, OWN, code, derived, mf, relocated

CASES = int(os.environ.get("MADE_FROM_RANDOM_UNITS", "35"))
# seconds per case: well over the slowest of the first 3,000 (1.1 s where they were measured), and short, since a run
# that does not end is stopped only by this limit: a case over it fails (its SIGALRM).  Each command line run of a case
# is given timeout=HANG too.  The case's alarm comes before that limit, so what the argument does is put the command in
# a session of its own (test_made_from.Tree.cli starts one only for a timed command): the alarm, or an outer timeout's
# SIGTERM, unwinding through Tree.cli, then kills the command's whole process group, the two runs a --check starts
# among them, where an untimed command would be killed alone; and where the platform has no SIGALRM, the argument is
# the limit of each command.
# (Before its guard, the walk of named origins that never ended grew a list by some 37 MiB/s, near 1.1 GiB in 30 s;
# now it stops with a Fault.)
HANG = 30
HEADERS = ("anthropic", "none", "tag", "own", "mit")


class RandomUnits(t.Cases):
    """The cases of the module docstring, one unit after another in one scratch checkout."""

    def build(self, rnd, n):
        stems = ["F%d" % i for i in range(n)]
        blocks = [code("b%d" % i, rnd.choice((6, 7, 12, 20, 31, 45))) for i in range(rnd.randint(2, 5))]
        heads, origins, texts = {}, {}, {}
        for s in stems:
            heads[s] = rnd.choices(HEADERS, weights=(3, 4, 1, 1, 1))[0]
        if "anthropic" not in heads.values():   # --check refuses a unit with no file with Anthropic's lines (exit 4)
            heads[rnd.choice(stems)] = "anthropic"
        for s in stems:
            body = []
            for b in rnd.sample(blocks, rnd.randint(0, min(3, len(blocks)))):
                if rnd.random() < 0.6:
                    body += b
                else:
                    i = rnd.randint(0, max(0, len(b) - 6))
                    body += b[i:i + rnd.randint(6, len(b))]
            body += code("own" + s, rnd.randint(0, 12))
            header = {"anthropic": ANTHROPIC, "none": [], "tag": [mf.APACHE_TAG], "own": [OWN],
                      "mit": [mf.MIT_TAG]}[heads[s]]
            note = []
            if heads[s] in ("none", "tag", "own") and rnd.random() < 0.5:
                o = rnd.choice([x for x in stems if x != s] + ["Gone"])
                origins[s] = o
                note = [relocated("lib/%s.v" % o) if rnd.random() < 0.5 else derived("lib/%s.v" % o)]
            texts[s] = header + note + body + ["Definition %s_end := 0." % s.lower()]
        times = {s: rnd.randint(1, 4) for s in stems}
        self.files("", times, **texts)
        decided = [s for s in stems if heads[s] in ("none", "tag", "own")]
        for s in decided:
            if rnd.random() < 0.3:
                self.named.append(("lib/%s.v" % s, "lib/%s.v" % rnd.choice([x for x in stems if x != s])))
        bare = [s for s in decided if heads[s] == "none" and s not in origins]
        if bare and rnd.random() < 0.3:
            self.declared.append(("lib/%s.v" % rnd.choice(bare), "ours: written here"))

    def one(self, case):
        rnd = random.Random(case)
        lib = os.path.join(self.top, self.root, "lib")
        if os.path.isdir(lib):
            shutil.rmtree(lib)   # the case before's unit, as its --apply left it: a case reads only its own
        self.times, self.named, self.declared = {}, [], []
        self.build(rnd, rnd.randint(6, 11))
        self.finish()
        # the progress lines licensed_in_order and named_origins print: the test prints nothing when it passes
        with contextlib.redirect_stderr(io.StringIO()):
            first = None
            # shuffles of the case's own: three fixed seeds would give every unit of n files the same three orders
            for order in ("path", "reversed") + tuple(rnd.randrange(1 << 30) for _ in range(3)):
                for shortcut in (True, False):
                    got = self.direct(order, shortcut)
                    if first is None:
                        first = got
                    elif got != first:
                        diff = sorted(p for p in set(got[0]) | set(first[0]) if got[0].get(p) != first[0].get(p))
                        self.fail("order %r shortcut %r differs from path order in %s: %s vs %s"
                                  % (order, shortcut, diff, [first[0].get(p) for p in diff],
                                     [got[0].get(p) for p in diff]))
            u = mf.Unit(self.top, self.layout)
            before = set(u.anthropic)
            origins = mf.named_origins(u, mf.to_decide(u)[1], self.layout.unit)[0]
        history = dict(self.named)
        t.chains({p: [p, r[0], r[1], r[2], r[3], r[4] or "-", r[5]] for p, r in first[0].items()}, before)
        for p, r in first[0].items():
            if r[5] == mf.NAMED:
                self.assertEqual(r[4], origins.get(p), "%s: a `made from (named origin)` row's source" % p)
            elif r[5].startswith("made from (history"):
                self.assertEqual(r[4], history.get(p), "%s: a `made from (history...)` row's source" % p)
        if case % 5 == 0:
            self.outs_under_two_hash_seeds(timeout=HANG)
        # review round 2's property: each row that a run on --apply's own output gives again is --apply's row, so
        # --check passes right after --apply (the record is the OUT of the --apply run)
        rc, out = self.cli(self.layout.record, "--apply", *self.history_args(), timeout=HANG)
        self.assertEqual(rc, 0, "--apply exits %d: every comment of a random unit closes and every file's licence "
                                "lines stand in its first lines, so what --apply refuses to write is the run's own "
                                "decision:\n%s" % (rc, out))
        rc, out = self.check(timeout=HANG)
        self.assertEqual(rc, 0, "--check after --apply exits %d:\n%s" % (rc, out))

    def test_random_units(self):
        alarm = hasattr(signal, "SIGALRM")
        if alarm:
            def hang(_signum, _frame):
                raise AssertionError("a case ran over %d s: the run does not end" % HANG)

            self.addCleanup(signal.signal, signal.SIGALRM, signal.signal(signal.SIGALRM, hang))
        for case in range(CASES):
            failed = True
            with self.subTest(case=case):
                if alarm:
                    signal.alarm(HANG)
                try:
                    self.one(case)
                finally:
                    if alarm:
                        signal.alarm(0)
                failed = False
            # the first failing case is the one to read; and when the run does not end, each later case would take
            # HANG seconds too
            if failed:
                break


if __name__ == "__main__":
    unittest.main()
