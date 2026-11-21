"""oft lps-impact: the consumer impact list of an LPS commit."""
import argparse
import contextlib
import io
import os
import re
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

from oft import keys, lps_impact

HARNESSES = (
    "project\tharness\torigin\tbuilds\tstatements\topen\tproved\tfalse\n"
    "a\th1\toss-fuzz\tplain\t2\t2\t0\t0\n"
    "a\th2\toss-fuzz\tplain\t1\t1\t0\t0\n"
    "b\th1\toss-fuzz\tplain\t1\t0\t1\t0\n"
    "c\th1\toss-fuzz\tplain\t1\t1\t0\t0\n"
    "d\th1\toss-fuzz\tplain\t1\t1\t0\t0\n"
    "e\th1\toss-fuzz\tplain\t1\t1\t0\t0\n"
    "f\th1\toss-fuzz\tplain\t1\t1\t0\t0\n"
)
# b/h1 has two proofs, as most proved units of the corpus do: a unit's verdict is not a statement's.
PROOFS = (
    "library\tentry_point\tstatement\tkind\tbuild\tfailures\tstatement_file\tproof\tbuild_record\n"
    "b\th1\tplain_halts\thalts\tplain\t-\tprojects/b/h1/Statements.v\tprojects/b/h1/proofs/plain_halts\t-\n"
    "b\th1\textra_halts\thalts\tplain\t-\tprojects/b/h1/Statements.v\tprojects/b/h1/proofs/extra_halts\t-\n"
)
STATEMENTS = (
    "id\tkind\tbuilds\treading\texits\tstatus\tdetail\trevision\tfingerprint\tproof\n"
    "a/h1/plain_halts\thalts\tplain\tbudget\t0\topen\t-\t1\tff\t-\n"
    "b/h1/plain_halts\thalts\tplain\tbudget\t0\tproved\t-\t1\tff\tprojects/b/h1/proofs/plain_halts\n"
    "b/h1/extra_halts\thalts\tplain\tbudget\t0\tproved\t-\t1\tff\tprojects/b/h1/proofs/extra_halts\n"
    # b/h1 is checked with both parts and has this statement unproved: a failure of a proof above is not its
    "b/h1/ubsan_halts\thalts\tubsan\tbudget\t0\topen\t-\t1\tff\t-\n"
)
PLAIN, EXTRA = "projects/b/h1/proofs/plain_halts", "projects/b/h1/proofs/extra_halts"
WITNESS = "Error: Unable to unify the witness with the goal"
# What `oft check` prints: a FAIL line for each step it failed, and check_proof's own line for each proof that
# passed (check.py:435, :551, :819).  Both in one run: the unit failed, one of its two proofs did not.
PASSES_EXTRA = "%s: proves b/h1/extra_halts; assumptions: 3 axioms, all allowed\n" % EXTRA
FAILS_PLAIN = "FAIL %s: %s\n" % (PLAIN, WITNESS)
FAILS_EXTRA = "FAIL %s: %s\n" % (EXTRA, WITNESS)
ONE_OF_TWO = "b/h1: 2 statement(s) with a proof\n" + FAILS_PLAIN + PASSES_EXTRA
# The line each log path the reader refuses prints on standard error: the arm (`b__h1` for b/h1's checker arm), then
# the path.  It is written out here so that a change to it fails.
REFUSED = ("lps-impact: %s: refused the log path a failure names, "
           "it is not a file of this unit's harvested logs: %s")
TOOLS = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))   # tools/oft/tests -> tools


def tree(d):
    os.makedirs(os.path.join(d, "index"), exist_ok=True)
    for name, text in (("harnesses.tsv", HARNESSES), ("proofs.tsv", PROOFS), ("statements.tsv", STATEMENTS)):
        with open(os.path.join(d, "index", name), "w", encoding="utf-8") as f:
            f.write(text)
    return d


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


class Units(unittest.TestCase):
    def test_shard_splits_units_disjointly(self):
        units = ["u%d" % i for i in range(7)]
        parts = [lps_impact.shard(units, k, 3) for k in (1, 2, 3)]
        self.assertEqual(sorted(sum(parts, [])), sorted(units))
        self.assertEqual(sum(len(p) for p in parts), len(units))
        for i, p in enumerate(parts):
            for q in parts[i + 1:]:
                self.assertFalse(set(p) & set(q))

    def test_first_file_units_run_first(self):
        self.assertEqual(lps_impact.order_first(["a", "b", "c"], ["c", "zz"]), ["c", "a", "b"])

    def test_a_unit_named_twice_in_the_first_file_is_checked_once(self):
        self.assertEqual(lps_impact.order_first(["a", "b", "c"], ["c", "c", "a"]), ["c", "a", "b"])

    def test_a_timeout_below_one_second_is_refused(self):
        seconds = lps_impact.positive("number of seconds")
        self.assertEqual(seconds("30"), 30)
        for bad in ("0", "-1", "half"):
            with self.subTest(value=bad), self.assertRaises(argparse.ArgumentTypeError):
                seconds(bad)

    def test_a_malformed_shard_is_refused_by_the_parser(self):
        self.assertEqual(lps_impact.shard_arg("2/3"), (2, 3))
        for bad in ("2", "x/3", "2/", "0/4", "5/4", "/3"):
            with self.subTest(value=bad), self.assertRaises(argparse.ArgumentTypeError):
                lps_impact.shard_arg(bad)

    def test_units_all_checks_statements_of_units_without_proofs(self):
        with tempfile.TemporaryDirectory() as d:
            tree(d)
            self.assertEqual(len(lps_impact.units_of(d, "all")), 7)
            self.assertEqual(lps_impact.units_of(d, "proved"), ["b/h1"])
            self.assertEqual(lps_impact.proof_units(d), {"b/h1"})


class Outcomes(unittest.TestCase):
    def test_a_log_with_a_fail_and_a_pass_gives_each_proof_its_own(self):
        failed, passed = lps_impact.proof_outcomes(ONE_OF_TWO)
        self.assertEqual(sorted(failed), [PLAIN])
        self.assertIn(WITNESS, failed[PLAIN])
        self.assertEqual(passed, {EXTRA})

    def test_a_line_echoed_from_a_worker_process_is_not_a_verdict(self):
        """proofs_apart echoes each worker's own output with a `  | ` prefix and then prints the parent's
        verdict for that proof: only the parent's line counts."""
        failed, passed = lps_impact.proof_outcomes("  | %s  | FAIL %s: boom\n" % (PASSES_EXTRA, PLAIN))
        self.assertEqual((failed, passed), ({}, set()))

    def test_the_statements_step_is_not_a_proof(self):
        failed, passed = lps_impact.proof_outcomes("FAIL statements: Error: Unable to unify\n")
        self.assertEqual((failed, passed), ({}, set()))

    def test_stage_names_why_a_unit_ended_where_it_did(self):
        for code, err, stage in ((0, "", "none"),
                                 (137, "", "oom-killed"),
                                 (125, "", "docker-start"),
                                 (124, "", "timeout"),
                                 (1, "", "no-diagnostic"),
                                 (1, "FAIL statements: Error: x", "statements"),
                                 (1, "FAIL %s: Error: x" % PLAIN, "proofs"),
                                 (1, "FAIL b/h1: no such harness", "checker")):
            with self.subTest(code=code, err=err):
                self.assertEqual(lps_impact.stage_of(code, err), stage)


class Classes(unittest.TestCase):
    def test_classifies_arity_error(self):
        err = "FAIL a/h1 statements: Error: The constructor mkProcInput_full expects 16 arguments, not 15."
        self.assertEqual(lps_impact.classify("fail", err), "arity")

    def test_classifies_witness_error(self):
        err = "FAIL b/h1 plain_halts: Error: Unable to unify the witness with the goal"
        self.assertEqual(lps_impact.classify("fail", err), "witness")

    def test_unchanged_when_check_passes(self):
        self.assertEqual(lps_impact.classify("pass", ""), "unchanged")

    def test_control_failure_marks_pre_existing(self):
        err = "FAIL a/h1: Error: Unable to unify"
        self.assertEqual(lps_impact.classify("fail", err, control="fail"), "pre-existing")

    def test_a_control_that_could_not_run_attributes_the_failure_to_nothing(self):
        err = "FAIL a/h1: Error: Unable to unify"
        self.assertEqual(lps_impact.classify("fail", err, control="infra"), "control-infra")

    def test_a_unit_that_could_not_run_is_infra_before_any_pattern(self):
        """`other` means a break the move caused that no pattern names.  A check the host or the image stopped
        says nothing about the model, so it is never given a failure class."""
        self.assertEqual(lps_impact.classify("infra", "exit 137"), "infra")
        self.assertEqual(lps_impact.classify("infra", "Error: Unable to unify"), "infra")
        for stage in lps_impact.INFRA_STAGES:
            with self.subTest(stage=stage):
                self.assertEqual(lps_impact.classify("fail", "Error: Unable to unify", stage=stage), "infra")

    def test_a_run_the_checker_refused_before_any_step_is_infra(self):
        """`oft check` refuses a run before its first step when it cannot raise the stack limit, when a unit's
        facts cannot be read, or when --parts names a part the unit has not (check.py:754,771,783,810).  Each
        is a `FAIL` line, so each reaches the pattern scan unless its stage stops it: nothing of the model was
        examined, and `other` would say the move broke it."""
        self.assertIn("checker", lps_impact.INFRA_STAGES)
        for err in ("FAIL cannot raise the stack limit: Operation not permitted",
                    "FAIL b/h1: the facts of this unit cannot be read: Unable to unify",
                    "FAIL b/h1: nothing to check for part proofs: the unit has no proof"):
            with self.subTest(err=err):
                self.assertEqual(lps_impact.stage_of(1, err), "checker")
                self.assertEqual(lps_impact.classify("fail", err, stage="checker"), "infra")
                # and the control arm attributes nothing to the move either
                self.assertEqual(lps_impact.classify("fail", err, control="pass", stage="checker"), "infra")

    def test_a_check_that_ran_past_the_limit_is_not_a_model_finding(self):
        self.assertEqual(lps_impact.classify("fail", "FAIL b/h1: the check ran past the 10 s limit",
                                             stage="timeout"), "timeout")

    def test_the_word_exists_alone_is_not_a_witness(self):
        self.assertEqual(lps_impact.classify("fail", "FAIL a/h1: Error: File exists"), "other")
        self.assertEqual(lps_impact.classify("fail", "FAIL a/h1: Error: Unable to satisfy the side condition"),
                         "guard")

    def test_first_error_is_the_first_failing_line(self):
        out = "a/h1: 3 steps\nFAIL a/h1 statements: Error: one\nFAIL a/h1: Error: two\n"
        self.assertEqual(lps_impact.first_error(out), "FAIL a/h1 statements: Error: one")


class Rows(unittest.TestCase):
    def run_tree(self, codes, control=None):
        """Run over the fixture with docker_check stubbed; codes maps a unit to (exit, output)."""
        with tempfile.TemporaryDirectory() as d:
            root, out = tree(os.path.join(d, "tree")), os.path.join(d, "out")
            os.makedirs(out)
            seen = []

            def fake(image, work, tools, pydeps, cache, unit, parts, timeout, proof_jobs=1, tmp=None):
                seen.append((image, unit, parts))
                code, text = codes.get((image, unit), codes.get(unit, (0, "")))
                return code, text, 1.0

            with mock.patch.object(lps_impact, "docker_check", fake), \
                 mock.patch.object(lps_impact, "_worktree", lambda r, w, n, j: r):
                lps_impact.run(root, out, "abc", "img", control=control, scope="all", jobs=1,
                               work_root=os.path.join(d, "w"), line="def", printer=lambda *a: None)
            with open(os.path.join(out, "units.tsv"), encoding="utf-8") as f:
                units = [l.rstrip("\n").split("\t") for l in f]
            with open(os.path.join(out, "impact.tsv"), encoding="utf-8") as f:
                impact = [l.rstrip("\n").split("\t") for l in f]
            return units, impact, seen

    def unit_row(self, units, unit):
        at = {name: i for i, name in enumerate(units[1])}
        row = [r for r in units[2:] if r[0] == unit][0]
        return {name: row[i] for name, i in at.items()}

    def impact_rows(self, impact):
        at = {name: i for i, name in enumerate(impact[0])}
        return {r[0]: {name: r[i] for name, i in at.items()} for r in impact[1:]}

    def test_units_tsv_header_names_commit_image_and_scope(self):
        units, _, _ = self.run_tree({})
        self.assertEqual(units[0][0], "# commit abc image img line def units all")
        self.assertEqual(tuple(units[1]), lps_impact.HEADER_UNITS)
        self.assertEqual(len(units) - 2, 7)

    def test_a_unit_with_a_proof_is_checked_with_both_parts(self):
        _, _, seen = self.run_tree({})
        parts = {u: p for _, u, p in seen}
        self.assertEqual(parts["b/h1"], "statements,proofs")
        self.assertEqual(parts["a/h1"], "statements")

    def test_a_proof_that_passed_in_the_same_run_is_not_reported_broken(self):
        """The defect this command exists to avoid: b/h1 fails, and its proof of extra_halts printed its pass
        line in that very run.  Reporting extra_halts broken invents a break the LPS move did not cause."""
        units, impact, _ = self.run_tree({"b/h1": (1, ONE_OF_TWO)})
        rows = self.impact_rows(impact)
        self.assertEqual(rows["b/h1/plain_halts"]["recheck"], "fail")
        self.assertEqual(rows["b/h1/plain_halts"]["class"], "witness")
        self.assertIn(WITNESS, rows["b/h1/plain_halts"]["first_error"])
        self.assertEqual(rows["b/h1/extra_halts"]["recheck"], "pass")
        self.assertEqual(rows["b/h1/extra_halts"]["class"], "unchanged")
        self.assertEqual(rows["b/h1/extra_halts"]["first_error"], "")
        row = self.unit_row(units, "b/h1")
        self.assertEqual(row["proofs_pass"], EXTRA)
        self.assertEqual(row["proofs_fail"], PLAIN)

    def test_a_pre_existing_break_does_not_hide_a_new_one_in_the_same_unit(self):
        """Both proofs of b/h1 fail in the checker image; in the control image plain_halts fails and
        extra_halts passes.  A per-unit control would call the whole unit pre-existing and hide the break the
        move caused in extra_halts."""
        head = FAILS_PLAIN + FAILS_EXTRA
        control = FAILS_PLAIN + PASSES_EXTRA
        units, impact, seen = self.run_tree({("img", "b/h1"): (1, head), ("ctl", "b/h1"): (1, control)},
                                            control="ctl")
        self.assertIn(("ctl", "b/h1", "statements,proofs"), seen)
        rows = self.impact_rows(impact)
        self.assertEqual(rows["b/h1/plain_halts"]["class"], "pre-existing")
        self.assertEqual(rows["b/h1/extra_halts"]["recheck"], "fail")
        self.assertEqual(rows["b/h1/extra_halts"]["class"], "witness")
        row = self.unit_row(units, "b/h1")
        self.assertEqual(row["control"], "fail")
        self.assertEqual(row["control_stage"], "proofs")
        self.assertEqual(row["control_exit"], "1")

    def test_a_control_run_that_never_reached_a_proof_attributes_nothing_to_it(self):
        head = FAILS_PLAIN + FAILS_EXTRA
        control = FAILS_PLAIN          # the control run ended before extra_halts
        _, impact, _ = self.run_tree({("img", "b/h1"): (1, head), ("ctl", "b/h1"): (1, control)}, control="ctl")
        rows = self.impact_rows(impact)
        self.assertEqual(rows["b/h1/plain_halts"]["class"], "pre-existing")
        self.assertEqual(rows["b/h1/extra_halts"]["class"], "control-infra")

    def test_a_unit_that_could_not_run_is_infra_and_says_what_stopped_it(self):
        units, impact, _ = self.run_tree({"a/h1": (137, "killed")})
        row = self.unit_row(units, "a/h1")
        self.assertEqual((row["result"], row["stage"], row["exit"]), ("infra", "oom-killed", "137"))
        got = self.impact_rows(impact)["a/h1/plain_halts"]
        self.assertEqual((got["recheck"], got["class"], got["stage"]), ("infra", "infra", "oom-killed"))

    def test_a_failure_with_no_diagnostic_is_recorded_as_one(self):
        """The row that a shard whose credential was disabled writes: exit 1 and no output.  It must not be
        indistinguishable from a model finding, in `result` as much as in `class`: a tally of `result == fail`
        is the obvious count of the units the move broke."""
        units, impact, _ = self.run_tree({"a/h1": (1, "")})
        row = self.unit_row(units, "a/h1")
        self.assertEqual((row["result"], row["stage"], row["exit"], row["first_error"]),
                         ("infra", "no-diagnostic", "1", "exit 1"))
        got = self.impact_rows(impact)["a/h1/plain_halts"]
        self.assertEqual((got["recheck"], got["class"]), ("infra", "infra"))

    def test_a_run_the_checker_refused_is_not_a_break_of_the_model(self):
        """In an image or a host where the stack limit cannot be raised, every unit of the run fails this way
        and nothing of the model is examined.  `other` would read as a break the move caused, and `fail` would
        count it as one; and there is no failure to attribute, so the control image is not spent on it."""
        err = "FAIL cannot raise the stack limit: Operation not permitted\n"
        units, impact, seen = self.run_tree({("img", "a/h1"): (1, err), ("ctl", "a/h1"): (0, "")},
                                            control="ctl")
        row = self.unit_row(units, "a/h1")
        self.assertEqual((row["result"], row["stage"], row["exit"]), ("infra", "checker", "1"))
        self.assertEqual(row["control"], "not-run")
        self.assertNotIn(("ctl", "a/h1", "statements"), seen)
        got = self.impact_rows(impact)["a/h1/plain_halts"]
        self.assertEqual((got["recheck"], got["class"], got["stage"]), ("infra", "infra", "checker"))

    def test_result_never_disagrees_with_the_class(self):
        """`result` is the unit's and `class` each statement's, so neither is derived from the other; both
        decide `infra` on INFRA_STAGES, and this pins that they cannot part."""
        for stage, code, text in (("checker", 1, "FAIL cannot raise the stack limit: Operation not permitted\n"),
                                  ("no-diagnostic", 1, ""),
                                  ("oom-killed", 137, "killed"),
                                  ("docker-start", 125, "no such image")):
            with self.subTest(stage=stage):
                units, impact, _ = self.run_tree({"a/h1": (code, text)})
                row = self.unit_row(units, "a/h1")
                self.assertEqual((row["result"], row["stage"]), ("infra", stage))
                self.assertEqual(self.impact_rows(impact)["a/h1/plain_halts"]["class"], "infra")

    def test_a_host_error_while_a_unit_is_checked_is_not_a_tree_that_could_not_be_copied(self):
        with tempfile.TemporaryDirectory() as d:
            root, out = tree(os.path.join(d, "tree")), os.path.join(d, "out")
            os.makedirs(out)

            def boom(*a, **kw):
                raise OSError("docker client: no space left on device")

            with mock.patch.object(lps_impact, "docker_check", boom), \
                 mock.patch.object(lps_impact, "_worktree", lambda r, w, n, j: r):
                lps_impact.run(root, out, "abc", "img", jobs=1, work_root=os.path.join(d, "w"),
                               printer=lambda *a: None)
            with open(os.path.join(out, "units.tsv"), encoding="utf-8") as f:
                units = [l.rstrip("\n").split("\t") for l in f]
        at = {name: i for i, name in enumerate(units[1])}
        for row in units[2:]:
            self.assertEqual(row[at["result"]], "infra")
            self.assertEqual(row[at["stage"]], "host-error")
            self.assertIn("no space left on device", row[at["first_error"]])

    def test_a_library_failure_counts_every_proof_of_the_unit(self):
        """A proof library that does not build fails each proof of the unit in its own FAIL line
        (check.py:511, :819), so each statement is reported broken on its own evidence."""
        err = ("FAIL %s: the proof library does not build: %s\n" % (PLAIN, WITNESS)
               + "FAIL %s: the proof library does not build: %s\n" % (EXTRA, WITNESS))
        _, impact, _ = self.run_tree({"b/h1": (1, err)})
        rows = self.impact_rows(impact)
        self.assertEqual(rows["b/h1/plain_halts"]["recheck"], "fail")
        self.assertEqual(rows["b/h1/plain_halts"]["class"], "witness")
        self.assertEqual(rows["b/h1/extra_halts"]["recheck"], "fail")
        self.assertEqual(rows["a/h1/plain_halts"]["recheck"], "not-run")

    def test_a_failure_is_checked_again_in_the_control_image(self):
        err = "FAIL statements: %s\n" % WITNESS
        _, impact, seen = self.run_tree({("img", "a/h1"): (1, err), ("ctl", "a/h1"): (1, err)}, control="ctl")
        self.assertIn(("ctl", "a/h1", "statements"), seen)
        self.assertEqual(self.impact_rows(impact)["a/h1/plain_halts"]["class"], "pre-existing")

    def test_revision_change_column_says_every_statement_rekeys(self):
        _, impact, _ = self.run_tree({})
        self.assertEqual(impact[0][4], "revision_change")
        self.assertTrue(all(r[4] == "yes" for r in impact[1:]))

    def test_a_proof_failure_is_not_another_statements_failure(self):
        """b/h1 is checked with both parts.  Its proof of plain_halts fails; ubsan_halts has no proof, and the
        statements step passed, so the impact list must not show ubsan_halts broken."""
        _, impact, _ = self.run_tree({"b/h1": (1, FAILS_PLAIN)})
        rows = self.impact_rows(impact)
        self.assertEqual(rows["b/h1/plain_halts"]["recheck"], "fail")
        self.assertEqual(rows["b/h1/ubsan_halts"]["recheck"], "not-run")
        self.assertEqual(rows["b/h1/ubsan_halts"]["class"], "not-attributed")

    def test_a_statements_failure_is_every_statements_failure(self):
        err = "FAIL statements: dune build failed (see /tmp/dune.log)\n"
        said = io.StringIO()
        with contextlib.redirect_stderr(said):
            _, impact, _ = self.run_tree({"b/h1": (1, err)})
        rows = self.impact_rows(impact)
        self.assertEqual(rows["b/h1/plain_halts"]["recheck"], "fail")
        self.assertEqual(rows["b/h1/ubsan_halts"]["recheck"], "fail")
        self.assertEqual(rows["b/h1/ubsan_halts"]["class"], "other")
        # /tmp/dune.log is not under /oftwork/, so it is no log of b/h1: one line refuses it
        self.assertEqual(said.getvalue().splitlines(), [REFUSED % ("b__h1", "/tmp/dune.log")])

    def test_units_tsv_says_what_the_control_image_did(self):
        err = "FAIL statements: %s\n" % WITNESS
        units, impact, _ = self.run_tree({("img", "a/h1"): (1, err), ("ctl", "a/h1"): (125, "no such image")},
                                         control="ctl")
        row = self.unit_row(units, "a/h1")
        self.assertEqual((row["control"], row["control_exit"], row["control_stage"]),
                         ("infra", "125", "docker-start"))
        self.assertEqual(self.unit_row(units, "b/h1")["control"], "not-run")
        self.assertEqual(self.impact_rows(impact)["a/h1/plain_halts"]["class"], "control-infra")

    def test_a_worker_whose_tree_cannot_be_made_says_so_in_every_row(self):
        with tempfile.TemporaryDirectory() as d:
            root, out = tree(os.path.join(d, "tree")), os.path.join(d, "out")
            os.makedirs(out)

            def boom(*a):
                raise OSError("No space left on device")

            with mock.patch.object(lps_impact, "_worktree", boom):
                lps_impact.run(root, out, "abc", "img", jobs=2, work_root=os.path.join(d, "w"),
                               printer=lambda *a: None)
            with open(os.path.join(out, "units.tsv"), encoding="utf-8") as f:
                units = [l.rstrip("\n").split("\t") for l in f]
        at = {name: i for i, name in enumerate(units[1])}
        for row in units[2:]:
            self.assertEqual(row[at["result"]], "infra")
            self.assertEqual(row[at["stage"]], "worker-tree")
            self.assertIn("No space left on device", row[at["first_error"]])


class Diagnostic(unittest.TestCase):
    """Finding 6: the Rocq log a failure names is written under the container's TMPDIR, and the container is
    --rm.  Without the mount and the copy, every failure names a file that no longer exists."""

    def read_back(self, text, dest):
        """What _arm makes of the output `text` with the logs harvested into `dest`, a directory named
        `<name>.d`: (the unit's error, {proof: its error}, the lines written on standard error).  docker_check is
        stubbed to give exit 1 with `text`."""
        logs, base = os.path.split(dest)
        self.assertTrue(base.endswith(".d"), dest)
        said = io.StringIO()
        with mock.patch.object(lps_impact, "docker_check", lambda *a, **kw: (1, text, 0.0)), \
             contextlib.redirect_stderr(said):
            a = lps_impact._arm("img", "/w", "/t", "/p", logs, "b/h1", "statements,proofs", 10, 1, logs,
                                base[:-len(".d")], None)
        return a["error"], a["failed"], said.getvalue().splitlines()

    def harvested(self, d):
        """The harvested logs of b/h1 under d, logs/b__h1.d/, with one log, oft-check-a/x.log, that holds an
        `Error:` line."""
        dest = os.path.join(d, "logs", "b__h1.d")
        write(os.path.join(dest, "oft-check-a", "x.log"), "Compiling Proof.v\nError: marker-x\n")
        return dest

    def test_the_container_gets_a_work_directory_of_the_host_for_tmpdir(self):
        calls = []
        with mock.patch.object(lps_impact.subprocess, "run",
                               lambda cmd, **kw: calls.append(cmd) or mock.Mock(returncode=0, stdout="",
                                                                                stderr="")):
            lps_impact.docker_check("img", "/w", "/t", "/p", "/c", "a/h1", "statements", 10, tmp="/host/work")
        cmd = " ".join(calls[0])
        self.assertIn("-e TMPDIR=/oftwork", cmd)
        self.assertIn("-v /host/work:/oftwork", cmd)
        self.assertLess(cmd.index("/oftwork"), cmd.index(" img "))

    def test_the_log_the_error_names_is_copied_out_and_read_into_the_error(self):
        with tempfile.TemporaryDirectory() as d:
            tmp, dest = os.path.join(d, "tmp"), os.path.join(d, "dest")
            os.makedirs(os.path.join(tmp, "oft-check-x", "proof-y"))
            with open(os.path.join(tmp, "oft-check-x", "proof-y", "wrapper.log"), "w", encoding="utf-8") as f:
                f.write("Compiling Wrapper.v\n"
                        "Error: The term f has type A while it is expected to have type B -> C.\n")
            self.assertEqual(lps_impact.harvest_logs(tmp, dest), 1)
            err = ("FAIL %s: the wrapper does not type-check: the proof is not of this statement "
                   "(see /oftwork/oft-check-x/proof-y/wrapper.log)" % PLAIN)
            got = lps_impact.with_detail(err, lps_impact.fail_details(err, dest, "b__h1"))
            self.assertIn("Error: The term f has type A", got)
            # without the diagnostic this reads `other`: the class is only as good as the log
            self.assertEqual(lps_impact.classify("fail", err, stage="proofs"), "other")
            self.assertEqual(lps_impact.classify("fail", got, stage="proofs"), "arity")

    def test_an_error_that_names_no_log_of_ours_is_left_alone(self):
        with tempfile.TemporaryDirectory() as d:
            line, dest = "FAIL statements: boom (see /tmp/dune.log)", os.path.join(d, "b__h1.d")
            self.assertEqual(self.read_back(line, dest), (line, {}, [REFUSED % ("b__h1", "/tmp/dune.log")]))

    def test_a_link_the_container_left_is_not_copied_into_the_evidence(self):
        """The container is the thing being measured and it chose these paths: a link it leaves behind would
        copy a file of this host into a unit's published evidence."""
        with tempfile.TemporaryDirectory() as d:
            tmp, dest = os.path.join(d, "tmp"), os.path.join(d, "dest")
            os.makedirs(os.path.join(tmp, "oft-check-x"))
            outside = os.path.join(d, "secret.txt")
            with open(outside, "w", encoding="utf-8") as f:
                f.write("Error: a file of this host\n")
            os.symlink(outside, os.path.join(tmp, "oft-check-x", "stolen.log"))
            os.symlink(os.path.dirname(outside), os.path.join(tmp, "elsewhere"))
            with open(os.path.join(tmp, "oft-check-x", "wrapper.log"), "w", encoding="utf-8") as f:
                f.write("Error: Unable to unify\n")
            self.assertEqual(lps_impact.harvest_logs(tmp, dest), 1)
            self.assertTrue(os.path.exists(os.path.join(dest, "oft-check-x", "wrapper.log")))
            self.assertFalse(os.path.exists(os.path.join(dest, "oft-check-x", "stolen.log")))
            self.assertFalse(os.path.exists(os.path.join(dest, "elsewhere")))

    def test_a_path_that_climbs_out_of_the_unit_directory_is_not_read(self):
        with tempfile.TemporaryDirectory() as d:
            dest = os.path.join(d, "dest.d")
            os.makedirs(dest)
            with open(os.path.join(d, "outside.log"), "w", encoding="utf-8") as f:
                f.write("Error: a file of this host\n")
            os.symlink(os.path.join(d, "outside.log"), os.path.join(dest, "linked.log"))
            for named in ("/oftwork/../outside.log", "/oftwork/x/../../outside.log", "/oftwork/linked.log"):
                with self.subTest(named=named):
                    err = "FAIL %s: the wrapper does not type-check (see %s)" % (PLAIN, named)
                    self.assertEqual(lps_impact.log_detail(named, dest), ("", True))
                    self.assertEqual(self.read_back(err, dest), (err, {PLAIN: err}, [REFUSED % ("dest", named)]))

    def test_a_fail_line_that_names_a_file_of_this_host_is_refused(self):
        """Neither path is under /oftwork/, so neither is a log of this unit: nothing is read, and each path is
        one line on standard error."""
        with tempfile.TemporaryDirectory() as d:
            dest = self.harvested(d)
            outside = os.path.join(d, "outside.log")
            write(outside, "Error: marker-outside\n")
            for named in ("/etc/passwd", outside):
                with self.subTest(named=named):
                    line = "FAIL %s: does not compile (see %s)" % (PLAIN, named)
                    self.assertEqual(self.read_back(line, dest),
                                     (line, {PLAIN: line}, [REFUSED % ("b__h1", named)]))

    def test_a_relative_path_is_refused(self):
        """From this unit's logs, `../other-run/log` is a file of another run."""
        with tempfile.TemporaryDirectory() as d:
            dest = self.harvested(d)
            write(os.path.join(d, "logs", "other-run", "log"), "Error: marker-other\n")
            line = "FAIL %s: does not compile (see ../other-run/log)" % PLAIN
            self.assertEqual(self.read_back(line, dest),
                             (line, {PLAIN: line}, [REFUSED % ("b__h1", "../other-run/log")]))

    def test_a_path_with_dotdot_is_refused_where_it_resolves_to_a_log_of_the_unit(self):
        """The `..` alone refuses it: the same log, named without one, is read."""
        with tempfile.TemporaryDirectory() as d:
            dest = self.harvested(d)
            named = "/oftwork/oft-check-a/../oft-check-a/x.log"
            line = "FAIL %s: does not compile (see %s)" % (PLAIN, named)
            self.assertEqual(self.read_back(line, dest), (line, {PLAIN: line}, [REFUSED % ("b__h1", named)]))
            unit, _, said = self.read_back(line.replace(named, "/oftwork/oft-check-a/x.log"), dest)
            self.assertEqual((unit.endswith(" | Error: marker-x"), said), (True, []))

    def test_a_path_that_holds_a_nul_is_refused_and_the_arm_goes_on(self):
        """os.path.realpath raises on a NUL: without the refusal one forged line would end the unit's read."""
        with tempfile.TemporaryDirectory() as d:
            dest = self.harvested(d)
            named = "/oftwork/oft-check-a/x.log\0"
            line = "FAIL %s: does not compile (see %s)" % (PLAIN, named)
            self.assertEqual(self.read_back(line, dest), (line, {PLAIN: line}, [REFUSED % ("b__h1", named)]))

    def test_a_path_on_a_line_that_is_not_a_fail_line_is_never_read(self):
        """first_error takes an `error: ` line as the unit's first error, but only a `FAIL ` line names a log."""
        with tempfile.TemporaryDirectory() as d:
            dest = self.harvested(d)
            line = "error: the statements do not compile (see /oftwork/oft-check-a/x.log)"
            self.assertEqual(self.read_back(line, dest), (line, {}, []))

    def test_a_log_named_after_the_400_characters_a_row_keeps_is_still_read(self):
        with tempfile.TemporaryDirectory() as d:
            dest = self.harvested(d)
            line = "FAIL %s: does not compile: %s (see /oftwork/oft-check-a/x.log)" % (PLAIN, "x" * 400)
            self.assertGreater(line.index("(see "), 400)
            unit, proofs, said = self.read_back(line, dest)
            self.assertNotIn("(see ", unit)
            self.assertTrue(unit.endswith(" | Error: marker-x"), unit)
            self.assertEqual((proofs, said), ({PLAIN: unit}, []))

    def test_a_log_of_the_unit_that_is_not_there_gives_no_detail_and_no_line(self):
        with tempfile.TemporaryDirectory() as d:
            dest = self.harvested(d)
            line = "FAIL %s: does not compile (see /oftwork/oft-check-a/gone.log)" % PLAIN
            self.assertEqual(self.read_back(line, dest), (line, {PLAIN: line}, []))

    def test_a_forged_path_that_two_fail_lines_name_is_one_line(self):
        with tempfile.TemporaryDirectory() as d:
            dest = self.harvested(d)
            lines = ["FAIL %s: does not compile (see /etc/passwd)" % p for p in (PLAIN, EXTRA)]
            self.assertEqual(self.read_back("\n".join(lines) + "\n", dest),
                             (lines[0], {PLAIN: lines[0], EXTRA: lines[1]}, [REFUSED % ("b__h1", "/etc/passwd")]))

    def test_check_one_copies_the_logs_out_and_removes_the_work_directory(self):
        with tempfile.TemporaryDirectory() as d:
            logs, tmp_root = os.path.join(d, "logs"), os.path.join(d, "work")
            os.makedirs(logs)
            os.makedirs(tmp_root)
            err = ("FAIL %s: the wrapper does not type-check "
                   "(see /oftwork/oft-check-x/wrapper.log)" % PLAIN)

            def fake(image, work, tools, pydeps, cache, unit, parts, timeout, proof_jobs=1, tmp=None):
                os.makedirs(os.path.join(tmp, "oft-check-x"))
                with open(os.path.join(tmp, "oft-check-x", "wrapper.log"), "w", encoding="utf-8") as f:
                    f.write("Error: Unable to unify the witness with the goal\n")
                with open(os.path.join(tmp, "oft-check-x", "Wrapper.vo"), "wb") as f:
                    f.write(b"\x00" * 16)
                return 1, err, 2.0

            with mock.patch.object(lps_impact, "docker_check", fake):
                row = lps_impact.check_one("/w", "/t", "/p", d, "b/h1", "statements,proofs", "img", None, 10,
                                           logs, 1, tmp_root=tmp_root)
            self.assertFalse(os.path.exists(os.path.join(tmp_root, "b__h1")))
            kept = os.path.join(logs, "b__h1.d", "oft-check-x")
            self.assertTrue(os.path.exists(os.path.join(kept, "wrapper.log")))
            self.assertFalse(os.path.exists(os.path.join(kept, "Wrapper.vo")))
            self.assertIn("Unable to unify", row["proofs_fail"][PLAIN])
            self.assertEqual(row["stage"], "proofs")
            self.assertEqual(row["exit"], 1)


# A stand-in for docker, run as `python3 STAND_IN run ... -v <host>:/oftwork ... python3 -m oft.check --root /work
# <unit> --parts <parts>`.  For a/h1 and b/h1 it plants logs under <host>, the container's TMPDIR, each with an
# `Error:` line that holds a marker word of its own, prints lines that name them, and exits 1.  Every other unit
# passes with no output.
STAND_IN = r'''import os
import sys

args = sys.argv[1:]
unit = args[args.index("--root") + 2]
host = [a[:-len(":/oftwork")] for a in args if a.endswith(":/oftwork")][0]


def plant(name, marker):
    os.makedirs(os.path.join(host, "oft-check-a"), exist_ok=True)
    with open(os.path.join(host, "oft-check-a", name), "w", encoding="utf-8") as f:
        f.write("Compiling Proof.v\nError: " + marker + "\n")


if unit == "a/h1":
    plant("inrun.log", "marker-inrun")
    print("error: the statements do not compile (see /oftwork/oft-check-a/inrun.log)")
    sys.exit(1)
if unit == "b/h1":
    plant("dotdot.log", "marker-dotdot")
    plant("real.log", "marker-real")
    lib = "FAIL projects/b/h1/proofs/lib: the proof library does not build (see %s)"
    print("FAIL projects/b/h1/proofs/plain_halts: does not compile "
          "(see /oftwork/oft-check-a/../oft-check-a/dotdot.log)")
    print(lib % "/etc/passwd")
    print(lib % "../other-run/log")
    print(lib % os.environ["STAND_IN_OUTSIDE"])
    print("FAIL projects/b/h1/proofs/extra_halts: does not compile (see /oftwork/oft-check-a/real.log)")
    sys.exit(1)
'''


class StandInDocker(unittest.TestCase):
    """`python3 -m oft.lps_impact` itself, as a process, with OFT_DOCKER a stand-in for docker that prints lines
    naming forged log paths.  `oft check` starts each line of a log it quotes with `  | ` (check.py QUOTE), so its
    real output cannot start a line with a path a proof wrote: this is the reader's second barrier.  The class
    reads only the command's output and the files it writes, and calls no function of lps_impact, so it runs the
    same against any version of that module."""

    MARKERS = ("marker-real", "marker-inrun", "marker-dotdot", "marker-outside", "marker-other")
    maxDiff = None              # a failure shows each marker that reached a row, and each refusal line

    def marked(self, path):
        """(first column, marker) for each marker that a row of the TSV file `path` holds."""
        with open(path, encoding="utf-8") as f:
            return sorted((row.split("\t")[0], m) for row in f for m in self.MARKERS if m in row)

    def test_only_a_fail_line_names_a_log_and_each_forged_path_is_refused_once(self):
        with tempfile.TemporaryDirectory() as d:
            root, out = tree(os.path.join(d, "tree")), os.path.join(d, "out")
            outside = os.path.join(d, "outside.log")
            write(outside, "Error: marker-outside\n")
            # where `../other-run/log` resolves from b/h1's harvested logs, out/logs/b__h1.d/
            write(os.path.join(out, "logs", "other-run", "log"), "Error: marker-other\n")
            docker = os.path.join(d, "docker.py")
            write(docker, STAND_IN)
            env = dict(os.environ, OFT_DOCKER="%s %s" % (sys.executable, docker), STAND_IN_OUTSIDE=outside,
                       PYTHONPATH=TOOLS, PYTHONDONTWRITEBYTECODE="1")
            done = subprocess.run([sys.executable, "-m", "oft.lps_impact", "--root", root, "--commit", "c1",
                                   "--checker-image", "stand-in", "--units", "all", "--jobs", "1",
                                   "--work", os.path.join(d, "w"), "--out", out],
                                  cwd=d, env=env, capture_output=True, text=True, timeout=300)
            self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
            logs = ("a__h1.d/oft-check-a/inrun.log", "b__h1.d/oft-check-a/dotdot.log",
                    "b__h1.d/oft-check-a/real.log")
            got = {"harvested": [p for p in logs if os.path.isfile(os.path.join(out, "logs", p))],
                   "units.tsv": self.marked(os.path.join(out, "units.tsv")),
                   "impact.tsv": self.marked(os.path.join(out, "impact.tsv")),
                   "refused": [l for l in done.stderr.splitlines() if l.startswith("lps-impact: ")]}
        self.assertEqual(got, {
            # the logs the forged paths resolve to inside the run were there to be read
            "harvested": list(logs),
            # a/h1's first error is its `error: ` line, and b/h1's is the refused plain_halts line
            "units.tsv": [],
            "impact.tsv": [("b/h1/extra_halts", "marker-real")],
            "refused": [REFUSED % ("b__h1", p) for p in ("/oftwork/oft-check-a/../oft-check-a/dotdot.log",
                                                         "/etc/passwd", "../other-run/log", outside)]})


class Timeout(unittest.TestCase):
    def test_a_timed_out_check_removes_its_container(self):
        """subprocess.run's timeout kills the docker client; the daemon keeps running the container, which
        would go on building in the same /work the next unit is checked in."""
        calls = []

        def fake_run(cmd, **kw):
            calls.append(cmd)
            if "run" in cmd:
                raise subprocess.TimeoutExpired(cmd, kw.get("timeout", 1))
            return mock.Mock(returncode=0, stdout="", stderr="")

        with mock.patch.object(lps_impact.subprocess, "run", fake_run):
            code, text, _ = lps_impact.docker_check("img", "/w", "/t", "/p", "/c", "a/h1", "statements", 1)
        self.assertEqual(code, 124)
        name = calls[0][calls[0].index("--name") + 1]
        self.assertTrue(name.startswith("lps-impact-"))
        self.assertEqual(calls[1], ["docker", "rm", "-f", name])
        self.assertIn("the container %s was removed" % name, text)

    def test_a_container_that_could_not_be_removed_is_said_so_in_the_row(self):
        def fake_run(cmd, **kw):
            if "run" in cmd:
                raise subprocess.TimeoutExpired(cmd, 1)
            return mock.Mock(returncode=1, stdout="", stderr="No such container")

        with mock.patch.object(lps_impact.subprocess, "run", fake_run):
            code, text, _ = lps_impact.docker_check("img", "/w", "/t", "/p", "/c", "a/h1", "statements", 1)
        self.assertEqual(code, 124)
        self.assertIn("could not be removed: No such container", text)
        self.assertEqual(lps_impact.stage_of(code, lps_impact.first_error(text)), "timeout")


class Flags(unittest.TestCase):
    def test_the_command_line_has_one_definition_of_its_flags(self):
        """`./oft lps-impact` builds its subparser from lps_impact.add_arguments, as `oft check` and `oft fetch`
        do, so no flag, default or help text can drift between two copies."""
        self.assertFalse(hasattr(lps_impact, "main"))
        from oft import __main__ as entry
        got = {}
        with tempfile.TemporaryDirectory() as d:
            with mock.patch.object(lps_impact, "run", lambda *a, **kw: got.update(kw) or 0):
                rc = entry.main(["--root", d, "lps-impact", "--commit", "c", "--checker-image", "i",
                                 "--shard", "2/3", "--jobs", "3", "--out", os.path.join(d, "out")])
            self.assertTrue(os.path.isdir(os.path.join(d, "out")))
        self.assertEqual(rc, 0)
        self.assertEqual(got["shard_spec"], (2, 3))
        self.assertEqual(got["jobs"], 3)


class Checker(unittest.TestCase):
    def test_does_not_touch_the_checker_key(self):
        self.assertTrue(keys.not_the_checker("tools/oft/lps_impact.py"))

    def test_runs_the_unit_as_check_units_runs_it(self):
        calls = []
        with mock.patch.object(lps_impact.subprocess, "run",
                               lambda cmd, **kw: calls.append(cmd) or mock.Mock(returncode=0, stdout="", stderr="")):
            lps_impact.docker_check("img", "/w", "/t", "/p", "/c", "a/h1", "statements", 10)
        cmd = " ".join(calls[0])
        self.assertIn("--network none", cmd)
        self.assertIn("python3 -m oft.check --root /work a/h1 --parts statements", cmd)
        self.assertTrue(re.search(r"DUNE_CACHE_STORAGE_MODE=copy", cmd))


if __name__ == "__main__":
    unittest.main()
