"""oft lps-impact: the consumer impact list of an LPS commit."""
import argparse
import os
import re
import subprocess
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


def tree(d):
    os.makedirs(os.path.join(d, "index"), exist_ok=True)
    for name, text in (("harnesses.tsv", HARNESSES), ("proofs.tsv", PROOFS), ("statements.tsv", STATEMENTS)):
        with open(os.path.join(d, "index", name), "w", encoding="utf-8") as f:
            f.write(text)
    return d


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
        _, impact, _ = self.run_tree({"b/h1": (1, err)})
        rows = self.impact_rows(impact)
        self.assertEqual(rows["b/h1/plain_halts"]["recheck"], "fail")
        self.assertEqual(rows["b/h1/ubsan_halts"]["recheck"], "fail")
        self.assertEqual(rows["b/h1/ubsan_halts"]["class"], "other")

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
            got = lps_impact.with_detail(err, dest)
            self.assertIn("Error: The term f has type A", got)
            # without the diagnostic this reads `other`: the class is only as good as the log
            self.assertEqual(lps_impact.classify("fail", err, stage="proofs"), "other")
            self.assertEqual(lps_impact.classify("fail", got, stage="proofs"), "arity")

    def test_an_error_that_names_no_log_of_ours_is_left_alone(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(lps_impact.with_detail("FAIL statements: boom (see /tmp/dune.log)", d),
                             "FAIL statements: boom (see /tmp/dune.log)")

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
            dest = os.path.join(d, "dest")
            os.makedirs(dest)
            with open(os.path.join(d, "outside.log"), "w", encoding="utf-8") as f:
                f.write("Error: a file of this host\n")
            os.symlink(os.path.join(d, "outside.log"), os.path.join(dest, "linked.log"))
            for named in ("/oftwork/../outside.log", "/oftwork/x/../../outside.log", "/oftwork/linked.log"):
                with self.subTest(named=named):
                    err = "FAIL %s: the wrapper does not type-check (see %s)" % (PLAIN, named)
                    self.assertEqual(lps_impact.log_detail(err, dest), "")
                    self.assertEqual(lps_impact.with_detail(err, dest), err)

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
