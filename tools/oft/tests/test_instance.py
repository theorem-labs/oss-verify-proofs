"""A statement's instance (harness.yaml statements.<s>.instance, OSSV-484 R4): the input shapes.instance_input renders
from the record and the file's bytes, the type shapes.instance_type gives its lemma for each shape, and how oft check
checks it (check.check_instance, check.audit_instance), in the unit path a farm job takes too and never in a
statement's process of proofs_apart.  tests/check.sh's instance controls (tests/instances/) check the lemmas
themselves in Rocq."""
import glob
import hashlib
import io
import os
import re
import tempfile
import unittest
from unittest import mock

from oft import check, facts, layout, shapes
from oft.tests.helpers import REPO, edit
from oft.tests.test_lint import ZLIB_HARNESS, ported_tree, put_instance

UNIT = "zlib/checksum_fuzzer"
DIST = {"distribution": {"argv0": "ab", "input_file": "in"}}
PROG, FILE = "[Z_to_bv 8 97; Z_to_bv 8 98]", "[Z_to_bv 8 105; Z_to_bv 8 110]"
DATA = b"\x00\x01"
DATA_TERM = "[Z_to_bv 8 0; Z_to_bv 8 1]"
REST = "IEof (Z_to_bv 64 0) (Z_to_bv 64 0) [] net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc"


def fields(kind, builds, reading, path="reaches-harness", **over):
    return dict({"kind": kind, "builds": builds, "reading": reading,
                 "instance": {"file": "in.bin", "sha256": "0" * 64, "bytes": 2, "path": path}}, **over)


HALTS = fields("halts", ["plain"], "budget", exits=[0, 2])
MAY_FAIL = fields("halts", ["ubsan"], "may-fail", exits="any")
BOUND = fields("bound", ["plain", "asan"], "may-fail")
DECIDABLE = fields("decidability", ["plain", "asan"], "alloc-forced-only")


def agreement(reading, abort="error", machine="rv64g", budgets="asan"):
    out = fields("agreement", ["plain", "asan"], reading, budgets=budgets, abort=abort)
    if machine != "rv64g":
        out["machine"] = machine
    return out


class InstanceInput(unittest.TestCase):
    """instance_input: argv follows the record's path, the file system holds the input file with the instance file's
    bytes, and the other fields are Premises.witness_input's; the abort declaration is the shape's."""

    def test_reaches_harness_reads_the_file(self):
        self.assertEqual(shapes.instance_input(DIST, HALTS, DATA),
                         "mkProcInput [%s; %s] [] [(%s, %s)] %s false Sv48" % (PROG, FILE, FILE, DATA_TERM, REST))

    def test_refused_by_driver_has_argv0_alone(self):
        self.assertEqual(shapes.instance_input(DIST, fields("halts", ["plain"], "budget", "refused-by-driver"), b""),
                         "mkProcInput [%s] [] [(%s, [])] %s false Sv48" % (PROG, FILE, REST))

    def test_the_abort_declaration_is_the_shapes(self):
        for st, abort in ((agreement("may-fail", "signal"), "true"), (agreement("alloc-forced-only", "signal"), "true"),
                          (agreement("may-fail", "signal", "rv64gc"), "true"), (agreement("may-fail"), "false"),
                          (agreement("alloc-forced-only", machine="rv64gc"), "false"), (HALTS, "false"),
                          (MAY_FAIL, "false")):
            with self.subTest(st=st):
                self.assertTrue(shapes.instance_input(DIST, st, DATA).endswith(" %s Sv48" % abort))

    def test_the_abort_declaration_reads_valid_input_abort_on_every_agreement_shape(self):
        """instance_abort decides from the statement's abort; on each shape of AGREEMENT that is whether its input
        predicate (agreement_premises, which test_the_agreement_premises_are_those_of_shapes_v holds to
        theories/Shapes.v) is valid_input_abort."""
        for (reading, abort, machine), shape in shapes.AGREEMENT.items():
            with self.subTest(shape=shape):
                st = agreement(reading, abort, machine)
                read = "abort" in shapes.agreement_premises(st)[0]
                self.assertEqual(read, abort == "signal")
                self.assertEqual(shapes.instance_abort(st), read)

    def test_a_finite_input_is_the_core_distribution_v_builds(self):
        for st in (BOUND, DECIDABLE, dict(BOUND, machine="rv64gc"), dict(DECIDABLE, machine="rv64gc")):
            with self.subTest(st=st):
                self.assertTrue(shapes.instance_finite(st))
                self.assertEqual(shapes.instance_input(DIST, st, DATA), "core_input (file_core [%s; %s] [] [(%s, [])] "
                                 "%s [] %s)" % (PROG, FILE, FILE, FILE, DATA_TERM))
        self.assertEqual(shapes.instance_input(DIST, dict(BOUND, instance=dict(BOUND["instance"],
                                                                               path="refused-by-driver")), b""),
                         "core_input (file_core [%s] [] [(%s, [])] %s [] [])" % (PROG, FILE, FILE))
        self.assertFalse(shapes.instance_finite(HALTS))

    def test_with_no_distribution_the_harness_name_and_input_bin(self):
        """A harness with no distribution: argv0 is the harness's name, the input file input.bin."""
        prog, file = shapes.bytes_term(b"fuzz_one"), shapes.bytes_term(b"input.bin")
        self.assertEqual(shapes.instance_input({"harness": "fuzz_one"}, HALTS, DATA),
                         "mkProcInput [%s; %s] [] [(%s, %s)] %s false Sv48" % (prog, file, file, DATA_TERM, REST))
        self.assertEqual(shapes.instance_input({"harness": "fuzz_one"}, fields("halts", ["plain"], "budget",
                                                                                "refused-by-driver"), b""),
                         "mkProcInput [%s] [] [(%s, [])] %s false Sv48" % (prog, file, REST))

    def test_another_path_is_refused(self):
        self.assertRaisesRegex(shapes.ShapeError, "instance path 'elsewhere' has no input form", shapes.instance_input,
                               DIST, fields("halts", ["plain"], "budget", "elsewhere"), DATA)


class InstanceType(unittest.TestCase):
    """instance_type: the hypotheses of the statement's shape over oft_input, one form per shape."""

    def test_halts_within_budget(self):
        self.assertEqual(shapes.instance_type(HALTS),
                         r"exists en, valid_entry Images.plain en oft_input /\ valid_input oft_input /\ "
                         r"~ run_scfg_budget_refused forced_only_cfg Images.plain Budgets.Standard.lim_source en "
                         r"oft_input")

    def test_halts_may_fail(self):
        self.assertEqual(shapes.instance_type(MAY_FAIL),
                         r"exists en, valid_entry Images.ubsan en oft_input /\ valid_input oft_input")

    def test_each_agreement_shape(self):
        pre = r"exists ep es, valid_entry Images.plain ep oft_input /\ valid_entry Images.asan es oft_input /\ "
        run = r"~ run_budget_refused Images.plain Budgets.Asan.lim_source ep oft_input"
        scfg = r"~ run_scfg_budget_refused Env.alloc_forced_only Images.plain Budgets.Asan.lim_source ep oft_input"
        want = {
            ("may-fail", "error", "rv64g"): "valid_input oft_input /\\ " + run,
            ("may-fail", "signal", "rv64g"): "valid_input_abort oft_input /\\ " + run,
            ("alloc-forced-only", "error", "rv64g"): "valid_input oft_input /\\ " + scfg,
            ("alloc-forced-only", "signal", "rv64g"): "valid_input_abort oft_input /\\ " + scfg,
            ("may-fail", "error", "rv64gc"): "valid_input_hwcap_rv64gc oft_input /\\ " + run,
            ("may-fail", "signal", "rv64gc"): "valid_input_abort_hwcap_rv64gc oft_input /\\ " + run,
            ("alloc-forced-only", "error", "rv64gc"): "valid_input_hwcap_rv64gc oft_input /\\ " + scfg,
        }
        self.assertEqual(set(want), set(shapes.AGREEMENT))
        for (reading, abort, machine), rest in want.items():
            with self.subTest(shape=shapes.AGREEMENT[reading, abort, machine]):
                self.assertEqual(shapes.instance_type(agreement(reading, abort, machine)), pre + rest)

    def test_an_agreement_with_the_projects_own_budgets(self):
        project = {"budgets": {"agrees": {"address": ["4GiB", "1TiB"]}}}
        st = agreement("may-fail", "signal")
        del st["budgets"]
        self.assertTrue(shapes.instance_type(st, project).endswith(
            "~ run_budget_refused Images.plain 0x100000000%Z ep oft_input"))

    def test_the_finite_shapes(self):
        p = "(to_proc_input oft_input)"
        entries = r"(exists ep es, valid_entry Images.plain ep %s /\ valid_entry Images.asan es %s)" % (p, p)
        for st in (BOUND, DECIDABLE):
            with self.subTest(kind=st["kind"]):
                self.assertEqual(shapes.instance_type(st), r"valid_fin_input oft_input /\ " + entries)
                self.assertEqual(shapes.instance_type(dict(st, machine="rv64gc")),
                                 r"valid_fin_input oft_input /\ in_hwcap %s = hwcap_rv64gc /\ %s" % (p, entries))

    def test_fields_that_choose_no_shape_are_refused(self):
        """instance_type takes its form from the fields that choose the shape, so fields that choose none are refused
        as term() refuses them."""
        for st, why in ((agreement("alloc-forced-only", "signal", "rv64gc"), "^no agreement shape for reading/abort/"),
                        (fields("halts", ["plain"], "alloc-forced-only"), "^halts statements have the readings"),
                        (fields("bound", ["plain", "asan"], "budget"), "^pair statements have the readings")):
            with self.subTest(st=st):
                self.assertRaisesRegex(shapes.ShapeError, why, shapes.instance_type, st)

    def test_the_agreement_premises_are_those_of_shapes_v(self):
        """agreement_premises, from the fields of each combination of AGREEMENT, reads theories/Shapes.v's definition
        of the shape AGREEMENT names: its input predicate, and its budget premise over run_scfg under the environment
        or over run."""
        with open(os.path.join(REPO, "theories", "Shapes.v"), encoding="utf-8") as f:
            text = f.read()
        for (reading, abort, machine), shape in shapes.AGREEMENT.items():
            with self.subTest(shape=shape):
                predicate, scfg = shapes.agreement_premises(agreement(reading, abort, machine))
                body = re.search(r"Definition %s \(.*?\n\n" % shape, text, re.S).group(0)
                self.assertIn("    %s inp ->\n" % predicate, body)
                self.assertIn("~ run_scfg_budget_refused env plain" if scfg else "~ run_budget_refused plain", body)


class RequiredProjects(unittest.TestCase):
    """REQUIRED is in shapes.py, the checker, which lint reads too; deviation.py, which oft check never opens, does
    not hold it."""

    def test_required_is_the_checkers(self):
        from oft import deviation
        self.assertEqual(shapes.REQUIRED, ())
        self.assertFalse(hasattr(deviation, "REQUIRED"))


def statement(project, data):
    """A statement plain_halts of fuzz target toy/exit0, with distribution DIST, in project `project`."""
    h = facts.Harness(facts.Project(facts.Tree("/nonexistent"), project, {}), "exit0",
                      dict(DIST, rocq="OSSVerify.Tests.toy.exit0"))
    return facts.Statement(h, "plain_halts", data)


class AuditInstance(unittest.TestCase):
    """audit_instance without Rocq: a missing lemma, a file that is not its record's, and the wrapper it writes."""

    def setUp(self):
        self.d = tempfile.TemporaryDirectory()
        self.addCleanup(self.d.cleanup)
        self.data = os.path.join(self.d.name, "in.bin")
        with open(self.data, "wb") as f:
            f.write(DATA)
        self.lemma = os.path.join(self.d.name, "plain_halts.v")

    def audit(self, st, required=(), compilation=None, loadpath=lambda: ["-Q", "lib", "Lib"]):
        out = io.StringIO()
        check.audit_instance(st, "toy/exit0", self.data, self.lemma, "lib/Instances/plain_halts.v", loadpath,
                             "Lib.Instances.plain_halts", "OSSVerify.Core", required, {"Ax.ok"}, self.d.name, out,
                             compilation=compilation)
        return out.getvalue()

    def record(self, **over):
        return dict(HALTS, instance=dict(dict(HALTS["instance"], sha256=hashlib.sha256(DATA).hexdigest()), **over))

    def test_a_missing_lemma_fails_only_a_required_project(self):
        st = statement("toy", self.record())
        self.assertEqual(self.audit(st), "toy/exit0: instance of toy/exit0/plain_halts at in.bin (reaches-harness): has "
                                         "no lemma (lib/Instances/plain_halts.v), and project toy does not require one\n")
        with self.assertRaises(check.InstanceError) as e:
            self.audit(st, required=("toy",))
        self.assertEqual(e.exception.step, "missing")
        self.assertEqual(str(e.exception), "no lemma plain_halts_instance: lib/Instances/plain_halts.v is missing, and "
                                           "project toy requires one for every statement")

    def test_a_file_that_is_not_its_records_fails_always(self):
        open(self.lemma, "w").close()
        for over, words in (({"bytes": 3}, "has 2 bytes and sha256 "), ({"sha256": "f" * 64}, "not the record's 2")):
            with self.subTest(over=over), self.assertRaises(check.InstanceError) as e:
                self.audit(statement("toy", self.record(**over)))
            self.assertEqual(e.exception.step, "input")
            self.assertIn(words, str(e.exception))

    def test_the_wrapper_that_does_not_type_check(self):
        open(self.lemma, "w").close()
        ran = []

        class Refuses(check.Compilation):
            def run(self, cmd, cwd, log, count=1):
                ran.append(cmd)
                return 1

        with self.assertRaises(check.InstanceError) as e:
            self.audit(statement("toy", self.record()), compilation=Refuses())
        self.assertEqual(e.exception.step, "wrapper")
        self.assertIn("plain_halts_instance is not of this input and this type", str(e.exception))
        self.assertEqual(ran[0][:6], ["rocq", "compile", "-w", "-all", "-Q", "lib"])
        [wrapper] = glob.glob(os.path.join(self.d.name, "instance-*", "wrap", "Wrapper.v"))
        with open(wrapper, encoding="utf-8") as f:
            text = f.read()
        self.assertEqual(text, check.instance_wrapper(statement("toy", self.record()), DATA,
                                                      "Lib.Instances.plain_halts", "OSSVerify.Core"))
        self.assertIn("From OSSVerify.Core Require Import Shapes.\nFrom OSSVerify.Tests.toy.exit0 Require Images.\n"
                      "Import ListNotations.\n", text)
        self.assertIn("Definition oft_input : ProcInput := %s.\n" % shapes.instance_input(DIST, HALTS, DATA), text)
        self.assertIn("Definition oft_instance_type : Prop := %s.\nRequire Lib.Instances.plain_halts.\n"
                      "Definition certified : oft_instance_type := Lib.Instances.plain_halts.plain_halts_instance.\n"
                      % shapes.instance_type(HALTS), text)
        self.assertIn('Redirect "assumptions" Print Assumptions certified.\n', text)

    FORMS = [HALTS, MAY_FAIL, BOUND, DECIDABLE, dict(BOUND, machine="rv64gc"), dict(DECIDABLE, machine="rv64gc")] + [
        agreement(*k) for k in shapes.AGREEMENT]

    def test_the_wrapper_fixes_the_input_and_the_type_before_it_loads_the_library(self):
        """The lemma's library is the pull request's own, and once it is loaded a file of it named like a library of
        the checker (an Images.v) takes a partly qualified name (Images.plain, Budgets.*, Env.*).  So, for every
        instance form, the input and the type are Definitions above the Require of the library, and after the Require
        the wrapper names only its own oft_instance_type and the lemma by its full name.  tests/instances/
        shadowed_images is the control in Rocq."""
        tail = ("Require Lib.Instances.plain_halts.\n"
                "Definition certified : oft_instance_type := Lib.Instances.plain_halts.plain_halts_instance.\n"
                "Set Printing Fully Qualified.\nRedirect \"assumptions\" Print Assumptions certified.\n")
        for data in self.FORMS:
            with self.subTest(st=data):
                text = check.instance_wrapper(statement("toy", data), DATA, "Lib.Instances.plain_halts",
                                              "OSSVerify.Core")
                self.assertTrue(text.endswith("\n" + tail), text)
                head = text[:-len(tail)]
                self.assertEqual(text.count("Require Lib."), 1)
                self.assertTrue(head.endswith("\nImport ListNotations.\nDefinition oft_input : %s := %s.\n"
                                              "Definition oft_instance_type : Prop := %s.\n"
                                              % ("FinProcInput" if shapes.instance_finite(data) else "ProcInput",
                                                 shapes.instance_input(DIST, data, DATA),
                                                 shapes.instance_type(data))), head)
                self.assertTrue(re.search(r"\b(?:Images|Budgets|Env)\.", shapes.instance_type(data)))


def put_proof(t, s):
    """Give statement s of the zlib fixture in the ported tree t a proof: its proof.yaml, of the statement's fingerprint,
    and a Proof.v."""
    st = next(x for x in facts.load(t.root).statements() if x.id == "%s/%s" % (UNIT, s))
    d = layout.proof_dir("zlib", "checksum_fuzzer", s, layout.NEW)
    t.put_yaml(d + "/proof.yaml", {"schema": "oss-fuzz-theorems/proof/1", "proves": st.id,
                                   "fingerprint": st.fingerprint})
    t.write(d + "/Proof.v", "Theorem %s_holds : True. Proof. exact I. Qed.\n" % s)


class InstanceSteps(unittest.TestCase):
    """run: each instance of a statement Statements.v carries is checked once per unit, after the proofs: in the proofs
    part, in the statements part of a unit with no proof, in the plain unit path and in the farm's (--facts-from), and
    across the farm's jobs of one unit split by --statements; a statement's process of proofs_apart
    (--no-instances) leaves them to its parent."""

    def run_check(self, t, **kw):
        seen = []
        with mock.patch.object(check, "prepare_stack"), \
                mock.patch.object(check.fetch, "verify_builds", return_value=([], [])), \
                mock.patch.object(check, "check_statements"), mock.patch.object(check, "check_counterexample"), \
                mock.patch.object(check, "build_proof_dirs"), \
                mock.patch.object(check, "check_proof", side_effect=lambda root, st, *a, **k: seen.append(
                    "proof " + st.name)), \
                mock.patch.object(check, "proofs_apart", side_effect=lambda root, unit, h, apart, *a: (seen.append(
                    "apart " + " ".join(st.name for st in apart)), (len(apart), 0))[1]), \
                mock.patch.object(check, "check_instance", side_effect=lambda root, st, *a, **k: seen.append(st.name)):
            check.run(t.root, [UNIT], out=io.StringIO(), **kw)
        return seen

    def instances(self, t):
        """Instances for plain_halts, asan_agrees and ubsan_halts, and one for plain_halts_may_fail, which
        Statements.v does not carry (withheld)."""
        t.write("toolchain/allowed-axioms.txt", "Ax.ok\n")
        put_instance(t, "plain_halts", b"\0" * 6)
        put_instance(t, "asan_agrees", b"\0" * 6)
        put_instance(t, "ubsan_halts", b"\0" * 6)
        edit(t, ZLIB_HARNESS, lambda y: y["statements"]["plain_halts_may_fail"].update(
            status="withheld", withheld="not-yet-published",
            instance={"file": "input.bin", "sha256": "0" * 64, "bytes": 6, "path": "reaches-harness"}))

    def test_a_unit_with_no_proof_checks_each_instance_once(self):
        with ported_tree() as t:
            self.instances(t)
            every = ["asan_agrees", "plain_halts", "ubsan_halts"]
            self.assertEqual(sorted(self.run_check(t)), every)
            self.assertEqual(sorted(self.run_check(t, parts="statements")), every, "check-units.sh runs it so")
            self.assertEqual(self.run_check(t, parts="counterexamples"), [])
            self.assertEqual(self.run_check(t, checks_instances=False), [])
            self.assertEqual(sorted(self.run_check(t, stack_from_parent=True)), every, "the stack is another flag")
            with tempfile.TemporaryDirectory() as d:
                self.assertEqual(check.run(t.root, [UNIT], facts_to=d, out=io.StringIO()), 0)
                self.assertEqual(sorted(self.run_check(t, facts_from=d)), every)
                self.assertEqual(sorted(self.run_check(t, facts_from=d, parts="statements")), every)

    def test_a_unit_with_proofs_checks_its_instances_in_the_proofs_part_after_them(self):
        with ported_tree() as t:
            self.instances(t)
            put_proof(t, "plain_halts")
            put_proof(t, "asan_agrees")
            self.assertEqual(t.generate(), 0, t.last_output)
            every = ["asan_agrees", "plain_halts", "ubsan_halts"]
            seen = self.run_check(t)
            self.assertEqual(seen[:2], ["proof plain_halts", "proof asan_agrees"])
            self.assertEqual(sorted(seen[2:]), every)
            self.assertEqual(self.run_check(t, parts="statements"), [], "its proofs part checks them")
            self.assertEqual(self.run_check(t, parts="proofs", stack_from_parent=True, proofs_built=True,
                                            checks_instances=False, statements=["plain_halts"]), ["proof plain_halts"])
            # with --proof-jobs, after the statements' processes
            seen = self.run_check(t, parts="proofs", proof_jobs=2)
            self.assertEqual(seen[0], "apart plain_halts asan_agrees")
            self.assertEqual(sorted(seen[1:]), every)

    def test_a_split_unit_checks_each_instance_in_one_job(self):
        """The farm's jobs of one unit, `--parts proofs --statements S`: each checks the instances of S, and the job of
        asan_agrees, the first proved statement by name, those of the statements with no proof too."""
        with ported_tree() as t:
            self.instances(t)
            put_proof(t, "plain_halts")
            put_proof(t, "asan_agrees")
            self.assertEqual(t.generate(), 0, t.last_output)
            with tempfile.TemporaryDirectory() as d:
                self.assertEqual(check.run(t.root, [UNIT], facts_to=d, out=io.StringIO()), 0)
                for kw in ({}, {"facts_from": d}):
                    with self.subTest(kw=kw):
                        jobs = [self.run_check(t, parts="proofs", statements=[s], **kw)
                                for s in ("plain_halts", "asan_agrees")]
                        self.assertEqual(jobs, [["proof plain_halts", "plain_halts"],
                                                ["proof asan_agrees", "ubsan_halts", "asan_agrees"]])
                        both = self.run_check(t, parts="proofs", statements=["plain_halts", "asan_agrees"], **kw)
                        self.assertEqual(sorted(both[2:]), ["asan_agrees", "plain_halts", "ubsan_halts"])


class InstancesToCheck(unittest.TestCase):
    """instances_to_check, the rule alone: the jobs of a split unit, one per proved statement, check each instance
    exactly once."""

    def harness(self, proved):
        """A harness with an instance on statements a to e, proofs of those in `proved`, d withheld (Statements.v does
        not carry it), and f with no instance."""
        h = facts.Harness(facts.Project(facts.Tree("/nonexistent"), "p", {}), "h", {})
        for name in "abcdef":
            data = {"kind": "halts"} if name == "f" else {"kind": "halts", "instance": {"path": "reaches-harness"}}
            if name == "d":
                data["status"] = "withheld"
            h.statements[name] = st = facts.Statement(h, name, data)
            st.proof = object() if name in proved else None
        return h

    def test_the_jobs_of_a_split_unit_check_each_instance_once(self):
        for proved in (("a",), ("b", "e"), ("a", "b", "c", "e"), ("e", "c")):
            with self.subTest(proved=proved):
                h = self.harness(proved)
                checked = [st.name for s in proved for st in check.instances_to_check(h, {"proofs"}, [s], True)]
                self.assertEqual(sorted(checked), ["a", "b", "c", "e"])
                self.assertEqual(sorted(st.name for st in check.instances_to_check(h, {"proofs"}, None, True)),
                                 ["a", "b", "c", "e"], "one job of the whole unit")

    def test_a_statements_process_and_a_statements_run_of_a_proved_unit_check_none(self):
        h = self.harness(("b",))
        self.assertEqual(check.instances_to_check(h, {"proofs"}, ["b"], False), [])
        self.assertEqual(check.instances_to_check(h, {"statements"}, None, True), [], "its proofs part checks them")
        self.assertEqual(check.instances_to_check(h, {"counterexamples"}, None, True), [])
        self.assertEqual(sorted(st.name for st in check.instances_to_check(self.harness(()), {"statements"}, None,
                                                                            True)), ["a", "b", "c", "e"])


if __name__ == "__main__":
    unittest.main()
