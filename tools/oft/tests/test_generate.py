"""oft generate: deterministic, complete, and checked; and the schemas under it."""
import glob
import io
import os
import re
import shutil
import subprocess
import sys
import unittest

from oft import facts, generate, layout, names, paths, port, rocq, schema, shapes, symbols, yamlio
from oft.tests.helpers import NEW_NAMESPACE, rename_namespace, tree
from oft.tests.test_layout import old_layout_tree


class Rendering(unittest.TestCase):
    def test_deterministic(self):
        with tree() as a, tree() as b:
            ra = generate.render_all(facts.load(a.root))
            rb = generate.render_all(facts.load(b.root))
            self.assertEqual(ra, rb)
            self.assertEqual(generate.render_all(facts.load(a.root)), ra)

    def test_check_passes_on_a_rendered_tree(self):
        with tree() as t:
            self.assertEqual(t.generate(check=True), 0, t.last_output)

    def test_a_hand_edit_fails_the_check(self):
        with tree() as t:
            t.write("projects/zlib/checksum_fuzzer/Statements.v", "(* an edit *)\n", "a")
            self.assertEqual(t.generate(check=True), 1)
            self.assertIn("differs from its rendering", t.last_output)

    def test_a_facts_change_without_its_rendering_fails(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["statements"]["asan_agrees"]["budgets"] = "standard"
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertEqual(t.generate(check=True), 1)
            self.assertIn("projects/zlib/checksum_fuzzer/Statements.v: differs", t.last_output)

    def test_a_stale_generated_file_fails(self):
        with tree() as t:
            t.write("projects/json/fuzzer-parse_bjdata/Characterise.v", "(* left over *)\n")
            self.assertEqual(t.generate(check=True), 1)
            self.assertIn("no longer produce", t.last_output)

    def test_a_distribution_header_edit_fails(self):
        with tree() as t:
            p = "projects/zlib/checksum_fuzzer/Distribution.v"
            t.write(p, t.read(p).replace("mean 4,096", "mean 4,097"))
            self.assertEqual(t.generate(check=True), 1)

    def test_bad_facts_render_nothing(self):
        with tree() as t:
            t.write("projects/zlib/project.yaml", "extra: 1\n", "a")
            self.assertEqual(t.generate(), 1)
            self.assertIn("nothing rendered", t.last_output)


class StatementText(unittest.TestCase):
    def test_zlib_checksum_fuzzer(self):
        with tree() as t:
            s = t.read("projects/zlib/checksum_fuzzer/Statements.v")
        self.assertIn("Definition plain_halts : Prop :=\n  halts_within_budget Budgets.Standard.lim_source "
                      "Exits.ok_or_refused Images.plain.", s)
        self.assertIn("Definition plain_halts_may_fail : Prop :=\n  halts_may_fail Exits.any Images.plain.", s)
        self.assertIn("Definition asan_agrees : Prop :=\n  agrees Budgets.Asan.lim_source Budgets.Asan.lim_target "
                      "Images.plain Images.asan.", s)
        self.assertIn("Definition ubsan_agrees : Prop :=\n  agrees Budgets.Standard.lim_source "
                      "Budgets.Standard.lim_target Images.plain Images.ubsan.", s)
        self.assertIn("Definition asan_disagrees_at_most (b : Q) : Prop :=\n  disagrees_at_most Env.may_fail "
                      "Distribution.w Distribution.M Images.plain Images.asan b.", s)
        self.assertIn("From OssFuzzTheorems.zlib.checksum_fuzzer Require Images Distribution.", s)
        self.assertNotIn("Admitted", s)
        self.assertEqual(s.count("(*"), s.count("*)"))

    def test_a_may_fail_halts_statement_is_not_called_stronger_than_the_budget_one(self):
        """halts_may_fail with Exits.any does not imply halts_within_budget with exits 0 and 2: an exit with
        status 77 or 78 satisfies the first and falsifies the second."""
        with tree() as t:
            s = " ".join(t.read("projects/zlib/checksum_fuzzer/Statements.v").split())
        self.assertIn("It covers every input and any refusal, unlike [plain_halts], but allows any exit status.", s)
        self.assertIn("It covers every input and any refusal, unlike [ubsan_halts], but allows any exit status.", s)
        self.assertNotIn("stronger than", s)

    HALTS_BUDGET = ("plain_halts", "ubsan_halts", "asan_halts", "asan_ubsan_halts")

    def rejecting(self, t, exits=(0, 2, 78), rejects=True):
        p = "projects/zlib/checksum_fuzzer/harness.yaml"
        y = t.yaml(p)
        if rejects:
            y["rejects"] = [{"where": "source/checksum_fuzzer.c:10-12", "what": "A short input is returned 1."}]
        for n in self.HALTS_BUDGET:
            y["statements"][n]["exits"] = list(exits)
        t.put_yaml(p, y)

    def test_a_harness_that_rejects_allows_78(self):
        with tree() as t:
            self.rejecting(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            s = t.read("projects/zlib/checksum_fuzzer/Statements.v")
            r = t.read("projects/zlib/checksum_fuzzer/README.md")
        self.assertIn("Definition plain_halts : Prop :=\n  halts_within_budget Budgets.Standard.lim_source "
                      "(cons (stdpp.bitvector.definitions.Z_to_bv _ 78%Z) Exits.ok_or_refused) Images.plain.", s)
        self.assertIn("Status 78 is", s)
        self.assertIn("Definition plain_halts_may_fail : Prop :=\n  halts_may_fail Exits.any Images.plain.", s)
        self.assertIn("returning a value other than 0 or -1", r)
        self.assertIn("([lines 10-12](source/checksum_fuzzer.c#L10-L12))", r)

    def test_78_goes_with_rejects_both_ways(self):
        for exits, rejects in (((0, 2), True), ((0, 2, 78), False)):
            with tree() as t:
                self.rejecting(t, exits, rejects)
                self.assertEqual(t.generate(), 1)
                self.assertIn("exits include 78 exactly when the harness lists rejects", t.last_output)

    def test_a_rejecting_project_page_names_78(self):
        with tree() as t:
            self.rejecting(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertIn("0, 2 or 78", t.read("projects/zlib/README.md"))

    def test_mixed_exit_sets_keep_apart(self):
        """A statement is written "As [first]" only after one with the same exit
        set, and the project page names an exit set other than the commonest."""
        p = "projects/zlib/checksum_fuzzer/harness.yaml"
        with tree() as t:
            self.rejecting(t)
            y = t.yaml(p)
            y["statements"]["asan_halts"]["exits"] = "any"
            t.put_yaml(p, y)
            self.assertEqual(t.generate(), 0, t.last_output)
            s = t.read("projects/zlib/checksum_fuzzer/Statements.v")
            page = t.read("projects/zlib/README.md")
        ubsan = s[s.index("Definition plain_halts :"):s.index("Definition ubsan_halts :")]
        asan = s[s.index("Definition ubsan_halts :"):s.index("Definition asan_halts :")]
        self.assertNotIn("As [plain_halts]", asan)
        self.assertIn("As [plain_halts]", ubsan)
        self.assertIn("any status (status 0, 2 or 78 for checksum_fuzzer)", page)

    def test_a_return_only_check_beside_rejects_is_named(self):
        """78 does not say which line returned, so a check that reports a failure by
        returning is allowed too; the page says so."""
        p = "projects/zlib/checksum_fuzzer/harness.yaml"
        with tree() as t:
            self.rejecting(t)
            y = t.yaml(p)
            y["checks"] = [{"kind": "invariant", "strength": "weak", "stops_with": "return-only", "live": "unknown",
                            "where": "source/checksum_fuzzer.c:10-11", "what": "A failed round trip returns 1."}]
            for s in y["statements"].values():
                if "binds_checks" in s:
                    s["binds_checks"] = False
            t.put_yaml(p, y)
            self.assertEqual(t.generate(), 0, t.last_output)
            r = t.read("projects/zlib/checksum_fuzzer/README.md")
        self.assertIn("a failure of a check above that reports it by returning (checksum_fuzzer.c:10-11) also "
                      "exits with status 78", r)

    def test_a_rejects_entry_must_point_into_the_source(self):
        p = "projects/zlib/checksum_fuzzer/harness.yaml"
        for where, msg in (("source/nope.c:1-2", "rejects[0].where names source/nope.c, which is not a source file"),
                           ("source/checksum_fuzzer.c:9000-9001", "rejects[0].where runs past the end of")):
            with tree() as t:
                self.rejecting(t)
                y = t.yaml(p)
                y["rejects"][0]["where"] = where
                t.put_yaml(p, y)
                self.assertEqual(t.generate(), 1)
                self.assertIn(msg, t.last_output)

    def test_a_pending_source_lists_no_rejects(self):
        p = "projects/zlib/checksum_fuzzer/harness.yaml"
        with tree() as t:
            self.rejecting(t)
            y = t.yaml(p)
            y["source"]["pending"] = True
            y["source"]["files"] = []
            y["checks"] = []
            for s in y["statements"].values():
                s.pop("binds_checks", None)
            t.put_yaml(p, y)
            self.assertEqual(t.generate(), 1)
            self.assertIn("checks and rejects name lines of a source that is not published", t.last_output)

    def test_characterise_and_images(self):
        with tree() as t:
            c = t.read("projects/zlib/checksum_fuzzer/Characterise.v")
            i = t.read("projects/zlib/checksum_fuzzer/Images.v")
            d = t.read("projects/zlib/checksum_fuzzer/images/dune")
        self.assertIn("Definition asan_classifies (C : Image) : Prop :=\n  classifies Env.may_fail Images.plain "
                      "Images.asan C.", c)
        self.assertIn("Lemma asan_ubsan_wf : image_wf asan_ubsan.", i)
        self.assertIn("(targets Plain.v Plain_seg_000.hex Plain_seg_001.hex Plain_seg_002.hex Plain_seg_003.hex)", d)

    def test_chunked_segments(self):
        self.assertEqual(generate.hex_targets("Plain", [1, 2]),
                         ["Plain_seg_000.hex", "Plain_seg_001_chunk_000.hex", "Plain_seg_001_chunk_001.hex"])

    def test_a_harness_name_that_is_not_an_identifier(self):
        with tree() as t:
            s = t.read("projects/json/fuzzer-parse_bjdata/Statements.v")
            dune = t.read("projects/json/fuzzer-parse_bjdata/dune")
        self.assertIn("(name OssFuzzTheorems.json.fuzzer_parse_bjdata)", dune)
        self.assertIn("agrees_in_abort_modelled Env.alloc_forced_only Budgets.Asan.lim_source", s)

    def test_a_withheld_statement_is_listed_not_stated(self):
        with tree() as t:
            s = t.read("projects/zlib/api-driver/Statements.v")
            r = t.read("projects/zlib/api-driver/README.md")
        self.assertIn("(* asan_ubsan_agrees: withheld; see README.md. *)", s)
        self.assertNotIn("Definition asan_ubsan_agrees", s)
        self.assertIn("withheld: not in this release yet", r)
        self.assertNotIn("disclosure", r)

    def test_text_is_safe_inside_a_rocq_comment(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["summary"] = 'Says "hi" (* and *) leaves.'
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertEqual(t.generate(), 0, t.last_output)
            s = t.read("projects/zlib/checksum_fuzzer/Statements.v")
        self.assertNotIn('"hi"', s)
        self.assertIn("( * and * )", s)

    def test_derived_statuses(self):
        with tree() as t:
            st = {s.id: s.status for s in facts.load(t.root).statements()}
            tsv = t.read("index/statements.tsv")
        self.assertEqual(st["json/fuzzer-parse_bjdata/plain_halts"], "counterexample")
        # the same run (the plain build aborts) refutes the agreement statement that names the plain build
        self.assertEqual(st["json/fuzzer-parse_bjdata/asan_agrees"], "counterexample")
        self.assertIn("json/fuzzer-parse_bjdata/plain_halts\thalts\tplain\tbudget\t0,2\tcounterexample\t"
                      "counterexamples/json/fuzzer-parse_bjdata/plain_halts\t1\t", tsv)

    def test_a_counterexample_that_exits_does_not_refute_agreement(self):
        with tree() as t:
            y = t.yaml("counterexamples/json/fuzzer-parse_bjdata/plain_halts/expect.yaml")
            y["observed"] = {"build": "plain", "exit": 77}
            t.put_yaml("counterexamples/json/fuzzer-parse_bjdata/plain_halts/expect.yaml", y)
            st = {s.id: s.status for s in facts.load(t.root).statements()}
        self.assertEqual(st["json/fuzzer-parse_bjdata/plain_halts"], "counterexample")
        self.assertEqual(st["json/fuzzer-parse_bjdata/asan_agrees"], "suspected-false")

    def test_a_witness_is_described_from_its_fields(self):
        with tree() as t:
            r = t.read("projects/zlib/checksum_fuzzer/README.md")
            k = t.read("analyses/known-issues.md")
        want = ("false (witnessed): with the input file `01 00 00 00 00 00 00`, refusing the 3rd memory request "
                "(an mmap of 4,096 bytes) makes the UBSan build end in an abort (SIGABRT) on an uncaught "
                "std::bad_alloc (run under qemu-riscv64 10.0.11)")
        self.assertIn(want, r)
        self.assertIn("zlib/checksum_fuzzer/ubsan_halts_may_fail", k)

    def test_a_statement_level_model_gap(self):
        with tree() as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["statements"]["plain_halts"].update(status="model-gap", gap=["vector-instructions"])
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            r = t.read("projects/zlib/checksum_fuzzer/README.md")
        self.assertIn("blocked by the model: the binary runs RISC-V vector instructions", r)
        self.assertIn("Some statements are blocked by the model", r)

    def test_the_identity_and_descriptor_range_features(self):
        """close_range, getresuid and getresgid, setgroups as root, capget, getppid and getsid each have a feature name
        of their own, narrower than process-control (prctl) and fd-flags (F_GETFD, F_SETFD); each renders its own words."""
        for name, words in (("descriptor-ranges", "closes ranges of descriptors"),
                            ("credentials", "calls getresuid or getresgid, or setgroups as root"),
                            ("capabilities", "calls capget"),
                            ("process-relations", "asks for its parent process or its session")):
            with self.subTest(name=name), tree() as t:
                y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
                y["statements"]["plain_halts"].update(status="model-gap", gap=[name])
                t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
                self.assertEqual(t.generate(), 0, t.last_output)
                self.assertEqual([str(f) for f in t.lint()], [])
                r = t.read("projects/zlib/checksum_fuzzer/README.md")
                self.assertIn("blocked by the model: the binary %s |" % words, r)

    def test_fingerprints_ignore_docstrings_but_not_bytes(self):
        with tree() as t:
            before = {s.id: s.fingerprint for s in facts.load(t.root).statements()}
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["summary"] = "A different summary."
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            self.assertEqual(before, {s.id: s.fingerprint for s in facts.load(t.root).statements()})
            y["builds"]["plain"]["sha256"] = "0" * 63 + "a"
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            after = {s.id: s.fingerprint for s in facts.load(t.root).statements()}
        changed = sorted(k for k in before if before[k] != after[k])
        self.assertIn("zlib/checksum_fuzzer/plain_halts", changed)
        self.assertNotIn("zlib/checksum_fuzzer/ubsan_halts", changed)

    def test_the_project_pages(self):
        with tree() as t:
            z = t.read("projects/zlib/README.md")
            im = t.read("projects/imagemagick/README.md")
            top = t.read("README.md")
            status = t.read("index/STATUS.md")
        self.assertIn("1 of OSS-Fuzz's 2 fuzz targets has statements, plus an API driver", z)
        self.assertIn("**minigzip_fuzzer** (not built yet)", z)
        self.assertIn("Some builds are not in this release yet.", z)
        for word in ("disclosure", "finding", "withheld patch"):
            self.assertNotIn(word, z)
        self.assertIn("**Status: not yet built.** Needs Ghostscript in the build image. [What the statuses mean]", im)
        self.assertIn("[`zlib/checksum_fuzzer/plain_halts`]", top)
        self.assertIn("0 proved", top)
        self.assertIn("| [zlib](../projects/zlib/) | c++ | available | 1 of 2 + API driver | 8 |", status)

    def test_a_rebuild_is_invited_only_beside_a_source_bundle(self):
        """A rebuild needs the build scripts, which come with the source bundle:
        a real builder digest alone must not make the page invite one."""
        digest = "ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:" + "3" * 64
        invite = "A binary whose SHA-256 differs after a rebuild with it is a bug"
        with tree() as t:
            z = t.read("projects/zlib/README.md")       # has a source bundle
            j = t.read("projects/json/README.md")       # has none
            self.assertIn("Builder image: `%s`. %s" % (digest, invite), z)
            self.assertIn("Builder image: `%s`. These binaries cannot yet be rebuilt from this release" % digest, j)
            self.assertNotIn(invite, j)
            zero = digest.split("@")[0] + "@sha256:" + "0" * 64
            r = t.yaml("release.yaml")
            r["images"]["builder"].append(zero)
            t.put_yaml("release.yaml", r)
            y = t.yaml("projects/json/project.yaml")
            y["build"]["builder"] = zero
            t.put_yaml("projects/json/project.yaml", y)
            self.assertEqual(t.generate(), 0, t.last_output)
            j = t.read("projects/json/README.md")
            self.assertIn("Builder image: not published yet", j)
            self.assertNotIn(invite, j)

    def test_counts_agree_everywhere(self):
        """The README's counts, STATUS.md's rows and index/statements.tsv are one set of numbers."""
        with tree() as t:
            tree_ = facts.load(t.root)
            n, by, held = generate.statement_counts(tree_)
            top = t.read("README.md")
            rows = [l.split("\t") for l in t.read("index/statements.tsv").splitlines()[1:]]
            prow = [l.split("\t") for l in t.read("index/projects.tsv").splitlines()[1:]]
        self.assertEqual(len(rows), n)
        for status, k in by.items():
            self.assertEqual(sum(1 for r in rows if r[5] == status), k, status)
        self.assertIn(generate.counts_sentence(tree_), top)
        self.assertEqual(sum(int(r[9]) for r in prow), n)
        self.assertEqual(sum(int(r[15]) for r in prow), by["withheld"])

    def test_project_page_links_resolve(self):
        with tree() as t:
            for rel in ("projects/json/README.md", "projects/json/fuzzer-parse_bjdata/README.md", "README.md",
                        "analyses/known-issues.md", "index/STATUS.md"):
                import re
                base = os.path.dirname(t.path(rel))
                for target in re.findall(r"\]\(([^)#:]+)(?:#[^)]*)?\)", t.read(rel)):
                    if not any(x in target for x in ("counterexamples/", "projects/", "index/", "analyses/")):
                        continue          # docs/ and the hand-written files are not in the fixture
                    self.assertTrue(os.path.exists(os.path.normpath(os.path.join(base, target))),
                                    "%s links to %s" % (rel, target))


class Shapes(unittest.TestCase):
    def st(self, **kw):
        base = {"kind": "agreement", "builds": ["plain", "asan"], "reading": "may-fail", "budgets": "asan"}
        base.update(kw)
        return base

    def test_every_agreement_shape(self):
        want = {("may-fail", "error", "rv64g"): "agrees", ("may-fail", "signal", "rv64g"): "agrees_abort_modelled",
                ("alloc-forced-only", "error", "rv64g"): "agrees_in",
                ("alloc-forced-only", "signal", "rv64g"): "agrees_in_abort_modelled",
                ("may-fail", "error", "rv64gc"): "agrees_rv64gc",
                ("may-fail", "signal", "rv64gc"): "agrees_abort_modelled_rv64gc",
                ("alloc-forced-only", "error", "rv64gc"): "agrees_in_rv64gc"}
        for (reading, abort, machine), name in want.items():
            self.assertEqual(shapes.shape_name(self.st(reading=reading, abort=abort, machine=machine)), name)

    def test_combinations_with_no_shape_are_refused(self):
        for bad in (self.st(reading="alloc-forced-only", abort="signal", machine="rv64gc"),
                    self.st(reading="budget"), self.st(budgets=None),
                    {"kind": "halts", "builds": ["asan"], "reading": "budget", "exits": [0, 1]},
                    {"kind": "halts", "builds": ["asan"], "reading": "alloc-forced-only", "exits": "any"},
                    {"kind": "bound", "builds": ["plain", "asan"], "reading": "may-fail", "abort": "signal"}):
            bad = {k: v for k, v in bad.items() if v is not None}
            with self.assertRaises(shapes.ShapeError):
                shapes.term(bad)

    def test_rv64gc_input_set_shapes(self):
        st = {"kind": "decidability", "builds": ["plain", "asan"], "reading": "may-fail", "machine": "rv64gc"}
        self.assertEqual(shapes.shape_name(st), "agreement_decidable_rv64gc")

    HALTS = {"kind": "halts", "builds": ["plain"], "reading": "budget", "exits": [0, 2]}
    READ = {"failure_handlers": "none"}   # a harness whose linked code was read and installs no failure handler

    def test_binding(self):
        halts = self.HALTS
        check = {"stops_with": "exit", "exit_status": 1, "exit_reaches_guard": True, "live": True}
        self.assertTrue(shapes.binds(check, halts, self.READ))
        # the process ends with 77 whatever argument the source passes, so exit_status does not decide this
        self.assertTrue(shapes.binds(dict(check, exit_status=2), halts, self.READ))
        self.assertTrue(shapes.binds(dict(check, exit_status=-1), halts, self.READ))
        self.assertFalse(shapes.binds(check, dict(halts, exits=[0, 2, 77]), self.READ))
        self.assertFalse(shapes.binds(dict(check, live="unknown"), halts, self.READ))
        self.assertFalse(shapes.binds({"stops_with": "print-only", "live": True}, halts, self.READ))

    def test_an_exit_that_does_not_reach_the_guard_binds_nothing(self):
        """An exit() outside a call of the fuzz target, in LLVMFuzzerInitialize say, is not 77, so the statement
        does not prove the check (docs/running.md, "What status 77 needs")."""
        check = {"stops_with": "exit", "exit_status": 1, "live": True}
        for guard in (False, "unknown"):
            self.assertFalse(shapes.binds(dict(check, exit_reaches_guard=guard), self.HALTS, self.READ), guard)
        self.assertFalse(shapes.binds(check, self.HALTS, self.READ))  # the fact left out binds nothing either

    def test_a_failure_handler_present_or_not_read_binds_nothing(self):
        """A signal handler, a terminate handler, a panic hook or a later exit handler that linked code installs can
        end a failed check with a status the statement allows (docs/facts.md, "Failure handlers"), so every stop
        kind binds only when the harness's failure_handlers is none; absent is unknown."""
        checks = [{"stops_with": s, "live": True} for s in ("abort", "assert", "trap", "throw", "panic", "raise", "fail")]
        checks.append({"stops_with": "exit", "exit_status": 1, "exit_reaches_guard": True, "live": True})
        for check in checks:
            self.assertTrue(shapes.binds(check, self.HALTS, self.READ), check)
            for harness in ({"failure_handlers": "present"}, {"failure_handlers": "unknown"}, {}):
                self.assertFalse(shapes.binds(check, self.HALTS, harness), (check, harness))

    def test_a_rust_panic_is_an_exit_with_status_79(self):
        panic = {"stops_with": "panic", "live": True}
        halts = self.HALTS
        self.assertTrue(shapes.binds(panic, halts, self.READ))
        self.assertFalse(shapes.binds(panic, dict(halts, reading="may-fail", exits="any"), self.READ))
        self.assertFalse(shapes.binds(panic, dict(halts, exits=[0, 2, 79]), self.READ))

    def test_an_uncaught_python_exception_is_an_exit_with_status_79(self):
        raised = {"stops_with": "raise", "live": True}
        halts = self.HALTS
        self.assertTrue(shapes.binds(raised, halts, self.READ))
        self.assertFalse(shapes.binds(raised, dict(halts, reading="may-fail", exits="any"), self.READ))
        self.assertFalse(shapes.binds(raised, dict(halts, exits=[0, 2, 79]), self.READ))
        self.assertFalse(shapes.binds(dict(raised, live="unknown"), halts, self.READ))

    def test_a_failing_go_fuzz_test_is_an_exit_with_status_79(self):
        failed = {"stops_with": "fail", "live": True}
        halts = self.HALTS
        self.assertTrue(shapes.binds(failed, halts, self.READ))
        self.assertFalse(shapes.binds(failed, dict(halts, reading="may-fail", exits="any"), self.READ))
        self.assertFalse(shapes.binds(failed, dict(halts, exits=[0, 2, 79]), self.READ))
        self.assertFalse(shapes.binds(dict(failed, live="unknown"), halts, self.READ))


class Code(unittest.TestCase):
    """rocq.code: what a fingerprint hashes of theories/Shapes.v and theories/Images.v."""

    def test_comments_and_blanks(self):
        self.assertEqual(rocq.code("(** doc (* nested *) *)\nDefinition  a :=\n\t0. (* end *)\n"), "Definition a := 0.")
        self.assertEqual(rocq.code("a (*c*) b\r\n(*d*)(*e*)c"), "a b c")
        self.assertNotEqual(rocq.code("a (*c*) b"), rocq.code("ab"))

    def test_a_comment_bracket_inside_a_token_is_code(self):
        """Rocq takes a declared token such as `tok(*` whole, so `tok(* 0 *)` and `tok(* 1 *)` are different code."""
        self.assertNotEqual(rocq.code("Definition t := tok(* 0 *)."), rocq.code("Definition t := tok(* 1 *)."))
        self.assertEqual(rocq.code('x."(*" "y"(* z *)'), 'x."(*" "y"(* z *)')
        self.assertEqual(rocq.code("x (* 0 *)."), rocq.code("x (* 1 *)."))

    def test_only_rocqs_blanks_are_layout(self):
        self.assertNotEqual(rocq.code("a\fb"), rocq.code("a b"))
        self.assertEqual(rocq.code("a \t\r\n b"), "a b")

    def test_a_carriage_return_in_a_string_is_code(self):
        def code(t, rel):
            return facts.code_sha256(t.path(rel), names.NAMESPACE_DEFAULT)

        with tree(render=False) as t:
            t.write("lf.v", 'Definition s := "a\nb".\n')
            t.write("crlf.v", 'Definition s := "a\r\nb".\r\n')
            self.assertNotEqual(code(t, "lf.v"), code(t, "crlf.v"))
            t.write("crlf.v", 'Definition s := "a\nb".\r\n')
            self.assertEqual(code(t, "lf.v"), code(t, "crlf.v"))

    def test_strings_are_code(self):
        self.assertEqual(rocq.code('Definition s := "(*  ""x""  *)".'), 'Definition s := "(*  ""x""  *)".')
        self.assertEqual(rocq.code('(* "*)" *) a'), "a")
        self.assertNotEqual(rocq.code('Definition s := "a  b".'), rocq.code('Definition s := "a b".'))

    def test_edges(self):
        """`(*)` opens a comment, a stray `*)` is code, an unterminated comment runs to the end (Rocq rejects the
        file), and an unterminated string stays as it is."""
        self.assertEqual(rocq.code("a (*) b *) c"), "a c")
        self.assertEqual(rocq.code("a *) b"), "a *) b")
        self.assertEqual(rocq.code("a (* b"), "a")
        self.assertEqual(rocq.code('a "b c'), 'a "b c')

    def test_a_crlf_distribution_header_splits_like_an_lf_one(self):
        self.assertEqual(facts.split_distribution("(** h *)\r\nDefinition a := 0.\r\n")[1], "Definition a := 0.\r\n")
        self.assertEqual(facts.split_distribution("(** h *)\nDefinition a := 0.\n")[1], "Definition a := 0.\n")


class Fingerprints(unittest.TestCase):
    """A statement's fingerprint hashes the code of theories/Shapes.v and theories/Images.v, not their bytes."""
    SHAPES = ('(** * The shapes\n\n    Prose (* nested *) about them. *)\nDefinition tag : string := "(* not a comment".\n'
              "Definition halts (x : nat) : Prop :=\n  x = 0.\n")

    def edited(self, rel, edit):
        """Every statement's fingerprint, before and after rel goes from SHAPES to edit(SHAPES)."""
        with tree() as t:
            t.write(rel, self.SHAPES)
            before = {s.id: s.fingerprint for s in facts.load(t.root).statements() if s.fingerprint}
            t.write(rel, edit(self.SHAPES))
            after = {s.id: s.fingerprint for s in facts.load(t.root).statements() if s.fingerprint}
        self.assertTrue(before)
        self.assertEqual(sorted(before), sorted(after))
        return before, after

    def test_a_comment_edit_changes_none(self):
        for rel in ("theories/Shapes.v", "theories/Images.v"):
            before, after = self.edited(rel, lambda s: s.replace("about them", "about (* the *) shapes") + "(* end *)\n")
            self.assertEqual(before, after, rel)

    def test_a_layout_edit_changes_none(self):
        before, after = self.edited("theories/Shapes.v", lambda s: s.replace(":=\n  x = 0.", ":=   x\t= 0.\n\n"))
        self.assertEqual(before, after)

    def test_a_comment_bracket_in_a_string_opens_no_comment(self):
        before, after = self.edited("theories/Shapes.v", lambda s: s.replace("x = 0", "x = 1"))
        self.assertTrue(all(before[k] != after[k] for k in before))

    def test_a_string_literal_is_code(self):
        before, after = self.edited("theories/Shapes.v", lambda s: s.replace("not a comment", "not  a comment"))
        self.assertTrue(all(before[k] != after[k] for k in before))

    def test_a_carriage_return_in_a_distribution_string_is_hashed(self):
        bound, dist = "zlib/checksum_fuzzer/asan_disagrees_at_most", "projects/zlib/checksum_fuzzer/Distribution.v"
        with tree() as t:
            text = t.read(dist)
            seen = set()
            for literal in ('"a\nb"', '"a\r\nb"'):
                t.write(dist, text + "Definition s := %s.\n" % literal)
                seen.add(next(s.fingerprint for s in facts.load(t.root).statements() if s.id == bound))
        self.assertEqual(len(seen), 2)

    def test_a_carriage_return_in_a_distribution_string_survives_generate_then_check(self):
        dist = "projects/zlib/checksum_fuzzer/Distribution.v"
        with tree() as t:
            t.write(dist, t.read(dist) + 'Definition s := "a\rb".\n')
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(t.generate(check=True), 0, t.last_output)


class Namespace(unittest.TestCase):
    """release.yaml's `namespace` and `opam_stem` name the theories and the opam packages (OSSV-162).  A fingerprint
    reads the namespace as facts.FINGERPRINT_NAMESPACE, so a release that renames it states the same statements."""

    # a theory that names the namespace, as theories/Shapes.v does (`From <namespace>.Core Require Import Images.`)
    THEORY = "(** * The core *)\nFrom %s.Core Require Import Images.\nDefinition halts (x : nat) : Prop := x = 0.\n"
    # what a generated file holds when it names the old namespace or an old package
    OLD = ("OssFuzzTheorems", "rocq-oss-fuzz-theorems")

    def test_a_release_naming_a_namespace_renders_it_everywhere(self):
        with tree(render=False) as t:
            rename_namespace(t)
            out = generate.render_all(facts.load(t.root))
            gen = {p: text for p, text in out.items()
                   if p == "dune-project" or p.endswith(("Statements.v", "Images.v", "Characterise.v", "/dune", ".opam"))}
            self.assertTrue(gen)
            self.assertEqual([p for p, text in gen.items() if any(o in text for o in self.OLD)], [])
            self.assertIn("From OSSVerify.Core Require Import Shapes.", out["projects/zlib/checksum_fuzzer/Statements.v"])
            self.assertIn("(see Vocabulary in OSSVerify.Core.Shapes)",
                          " ".join(out["projects/zlib/checksum_fuzzer/Statements.v"].split()))
            self.assertIn("From OSSVerify.Core Require Import Images.", out["projects/zlib/checksum_fuzzer/Images.v"])
            self.assertIn("(theories Stdlib stdpp ReadFile Flocq LinuxProcessSemantics OSSVerify.Core)",
                          out["projects/zlib/checksum_fuzzer/dune"])
            self.assertIn("projects/zlib/rocq-oss-verify-zlib.opam", out)
            self.assertNotIn("projects/zlib/rocq-oss-fuzz-theorems-zlib.opam", out)
            for line in ("(name oss-verify)", "(name rocq-oss-verify-core)", "(name rocq-oss-verify)",
                         "(depends rocq-oss-verify-core)", "(name rocq-oss-verify-zlib-proofs)"):
                self.assertIn(line, out["dune-project"])
            # the tree renders, checks against its rendering and lints clean under its new names
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(t.generate(check=True), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            # a proof and a proof library: their dune files name the theories and the package in the new names
            st = next(s for s in facts.load(t.root).statements() if s.id == "zlib/checksum_fuzzer/plain_halts")
            t.write("proofs/zlib/checksum_fuzzer/lib/Base.v", "Definition one := 1.\n")
            t.put_yaml("proofs/zlib/checksum_fuzzer/plain_halts/proof.yaml", {
                "schema": "oss-fuzz-theorems/proof/1", "proves": st.id, "fingerprint": st.fingerprint})
            t.write("proofs/zlib/checksum_fuzzer/plain_halts/Proof.v", "Theorem plain_halts_holds : True. Proof. exact I. Qed.\n")
            out = generate.render_all(facts.load(t.root))
            proof, lib = (out["proofs/zlib/checksum_fuzzer/%s/dune" % d] for d in ("plain_halts", "lib"))
            for line in ("(name OSSVerify.Proofs.zlib.checksum_fuzzer.plain_halts)", "(package rocq-oss-verify-zlib-proofs)",
                         "OSSVerify.Core", " OSSVerify.zlib.checksum_fuzzer ", "OSSVerify.Proofs.zlib.checksum_fuzzer.lib"):
                self.assertIn(line, proof + " ")
            for line in ("(name OSSVerify.Proofs.zlib.checksum_fuzzer.lib)", "(package rocq-oss-verify-zlib-proofs)",
                         "OSSVerify.Core"):
                self.assertIn(line, lib)
            self.assertEqual([p for p, text in out.items() if p.endswith("/dune") and any(o in text for o in self.OLD)],
                             [])

    def test_no_namespace_renders_as_before(self):
        """A release.yaml that names neither (every tree up to v2026.10.2) renders today's names, and one that names
        the defaults renders every file byte for byte as one that names none."""
        with tree() as t:
            self.assertEqual(t.generate(check=True), 0, t.last_output)
            before = generate.render_all(facts.load(t.root))
            self.assertIn("From OssFuzzTheorems.Core Require Import Shapes.",
                          before["projects/zlib/checksum_fuzzer/Statements.v"])
            self.assertIn("projects/zlib/rocq-oss-fuzz-theorems-zlib.opam", before)
            for line in ("(name oss-fuzz-theorems)", "(name rocq-oss-fuzz-theorems-core)",
                         "(depends rocq-oss-fuzz-theorems-core)"):
                self.assertIn(line, before["dune-project"])
            rename_namespace(t, names.NAMESPACE_DEFAULT, names.OPAM_STEM_DEFAULT)
            self.assertEqual(generate.render_all(facts.load(t.root)), before)
            self.assertEqual(t.generate(check=True), 0, t.last_output)

    def fingerprints(self, t):
        """The fingerprint of every statement that has one (a withheld statement has none)."""
        return {s.id: s.fingerprint for s in facts.load(t.root).statements() if s.fingerprint}

    def theories(self, t, namespace):
        for rel in facts.THEORIES:
            t.write(rel, self.THEORY % namespace)

    def test_a_renamed_release_keeps_every_fingerprint(self):
        with tree(render=False) as a, tree(render=False) as b:
            self.theories(a, names.NAMESPACE_DEFAULT)
            self.theories(b, NEW_NAMESPACE)
            rename_namespace(b)
            self.assertNotEqual(a.read("theories/Shapes.v"), b.read("theories/Shapes.v"))
            want = self.fingerprints(a)
            self.assertTrue(want)
            self.assertEqual(self.fingerprints(b), want)
            # a theory edit that is not the namespace still moves every one
            b.write("theories/Shapes.v", b.read("theories/Shapes.v").replace("x = 0", "x = 1"))
            got = self.fingerprints(b)
            self.assertEqual(sorted(got), sorted(want))
            self.assertTrue(all(got[k] != want[k] for k in want))

    def test_only_a_dotted_prefix_is_read_as_the_fingerprint_namespace(self):
        f = facts.in_fingerprint_namespace
        self.assertEqual(f("From OSSVerify.Core Require Images.", NEW_NAMESPACE),
                         "From OssFuzzTheorems.Core Require Images.")
        for text in ("OSSVerify", "x.OSSVerify.y", "NotOSSVerify.Core", "OSSVerify_core.x", "OSSVerify'.x"):
            self.assertEqual(f(text, NEW_NAMESPACE), text)
        self.assertEqual(f("OssFuzzTheorems.Core", names.NAMESPACE_DEFAULT), "OssFuzzTheorems.Core")


class Schemas(unittest.TestCase):
    def test_the_fixture_validates(self):
        with tree(render=False) as t:
            for rel, kind in (("release.yaml", "release"), ("projects/zlib/project.yaml", "project"),
                              ("projects/zlib/checksum_fuzzer/harness.yaml", "harness")):
                self.assertEqual(schema.validate(kind, t.yaml(rel)), [], rel)

    def test_closed(self):
        with tree(render=False) as t:
            y = t.yaml("projects/zlib/project.yaml")
            y["colour"] = {"shade": "blue"}
            self.assertTrue(any("unknown key" in e for e in schema.validate("project", y)))

    def test_yaml_is_strict(self):
        self.assertEqual(yamlio.load("d: 2026-11-02\nb: yes\n"), {"d": "2026-11-02", "b": "yes"})
        with self.assertRaises(yamlio.YamlError):
            yamlio.load("a: 1\na: 2\n")

    def test_every_template_placeholder_has_a_value(self):
        """A missing value raises; rendering the fixture exercises every block used."""
        with tree() as t:
            self.assertTrue(os.path.isfile(t.path("projects/zlib/checksum_fuzzer/Characterise.v")))



class UninstrumentedWords(unittest.TestCase):
    def test_the_readme_names_what_each_build_links_uninstrumented(self):
        with tree() as t:
            h = "projects/zlib/checksum_fuzzer/harness.yaml"
            y = t.yaml(h)
            y["builds"]["asan"]["uninstrumented"] = [
                {"name": "libclang_rt.asan.a", "kind": "sanitizer-runtime"},
                {"name": "crc32_x86.S.o", "kind": "assembly", "source": "contrib/crc32_x86.S"}]
            t.put_yaml(h, y)
            self.assertEqual(t.generate(), 0)
            readme = t.read("projects/zlib/checksum_fuzzer/README.md")
            self.assertIn("- asan: `libclang_rt.asan.a` (the sanitizer runtime), `crc32_x86.S.o` from "
                          "`contrib/crc32_x86.S` (assembly)", readme)
            self.assertNotIn("is not recorded in this release", readme)

    def test_with_no_list_the_readme_says_it_is_not_recorded(self):
        with tree() as t:
            readme = t.read("projects/zlib/checksum_fuzzer/README.md")
            self.assertIn("Which other code each build links uninstrumented is not recorded in this release.", readme)
            st = t.read("projects/zlib/checksum_fuzzer/Statements.v")
            self.assertIn("in the code it instruments", st)


class PublishedModel(unittest.TestCase):
    def test_publishing_the_model_changes_the_readme_and_no_fingerprint(self):
        """semantics.published: the model is public at its commit while its version is still unreleased."""
        with tree() as t:
            r = t.yaml("release.yaml")
            r["semantics"]["version"] = "unreleased"
            t.put_yaml("release.yaml", r)
            for p in ("proofs", "counterexamples"):         # fingerprints move with the version: no evidence here
                shutil.rmtree(t.path(p), ignore_errors=True)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertIn("Nothing here can be checked from outside yet", t.read("README.md"))
            before = t.read("index/statements.tsv")
            r["semantics"]["published"] = True
            t.put_yaml("release.yaml", r)
            self.assertEqual(t.generate(), 0, t.last_output)
            readme = t.read("README.md")
            self.assertNotIn("Nothing here can be checked from outside yet", readme)
            c = r["semantics"]["commit"]
            self.assertIn("commit [`%s`](%s/commit/%s)" % (c[:12], r["semantics"]["repository"], c), readme)
            self.assertEqual(t.read("index/statements.tsv"), before)


ZLIB_UBSAN_AGREES = ("projects/zlib/checksum_fuzzer/harness.yaml", "projects/zlib/api-driver/harness.yaml")


def set_project_budgets(t, budgets, drop=("ubsan_agrees",)):
    """Give zlib project.yaml `budgets` and drop the harness.yaml `budgets` field of the statements in `drop`."""
    y = t.yaml("projects/zlib/project.yaml")
    y["budgets"] = budgets
    t.put_yaml("projects/zlib/project.yaml", y)
    for rel in ZLIB_UBSAN_AGREES:
        h = t.yaml(rel)
        for name in drop:
            h["statements"][name].pop("budgets", None)
        t.put_yaml(rel, h)


def fingerprints(t):
    return {s.id: s.fingerprint for s in facts.load(t.root).statements()}


class ProjectBudgets(unittest.TestCase):
    """project.yaml `budgets.agrees`: a project's own budget pair for the agreement statements of one sanitizer."""

    PAIR = {"agrees": {"undefined": ["2GiB", "5TiB"]}}

    def test_a_pair_changes_the_ubsan_agrees_fingerprints_and_no_other(self):
        with tree() as t:
            before = fingerprints(t)
            set_project_budgets(t, self.PAIR)
            after = fingerprints(t)
            self.assertEqual(sorted(k for k in before if before[k] != after[k]),
                             ["zlib/api-driver/ubsan_agrees", "zlib/checksum_fuzzer/ubsan_agrees"])
            self.assertTrue(after["zlib/checksum_fuzzer/ubsan_agrees"] and after["zlib/api-driver/ubsan_agrees"])
            y = t.yaml("projects/zlib/project.yaml")
            y["budgets"]["agrees"]["undefined"] = ["2GiB", "3TiB"]
            t.put_yaml("projects/zlib/project.yaml", y)
            again = fingerprints(t)
            self.assertEqual(sorted(k for k in after if after[k] != again[k]),
                             ["zlib/api-driver/ubsan_agrees", "zlib/checksum_fuzzer/ubsan_agrees"])

    def test_a_pair_renders_literals_and_names_both_budgets(self):
        with tree() as t:
            set_project_budgets(t, self.PAIR)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            s = t.read("projects/zlib/checksum_fuzzer/Statements.v")
            r = t.read("projects/zlib/checksum_fuzzer/README.md")
            facts_tree = facts.load(t.root)
        self.assertIn("Definition ubsan_agrees : Prop :=\n  agrees 0x80000000%Z 0x50000000000%Z Images.plain "
                      "Images.ubsan.", s)
        doc = s[:s.index("Definition ubsan_agrees")]
        flat = " ".join(doc[doc.rindex("(**"):].split())
        # stated in full, never "As [asan_agrees]": the own pair puts it in a family of its own
        self.assertTrue(flat.startswith("(** On every input on which the plain build is never refused memory for "
                                        "exceeding 2 GiB,"), flat)
        self.assertIn("This statement has this project's own budgets: 2 GiB for the plain build (default 16 GiB) and "
                      "5 TiB for the UBSan build (default 512 GiB). The project's notes say why.", flat)
        self.assertIn("Not claimed: anything about inputs on which the plain build needs more than 2 GiB.", flat)
        self.assertIn("(this project's own budgets: 2 GiB / 5 TiB)", r)
        # the ASan statements keep their enum
        self.assertIn("agrees Budgets.Asan.lim_source Budgets.Asan.lim_target Images.plain Images.asan.", s)
        self.assertNotIn("for the UBSan build, with 2 GiB for the plain build", s)
        st = next(x for x in facts_tree.statements() if x.id == "zlib/checksum_fuzzer/ubsan_agrees")
        self.assertEqual(shapes.shape_name(st.data), "agrees")

    def test_the_as_path_carries_the_own_budgets_sentence(self):
        with tree() as t:
            set_project_budgets(t, {"agrees": {"address": ["1GiB", "1TiB"]}},
                                drop=("asan_agrees", "asan_ubsan_agrees"))
            self.assertEqual(t.generate(), 0, t.last_output)
            s = " ".join(t.read("projects/zlib/checksum_fuzzer/Statements.v").split())
        self.assertIn("As [asan_agrees], for the ASan+UBSan build, with 1 GiB for the plain build.", s)
        self.assertEqual(s.count("This statement has this project's own budgets: 1 GiB for the plain build "
                                 "(default 2 GiB) and 1 TiB for the"), 2)
        self.assertIn("1 TiB for the ASan+UBSan build (default 512 GiB)", s)
        # an address pair says nothing of UBSan's budgets, and the UBSan statement, on the enum, is not stated
        # "As" one with the pair
        self.assertNotIn("default 16 GiB", s)
        self.assertNotIn("As [asan_agrees], for the UBSan build", s)
        # the UBSan statement keeps the enum
        self.assertIn("agrees Budgets.Standard.lim_source Budgets.Standard.lim_target Images.plain Images.ubsan.", s)

    def test_a_pair_beside_a_harness_enum_is_refused(self):
        with tree() as t:
            set_project_budgets(t, self.PAIR, drop=())
            self.assertEqual(t.generate(), 1)
            self.assertIn("project.yaml budgets.agrees.undefined sets this statement's budgets, so it names none",
                          t.last_output)

    def test_bad_pairs_are_refused(self):
        st = {"kind": "agreement", "builds": ["plain", "ubsan"], "reading": "may-fail"}
        for pair, words in ((["2GiB"], "is [plain, sanitizer]"), (["2GiB", "5TiB", "6TiB"], "is [plain, sanitizer]"),
                            (["4095", "5TiB"], "at least 4096 bytes"), (["5TiB", "2GiB"], "at least the plain one"),
                            (["2 GiB", "5TiB"], "not a size"), ([2, "5TiB"], "not a size")):
            with self.assertRaises(shapes.ShapeError) as e:
                shapes.term(st, {"budgets": {"agrees": {"undefined": pair}}})
            self.assertIn(words, str(e.exception))
        with self.assertRaises(shapes.ShapeError) as e:
            shapes.term(st, {"budgets": {"agrees": {"address": ["1GiB", "1TiB"]}}})     # no pair for ubsan and no enum
        self.assertIn("an agreement statement names its budgets", str(e.exception))
        with self.assertRaises(shapes.ShapeError) as e:
            shapes.term(dict(st, budgets="standard"), {"budgets": {"agrees": {"undefined": ["2GiB", "5TiB"]}}})
        self.assertIn("sets this statement's budgets, so it names none", str(e.exception))

    def test_a_pair_equal_to_the_default_is_the_enum(self):
        st = {"kind": "agreement", "builds": ["plain", "ubsan"], "reading": "alloc-forced-only"}
        enum = shapes.term(dict(st, budgets="standard"))
        for pb in ({"budgets": {"agrees": {"undefined": ["16GiB", "512GiB"]}}},
                   {"budgets": {"agrees": {"undefined": ["16384MiB", "512GiB"]}}}):
            self.assertEqual(shapes.term(st, pb), enum)
            self.assertIsNone(shapes.own_budgets(st, pb))
        with tree() as t:
            before = fingerprints(t)
            set_project_budgets(t, {"agrees": {"undefined": ["16GiB", "512GiB"]}})
            self.assertEqual(fingerprints(t), before)
            s = t.read("projects/zlib/checksum_fuzzer/Statements.v")
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(t.read("projects/zlib/checksum_fuzzer/Statements.v"), s)

    def test_literals_and_words_come_from_bytes(self):
        st = {"kind": "agreement", "builds": ["plain", "ubsan"], "reading": "alloc-forced-only"}
        pb = {"budgets": {"agrees": {"undefined": ["1024MiB", "4352GiB"]}}}
        self.assertEqual(shapes.term(st, pb)[1],
                         "agrees_in Env.alloc_forced_only 0x40000000%Z 0x44000000000%Z Images.plain Images.ubsan")
        self.assertEqual(shapes.budget_words(st, pb), ("1 GiB", "4352 GiB", True))
        self.assertEqual(shapes.size_bytes("4096"), 4096)

    def test_the_units_are_the_schemas(self):
        """shapes.UNITS turns the units of schemas/project.yaml's size pattern into bytes: the two name the same."""
        import re
        pattern = schema.load_schema("project")["defs"]["size"]["pattern"]
        self.assertEqual(set(re.search(r"\(([^)]*)\)\?\$$", pattern).group(1).split("|")), set(shapes.UNITS) - {""})

    def test_empty_blocks_mean_no_pair(self):
        with tree() as t:
            before = fingerprints(t)
            for pb in ({}, {"agrees": {}}):
                y = t.yaml("projects/zlib/project.yaml")
                y["budgets"] = pb
                t.put_yaml("projects/zlib/project.yaml", y)
                self.assertEqual(fingerprints(t), before)
                self.assertEqual(t.generate(check=True), 0, t.last_output)

    def test_a_pair_needs_the_projects_notes(self):
        """The text says the project's notes give the reason, so a project with its own pair has notes."""
        for notes in (None, "  \n"):
            with tree() as t:
                if notes is None:
                    os.remove(t.path("notes/zlib.md"))
                else:
                    t.write("notes/zlib.md", notes)
                set_project_budgets(t, self.PAIR)
                self.assertEqual(t.generate(), 1)
                self.assertIn("projects/zlib/project.yaml: budgets.agrees.undefined is this project's own pair, so "
                              "notes/zlib.md says why", t.last_output)
                found = [str(f) for f in t.lint()]
            self.assertTrue(any("so notes/zlib.md says why" in f for f in found), found)

    def test_a_pair_no_statement_uses_is_still_checked(self):
        """json has no UBSan agreement statement; its bad undefined pair is refused at project.yaml all the same."""
        with tree() as t:
            y = t.yaml("projects/json/project.yaml")
            y["budgets"] = {"agrees": {"undefined": ["5TiB", "2GiB"]}}
            t.put_yaml("projects/json/project.yaml", y)
            self.assertEqual(t.generate(), 1)
            self.assertIn("projects/json/project.yaml: budgets.agrees.undefined: the sanitizer budget is at least the "
                          "plain one", t.last_output)

    def test_a_bad_pair_is_reported_once(self):
        with tree() as t:
            set_project_budgets(t, {"agrees": {"undefined": ["4095", "5TiB"]}})
            self.assertEqual(facts.load(t.root).errors,
                             ["projects/zlib/project.yaml: budgets.agrees.undefined: the plain budget is at least "
                              "4096 bytes"])
            self.assertEqual(t.generate(), 1)
            self.assertEqual(t.last_output.count("budgets.agrees.undefined: the plain budget is at least 4096 bytes"),
                             1, t.last_output)

    def test_a_bad_pair_hides_no_other_shape_error(self):
        with tree() as t:
            set_project_budgets(t, {"agrees": {"address": ["1GiB", "2GiB", "3GiB"]}},
                                drop=("asan_agrees", "asan_ubsan_agrees"))
            h = t.yaml(ZLIB_UBSAN_AGREES[0])
            h["statements"]["asan_agrees"]["exits"] = "any"
            h["statements"]["asan_ubsan_agrees"]["shape"] = "agrees_in"
            t.put_yaml(ZLIB_UBSAN_AGREES[0], h)
            self.assertEqual(t.generate(), 1)
        self.assertIn("projects/zlib/project.yaml: budgets.agrees.address is [plain, sanitizer]", t.last_output)
        self.assertIn("statements.asan_agrees: only halts statements have exits", t.last_output)
        self.assertIn("statements.asan_ubsan_agrees: shape is agrees_in, but its fields give agrees", t.last_output)

    def test_revisions_refuses_a_tree_with_a_bad_pair(self):
        from oft import revisions
        for bad in ("previous", "current"):
            with tree() as prev, tree() as cur:
                set_project_budgets(prev if bad == "previous" else cur, {"agrees": {"undefined": ["5TiB", "2GiB"]}})
                buf = io.StringIO()
                self.assertEqual(revisions.run(cur.root, prev.root, out=buf), 1, bad)
                self.assertIn("budgets.agrees.undefined: the sanitizer budget is at least the plain one", buf.getvalue())

    def test_the_internal_schema_is_a_strict_subset_of_the_public_shape(self):
        """String sizes with an optional unit, per sanitizer; public validate.py also takes a bare integer."""
        ok = {"agrees": {"undefined": ["2GiB", "5TiB"], "address": ["512MiB", "1TiB"]}}
        base = {"schema": "oss-fuzz-theorems/project/1", "project": "x", "language": "c", "status": "available"}
        self.assertEqual(schema.validate("project", dict(base, budgets=ok)), [])
        for bad in ({"agrees": {"undefined": ["2 GiB", "5TiB"]}}, {"agrees": {"thread": ["2GiB", "5TiB"]}},
                    {"halts": "16GiB"}, {"agrees": {"undefined": [2147483648, "5TiB"]}}):
            self.assertNotEqual(schema.validate("project", dict(base, budgets=bad)), [], bad)


if __name__ == "__main__":
    unittest.main()


class HeldAndExitWitness(unittest.TestCase):
    """A project or a fuzz target held from the release says only that, with no reason; a witness may end in an
    exit with a status the halts statement does not allow."""

    def test_a_held_project_page_says_only_that_it_is_held(self):
        with tree() as t:
            y = t.yaml("projects/imagemagick/project.yaml")
            y.update(status="held", reason="held")
            y.pop("reason_args")
            t.put_yaml("projects/imagemagick/project.yaml", y)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            page = t.read("projects/imagemagick/README.md")
            status = t.read("index/STATUS.md")
        self.assertIn("**Status: held.** Held from this release. [What the statuses mean]", page)
        self.assertNotIn("Ghostscript", page)
        self.assertIn("| [imagemagick](../projects/imagemagick/) | c++ | held |", status)

    def test_a_held_project_takes_no_reason_text(self):
        with tree() as t:
            y = t.yaml("projects/imagemagick/project.yaml")
            y.update(status="held", reason="dependency")
            t.put_yaml("projects/imagemagick/project.yaml", y)
            t.generate()
            self.assertTrue(any("is not a held reason" in f.msg for f in t.lint()))

    def test_a_held_fuzz_target_is_listed_as_held(self):
        with tree() as t:
            y = t.yaml("projects/zlib/project.yaml")
            for e in y["harnesses"]:
                if e["name"] == "minigzip_fuzzer":
                    e["reason"] = "held"
            t.put_yaml("projects/zlib/project.yaml", y)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            page = t.read("projects/zlib/README.md")
        self.assertIn("**minigzip_fuzzer** (held from this release)", page)

    def hold_zlib_api_driver(self, t, origin=True):
        """zlib's API driver held: listed as not included with reason held, its directory moved out of the tree (not
        deleted), and release.yaml's counts without its harness and builds."""
        y = t.yaml("projects/zlib/project.yaml")
        for e in y["harnesses"]:
            if e["name"] == "api-driver":
                e.update(status="not-included", reason="held")
                if not origin:
                    e.pop("origin")
        y.pop("withheld")           # the fixture's only withheld statement is the API driver's
        t.put_yaml("projects/zlib/project.yaml", y)
        n_builds = len(t.yaml("projects/zlib/api-driver/harness.yaml")["builds"])
        os.rename(t.path("projects/zlib/api-driver"), t.path("..", "api-driver-aside"))
        r = t.yaml("release.yaml")
        r["counts"]["harnesses"] -= 1
        r["counts"]["binaries"] -= n_builds
        t.put_yaml("release.yaml", r)

    def test_a_held_api_driver_is_listed_as_held_and_counted_nowhere(self):
        with tree() as t:
            self.hold_zlib_api_driver(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            page = t.read("projects/zlib/README.md")
            status = t.read("index/STATUS.md")
            row = [r for r in t.read("index/projects.tsv").splitlines() if r.startswith("zlib\t")]
        self.assertIn("**api-driver** (held from this release)", page)
        self.assertNotIn("plus an API driver", page)
        self.assertIn("| [zlib](../projects/zlib/) | c++ | available | 1 of 2 |", status)
        self.assertEqual(row[0].split("\t")[6], "no")
        # control: the included API driver is counted in both
        with tree() as t:
            self.assertIn("| [zlib](../projects/zlib/) | c++ | available | 1 of 2 + API driver |",
                          t.read("index/STATUS.md"))
            row = [r for r in t.read("index/projects.tsv").splitlines() if r.startswith("zlib\t")]
            self.assertEqual(row[0].split("\t")[6], "yes")

    def test_a_held_api_driver_still_has_origin_this_repository(self):
        with tree() as t:
            self.hold_zlib_api_driver(t, origin=False)
            t.generate()
            self.assertTrue(any("api-driver, and only api-driver, has origin this-repository" in f.msg
                                for f in t.lint()))

    def exit_witness(self, t, **w):
        y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
        wit = {"build": "plain", "input_hex": "01000000000000", "outcome": "exit", "exit": 78,
               "runner": "qemu-riscv64 10.0.11"}
        wit.update(w)
        y["statements"]["plain_halts"].update(status="witnessed-false", witness={k: v for k, v in wit.items()
                                                                                if v is not None})
        y["statements"]["plain_halts"].pop("binds_checks", None)
        t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)

    def test_a_witness_that_ends_in_an_exit(self):
        with tree() as t:
            self.exit_witness(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual([str(f) for f in t.lint()], [])
            r = t.read("projects/zlib/checksum_fuzzer/README.md")
        self.assertIn("false (witnessed): with the input file `01 00 00 00 00 00 00` and nothing refused, the plain "
                      "build ends in exit status 78 (run under qemu-riscv64 10.0.11)", r)

    def test_an_exit_witness_must_be_one_the_statement_forbids(self):
        for w, msg in (({"exit": 2}, "which the statement allows"),
                       ({"exit": None}, "exactly when it ends in an exit"),
                       ({"after": "failed-assertion"}, "`after` is for a witness that ends in a signal")):
            with tree() as t:
                self.exit_witness(t, **w)
                t.generate()
                self.assertTrue(any(msg in f.msg for f in t.lint()), (w, [str(f) for f in t.lint()]))
        with tree() as t:
            # an abort with an exit status is refused too: the status is the exit's
            self.exit_witness(t, outcome="abort")
            t.generate()
            self.assertTrue(any("exactly when it ends in an exit" in f.msg for f in t.lint()))


class ProofLibrary(unittest.TestCase):
    def test_a_harness_library_gets_a_dune_and_its_proofs_depend_on_it(self):
        with tree() as t:
            st = next(s for s in facts.load(t.root).statements() if s.id == "zlib/checksum_fuzzer/plain_halts")
            t.put_yaml("proofs/zlib/checksum_fuzzer/plain_halts/proof.yaml", {
                "schema": "oss-fuzz-theorems/proof/1", "proves": st.id, "fingerprint": st.fingerprint})
            t.write("proofs/zlib/checksum_fuzzer/plain_halts/Proof.v", "Theorem plain_halts_holds : True. Proof. exact I. Qed.\n")
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertNotIn("OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib",
                             t.read("proofs/zlib/checksum_fuzzer/plain_halts/dune"))
            t.write("proofs/zlib/checksum_fuzzer/lib/Sub/Deep.v", "Definition two := 2.\n")
            self.assertEqual(t.generate(), 0, t.last_output)
            lib = t.read("proofs/zlib/checksum_fuzzer/lib/dune")
            self.assertIn("(include_subdirs qualified)", lib)
            self.assertIn("(name OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib)", lib)
            self.assertIn("(package rocq-oss-fuzz-theorems-zlib-proofs)", lib)
            self.assertIn(" OssFuzzTheorems.zlib.checksum_fuzzer OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib)",
                          t.read("proofs/zlib/checksum_fuzzer/plain_halts/dune"))
            self.assertEqual(t.generate(check=True), 0, t.last_output)


SYMBOL_FACT = "projects/zlib/checksum_fuzzer/symbols/plain.tsv"
SYMBOLS_V = "projects/zlib/checksum_fuzzer/Symbols.v"
# Symbols.v of the fixture's stand-in symbol fact: zlib/checksum_fuzzer's plain build, three functions (_start of size
# 0), a data object and two sections
FIXTURE_SYMBOLS_V = (
    "(** * zlib / checksum_fuzzer: the functions, data objects and sections of one build\n"
    "\n"
    "    Each module below names the functions and data objects of one build of this\n"
    "    fuzz target, as the build's symbol fact [symbols/<build>.tsv] lists them:\n"
    "    [s_<name>] is the address of the function or object <name> and\n"
    "    [Size.s_<name>] its size in bytes, with each character of <name> other than\n"
    "    a letter, a digit or [_] written [_].  Its module [Sec] names each allocated\n"
    "    section of the build in the same way, less the leading [.] of the section's\n"
    "    name: [Sec.s_got] is the address of .got and [Sec.Size.s_got] its size, so\n"
    "    that data no symbol names, such as a GOT slot, is a section's address and an\n"
    "    offset.  [oft symbols] reads the fact from the build's unstripped twin and\n"
    "    from the binary that harness.yaml pins by SHA-256, and refuses any other\n"
    "    binary.  A contract names a function, an object or a section as\n"
    "    [Symbols.<Build>.s_<name>] or [Symbols.<Build>.Sec.s_<name>], never by its\n"
    "    address, so that a rebuild that moves it changes this file and not the\n"
    "    contract.  A name that two or more functions or objects, or two or more\n"
    "    sections, of a build share has no identifier in that build's module. *)\n"
    "From Stdlib Require Import ZArith.\n"
    "\n"
    "Module Plain.\n"
    "Definition s__start : Z := 0x11260.\n"
    "Definition s_LLVMFuzzerTestOneInput : Z := 0x11270.\n"
    "Definition s_crc32_z_llvm_42 : Z := 0x112dc.\n"
    "Definition s_crc_table : Z := 0x13000.\n"
    "\n"
    "Module Size.\n"
    "Definition s__start : Z := 0.\n"
    "Definition s_LLVMFuzzerTestOneInput : Z := 108.\n"
    "Definition s_crc32_z_llvm_42 : Z := 40.\n"
    "Definition s_crc_table : Z := 1024.\n"
    "End Size.\n"
    "\n"
    "Module Sec.\n"
    "Definition s_got : Z := 0x14000.\n"
    "Definition s_bss : Z := 0x15000.\n"
    "\n"
    "Module Size.\n"
    "Definition s_got : Z := 16.\n"
    "Definition s_bss : Z := 64.\n"
    "End Size.\n"
    "End Sec.\n"
    "End Plain.\n")


def put_symbol_fact(t, build, rows):
    """Write zlib/checksum_fuzzer's symbol fact of build, of the binary harness.yaml pins, with rows (name, kind,
    address, size), stand-in hashes (masked bytes - but for a function) and no source lines."""
    pin = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")["builds"][build]["sha256"]
    symbols.write(t.path(layout.symbol_fact("zlib", "checksum_fuzzer", build)),
                  [symbols.Sym(n, k, a, s, "1f" * 32, "2e" * 32 if k == "func" else "-", "-") for n, k, a, s in rows],
                  pin)


class SymbolsModule(unittest.TestCase):
    """Symbols.v: the functions and data objects of a fuzz target by name, a module for each build with a symbol fact,
    so that a contract names them and not their addresses."""

    def test_a_harness_with_a_symbol_fact_gets_symbols_v(self):
        with tree() as t:
            self.assertEqual(t.read(SYMBOLS_V), FIXTURE_SYMBOLS_V)
            h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
            self.assertEqual(generate.symbols_v(h), FIXTURE_SYMBOLS_V)
            self.assertTrue(paths.is_gen(SYMBOLS_V))
            # and no placeholder takes it as a harness's name
            self.assertEqual(paths.classify("projects/zlib/Symbols.v/README.md"), [])

    def test_a_harness_without_one_gets_none(self):
        with tree() as t:
            h = facts.load(t.root).projects["json"].harnesses["fuzzer-parse_bjdata"]
            self.assertTrue(h.builds())
            self.assertIsNone(generate.symbols_v(h))
            self.assertFalse(os.path.exists(t.path(h.dir, "Symbols.v")))

    def test_a_name_two_functions_or_objects_share_is_left_out(self):
        """One identifier cannot name two functions or objects (musl's static dummy, which several of its files
        define; a static function and a static object of two files): such a name gets none in that build's module,
        which says so; a build where one function alone has it keeps it."""
        with tree() as t:
            put_symbol_fact(t, "plain", [("LLVMFuzzerTestOneInput", "func", 0x11270, 108),
                                         ("dummy", "func", 0x112dc, 4), ("dummy", "object", 0x13000, 4)])
            put_symbol_fact(t, "asan", [("dummy", "func", 0x20000, 4), ("x.y", "func", 0x20004, 8),
                                        ("z", "func", 0x2000c, 8), ("x.y", "func", 0x20014, 8),
                                        ("z", "func", 0x2001c, 8)])
            self.assertEqual(t.generate(), 0, t.last_output)
            text = t.read(SYMBOLS_V)
            self.assertTrue(text.startswith(
                "(** * zlib / checksum_fuzzer: the functions, data objects and sections of two builds\n"), text)
            self.assertEqual(text[text.index("Module Plain."):text.index("End Plain.")], (
                "Module Plain.\n"
                "(** Two or more functions or objects of this build are named [dummy], so this\n"
                "    module defines no identifier for it. *)\n"
                "Definition s_LLVMFuzzerTestOneInput : Z := 0x11270.\n"
                "\n"
                "Module Size.\n"
                "Definition s_LLVMFuzzerTestOneInput : Z := 108.\n"
                "End Size.\n"))
            self.assertEqual(text[text.index("Module Asan."):], (
                "Module Asan.\n"
                "(** Two or more functions or objects of this build have each of the names [x.y]\n"
                "    and [z], so this module defines no identifier for them. *)\n"
                "Definition s_dummy : Z := 0x20000.\n"
                "\n"
                "Module Size.\n"
                "Definition s_dummy : Z := 4.\n"
                "End Size.\n"
                "End Asan.\n"))
        self.assertEqual(names.rocq_idents(["a", "dummy", "b.c", "dummy"]), {"a": "s_a", "b.c": "s_b_c"})

    def test_a_size_never_clashes_with_an_address(self):
        """musl's static old_tz and old_tz_size (__tz.c), in every ASan build of libreac: the size of old_tz and the
        address of old_tz_size are both s_old_tz_size, the one in Size and the other not, so both names are kept."""
        with tree() as t:
            put_symbol_fact(t, "plain", [("old_tz", "object", 0x13000, 8), ("old_tz_size", "object", 0x13008, 8)])
            self.assertEqual(t.generate(), 0, t.last_output)
            text = t.read(SYMBOLS_V)
            self.assertEqual(text[text.index("Module Plain."):], (
                "Module Plain.\n"
                "Definition s_old_tz : Z := 0x13000.\n"
                "Definition s_old_tz_size : Z := 0x13008.\n"
                "\n"
                "Module Size.\n"
                "Definition s_old_tz : Z := 8.\n"
                "Definition s_old_tz_size : Z := 8.\n"
                "End Size.\n"
                "End Plain.\n"))

    def test_sections_have_a_namespace_of_their_own(self):
        """A section is named in the build's module Sec, less the leading . of its name: the section .got and a
        function got are both s_got, in two modules; a name two sections share is left out of Sec, which says so."""
        with tree() as t:
            put_symbol_fact(t, "plain", [("got", "func", 0x11270, 8), (".got", "section", 0x14000, 16),
                                         (".data", "section", 0x15000, 8), (".data", "section", 0x16000, 8)])
            self.assertEqual(t.generate(), 0, t.last_output)
            text = t.read(SYMBOLS_V)
            self.assertEqual(text[text.index("Module Plain."):], (
                "Module Plain.\n"
                "Definition s_got : Z := 0x11270.\n"
                "\n"
                "Module Size.\n"
                "Definition s_got : Z := 8.\n"
                "End Size.\n"
                "\n"
                "Module Sec.\n"
                "(** Two or more sections of this build are named [.data], so this module defines\n"
                "    no identifier for it. *)\n"
                "Definition s_got : Z := 0x14000.\n"
                "\n"
                "Module Size.\n"
                "Definition s_got : Z := 16.\n"
                "End Size.\n"
                "End Sec.\n"
                "End Plain.\n"))

    def test_two_names_one_identifier_is_refused(self):
        """Two names that give one identifier of Symbols.v are an error of the facts, which names both, whether they
        are functions or objects, or two sections: no rendering could define the identifier twice."""
        for rows, clash in (([("crc32.z", "func", 0x11270, 8), ("crc32_z", "func", 0x11278, 8)],
                             "'crc32.z' and 'crc32_z' both give s_crc32_z"),
                            ([("crc32.z", "func", 0x11270, 8), ("crc32_z", "object", 0x13000, 8)],
                             "'crc32.z' and 'crc32_z' both give s_crc32_z"),
                            ([(".got", "section", 0x14000, 8), ("got", "section", 0x14008, 8)],
                             "'.got' and 'got' both give s_got")):
            with self.subTest(rows=rows), tree() as t:
                put_symbol_fact(t, "plain", rows)
                self.assertEqual(t.generate(), 1, t.last_output)
                errors = [line for line in t.last_output.splitlines() if line.startswith("error: ")]
                self.assertEqual(len(errors), 1, t.last_output)
                self.assertTrue(errors[0].startswith("error: %s: " % SYMBOL_FACT), errors)
                self.assertIn(clash, errors[0])
                self.assertIn("nothing rendered", t.last_output)
                self.assertRaisesRegex(ValueError, re.escape(clash), names.symbol_idents,
                                       [symbols.Sym(n, k, a, s, "-", "-", "-") for n, k, a, s in rows])

    def test_oft_checks_rules_leave_the_symbol_facts_alone(self):
        """The rule is not in rules.check, which `oft check` runs: symbols.py is not the checker
        (keys.NOT_THE_CHECKER), so a check opens it for no fuzz target, not even one whose symbol fact has a clash."""
        with tree() as t:
            put_symbol_fact(t, "plain", [("crc32.z", "func", 0x11270, 8), ("crc32_z", "func", 0x11278, 8)])
            tools = os.path.dirname(os.path.dirname(os.path.abspath(generate.__file__)))
            done = subprocess.run([sys.executable, "-c", "import sys; from oft import facts, rules; "
                                   "e = rules.check(facts.load(sys.argv[1])); "
                                   "print([x for x in e if 'symbols' in x], 'oft.symbols' in sys.modules)", t.root],
                                  capture_output=True, text=True, env=dict(os.environ, PYTHONPATH=tools))
            self.assertEqual((done.returncode, done.stdout, done.stderr), (0, "[] False\n", ""))

    def test_generate_check_reports_a_stale_symbols_v(self):
        with tree() as t:
            t.write(SYMBOL_FACT, t.read(SYMBOL_FACT).replace("0x11270", "0x11274"))
            self.assertEqual(t.generate(check=True), 1)
            self.assertIn("%s: differs from its rendering" % SYMBOLS_V, t.last_output)
            os.remove(t.path(SYMBOL_FACT))
            self.assertEqual(t.generate(check=True), 1)
            self.assertIn("%s: generated file that the facts no longer produce; remove it" % SYMBOLS_V, t.last_output)


class SharedFiles(unittest.TestCase):
    """The shared generated files (paths.SHARED): the ones `oft generate` renders from the whole tree, which the
    line's render writes after each merge instead of a pull request."""

    def run_generate(self, root, **kw):
        buf = io.StringIO()
        rc = generate.run(root, out=buf, **kw)
        return rc, buf.getvalue()

    def test_every_shared_pattern_is_a_gen_row(self):
        for p in paths.SHARED:
            self.assertIn(("gen", p), paths.TABLE)

    def test_is_shared(self):
        for rel in ("README.md", "index/STATUS.md", "index/PROOFS.md", "index/statements.tsv", "index/binaries.tsv",
                    "analyses/known-issues.md", "analyses/harness-checks/checks.tsv", "projects/zlib/README.md"):
            self.assertTrue(paths.is_shared(rel), rel)
        for rel in ("dune-project", "projects/zlib/checksum_fuzzer/README.md",
                    "projects/zlib/rocq-oss-fuzz-theorems-zlib.opam",
                    "proofs/zlib/checksum_fuzzer/plain_halts/dune", "proofs/zlib/checksum_fuzzer/lib/dune",
                    "index/x/statements.tsv", "docs/statements.md"):
            self.assertFalse(paths.is_shared(rel), rel)

    def test_skip_shared_ignores_a_stale_shared_file(self):
        with tree() as t:
            t.write("index/statements.tsv", "stale\n")
            rc, out = self.run_generate(t.root, check=True, shared=False)
            self.assertEqual(rc, 0, out)
            rc, out = self.run_generate(t.root, check=True)
            self.assertEqual(rc, 1, out)
            self.assertIn("index/statements.tsv", out)

    def test_skip_shared_still_checks_a_target_file(self):
        with tree() as t:
            t.write("projects/zlib/checksum_fuzzer/README.md", "stale\n")
            rc, out = self.run_generate(t.root, check=True, shared=False)
            self.assertEqual(rc, 1, out)
            self.assertIn("projects/zlib/checksum_fuzzer/README.md", out)

    def test_shared_only_writes_only_shared_files(self):
        with tree() as t:
            good = t.read("index/statements.tsv")
            t.write("index/statements.tsv", "stale\n")
            t.write("projects/zlib/checksum_fuzzer/README.md", "stale\n")
            rc, out = self.run_generate(t.root, shared=True)
            self.assertEqual(rc, 0, out)
            self.assertEqual(t.read("index/statements.tsv"), good)
            self.assertEqual(t.read("projects/zlib/checksum_fuzzer/README.md"), "stale\n")

    def test_skip_shared_writes_no_shared_file(self):
        with tree() as t:
            t.write("index/statements.tsv", "stale\n")
            rc, out = self.run_generate(t.root, shared=False)
            self.assertEqual(rc, 0, out)
            self.assertEqual(t.read("index/statements.tsv"), "stale\n")
            self.assertIn("are left to the line's render", out)

    def test_shared_only_deletes_a_shared_file_the_facts_no_longer_produce(self):
        with tree() as t:
            t.write("index/gone.tsv", "x\n")
            rc, out = self.run_generate(t.root, check=True, shared=True)
            self.assertEqual(rc, 1, out)
            self.assertIn("index/gone.tsv", out)
            rc, out = self.run_generate(t.root, shared=True)
            self.assertEqual(rc, 0, out)
            self.assertFalse(os.path.lexists(t.path("index/gone.tsv")), out)
            self.assertIn("removed index/gone.tsv", out)

    def test_the_summary_line_keeps_its_form(self):
        with tree() as t:
            for scope in (False, True):
                rc, out = self.run_generate(t.root, check=True, shared=scope)
                self.assertEqual(rc, 0, out)
                last = out.rstrip("\n").rsplit("\n", 1)[-1]
                self.assertRegex(last, r"\Aoft generate --check: \d+ files, 0 problem\(s\)\Z")

    def test_the_shared_files_do_not_read_proof_libraries(self):
        with tree() as t:
            t.write("proofs/zlib/checksum_fuzzer/lib/Helper.v", "Definition one := 1.\n")
            self.assertEqual(t.generate(), 0, t.last_output)
            shared = [rel for rel in generate.existing_generated(t.root) if paths.is_shared(rel)]
            self.assertTrue(shared)
            want = {rel: t.read(rel) for rel in shared}
            copy = t.path("..", "sparse")
            shutil.copytree(t.root, copy)
            for p in glob.glob(os.path.join(copy, "proofs", "*", "*", "lib")):
                shutil.rmtree(p)
            for rel in shared:
                with open(os.path.join(copy, rel), "w") as f:
                    f.write("stale\n")
            rc, out = self.run_generate(copy, shared=True)
            self.assertEqual(rc, 0, out)
            for rel in shared:
                with open(os.path.join(copy, rel), encoding="utf-8") as f:
                    self.assertEqual(f.read(), want[rel], rel)


class DuneProject(unittest.TestCase):
    """dune-project depends on the facts alone: a project's first proof no longer adds its proofs package, so two
    programs' first proof pull requests do not conflict in it."""

    def packages(self, text):
        return re.findall(r"\(name (rocq-oss-fuzz-theorems[\w-]*)\)", text)

    def test_every_statements_package_has_a_proofs_package(self):
        with tree() as t:
            text = t.read("dune-project")
            names_ = [n for n in self.packages(text)
                      if n not in ("rocq-oss-fuzz-theorems", "rocq-oss-fuzz-theorems-core")
                      and not n.endswith("-proofs")]
            self.assertTrue(names_)
            stanzas = {}
            for block in text.split("\n\n"):
                m = re.search(r"\(name (rocq-oss-fuzz-theorems[\w-]*)\)", block)
                if m:
                    stanzas[m.group(1)] = block
            for n in names_:
                self.assertIn(n + "-proofs", stanzas, n)
                self.assertIn("(allow_empty)", stanzas[n + "-proofs"], n)

    def test_a_first_proof_changes_no_byte_of_dune_project(self):
        with tree() as t:
            before = t.read("dune-project")
            st = next(s for s in facts.load(t.root).statements() if s.id == "zlib/checksum_fuzzer/plain_halts")
            t.put_yaml("proofs/zlib/checksum_fuzzer/plain_halts/proof.yaml", {
                "schema": "oss-fuzz-theorems/proof/1", "proves": st.id, "fingerprint": st.fingerprint})
            t.write("proofs/zlib/checksum_fuzzer/plain_halts/Proof.v",
                    "Theorem plain_halts_holds : True. Proof. exact I. Qed.\n")
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(t.read("dune-project"), before)
# The barrier: generated in each per-project proofs and counterexamples folder, byte for byte the text
# measured in the checker image (dune 3.23, Rocq 9.2) on the ported ossv/recipes tree.
BARRIER = ("; generated by oft generate; do not edit.\n"
           "; The statement theory of the folder above takes every subfolder (include_subdirs qualified).  What this "
           "folder\n; holds is not part of it: each proof and the proof library have their own dune file, and dune "
           "3.23 fails on a\n; theory nested in another's subfolders.\n(include_subdirs no)\n")


def ported_pair(a, b):
    """a and b the same old-layout tree, rendered; b then ported to the per-project layout and rendered again."""
    for t in (a, b):
        old_layout_tree(t)
        assert t.generate() == 0, t.last_output
    assert port.port_worktree(b.root, out=io.StringIO()) == 0
    assert b.generate() == 0, b.last_output


class Layout(unittest.TestCase):
    def test_a_ported_tree_renders_every_file_of_a_statement_folder_as_before(self):
        """D4: Statements.v, Images.v, Characterise.v, Distribution.v, dune and images/dune of every harness are
        byte-equal before and after the move; only README.md and files outside projects/<p>/<h>/ may differ."""
        with tree() as a, tree() as b:
            ported_pair(a, b)
            for h in facts.load(a.root).harnesses():
                for f in ("Statements.v", "Images.v", "Characterise.v", "Distribution.v", "dune", "images/dune"):
                    rel = os.path.join(h.dir, f)
                    self.assertEqual(os.path.isfile(a.path(rel)), os.path.isfile(b.path(rel)), rel)
                    if os.path.isfile(a.path(rel)):
                        self.assertEqual(a.read(rel), b.read(rel), rel)

    def test_a_ported_tree_renders_a_barrier_in_each_proofs_and_counterexamples_folder(self):
        self.assertEqual(generate.barrier_dune(), BARRIER)
        with tree() as a, tree() as b:
            ported_pair(a, b)
            for d in ("projects/zlib/checksum_fuzzer/proofs", "projects/zlib/api-driver/proofs",
                      "projects/json/fuzzer-parse_bjdata/counterexamples"):
                self.assertEqual(b.read(d + "/dune"), BARRIER, d)
            self.assertFalse(os.path.exists(b.path("projects/zlib/checksum_fuzzer/findings/dune")))
            self.assertEqual(b.read("projects/zlib/checksum_fuzzer/proofs/lib/dune"),
                             a.read("proofs/zlib/checksum_fuzzer/lib/dune"))
            self.assertEqual(b.read("projects/zlib/checksum_fuzzer/proofs/plain_halts/dune"),
                             a.read("proofs/zlib/checksum_fuzzer/plain_halts/dune"))
            self.assertFalse([f for f in b.files() if f.split("/")[0] in layout.OLD_TOPS])
            self.assertEqual(b.generate(check=True), 0, b.last_output)
            self.assertFalse([f for f in a.files() if f.endswith("/dune") and f.startswith("projects/")
                              and f.split("/")[3:4] in (["proofs"], ["counterexamples"])])

    def test_the_old_layout_renders_its_own_folders(self):
        with tree() as t:
            old_layout_tree(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            readme = t.read("README.md")
            self.assertIn("Each proof has a build record in `proofs/<project>/<harness>/provenance/`.", readme)
            self.assertIn("| `proofs/<project>/<harness>/<statement>/` | the proof of one statement", readme)
            self.assertIn("| `counterexamples/` | inputs that make a binary break a statement", readme)
            self.assertIn("generated by oft generate from project.yaml, */harness.yaml, proofs/, counterexamples/ and "
                          "notes/zlib.md;",
                          t.read("projects/zlib/README.md"))

    def test_the_new_layout_renders_its_own_folders(self):
        with tree() as a, tree() as b:
            ported_pair(a, b)
            readme = b.read("README.md")
            self.assertIn("Each proof has a build record in `projects/<project>/<harness>/proofs/provenance/`.", readme)
            self.assertIn("| `projects/<project>/<harness>/proofs/<statement>/` | the proof of one statement", readme)
            self.assertIn("| `projects/<project>/<harness>/counterexamples/` | inputs that make a binary break a "
                          "statement", readme)
            self.assertNotIn("`proofs/<project>", readme)
            self.assertIn("generated by oft generate from project.yaml, */harness.yaml, */proofs/, */counterexamples/ "
                          "and notes/zlib.md;",
                          b.read("projects/zlib/README.md"))

    def test_the_proving_paragraph_names_no_folder(self):
        with tree() as t:
            text = t.read("projects/zlib/checksum_fuzzer/Statements.v")
            self.assertIn("A proof is a directory named after the statement, in this fuzz target's\n    proofs folder "
                          "(docs/proving.md says where it is), whose Proof.v ends, for\n    example, in\n", text)
            self.assertNotIn("proofs/zlib", text)

    def test_harness_page_links_its_proofs_relatively(self):
        with tree() as a, tree() as b:
            ported_pair(a, b)
            self.assertIn("[proved](../../../proofs/zlib/checksum_fuzzer/plain_halts/)",
                          a.read("projects/zlib/checksum_fuzzer/README.md"))
            self.assertIn("[proved](proofs/plain_halts/)", b.read("projects/zlib/checksum_fuzzer/README.md"))
            self.assertIn("(../../proofs/zlib/checksum_fuzzer/plain_halts)", a.read("projects/zlib/README.md"))
            self.assertIn("(checksum_fuzzer/proofs/plain_halts)", b.read("projects/zlib/README.md"))

    def test_index_rows_name_the_proofs_folder_of_each_layout(self):
        with tree() as a, tree() as b:
            ported_pair(a, b)
            self.assertIn("[build record](../proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.md) | "
                          "[proofs/zlib/checksum_fuzzer/](../proofs/zlib/checksum_fuzzer/)", a.read("index/PROOFS.md"))
            self.assertIn("[build record](../projects/zlib/checksum_fuzzer/proofs/provenance/PROVENANCE.md) | "
                          "[projects/zlib/checksum_fuzzer/proofs/](../projects/zlib/checksum_fuzzer/proofs/)",
                          b.read("index/PROOFS.md"))
            self.assertIn("\tprojects/zlib/checksum_fuzzer/proofs/plain_halts\t"
                          "projects/zlib/checksum_fuzzer/proofs/provenance/PROVENANCE.md", b.read("index/proofs.tsv"))
