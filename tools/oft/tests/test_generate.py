"""oft generate: deterministic, complete, and checked; and the schemas under it."""
import ast
import glob
import io
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest

from oft import claims, facts, generate, layout, names, paths, port, rocq, rules, schema, shapes, symbols, yamlio
from oft.tests import test_classifier_images as ci
from oft.tests.helpers import NEW_NAMESPACE, REPO, git, git_repo, rename_namespace, tree
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


class DistributionBody(unittest.TestCase):
    """generate fails a Distribution.v whose body does not define the weights its harness.yaml gives, each above 0.
    Each changed definition here follows a comment holding harness.yaml's, the one rules._distribution reads."""
    DIST = "projects/zlib/checksum_fuzzer/Distribution.v"
    HARNESS = "projects/zlib/checksum_fuzzer/harness.yaml"

    def defining(self, t, **weights):
        text = t.read(self.DIST)
        for name, value in weights.items():
            old = re.search(r"Definition %s : Q := \(\d+ # \d+\)%%Q\." % name, text).group(0)
            text = text.replace(old, "(* %s *)\nDefinition %s : Q := (%s)%%Q." % (old, name, value))
        t.write(self.DIST, text)

    def test_harness_yaml_s_weights_pass(self):
        with tree() as t:
            body = facts.split_distribution(t.read(self.DIST))[1]
            self.assertIsNone(claims.distribution_body_error(body, t.yaml(self.HARNESS)))
            self.assertEqual(t.generate(check=True), 0, t.last_output)
            # a comment in the body changes a bound's fingerprint, which index/statements.tsv lists
            self.defining(t, m_payload="90 # 100")
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(t.generate(check=True), 0, t.last_output)

    def test_a_zero_weight_fails(self):
        with tree() as t:
            self.defining(t, m_payload="0 # 100")
            self.assertEqual(t.generate(check=True), 1)
            self.assertIn(self.DIST + ": its component weights 0, 1/50, 1/50, None, 3/50 are not harness.yaml's "
                          "components, each above 0", t.last_output)
        with tree() as t:
            t.write(self.DIST, t.read(self.DIST).replace("cd_lift cd.", "fun _ => 0%Q."))
            self.assertEqual(t.generate(check=True), 1)
            self.assertIn(self.DIST + ": it is not the form tools/oft/claims.py reads", t.last_output)

    def test_a_zero_weight_harness_yaml_gives_too_fails(self):
        with tree() as t:
            self.defining(t, m_payload="0 # 100")
            data = t.yaml(self.HARNESS)
            data["distribution"]["components"]["payload"] = "0"
            self.assertIn("each above 0", claims.distribution_body_error(
                facts.split_distribution(t.read(self.DIST))[1], data))

    def test_a_changed_weight_fails(self):
        with tree() as t:
            self.defining(t, m_payload="89 # 100", m_base="7 # 100")
            self.assertEqual(t.generate(check=True), 1)
            self.assertIn(self.DIST + ": its component weights 89/100, 1/50, 1/50, None, 7/100 are not harness.yaml's "
                          "components, each above 0", t.last_output)


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
        set, and the project page names an exit set other than the commonest, with
        the builds it holds for when the harness's statements differ."""
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
        self.assertIn("any status (status 0, 2 or 78 for checksum_fuzzer's plain, UBSan and ASan+UBSan builds)", page)

    def test_a_finite_may_fail_statement_does_not_say_any_status(self):
        """A may-fail statement with a finite exit set allows no more statuses than
        its budget twin, so its text names its set and does not say it allows any."""
        p = "projects/zlib/checksum_fuzzer/harness.yaml"
        with tree() as t:
            y = t.yaml(p)
            y["statements"]["plain_halts_may_fail"]["exits"] = [0, 2]
            t.put_yaml(p, y)
            self.assertEqual(t.generate(), 0, t.last_output)
            s = t.read("projects/zlib/checksum_fuzzer/Statements.v")
        doc = " ".join(s[s.index("Definition plain_halts :"):s.index("Definition plain_halts_may_fail :")].split())
        self.assertIn("Every execution of the plain build exits, with status 0 or 2, on every input", doc)
        self.assertIn("unlike [plain_halts].", doc)
        self.assertNotIn("allows any exit status", doc)
        self.assertIn("halts_may_fail Exits.ok_or_refused Images.plain.", s)

    def test_the_may_fail_family_names_each_exit_set_with_its_statements(self):
        """Where a project's may-fail statements differ in exit set, the project page gives each set with the
        statements it holds for, not "any status or status 0 or 2" for the whole family."""
        p = "projects/zlib/checksum_fuzzer/harness.yaml"
        with tree() as t:
            y = t.yaml(p)
            y["statements"]["plain_halts_may_fail"]["exits"] = [0, 2]
            t.put_yaml(p, y)
            self.assertEqual(t.generate(), 0, t.last_output)
            page = t.read("projects/zlib/README.md")
        line = next(x for x in page.splitlines() if x.startswith("- **`<build>_halts_may_fail`**"))
        self.assertIn("every execution exits, with any status (status 0 or 2 for checksum_fuzzer's plain build).",
                      line)
        self.assertNotIn("any status or status 0 or 2", page)

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
        self.assertEqual(claims.hex_targets("Plain", [1, 2]),
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
        """The page says which requests the position counts, so a reader who counts system calls is not misled."""
        with tree() as t:
            r = t.read("projects/zlib/checksum_fuzzer/README.md")
            k = t.read("analyses/known-issues.md")
        want = ("false (witnessed): with the input file `01 00 00 00 00 00 00`, refusing the 3rd memory request that "
                "backs an allocation (an mmap of 4,096 bytes; counted are each brk that asks for new pages, each "
                "anonymous mmap without MAP_FIXED and each mremap) makes the UBSan build end in an abort (SIGABRT) on "
                "an uncaught std::bad_alloc (run under qemu-riscv64 10.0.11)")
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

    def test_the_size_grammar_is_the_project_schema_s(self):
        self.assertEqual(shapes.SIZE.pattern, schema.load_schema("project")["defs"]["size"]["pattern"])

    def test_every_agreement_shape(self):
        want = {("may-fail", "error", "rv64g"): "agrees", ("may-fail", "signal", "rv64g"): "agrees_abort_modelled",
                ("alloc-forced-only", "error", "rv64g"): "agrees_in",
                ("alloc-forced-only", "signal", "rv64g"): "agrees_in_abort_modelled",
                ("may-fail", "error", "rv64gc"): "agrees_rv64gc",
                ("may-fail", "signal", "rv64gc"): "agrees_abort_modelled_rv64gc",
                ("alloc-forced-only", "error", "rv64gc"): "agrees_in_rv64gc"}
        for (reading, abort, machine), name in want.items():
            self.assertEqual(shapes.shape_name(self.st(reading=reading, abort=abort, machine=machine),
                                               distribution=False), name)

    def test_combinations_with_no_shape_are_refused(self):
        for bad in (self.st(reading="alloc-forced-only", abort="signal", machine="rv64gc"),
                    self.st(reading="budget"), self.st(budgets=None),
                    {"kind": "halts", "builds": ["asan"], "reading": "budget", "exits": [0, 1]},
                    {"kind": "halts", "builds": ["asan"], "reading": "alloc-forced-only", "exits": "any"},
                    {"kind": "bound", "builds": ["plain", "asan"], "reading": "may-fail", "abort": "signal"}):
            bad = {k: v for k, v in bad.items() if v is not None}
            with self.assertRaises(shapes.ShapeError):
                shapes.term(bad, distribution=False)

    def test_rv64gc_input_set_shapes(self):
        st = {"kind": "decidability", "builds": ["plain", "asan"], "reading": "may-fail", "machine": "rv64gc"}
        self.assertEqual(shapes.shape_name(st, distribution=False), "agreement_decidable_rv64gc")

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

    def test_a_carriage_return_in_distribution_v_s_body_survives_generate_then_check(self):
        dist = "projects/zlib/checksum_fuzzer/Distribution.v"
        with tree() as t:
            t.write(dist, t.read(dist) + '(* a\rb *)\n')
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

    def test_a_distribution_weight_or_mass_of_zero_is_refused(self):
        rel = "projects/zlib/checksum_fuzzer/harness.yaml"
        with tree(render=False) as t:
            for key in ("payload", "wrong_argc", "missing_file", "envp", "full_support", "mass"):
                for zero in ("0", "0/5"):
                    with self.subTest(key=key, zero=zero):
                        y = t.yaml(rel)
                        d = y["distribution"]
                        (d if key == "mass" else d["components"])[key] = zero
                        if key == "envp":
                            d["envp"] = ["A=1"]
                        self.assertTrue(any("distribution" in e for e in schema.validate("harness", y)), key)

    def test_the_statement_files_rocq_is_written_by_claims_alone(self):
        def calls(path, function):
            tree_ = ast.parse(open(os.path.join(os.path.dirname(generate.__file__), path)).read())
            node = next(n for n in tree_.body if isinstance(n, ast.FunctionDef) and n.name == function)
            return {(n.value.id, n.attr) for n in ast.walk(node)
                    if isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name)}
        self.assertNotIn(("shapes", "term"), calls("generate.py", "statements_v"))
        self.assertIn(("claims", "statements_v"), calls("generate.py", "statements_v"))
        self.assertIn(("shapes", "term"), calls("claims.py", "statements_v"))
        text = open(generate.__file__).read()
        for template in ("Images.v.tmpl", "images-dune.tmpl", "Distribution-header.v.tmpl"):
            self.assertNotIn(template, text)

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

    def test_the_rust_allocator_shim_is_a_kind(self):
        """oss-verify's link check lists the allocator shim of a Rust ASan build as kind rust-allocator-shim."""
        shim = {"name": "client.allocator_shim.rcgu.o", "sha256": "5e" * 32}
        with tree(render=False) as t:
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            y["builds"]["asan"]["uninstrumented"] = [dict(shim, kind="rust-allocator-shim")]
            self.assertEqual(schema.validate("harness", y), [])
            y["builds"]["asan"]["uninstrumented"] = [dict(shim, kind="not-a-kind")]
            errors = schema.validate("harness", y)
            self.assertEqual(len(errors), 1, errors)
            self.assertIn("uninstrumented[0].kind: 'not-a-kind' is not one of", errors[0])
        with tree() as t:
            h = "projects/zlib/checksum_fuzzer/harness.yaml"
            y = t.yaml(h)
            y["builds"]["asan"]["uninstrumented"] = [dict(shim, kind="rust-allocator-shim")]
            t.put_yaml(h, y)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertIn("- asan: `client.allocator_shim.rcgu.o` (Rust's allocator shim)",
                          t.read("projects/zlib/checksum_fuzzer/README.md"))


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


CHECKSUM = "projects/zlib/checksum_fuzzer/"
API_DRIVER = "projects/zlib/api-driver/"
# two scenarios of the upstream fuzz target and two functions of a debug build: stand-ins, not facts of zlib
SCENARIOS = [{"name": "gzip-stream", "reason": "The recipe builds zlib without its gzip file functions."},
             {"name": "large-window", "reason": "The driver caps the window at 15 bits."}]
DEBUG_ADDITIONS = [{"function": "z_debug_dump", "source": "zutil.c"},
                   {"function": "inflate_table_check", "source": "contrib/debug/inftrees_check.c"}]
SANITIZERS = {"plain": "none", "ubsan": "undefined", "asan": "address", "asan-ubsan": "address+undefined"}


def flat(text):
    """text with every run of white space read as one space: the words of wrapped prose."""
    return " ".join(text.split())


def statement_docs(text):
    """{statement name: its doc comment, flat} of a rendered Statements.v."""
    return {m.group(2): flat(m.group(1)) for m in re.finditer(r"\(\*\* (.*?) \*\)\nDefinition (\w+)", text, re.S)}


def definitions(text):
    """The Definitions of a rendered Statements.v, without their doc comments."""
    return re.findall(r"^Definition .*?\.$", text, re.M | re.S)


def with_fields(t, rel=CHECKSUM, scenarios=SCENARIOS, enable_debug=False, unittests=False, additions=None, **extra):
    """Give the harness at rel a deviation record (with enable_debug and unittests as given), excluded_scenarios and,
    with additions, debug_additions; extra sets other harness.yaml keys."""
    y = t.yaml(rel + "harness.yaml")
    y["deviation"] = {"library_commit": y["library"]["commit"], "tls_backend": "none", "enable_debug": enable_debug,
                      "unittests": unittests, "sanitizer": {b: SANITIZERS[b] for b in y["builds"]},
                      "harness_origin": "patched", "architecture": "riscv64"}
    if scenarios:
        y["excluded_scenarios"] = scenarios
    if additions:
        y["debug_additions"] = additions
    y.update(extra)
    t.put_yaml(rel + "harness.yaml", y)


EXCLUDED_DOC = ("No binary that this statement is about runs these scenarios of the upstream fuzz target: "
                "- gzip-stream: The recipe builds zlib without its gzip file functions. "
                "- large-window: The driver caps the window at 15 bits.")
EXCLUDED_README = ("No binary that the statements here are about runs these scenarios of the upstream fuzz target:\n\n"
                   "- `gzip-stream`: The recipe builds zlib without its gzip file functions.\n"
                   "- `large-window`: The driver caps the window at 15 bits.")
DEBUG_DOC = ("Each binary that this statement is about contains zlib built with its debug configuration: ENABLE_DEBUG "
             "and UNITTESTS. The statement claims only the exact binary of each build that it is about. It claims "
             "nothing about zlib built without this configuration. The harness calls these functions, which only the "
             "debug configuration exports: - [z_debug_dump] in zutil.c - [inflate_table_check] in "
             "contrib/debug/inftrees_check.c The maintainers of zlib can refuse a witness found only through these "
             "functions.")
DEBUG_README = ("Each binary that the statements here are about contains zlib built with its debug configuration: "
                "`ENABLE_DEBUG` and `UNITTESTS`. Each statement claims only the exact binary of each build that it is "
                "about. It claims nothing about zlib built without this configuration.\n\n"
                "The harness calls these functions, which only the debug configuration exports:\n\n"
                "- `z_debug_dump` in `zutil.c`\n- `inflate_table_check` in `contrib/debug/inftrees_check.c`\n\n"
                "The maintainers of zlib can refuse a witness found only through these functions.")


class ExcludedScenariosAndDebugBuild(unittest.TestCase):
    """harness.yaml excluded_scenarios, deviation and debug_additions: comment text in every rendered statement's doc
    and in the harness README, which `oft generate --check` holds to the facts (spec R3, check C3)."""

    def test_two_excluded_scenarios_are_in_each_statement_and_in_the_readme(self):
        with tree() as t:
            with_fields(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            docs = statement_docs(t.read(CHECKSUM + "Statements.v"))
            self.assertEqual(sorted(docs), sorted(t.yaml(CHECKSUM + "harness.yaml")["statements"]))
            for name, doc in docs.items():
                self.assertIn(EXCLUDED_DOC, doc, name)
                self.assertNotIn("debug configuration", doc, name)
            readme = t.read(CHECKSUM + "README.md")
            self.assertIn(EXCLUDED_README, readme)
            self.assertNotIn("debug configuration", readme)
            self.assertEqual(t.generate(check=True), 0, t.last_output)

    def test_a_debug_build_names_its_configuration_its_functions_and_the_refusal_in_both_files(self):
        with tree() as t:
            with_fields(t, scenarios=None, enable_debug=True, unittests=True, additions=DEBUG_ADDITIONS)
            self.assertEqual(t.generate(), 0, t.last_output)
            docs = statement_docs(t.read(CHECKSUM + "Statements.v"))
            self.assertEqual(len(docs), 11)
            for name, doc in docs.items():
                self.assertTrue(doc.endswith(DEBUG_DOC), name)
                self.assertNotIn("scenarios of the upstream fuzz target", doc, name)
            readme = t.read(CHECKSUM + "README.md")
            self.assertIn(DEBUG_README, readme)
            self.assertIn("- `enable_debug` is `true`: the builds compile zlib with its `ENABLE_DEBUG` setting.",
                          readme)
            self.assertIn("- `unittests` is `true`: the builds compile zlib with its `UNITTESTS` setting.", readme)

    def test_one_debug_setting_is_named_alone(self):
        with tree() as t:
            with_fields(t, scenarios=None, unittests=True)
            self.assertEqual(t.generate(), 0, t.last_output)
            doc = statement_docs(t.read(CHECKSUM + "Statements.v"))["plain_halts"]
            self.assertIn("contains zlib built with its debug configuration: UNITTESTS. The statement claims only", doc)
            self.assertNotIn("ENABLE_DEBUG", doc)
            self.assertNotIn("can refuse a witness", doc)       # no debug_additions: no list and no refusal note
            readme = t.read(CHECKSUM + "README.md")
            self.assertIn("its debug configuration: `UNITTESTS`. Each statement", readme)
            self.assertIn("- `enable_debug` is `false`: the builds compile zlib without its `ENABLE_DEBUG` setting.",
                          readme)

    def test_the_readme_says_each_deviation_field_in_words(self):
        with tree() as t:
            with_fields(t, scenarios=None)
            self.assertEqual(t.generate(), 0, t.last_output)
            readme = t.read(CHECKSUM + "README.md")
            self.assertIn(
                "## The build these statements are about\n"
                "The `deviation` record in harness.yaml says what these builds are. It also says where they differ "
                "from the builds of OSS-Fuzz.\n\n"
                "- `library_commit` is `51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf`: the builds use zlib at this "
                "commit.\n"
                "- `tls_backend` is `none`: the binaries link no TLS library.\n"
                "- `enable_debug` is `false`: the builds compile zlib without its `ENABLE_DEBUG` setting.\n"
                "- `unittests` is `false`: the builds compile zlib without its `UNITTESTS` setting.\n"
                "- `sanitizer` gives the sanitizers of each build:\n"
                "  - plain: no sanitizer\n  - ubsan: UndefinedBehaviorSanitizer\n  - asan: AddressSanitizer\n"
                "  - asan-ubsan: AddressSanitizer and UndefinedBehaviorSanitizer\n"
                "- `origin` (where the fuzz target comes from) is `oss-fuzz`: the fuzz target is the file of "
                "OSS-Fuzz.\n"
                "- `harness_origin` (what the harness source is) is `patched`: the build applies a patch to the "
                "harness source.\n"
                "- `architecture` is `riscv64`: the binaries are riscv64 programs.\n\n"
                "## What the harness checks\n", readme)
            self.assertNotIn("scenarios of the upstream fuzz target", readme)
            y = t.yaml(CHECKSUM + "harness.yaml")
            y["deviation"]["tls_backend"] = "wolfssl"
            t.put_yaml(CHECKSUM + "harness.yaml", y)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertIn("- `tls_backend` is `wolfssl`: the binaries link the TLS library wolfSSL.\n",
                          t.read(CHECKSUM + "README.md"))

    def test_with_every_build_withheld_the_readme_says_that_no_check_reads_tls_backend(self):
        """No published build has a scan, so deviation.compare takes any tls_backend: the README says that, and not
        what the binaries link.  A harness that publishes a build says what they link, as before, also with another
        build withheld."""
        unread = "- `tls_backend` is `%s`: no published build has a scan, so no check reads this value.\n"
        with tree() as t:
            n = 0
            for rel, only in ((CHECKSUM, None), (API_DRIVER, {"asan-ubsan"})):
                with_fields(t, rel=rel, scenarios=None)
                y = t.yaml(rel + "harness.yaml")
                y["deviation"]["tls_backend"] = "openssl"
                withheld = only or set(y["builds"])
                for b in withheld:
                    y["builds"][b] = {"file": y["builds"][b]["file"], "withheld": "not-yet-published"}
                    n += 1
                for s in y["statements"].values():
                    if withheld & set(s["builds"]):
                        for k in ("witness", "binds_checks"):
                            s.pop(k, None)
                        s["status"], s["withheld"] = "withheld", "not-yet-published"
                t.put_yaml(rel + "harness.yaml", y)
            r = t.yaml("release.yaml")
            r["counts"]["binaries"] -= n
            t.put_yaml("release.yaml", r)
            self.assertEqual(t.generate(), 1)         # checksum_fuzzer's statement files are no longer produced
            for line in t.last_output.splitlines():
                if line.endswith("no longer produce; remove it"):
                    os.unlink(t.path(line.split(":")[0]))
            for tls in ("openssl", "none"):
                y = t.yaml(CHECKSUM + "harness.yaml")
                y["deviation"]["tls_backend"] = tls
                t.put_yaml(CHECKSUM + "harness.yaml", y)
                self.assertEqual(t.generate(), 0, t.last_output)
                readme = t.read(CHECKSUM + "README.md")
                self.assertIn("commit.\n" + unread % tls + "- `enable_debug` is", readme)
                self.assertNotIn("TLS library", readme)
            readme = t.read(API_DRIVER + "README.md")
            self.assertIn("commit.\n- `tls_backend` is `openssl`: the binaries link the TLS library OpenSSL.\n", readme)
            self.assertNotIn("no check reads", readme)

    def test_a_withheld_statement_gets_none_of_the_text(self):
        with tree() as t:
            with_fields(t, rel=API_DRIVER, enable_debug=True, additions=DEBUG_ADDITIONS)
            self.assertEqual(t.generate(), 0, t.last_output)
            s = t.read(API_DRIVER + "Statements.v")
            self.assertIn("(* asan_ubsan_agrees: withheld; see README.md. *)\n", s)
            docs = statement_docs(s)
            self.assertNotIn("asan_ubsan_agrees", docs)
            for name, doc in docs.items():
                self.assertIn(EXCLUDED_DOC, doc, name)
                self.assertIn("The driver calls these functions, which only the debug configuration exports", doc)
            self.assertEqual(flat(s).count("No binary that this statement is about"), len(docs))

    def test_the_fields_change_no_definition_no_fingerprint_and_no_other_file(self):
        with tree() as t:
            before = generate.render_all(facts.load(t.root))
            prints, tsv = fingerprints(t), t.read("index/statements.tsv")
            with_fields(t, enable_debug=True, unittests=True, additions=DEBUG_ADDITIONS)
            self.assertEqual(t.generate(), 0, t.last_output)
            after = generate.render_all(facts.load(t.root))
            self.assertEqual(sorted(k for k in before if before[k] != after.get(k)),
                             [CHECKSUM + "README.md", CHECKSUM + "Statements.v"])
            self.assertEqual(sorted(after), sorted(before))
            self.assertEqual(definitions(after[CHECKSUM + "Statements.v"]),
                             definitions(before[CHECKSUM + "Statements.v"]))
            self.assertEqual(len(definitions(before[CHECKSUM + "Statements.v"])), 11)
            self.assertEqual(fingerprints(t), prints)
            self.assertEqual(t.read("index/statements.tsv"), tsv)

    def test_a_harness_with_none_of_the_fields_renders_as_before_them(self):
        """No section, no paragraph and no blank line of the new text: removing the fields renders every file as
        it was before they were added."""
        with tree() as t:
            before = generate.render_all(facts.load(t.root))
            readme = before[CHECKSUM + "README.md"]
            for absent in ("## The build these statements are about", "## Instances", "debug configuration",
                           "scenarios of the upstream fuzz target"):
                self.assertNotIn(absent, readme + before[CHECKSUM + "Statements.v"])
            self.assertIn("prints each return value.\n\n## What the harness checks\n", readme)
            self.assertIn("| open |\n\n## Builds\n", readme)
            plain = t.read(CHECKSUM + "harness.yaml")
            statements = t.yaml(CHECKSUM + "harness.yaml")["statements"]
            statements["plain_halts"]["instance"] = InstanceList.HALTS
            with_fields(t, enable_debug=True, additions=DEBUG_ADDITIONS, statements=statements)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertIn("## Instances", t.read(CHECKSUM + "README.md"))
            t.write(CHECKSUM + "harness.yaml", plain)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(generate.render_all(facts.load(t.root)), before)
            self.assertEqual(t.generate(check=True), 0, t.last_output)

    def test_rendered_before_a_scenario_was_added_fails_the_check(self):
        with tree() as t:
            with_fields(t, scenarios=SCENARIOS[:1])
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(t.generate(check=True), 0, t.last_output)
            with_fields(t)
            self.assertEqual(t.generate(check=True), 1)
            self.assertIn(CHECKSUM + "Statements.v: differs from its rendering", t.last_output)
            self.assertIn(CHECKSUM + "README.md: differs from its rendering", t.last_output)

    def test_rendered_before_enable_debug_was_set_true_fails_the_check(self):
        with tree() as t:
            with_fields(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            with_fields(t, enable_debug=True)
            self.assertEqual(t.generate(check=True), 1)
            self.assertIn(CHECKSUM + "Statements.v: differs from its rendering", t.last_output)
            self.assertIn(CHECKSUM + "README.md: differs from its rendering", t.last_output)

    def test_a_definition_edited_by_hand_fails_the_check(self):
        with tree() as t:
            with_fields(t, enable_debug=True, unittests=True, additions=DEBUG_ADDITIONS)
            self.assertEqual(t.generate(), 0, t.last_output)
            p = CHECKSUM + "Statements.v"
            s = t.read(p)
            edited = s.replace("halts_may_fail Exits.any Images.plain.", "halts_may_fail Exits.ok Images.plain.")
            self.assertNotEqual(edited, s)
            t.write(p, edited)
            self.assertEqual(t.generate(check=True), 1)
            self.assertIn(p + ": differs from its rendering", t.last_output)


WORKFLOWS = os.path.join(REPO, ".github", "workflows")
# partial_checkouts searches every file of the repository but those of the facts trees: projects/ and the old
# layout's top folders hold facts and proofs, and no script or workflow that makes a checkout.  It leaves out Markdown
# files too, since a document makes no checkout (no job runs it), and tests, which check out trees of their own.
FACTS_TREES = ("projects",) + layout.OLD_TOPS
# the paths the guard (partial_checkouts) leaves out: a file under a facts tree, a Markdown file, and a test (one under
# a tests or testdata folder, or whose name starts with test_).  pr.yml's reach step holds these patterns word for word,
# in this order, as the patterns of its `grep -vE` (test_keys.py checks it).
GUARD_SKIPS = (r"^(%s)/" % "|".join(FACTS_TREES), r"\.md$", r"(^|/)(tests|testdata)/", r"(^|/)test_[^/]*$")
# a line that makes or widens a partial checkout: a `git sparse-checkout set` or `add`, in shell or as the words of a
# Python list or call, or a write of git's sparse-checkout file itself.  pr.yml's reach step holds it word for word,
# with partial_checkouts' skips, and runs these tests when a changed file holds such a line: change the two together.
SPARSE_COMMAND = r"sparse-checkout[^A-Za-z0-9_-]+(set|add)([^A-Za-z0-9_-]|$)|info/sparse-checkout"
EXPRESSION = re.compile(r"\$\{\{.*?\}\}")   # a GitHub Actions expression
_WHOLE = "whole directories in cone mode, so each proof library is in the checkout whole or not at all"
_FOLDERS = ("whole folders in or out, none inside a proof library, so each proof library is in the checkout whole or "
            "not at all")
_CB = ("sp: '/*' with the projects and proofs folders out and, back in, proofs/lib and the unit's project and each "
       "donor, as /proofs/<x>/ and /projects/<x>/: " + _FOLDERS)
# Each line that partial_checkouts finds and cannot read, by (file, the line with its indent removed): a partial
# checkout whose patterns it cannot read, or a line that names one in another way; and why it makes no tree that keeps
# a proof library's lib/dune without its other sources.  A new such line, or a changed one, fails InstanceList until a
# person reads it and writes it here.
UNREAD = {
    (".github/workflows/pr.yml",
     "sparse='sparse-checkout[^A-Za-z0-9_-]+(set|add)([^A-Za-z0-9_-]|$)|info/sparse-checkout'"):
        "the pattern the reach step searches the changed files for, to run these tests: it makes no checkout",
    (".github/workflows/pr.yml", 'git -C base sparse-checkout set --no-cone "${paths[@]}"'):
        "the release_window job's DRIFT_PATHS (/tools/ /theories/ /toolchain/ /tests/ /dune-project /release.yaml "
        ".gitattributes), which platform_drift reads: no file of a proof library",
    (".github/workflows/pr.yml", 'git -C head sparse-checkout set --no-cone "${paths[@]}"'):
        "the release_window job's DRIFT_PATHS (/tools/ /theories/ /toolchain/ /tests/ /dune-project /release.yaml "
        ".gitattributes), which platform_drift reads: no file of a proof library",
    (".github/workflows/publish.yml", "${{ needs.cut.result != 'success' && 'tools/publish' || '' }}"):
        "tools/publish in cone mode, or no sparse checkout: no library, or each one whole",
    (".github/workflows/review.yml", 'git sparse-checkout add --stdin < "$RUNNER_TEMP/dirs"'):
        "the fuzz targets' directories that the step checks, added to the job's cone checkout: " + _WHOLE,
    ("dev/stream/bin/ossv-measure-clone", 'git "${cred[@]}" sparse-checkout add "proofs/$t1" checker-image vendor'):
        "added to the cone of `git clone --sparse`: " + _WHOLE,
    ("dev/stream/bin/ossv-measure-clone", 'git "${cred[@]}" sparse-checkout add "proofs/$t2"'):
        "added to the cone of `git clone --sparse`: " + _WHOLE,
    ("dev/stream/bin/ossv-measure-clone",
     'record "A2 sparse-checkout add proofs/$t1 checker-image vendor; submodule update --init" . "$s"'):
        "the name under which the script records the time of the add above it",
    ("dev/stream/bin/ossv-measure-clone", 'record "B1 sparse-checkout add proofs/$t2" . "$s"'):
        "the name under which the script records the time of the add above it",
    ("dev/stream/bin/ossv-queue-check",
     'must(["git", "-C", str(path), "sparse-checkout", "set", "--no-cone", sparse], "the sparse checkout")'):
        "each caller gives the one pattern tools: no file of a proof library",
    ("dev/stream/bin/ossv-wt-add",
     '${sparse_lock[@]+"${sparse_lock[@]}"} git -C "$destination" sparse-checkout set --cone -- "${sparse[@]}"'):
        "top-level directories, proofs/lib and the folders of the projects in the lane: " + _WHOLE,
    ("tools/oft/ci/facts-review-gather",
     'git -C "$git_dir" sparse-checkout set --no-cone "${paths[@]/#//}" "${sparse[@]}" "${moved[@]/#//}"'):
        "no file of a proof library: of a fuzz target's proofs it takes the provenance folder alone, in either layout",
    ("tools/oft/ci/pr-steps.sh",
     "printf '/*\\n!/proofs/*/*/lib/\\n!/projects/*/*/proofs/lib/\\n' > \"$checkout/.git/info/sparse-checkout\""):
        "release-check.yml's plan set (test_workflow_verdicts holds them equal): no library, dune included",
    ("tools/oft/layout.py", 'lines.append("  git sparse-checkout add %s" % (lib if in_cone else "/%s/" % lib))'):
        "advice that oft prints to a person: it adds one library back whole",
    ("tools/publish/dry-run", 'git(path, "sparse-checkout", "set", "--no-cone", *sparse)'):
        "each caller gives DRIFT_PATHS or a few of /tools/, /release.yaml, /toolchain/allowed-axioms.txt and "
        "/.github/actions/place-drafts/: no file of a proof library",
    # on main since #2581; the entry stands only where the file is, so it holds at every base too
    ("dev/stream/bin/ossv-find-mirror", 'git(["sparse-checkout", "set", "--no-cone"] + sparse_patterns(row), path)'):
        "a mirror of another repository's published proof corpus, at its pinned commit: not a tree of this "
        "repository, and no oft generate or lint runs over it",
    ("dev/stream/lane/tools/asan-unit-base.sh",
     'git -C "$WT" sparse-checkout set --no-cone "${cone[@]}" > /dev/null'):
        "asan_cone (lines 87-92): '/*' with the projects and proofs folders out and, back in, proofs/lib, the unit's "
        "project without its proofs folders, the unit's proofs folder and each donor: " + _FOLDERS,
    ("dev/stream/lane/tools/cb-01d729faac6c", 'git -C "$d" sparse-checkout set --no-cone "${sp[@]}" > /dev/null &&'):
        _CB,
    ("dev/stream/lane/tools/cb-1edd6bbbf529", 'git -C "$d" sparse-checkout set --no-cone "${sp[@]}" > /dev/null &&'):
        _CB,
    ("dev/stream/lane/tools/cb-28528e1b4dbc", 'git -C "$d" sparse-checkout set --no-cone "${sp[@]}" > /dev/null &&'):
        _CB,
    ("dev/stream/lane/tools/cb-4770bf02b744", 'git -C "$d" sparse-checkout set --no-cone "${sp[@]}" > /dev/null &&'):
        _CB,
    ("dev/stream/lane/tools/cb-5a64e42d3e50", 'git -C "$d" sparse-checkout set --no-cone "${sp[@]}" > /dev/null &&'):
        _CB,
    ("dev/stream/lane/tools/cb-8b16df1d4b9f", 'git -C "$d" sparse-checkout set --no-cone "${sp[@]}" > /dev/null &&'):
        _CB,
    ("dev/stream/lane/tools/cb-d02a58a345b9", 'git -C "$d" sparse-checkout set --no-cone "${sp[@]}" > /dev/null &&'):
        _CB,
    ("dev/stream/lane/tools/pr-vm-check-0f9b9814dfc0.sh",
     'm = re.findall(r"^\\s*git -C base sparse-checkout set (.*)$", s["run"], re.M)'):
        "Python that finds the patterns of the base step of the lint job of a pr.yml, to hold lint_base_sparse_args "
        "to them: it makes no checkout",
    ("dev/stream/lane/tools/pr-vm-check-0f9b9814dfc0.sh",
     'git -C "$P/head" sparse-checkout set --no-cone "${sparse[@]}"'):
        "nolib_patterns (lines 273-276): '/*' without the old layout's libraries, and without the per-project "
        "layout's too when L1_LAYOUT is true: no library, dune included, or each one whole",
    ("dev/stream/lane/tools/pr-vm-check-0f9b9814dfc0.sh",
     'else git -C "$P/base" sparse-checkout set --no-cone "${sparse[@]}"; fi'):
        "nolib_patterns (lines 273-276): '/*' without the old layout's libraries, and without the per-project "
        "layout's too when L1_LAYOUT is true: no library, dune included, or each one whole",
    ("dev/stream/lane/tools/pr-vm-check-0f9b9814dfc0.sh", 'git -C "$L/base" sparse-checkout set "${sparse[@]}"'):
        "lint_base_sparse_args (lines 279-285): --cone tools findings, or --no-cone '/*' '!/*/' with /tools/, "
        "/findings/ and the projects' unpatched.yaml and findings folders back in: no file of a proof library",
    ("dev/stream/lane/tools/pr-vm-check-8984a0871231.sh",
     'm = re.findall(r"^\\s*git -C base sparse-checkout set (.*)$", s["run"], re.M)'):
        "Python that finds the patterns of the base step of the lint job of a pr.yml, to hold lint_base_sparse_args "
        "to them: it makes no checkout",
    ("dev/stream/lane/tools/pr-vm-check-8984a0871231.sh",
     'git -C "$P/head" sparse-checkout set --no-cone "${sparse[@]}"'):
        "nolib_patterns (lines 261-264): '/*' without the old layout's libraries, and without the per-project "
        "layout's too when L1_LAYOUT is true: no library, dune included, or each one whole",
    ("dev/stream/lane/tools/pr-vm-check-8984a0871231.sh",
     'else git -C "$P/base" sparse-checkout set --no-cone "${sparse[@]}"; fi'):
        "nolib_patterns (lines 261-264): '/*' without the old layout's libraries, and without the per-project "
        "layout's too when L1_LAYOUT is true: no library, dune included, or each one whole",
    ("dev/stream/lane/tools/pr-vm-check-8984a0871231.sh", 'git -C "$L/base" sparse-checkout set "${sparse[@]}"'):
        "lint_base_sparse_args (lines 267-273): --cone tools findings, or --no-cone '/*' '!/*/' with /tools/, "
        "/findings/ and the projects' unpatched.yaml and findings folders back in: no file of a proof library",
    ("dev/stream/lane/tools/ship.sh", 'git -C "$WT" sparse-checkout set --no-cone "${want[@]}"'):
        "ship_cone (lines 314-335): '/*' with the projects and proofs folders out and, back in, proofs/lib, each "
        "unit's project without its proofs folders, each donor and each unit's proofs folder: " + _FOLDERS,
    # the line and the next, which its backslash joins to it
    ("dev/stream/lane/tools/ship.sh", '[ "$sparse" = "$(printf \'%s\\n\' "${want[@]}")" ]      '
     '|| git -C "$WT" sparse-checkout set --no-cone "${want[@]}"'):
        "ship_cone's set again, as at line 374, when the worktree's set is not that one: " + _FOLDERS,
    ("dev/stream/lane/tools/zdraftbase.py", "git('sparse-checkout', 'set', '--no-cone', *pats, cwd=wt)"):
        "sparse_patterns (lines 79-86): the unit's proofs folder, /projects/ (without its proofs folders in the "
        "per-project layout) and /theories/: " + _FOLDERS,
}


def _sparse_set(verb, words):
    """(cone, [pattern]) of `git sparse-checkout <verb> <words>`, or None when the words do not say what it checks
    out: an `add` widens a set made elsewhere, --stdin reads the patterns from elsewhere, a set that names neither
    --cone nor --no-cone keeps the mode the checkout had, and a pattern can hold a value of the script's own (a word
    that is not text, in Python, is None).  A value that is a whole part of a non-cone pattern's path, in a pattern
    with a part that is text, names one project or fuzz target: it reads as `*`, which is that set for each name at
    once (/projects/$p/ reads as /projects/*/).  A pattern of values alone ("$PATTERNS", or a workflow's
    ${{ inputs.x }}) can stand for any patterns at all, so it is not read."""
    if verb != "set":
        return None
    cone, patterns, options = None, [], True
    for w in words:
        if options and w == "--":
            options = False
        elif options and w in ("--cone", "--no-cone"):
            cone = w == "--cone"
        elif options and w in ("--skip-checks", "--sparse-index", "--no-sparse-index"):
            continue
        elif w is None or (options and w.startswith("-")):
            return None
        else:
            patterns.append(w)
    if cone is None or not patterns:
        return None
    out = []
    for p in patterns:
        if "$" in p or "`" in p:
            if cone:
                return None
            p = "/".join("*" if re.fullmatch(r"\$(\w+|\{\w+\})", part) else part for part in p.split("/"))
            if "$" in p or "`" in p or not re.search(r"[^!/*]", p):
                return None
        out.append(p)
    return cone, out


def _shell_lines(text):
    """(number, line) of each line of shell text, with a line that ends in a backslash joined to the next."""
    out, lines, i = [], text.split("\n"), 0
    while i < len(lines):
        n, line = i + 1, lines[i]
        while line.endswith("\\") and i + 1 < len(lines):
            i += 1
            line = line[:-1] + " " + lines[i]
        out.append((n, line))
        i += 1
    return out


def _folded_lines(text):
    """The numbers of the lines of YAML text inside a folded block scalar: after a key whose value is `>`, `>-` or
    `>+` (an indentation digit allowed), each later line that is blank or indented more than the key's line.  YAML
    joins those lines, so a command there can run on to the next line with no backslash: the test does not read them."""
    out, key = set(), None
    for n, line in enumerate(text.split("\n"), 1):
        if key is not None and (not line.strip() or len(line) - len(line.lstrip(" ")) > key):
            out.add(n)
            continue
        m = re.match(r"( *)(-\s+)?[^\s#][^#]*:\s+>([1-9][-+]?|[-+][1-9]?)?\s*(#.*)?$", line)
        key = len(m.group(1)) if m else None
    return out


def _shell_command(line):
    """(verb, [word]) of the `git sparse-checkout set` or `add` of one line of shell; "comment" when the line names
    one only in a comment; None when it names one in another way (in a string, or as git's sparse-checkout file)."""
    lex = shlex.shlex(EXPRESSION.sub("${expression}", line), posix=True, punctuation_chars=True)
    lex.whitespace_split = True
    try:
        tokens = list(lex)
    except ValueError:                  # a quote that the line does not close
        return None
    for i in range(len(tokens) - 1):
        if tokens[i] == "sparse-checkout" and tokens[i + 1] in ("set", "add"):
            words = []
            for w in tokens[i + 2:]:
                if w[:1] and w[0] in "();<>|&":
                    if w[0] in "<>" and words and words[-1].isdigit():
                        words.pop()     # the file descriptor of a redirection, as in 2>
                    break
                words.append(w)
            return tokens[i + 1], words
    named = re.search(SPARSE_COMMAND, line)
    if named and re.search(r"(^|\s)#", line[:named.start()]) and not re.search(SPARSE_COMMAND, " ".join(tokens)):
        return "comment"
    return None


def _python_commands(text):
    """{line: (verb, [word])} of each `git sparse-checkout set` or `add` of Python source: a list, a tuple or a call
    whose items run "sparse-checkout", then "set" or "add".  An item that is no string constant is None."""
    found = {}
    for node in ast.walk(ast.parse(text)):
        items = (node.elts if isinstance(node, (ast.List, ast.Tuple))
                 else node.args if isinstance(node, ast.Call) else [])
        words = [n.value if isinstance(n, ast.Constant) and isinstance(n.value, str) else None for n in items]
        for i in range(len(words) - 1):
            if words[i] == "sparse-checkout" and words[i + 1] in ("set", "add"):
                found[items[i].lineno] = (words[i + 1], words[i + 2:])
    return found


def _language(root, rel):
    """"python" or "shell": the language of the file rel of the repository at root, by its name or its #! line (the
    `run:` lines of a workflow or an action are shell); None for any other file."""
    if rel.endswith(".py"):
        return "python"
    if rel.endswith((".sh", ".bash", ".yml", ".yaml")):
        return "shell"
    with open(os.path.join(root, rel), "rb") as f:
        first = f.readline().decode("utf-8", "replace")
    if not first.startswith("#!"):
        return None
    return "python" if "python" in first else "shell" if re.search(r"\b(ba|da|z)?sh\b", first) else None


# What partial_checkouts does not see:
# - A file is searched only when git grep finds a line of it that matches SPARSE_COMMAND, such as `sparse-checkout`
#   and `set` on one line.  So a command split over two lines is never found in a file with no other such line: the
#   two words on two lines, a shell continuation before `set`, or a Python list with one item per line.
# - A plain (not folded) multi-line YAML value is read from its first line only.  `- run: git sparse-checkout set
#   --no-cone '/*'`, with more patterns on a deeper next line, reads as ['/*'], the whole tree.
# - _folded_lines takes the block's indent from the line of the key: the column of its `-`.  So after `- if: >-` it
#   counts the other keys of that step as folded.  A readable one-line `run:` there is refused, and its UNREAD entry
#   takes the set out of the comparison.
# - An UNREAD entry is keyed on the line of the `set` (or the line that names one) alone.  So for each entry whose
#   patterns come from other lines, a change to those lines is not seen: for example the asan_cone, ship_cone and
#   sparse_patterns of asan-unit-base.sh, ship.sh and zdraftbase.py, the cb scripts' sp, and pr-vm-check's
#   nolib_patterns and lint_base_sparse_args.
# - Each set is compared only on the fixture tree of InstanceList, in both layouts: its one proof library is
#   zlib/checksum_fuzzer's.  A set is never applied to this repository's own index.
# - A value that holds two path parts reads as one `*`, which matches one part.  In the cb scripts `$u` is `P/H`, so a
#   pattern such as `/proofs/$u/` there would be compared as `/proofs/*/`, which is not the script's set.
def partial_checkouts(root=REPO):
    """The partial checkouts of the repository at root: ([(where, cone, [pattern])], [(where, file, line)]).  The
    first list holds each one whose patterns this reads: the `sparse-checkout` of each step of a workflow or an
    action, and each `git sparse-checkout set` that git grep finds in a shell or Python file outside FACTS_TREES.  The
    second holds each one that _sparse_set cannot read (each `add` among them, and each set with a pattern of values
    alone), each line of a folded block of a YAML file (`run: >-`, _folded_lines), whose text this does not unfold,
    and each line that names one in another way: a string, a write of git's sparse-checkout file, a file in another
    language.  Markdown files and tests are left out (GUARD_SKIPS): a document makes no checkout, and a test checks
    out trees of its own."""
    read, unread = [], []

    def take(where, rel, text, verb, words):
        got = _sparse_set(verb, words)
        if got:
            read.append((where,) + got)
        else:
            unread.append((where, rel, text))

    steps = []
    for path in sorted(glob.glob(os.path.join(root, ".github", "workflows", "*.y*ml"))):
        for job, data in (yamlio.load_file(path).get("jobs") or {}).items():
            steps += [("%s: %s" % (os.path.relpath(path, root), job), s) for s in data.get("steps") or []]
    for path in sorted(glob.glob(os.path.join(root, ".github", "actions", "**", "action.y*ml"), recursive=True)):
        steps += [(os.path.relpath(path, root), s) for s in (yamlio.load_file(path).get("runs") or {}).get("steps")
                  or []]
    for where, step in steps:
        given = (step.get("with") or {}) if isinstance(step, dict) else {}
        text = str(given.get("sparse-checkout") or "").strip()
        if text:
            cone = given.get("sparse-checkout-cone-mode", True) not in (False, "false")
            take(where, where.split(":")[0], text, "set",
                 ["--cone" if cone else "--no-cone"] + EXPRESSION.sub("${expression}", text).split())
    r = subprocess.run(["git", "-C", root, "grep", "-z", "-l", "-I", "-E", "-e", SPARSE_COMMAND, "--", "."]
                       + [":(exclude)%s" % top for top in FACTS_TREES], capture_output=True, text=True)
    assert r.returncode in (0, 1), r.stderr
    for rel in sorted(p for p in r.stdout.split("\0") if p):
        if any(re.search(p, rel) for p in GUARD_SKIPS):
            continue
        language = _language(root, rel)
        with open(os.path.join(root, rel), encoding="utf-8", errors="replace") as f:
            source = f.read()
        folded = _folded_lines(source) if rel.endswith((".yml", ".yaml")) else set()
        lines = _shell_lines(source) if language == "shell" else list(enumerate(source.split("\n"), 1))
        commands = {}
        if language == "python":
            try:
                commands = _python_commands(source)
            except SyntaxError:
                pass
        for n, line in lines:
            if language == "python":
                got = commands.get(n)
                if got is None and (line.strip().startswith("#") or not re.search(SPARSE_COMMAND, line)):
                    continue
            elif not re.search(SPARSE_COMMAND, line):
                continue
            elif n in folded:
                got = None
            else:
                got = _shell_command(line) if language == "shell" else None
                if got == "comment":
                    continue
            if got is None:
                unread.append(("%s:%d" % (rel, n), rel, line.strip()))
            else:
                take("%s:%d" % (rel, n), rel, line.strip(), *got)
    return read, unread


class InstanceList(unittest.TestCase):
    """statements.<s>.instance: the harness README lists each statement's instance under what an instance shows.  A
    row names its lemma file (lib/Instances/<s>.v of the proof library) when the file is in the tree and `oft check`
    checks it, and only of those rows does the README say that every premise holds; a row with no lemma is recorded,
    not yet proved, and a withheld or withdrawn statement's row is not proved."""
    HALTS = {"file": "plain_halts.bin", "sha256": "ab" * 32, "bytes": 0, "path": "refused-by-driver"}
    BOUND = {"file": "asan_disagrees_at_most.bin", "sha256": "cd" * 32, "bytes": 4102, "path": "reaches-harness"}
    SHOWS = ("An instance is one input file that the record of a statement names. An instance does not show that any "
             "harness code ran on the input.")
    PROVED = ("For each row that names a lemma, the lemma proves that every premise of the statement holds on the "
              "file. Thus the premises of the statement can hold together.")
    RECORDED = ("For each row that is recorded, not yet proved, there is no lemma yet. Nothing proves that the "
                "premises of the statement hold on the file.")
    FINITE = ("For a bound or decidability statement, the lemma proves that the instance is a valid finite input with "
              "a valid entry on both builds. It does not show that the two builds disagree on it. A disagreement of "
              "the two builds is the event that a bound statement measures, not a premise.")
    HEAD = "| statement | file | bytes | sha256 | path | lemma |\n|---|---|---:|---|---|---|\n"
    HALTS_ROW = ("| `plain_halts` | `proofs/provenance/evidence/instances/plain_halts.bin` | 0 | `%s` | "
                 "`refused-by-driver`: the driver exits with status 2 before it calls the harness | " % ("ab" * 32))
    BOUND_ROW = ("| `asan_disagrees_at_most` | `proofs/provenance/evidence/instances/asan_disagrees_at_most.bin` | "
                 "4,102 | `%s` | `reaches-harness`: the driver calls the harness on the file | " % ("cd" * 32))

    def put(self, t, **instances):
        y = t.yaml(CHECKSUM + "harness.yaml")
        for name, rec in instances.items():
            y["statements"][name]["instance"] = rec
        t.put_yaml(CHECKSUM + "harness.yaml", y)

    def lemma(self, t, name):
        """Write the lemma file of statement name's instance; its path from the harness folder."""
        st = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"].statements[name]
        t.write(st.instance_lemma(), "Lemma %s_instance : True. Proof. exact I. Qed.\n" % name)
        return os.path.relpath(st.instance_lemma(), CHECKSUM)

    def section(self, t):
        readme = t.read(CHECKSUM + "README.md")
        return readme[readme.index("## Instances\n"):readme.index("\n\n## Builds\n")]

    def test_rows_with_no_lemma_are_recorded_not_yet_proved(self):
        with tree() as t:
            statements, prints = t.read(CHECKSUM + "Statements.v"), fingerprints(t)
            self.put(t, plain_halts=self.HALTS, asan_disagrees_at_most=self.BOUND)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertIn("|\n\n## Instances\n", t.read(CHECKSUM + "README.md"))
            self.assertEqual(self.section(t), "## Instances\n" + self.SHOWS + "\n\n" + self.RECORDED + "\n\n"
                             + self.HEAD + self.HALTS_ROW + "recorded, not yet proved |\n"
                             + self.BOUND_ROW + "recorded, not yet proved |")
            self.assertNotIn("every premise", self.section(t))
            self.assertEqual(t.read(CHECKSUM + "Statements.v"), statements)
            self.assertEqual(fingerprints(t), prints)

    def test_rows_with_a_lemma_name_it_and_only_they_have_every_premise_hold(self):
        with tree() as t:
            self.put(t, plain_halts=self.HALTS, asan_disagrees_at_most=self.BOUND)
            halts, bound = self.lemma(t, "plain_halts"), self.lemma(t, "asan_disagrees_at_most")
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(self.section(t), "## Instances\n" + self.SHOWS + "\n\n" + self.PROVED + "\n\n"
                             + self.FINITE + "\n\n" + self.HEAD + self.HALTS_ROW + "`%s` |\n" % halts
                             + self.BOUND_ROW + "`%s` |" % bound)
            self.assertEqual(halts, "proofs/lib/Instances/plain_halts.v")

    def test_a_lemma_on_some_rows_says_each_sentence_of_its_own_rows(self):
        with tree() as t:
            self.put(t, plain_halts=self.HALTS, asan_disagrees_at_most=self.BOUND)
            halts = self.lemma(t, "plain_halts")
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(self.section(t), "## Instances\n" + self.SHOWS + "\n\n" + self.PROVED + "\n\n"
                             + self.RECORDED + "\n\n" + self.HEAD + self.HALTS_ROW + "`%s` |\n" % halts
                             + self.BOUND_ROW + "recorded, not yet proved |")
            self.assertNotIn("valid finite input", self.section(t), "no lemma proves the bound's instance")

    def test_with_no_bound_or_decidability_instance_the_finite_sentence_is_absent(self):
        with tree() as t:
            self.put(t, plain_halts=self.HALTS)
            self.lemma(t, "plain_halts")
            self.assertEqual(t.generate(), 0, t.last_output)
            readme = t.read(CHECKSUM + "README.md")
            self.assertIn("## Instances\n" + self.SHOWS + "\n\n" + self.PROVED + "\n\n| statement |", readme)
            self.assertNotIn("valid finite input", readme)

    def test_a_withheld_statement_s_lemma_is_not_proved(self):
        """check.instances_to_check checks only the instances of the statements Statements.v carries, so a withheld
        statement's row is not proved although its lemma file is there; the bound's row, which is checked, names its
        lemma."""
        with tree() as t:
            self.put(t, plain_halts=self.HALTS, asan_disagrees_at_most=self.BOUND)
            y = t.yaml(CHECKSUM + "harness.yaml")
            y["statements"]["plain_halts"].update(status="withheld", withheld="not-yet-published")
            t.put_yaml(CHECKSUM + "harness.yaml", y)
            self.lemma(t, "plain_halts")
            bound = self.lemma(t, "asan_disagrees_at_most")
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(self.section(t), "## Instances\n" + self.SHOWS + "\n\n" + self.PROVED + "\n\n"
                             + self.FINITE + "\n\n" + self.HEAD + self.HALTS_ROW
                             + "not proved: `oft check` does not check the lemma of a withheld statement |\n"
                             + self.BOUND_ROW + "`%s` |" % bound)
            # the bound's lemma gone and the statement withdrawn: no row is proved, and the README says of none that a
            # lemma proves it
            os.remove(t.path(CHECKSUM, bound))
            y["statements"]["plain_halts"] = dict(y["statements"]["plain_halts"], status="withdrawn",
                                                  reason="A stand-in reason.")
            del y["statements"]["plain_halts"]["withheld"]
            t.put_yaml(CHECKSUM + "harness.yaml", y)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(self.section(t), "## Instances\n" + self.SHOWS + "\n\n" + self.RECORDED + "\n\n"
                             + self.HEAD + self.HALTS_ROW
                             + "not proved: `oft check` does not check the lemma of a withdrawn statement |\n"
                             + self.BOUND_ROW + "recorded, not yet proved |")

    @unittest.skipUnless(os.path.isdir(WORKFLOWS) and os.path.exists(os.path.join(REPO, ".git")),
                         "no .github/workflows or no git: tools/oft without the checkout around it")
    def test_a_checkout_without_the_library_sources_renders_the_same_readme(self):
        """Each partial checkout of the repository (partial_checkouts) that keeps a proof library's lib/dune is a tree
        that `oft generate` may render.  Three of them leave out the library's other sources and are rendered: pr.yml's
        lint job (`generate --check`), enroll.yml's facts job (facts-tree.sh: `generate`) and regenerate-shared.sh
        (`generate --check --skip-shared`).  Each one, applied by git, renders every generated file as the whole tree
        does, in both layouts, whether it leaves out the library's other sources (here lib/Helper.v) or keeps the
        whole library.  A checkout that `oft generate` refuses before it renders (generate.run: an error of the facts,
        or a proof library left unwritten) is not compared: such a tree gets no README from oft generate, so it cannot
        render a wrong one.  The controls: without its Instances/ lines a set that leaves out the other sources leaves
        out the lemma, and the row is recorded, not yet proved; and a set that keeps lib/dune and lib/Helper.v but not
        lib/Instances/ is rendered and compared, and its README differs, so its comparison fails.

        What the test reads: the `sparse-checkout` of each step of a workflow or an action, and each `git
        sparse-checkout set` with --cone or --no-cone and patterns of text, in a shell or Python file (a value that is
        a whole part of a non-cone pattern's path, in a pattern with a part that is text, reads as `*`).  What it
        refuses: a pattern of values alone ("$PATTERNS", ${{ inputs.x }}), a line of a folded YAML block (`run: >-`),
        an `add`, and each other line that it finds and cannot read; each one fails the test, naming the file and the
        line, until UNREAD says why it is no such tree.  What it leaves out: the facts trees (FACTS_TREES), Markdown
        files and tests.  A set that leaves out all of lib/, dune included, is out of scope: facts.load finds a library
        by its lib/dune, so that tree has no library at all, and it is no tree to render.

        What it does not see (the comment above partial_checkouts says each one in full).  git grep lists a file only
        when a line of it matches SPARSE_COMMAND, such as `sparse-checkout` and `set` on one line.  So a command split
        over two lines is never found in a file with no other such line: the two words on two lines, a shell
        continuation before `set`, or a Python list with one item per line.  A plain (not folded) multi-line YAML
        value is read from its first line only.  After `- if: >-`, _folded_lines counts the other keys of that step as
        folded: a readable one-line `run:` there is refused, and its UNREAD entry takes the set out of the comparison.
        An UNREAD entry is keyed on the line of the `set` (or the line that names one) alone, so for each entry whose
        patterns come from other lines a change to those lines is not seen: for example the asan_cone, ship_cone and
        sparse_patterns of asan-unit-base.sh, ship.sh and zdraftbase.py, the cb scripts' sp, and pr-vm-check's
        nolib_patterns and lint_base_sparse_args.  Each set is compared only on this test's fixture tree, in both
        layouts, and never applied to this repository's own index.  A value that holds two path parts (in the cb
        scripts, `$u` is `P/H`) reads as one `*`, which matches one part."""
        checkouts, unread = partial_checkouts()
        self.assertEqual(["%s: %s" % (where, text) for where, rel, text in unread if (rel, text) not in UNREAD], [],
                         "partial checkouts whose patterns this test cannot read: give each one literal patterns, or "
                         "add it to UNREAD with the reason that it keeps no proof library without its sources")
        found = {(rel, text) for _where, rel, text in unread}
        self.assertEqual([k for k in UNREAD if os.path.exists(os.path.join(REPO, k[0])) and k not in found], [],
                         "UNREAD entries that their file no longer holds")
        sets = {}
        for where, cone, patterns in checkouts:
            sets.setdefault((cone, tuple(patterns)), []).append(where)
        for name, make in (("new", lambda t: None), ("old", old_layout_tree)):
            with self.subTest(layout=name), tree() as t:
                make(t)
                self.put(t, plain_halts=self.HALTS)
                halts = self.lemma(t, "plain_halts")
                lib = os.path.normpath(os.path.join(CHECKSUM, halts, "..", ".."))
                lemma = os.path.normpath(os.path.join(CHECKSUM, halts))
                t.write(os.path.join(lib, "Helper.v"), "Definition one := 1.\n")
                self.assertEqual(t.generate(), 0, t.last_output)
                git_repo(t.root)
                work = t.path("..", "checkout")
                git(t.root, "worktree", "add", "-q", "--detach", work, "HEAD")
                want = generate.render_all(facts.load(work))
                self.assertIn(self.HALTS_ROW + "`%s` |" % halts, want[CHECKSUM + "README.md"])
                rendered = []
                for (cone, patterns), wheres in sorted(sets.items()):
                    if self.renders_alike(work, lib, lemma, want, cone, list(patterns), wheres):
                        rendered += wheres
                # the control: a set that keeps lib/dune and lib/Helper.v and leaves out lib/Instances/ is compared,
                # and its README, whose row is recorded, not yet proved, is not the whole tree's
                self.assertRaises(self.failureException, self.renders_alike, work, lib, lemma, want, False,
                                  ["/*", "!/proofs/*/*/lib/*/", "!/projects/*/*/proofs/lib/*/"], ["the control"])
                self.assertEqual([os.path.exists(os.path.join(work, p))
                                  for p in (os.path.join(lib, "dune"), os.path.join(lib, "Helper.v"), lemma)],
                                 [True, True, False])
                got = self.rendering(work)
                self.assertIsNotNone(got, "oft generate refuses the control's checkout")
                self.assertIn(self.HALTS_ROW + "recorded, not yet proved |", got[CHECKSUM + "README.md"])
                for where in (".github/workflows/pr.yml: lint", ".github/workflows/enroll.yml: facts",
                              "tools/oft/ci/regenerate-shared.sh:"):
                    if os.path.exists(os.path.join(REPO, where.split(":")[0])):
                        self.assertTrue([w for w in rendered if w.startswith(where)], (where, rendered))

    def renders_alike(self, work, lib, lemma, want, cone, patterns, wheres):
        """Check out the sparse set patterns in the worktree work; unless the checkout has no lib/dune of the library
        lib, or `oft generate` refuses it (rendering), assert that it renders every file as want (the whole tree's
        rendering) has it, failing with wheres.  When the checkout leaves out the library's other sources
        (lib/Helper.v), the control too: without its Instances/ lines the set leaves out the lemma file, and the row
        is recorded, not yet proved.  Whether it compared."""
        self.sparse(work, cone, patterns)
        if not os.path.isfile(os.path.join(work, lib, "dune")):
            return False
        got = self.rendering(work)
        if got is None:
            return False
        self.assertEqual(sorted(k for k in set(got) | set(want) if got.get(k) != want.get(k)), [], ", ".join(wheres))
        if not os.path.exists(os.path.join(work, lib, "Helper.v")) and any("/Instances/" in p for p in patterns):
            self.sparse(work, cone, [p for p in patterns if "/Instances/" not in p])
            self.assertFalse(os.path.exists(os.path.join(work, lemma)), ", ".join(wheres))
            got = self.rendering(work)
            self.assertIsNotNone(got, ", ".join(wheres))
            self.assertIn(self.HALTS_ROW + "recorded, not yet proved |", got[CHECKSUM + "README.md"], ", ".join(wheres))
        return True

    @staticmethod
    def rendering(root):
        """generate.render_all of the tree at root, or None when `oft generate` refuses the tree before it renders, as
        generate.run does: facts.load, rules.check and rules.symbol_facts give an error, or a proof library of the
        commit is left unwritten (layout.unwritten_libraries)."""
        loaded = facts.load(root)
        rules.check(loaded)
        rules.symbol_facts(loaded)
        if loaded.errors or layout.unwritten_libraries(
                root, sorted("%s/%s" % (h.project.name, h.name) for h in loaded.harnesses())):
            return None
        return generate.render_all(loaded)

    @staticmethod
    def sparse(path, cone, patterns):
        """Make the worktree at path hold what the sparse set patterns holds, in cone mode or not."""
        git(path, "sparse-checkout", "set", "--cone" if cone else "--no-cone", "--skip-checks", "--", *patterns)


class PartialCheckouts(unittest.TestCase):
    """partial_checkouts on a git repository of its own, by the path that the repository's test takes: what it reads,
    what it refuses, and what it leaves out."""
    VALUE_ALONE = 'git sparse-checkout set --no-cone "$PATTERNS"'
    LITERAL = "git -C \"$d\" sparse-checkout set --no-cone '/*' '!/proofs/*/*/lib/*/' \"/projects/$p/\""
    WORKFLOW = "\n".join([
        "on: push",
        "jobs:",
        "  build:",
        "    runs-on: ubuntu-latest",
        "    steps:",
        "      - uses: actions/checkout@v4",
        "        with:",
        "          sparse-checkout: ${{ inputs.paths }}",
        "          sparse-checkout-cone-mode: false",
        "      - run: >-",
        "          git sparse-checkout set --no-cone '/*'",
        "          '!/proofs/*/*/lib/*/'",
        "      - run: |",
        "          git sparse-checkout set --no-cone '/*' \\",
        "            '!/proofs/*/*/lib/*/'",
        ""])

    def test_what_it_reads_refuses_and_leaves_out(self):
        """It reads a script's literal patterns and a `run: |` block; it refuses a pattern of values alone and a line
        of a `run: >-` block, naming the file and the line; it reads no file of a facts tree and no Markdown file."""
        files = {"dev/lane/x.sh": "#!/bin/bash\n%s\n" % self.VALUE_ALONE,
                 "dev/lane/y.sh": "#!/bin/bash\n%s\n" % self.LITERAL,
                 ".github/workflows/w.yml": self.WORKFLOW,
                 "projects/zlib/x.sh": "#!/bin/bash\n%s\n" % self.VALUE_ALONE,
                 "proofs/zlib/y.sh": "#!/bin/bash\n%s\n" % self.LITERAL,
                 "docs/checkouts.md": "Check out a part of the tree with `%s`.\n" % self.VALUE_ALONE}
        with tempfile.TemporaryDirectory(prefix="oft-test-") as root:
            for rel, text in files.items():
                os.makedirs(os.path.join(root, os.path.dirname(rel)), exist_ok=True)
                with open(os.path.join(root, rel), "w", encoding="utf-8") as f:
                    f.write(text)
            git_repo(root)
            read, unread = partial_checkouts(root)
        self.assertEqual([c[0] for c in read + unread if c[0].startswith(("projects/", "proofs/")) or ".md:" in c[0]],
                         [], "a file of a facts tree, or a Markdown file")
        self.assertEqual(unread, [
            (".github/workflows/w.yml: build", ".github/workflows/w.yml", "${{ inputs.paths }}"),
            (".github/workflows/w.yml:11", ".github/workflows/w.yml", "git sparse-checkout set --no-cone '/*'"),
            ("dev/lane/x.sh:2", "dev/lane/x.sh", self.VALUE_ALONE)])
        self.assertEqual(read, [(".github/workflows/w.yml:14", False, ["/*", "!/proofs/*/*/lib/*/"]),
                                ("dev/lane/y.sh:2", False, ["/*", "!/proofs/*/*/lib/*/", "/projects/*/"])])


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
        self.assertEqual(st.shape_name(), "agrees")

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
                shapes.term(st, {"budgets": {"agrees": {"undefined": pair}}}, distribution=False)
            self.assertIn(words, str(e.exception))
        with self.assertRaises(shapes.ShapeError) as e:
            shapes.term(st, {"budgets": {"agrees": {"address": ["1GiB", "1TiB"]}}},   # no pair for ubsan and no enum
                        distribution=False)
        self.assertIn("an agreement statement names its budgets", str(e.exception))
        with self.assertRaises(shapes.ShapeError) as e:
            shapes.term(dict(st, budgets="standard"), {"budgets": {"agrees": {"undefined": ["2GiB", "5TiB"]}}},
                        distribution=False)
        self.assertIn("sets this statement's budgets, so it names none", str(e.exception))

    def test_a_pair_equal_to_the_default_is_the_enum(self):
        st = {"kind": "agreement", "builds": ["plain", "ubsan"], "reading": "alloc-forced-only"}
        enum = shapes.term(dict(st, budgets="standard"), distribution=False)
        for pb in ({"budgets": {"agrees": {"undefined": ["16GiB", "512GiB"]}}},
                   {"budgets": {"agrees": {"undefined": ["16384MiB", "512GiB"]}}}):
            self.assertEqual(shapes.term(st, pb, distribution=False), enum)
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
        self.assertEqual(shapes.term(st, pb, distribution=False)[1],
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
                  [symbols.Sym(n, k, a, s, "1f" * 32, "2e" * 32 if k == "func" else "-", "-", "-")
                   for n, k, a, s in rows],
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
                                       [symbols.Sym(n, k, a, s, "-", "-", "-", "-") for n, k, a, s in rows])

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
                    "index/x/statements.tsv", "docs/statements.md", "tools/publish/private-harnesses.txt"):
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


class PrivateHarnessesFile(unittest.TestCase):
    """tools/publish/private-harnesses.txt (generate.PRIVATE_HARNESSES; K10 of Dispatch issue OSSV-424): each name of
    each project's private_harnesses as one `<project>/<harness>` line, the lines sorted, each ended by a newline, and
    no byte when nothing is held.  Only a tree that has tools/publish/ gets the file.  `--check`, with --skip-shared
    too, refuses a tree whose file is missing or gives another list."""

    FILE = generate.PRIVATE_HARNESSES

    def hold(self, t, **fields):
        """Give each project of FIELDS its private_harnesses."""
        for project, field in fields.items():
            rel = "projects/%s/project.yaml" % project
            t.put_yaml(rel, dict(t.yaml(rel), private_harnesses=field))

    def check(self, t, shared=None):
        buf = io.StringIO()
        rc = generate.run(t.root, check=True, out=buf, shared=shared)
        return rc, buf.getvalue()

    def rendered(self, t):
        self.assertEqual(t.generate(), 0, t.last_output)
        with open(t.path(self.FILE), "rb") as f:
            return f.read()

    def test_a_tree_without_tools_publish_gets_no_file(self):
        with tree() as t:
            self.hold(t, zlib=["held_target"])
            self.assertNotIn(self.FILE, generate.render_all(facts.load(t.root)))
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertFalse(os.path.lexists(t.path("tools")))
            self.assertEqual(t.generate(check=True), 0, t.last_output)

    def test_the_file_is_empty_when_nothing_is_held(self):
        with tree() as t:
            os.makedirs(t.path("tools", "publish"))
            self.assertEqual(self.rendered(t), b"")
            self.assertEqual(self.check(t, shared=False)[0], 0)
            t.write(self.FILE, "zlib/held_target\n")
            rc, out = self.check(t, shared=False)
            self.assertEqual(rc, 1, out)
            self.assertIn(self.FILE + ": differs from its rendering", out)

    def test_two_held_harnesses_of_two_projects_render_two_sorted_lines(self):
        with tree() as t:
            os.makedirs(t.path("tools", "publish"))
            self.hold(t, zlib=["minigzip_fuzzer"], json=["fuzzer-parse_bjdata"])
            self.assertEqual(self.rendered(t), b"json/fuzzer-parse_bjdata\nzlib/minigzip_fuzzer\n")
            # the negative control: a file that matches its fields passes --check, with --skip-shared too
            for shared in (None, False):
                rc, out = self.check(t, shared)
                self.assertEqual(rc, 0, out)
            # each project's names are sorted too, whatever the order of its field
            self.hold(t, zlib=["minigzip_fuzzer", "held_target"])
            self.assertEqual(self.rendered(t),
                             b"json/fuzzer-parse_bjdata\nzlib/held_target\nzlib/minigzip_fuzzer\n")

    def test_check_refuses_a_file_that_lacks_a_line_has_one_more_or_is_missing(self):
        with tree() as t:
            os.makedirs(t.path("tools", "publish"))
            self.hold(t, zlib=["minigzip_fuzzer"], json=["fuzzer-parse_bjdata"])
            good = self.rendered(t).decode()
            for case, text in (("lacks a line", "json/fuzzer-parse_bjdata\n"),
                               ("has one more", good + "zlib/held_target\n"), ("is missing", None)):
                with self.subTest(case=case):
                    if text is None:
                        os.remove(t.path(self.FILE))
                    else:
                        t.write(self.FILE, text)
                    said = "missing" if text is None else "differs from its rendering"
                    for shared in (None, False):
                        rc, out = self.check(t, shared)
                        self.assertEqual(rc, 1, out)
                        self.assertIn("%s: %s" % (self.FILE, said), out)
                    # no shared file: the line's render, which writes the shared files alone, leaves it to the pull
                    # request
                    rc, out = self.check(t, shared=True)
                    self.assertEqual(rc, 0, out)
                    t.write(self.FILE, good)

    def test_the_port_form_none_reads_as_the_internal_copy(self):
        """The cut writes `none` as the port of a project with a held fuzz target whose port is the internal copy, so
        the release's page says what the internal page says.  The public port keeps its name."""
        words = generate._port_repository_words
        self.assertEqual(words({"repository": "none"}), "the internal copy of the OSS Verify port")
        self.assertEqual(words({"repository": schema.INTERNAL_PORT_REPOSITORY}), words({"repository": "none"}))
        self.assertEqual(words({"repository": schema.OSS_VERIFY_REPOSITORY}), "`theorem-labs/oss-verify`")


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


class ClaimsFollowDeclarations(unittest.TestCase):
    """A sentence a page writes says only what the declaration it comes from supports."""

    # the sentence a harness with no check of its own gives for each kind of its statements, in the order given
    NO_CHECK = (("halts", "Its halts statements say only that the code it calls never crashes, hangs or trips a "
                          "sanitizer."),
                ("agreement", "Its agreement statements say only that the code never crashes or trips a sanitizer, "
                              "and allow a run that never ends."),
                ("bound", "Its bound statements say only how often its builds may disagree."),
                ("decidability", "Its decidability statements say only that some program decides where its builds "
                                 "agree."))
    NOTHING = "No statement here says anything about the code it calls."
    # the one sentence of the four classifier kinds, after the others
    CLASSIFIER = "Its classifier statements say only how the classifier programs of its pairs answer."

    def no_check_pages(self, kinds):
        """The harness README and Statements.v of the fixture's checksum_fuzzer, each with its whitespace runs made
        one space, rendered once, after its checks are removed and each of its statements of a kind not in KINDS is
        withdrawn."""
        p = "projects/zlib/checksum_fuzzer/harness.yaml"
        with tree(render=False) as t:
            y = t.yaml(p)
            y["checks"] = []
            for st in y["statements"].values():
                st.pop("binds_checks", None)
                if st["kind"] not in kinds:
                    st.pop("witness", None)
                    st.update(status="withdrawn", reason="Withdrawn for this test.")
            t.put_yaml(p, y)
            self.assertEqual(t.generate(), 0, t.last_output)
            return [" ".join(t.read("projects/zlib/checksum_fuzzer/" + f).split())
                    for f in ("README.md", "Statements.v")]

    def assert_says_only(self, pages, sentences):
        """Each page says that the harness makes no check and then exactly SENTENCES, none of the other kinds' and
        none of the old forms."""
        for page in pages:
            self.assertIn("makes no check of its own beyond not crashing. " + " ".join(sentences), page)
            for _kind, other in self.NO_CHECK + ((None, self.NOTHING),):
                if other not in sentences:
                    self.assertNotIn(other, page)
            self.assertNotIn("a statement about it says only", page)
            for kind, _sentence in self.NO_CHECK:
                self.assertNotIn("; its %s statements" % kind, page)

    def test_a_harness_with_no_check_says_what_each_kind_of_its_statements_says(self):
        """Only a halts statement rules out a run that never ends: an agreement statement allows one, and a bound or a
        decidability statement says nothing of one run.  Each kind among the statements has a sentence of its own."""
        self.assert_says_only(self.no_check_pages({k for k, _ in self.NO_CHECK}), [s for _, s in self.NO_CHECK])
        with tree() as t:     # the fixture's api-driver has no check and agreement statements only
            agrees_only = " ".join(t.read("projects/zlib/api-driver/README.md").split())
        self.assert_says_only([agrees_only], [dict(self.NO_CHECK)["agreement"]])

    def test_each_kind_alone_gets_only_its_own_sentence(self):
        for kind, sentence in self.NO_CHECK:
            with self.subTest(kind=kind):
                self.assert_says_only(self.no_check_pages({kind}), [sentence])

    def test_a_harness_with_no_live_statement_says_none_says_anything(self):
        self.assert_says_only(self.no_check_pages(set()), [self.NOTHING])

    def test_the_classifier_statements_have_one_sentence_after_the_others(self):
        """The four classifier kinds share one sentence, after the decidability statements', as _order gives the
        kinds; a harness whose live statements are classifier statements says that sentence alone."""
        def no_check(y):
            y["checks"] = []
            for st in y["statements"].values():
                st.pop("binds_checks", None)

        def classifier_only(y):
            no_check(y)
            for st in y["statements"].values():
                if st["kind"] not in shapes.CLASSIFIER_KINDS:
                    st.pop("witness", None)
                    st.update(status="withdrawn", reason="Withdrawn for this test.")
        unit = "projects/zlib/checksum_fuzzer/"
        for change, sentences in ((no_check, [s for _, s in self.NO_CHECK] + [self.CLASSIFIER]),
                                  (classifier_only, [self.CLASSIFIER])):
            with self.subTest(change=change.__name__), tree(render=False) as t:
                ci.with_images(t, change)
                h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
                self.assertEqual(generate._no_check_claim(h), " ".join(sentences))
                self.assertEqual(t.generate(), 0, t.last_output)
                self.assert_says_only([" ".join(t.read(unit + f).split()) for f in ("README.md", "Statements.v")],
                                      sentences)

    def test_the_main_page_counts_the_statements_known_false(self):
        """It says some are known false only when the count beside it says so."""
        with tree() as t:
            n_false = sum(1 for s in facts.load(t.root).statements()
                          if s.status in ("refuted", "counterexample", "witnessed-false"))
            self.assertGreater(n_false, 0)
            self.assertIn("%d are known to be false" % n_false if n_false > 1 else "1 is known to be false",
                          t.read("README.md"))
            y = t.yaml("projects/zlib/checksum_fuzzer/harness.yaml")
            st = y["statements"]["ubsan_halts_may_fail"]
            del st["witness"]
            st["status"] = "open"
            t.put_yaml("projects/zlib/checksum_fuzzer/harness.yaml", y)
            shutil.rmtree(t.path("counterexamples"))
            self.assertEqual(t.generate(), 0, t.last_output)
            readme = t.read("README.md")
        self.assertIn("none is known to be false", readme)
        self.assertIn("0 known false", readme)
        self.assertNotIn("some are known to be false", readme)

    def test_unlisted_patches_are_placed_where_the_release_has_them(self):
        """A recipe-built project that attaches its source has its unlisted patches in that recipe; one that does
        not attach its source (the fixture's json: a recipe and no source archive, as mosquitto is) says that no
        published archive holds them.  Neither page says they ship in a source bundle."""
        with tree() as t:
            z = t.yaml("projects/zlib/project.yaml")
            del z["withheld"]
            z["library"]["patch_count"] = 3
            t.put_yaml("projects/zlib/project.yaml", z)
            j = t.yaml("projects/json/project.yaml")
            j["library"]["patch_count"] = 1
            t.put_yaml("projects/json/project.yaml", j)
            self.assertEqual(t.generate(), 0, t.last_output)
            zlib, json = t.read("projects/zlib/README.md"), t.read("projects/json/README.md")
        self.assertIn("  - 2 patches more, whose text is not in this repository: it is in `recipe.tar.zst` in release "
                      "[v2026.11.0](https://github.com/theorem-labs/oss-verify-proofs/releases/tag/v2026.11.0), under "
                      "`patches/`, in the order `patches/series.tsv` gives", zlib)
        self.assertIn("  - 1 patch, whose text is not in this repository, and no published archive holds it\n", json)
        for page in (zlib, json):
            self.assertNotIn("whose text is not in this release yet", page)
            self.assertNotIn("source bundle", page)
