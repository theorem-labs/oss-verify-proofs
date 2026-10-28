"""The hold: a project a finding holds back ships only as held, an enrolled project's open finding holds back only the
statements it breaks (facts.hold), and no file the cut keeps carries what is held back (disclosure)."""
import csv
import os
import shutil
import tempfile
import unittest

from oft import disclosure, facts, generate, schema
from oft.rules import counts as rules_counts
from oft.tests.helpers import (HELD_PATCH, HELD_PAYLOAD, Tree, add_findings, build_record, folded, patch_copies,
                               recount, tree)
from oft.tests.test_oss_verify import PORT, PORT_ASSET
from oft.tests.test_release_tree import (APPROVED, PACKAGE, RELEASED, UNAPPROVED, add_proof, approve, entry,
                                         index_status, make_private, release, snapshot, write_approvals)

FINDING = "findings/zlib/checksum_fuzzer/stand-in-abort"
SLUG, PATCH = "stand-in-abort", "0001-stand-in.patch"
# the encodings the shipped-text search reads a file's bytes in (disclosure.canonical), without a byte order mark
ENCODINGS = ("utf-8", "utf-16-le", "utf-16-be", "utf-32-le", "utf-32-be")
UNPATCHED = "findings/zlib/unpatched.yaml"
# the driver's header of every input of these tests: no config, so the harness is called once
HEADER = b"\0" * 6


def files_under(t, *tops):
    """{path: bytes} of every file under the given top-level paths of the checkout."""
    return {p: b for p, b in snapshot(t).items() if p.startswith(tuple(top + os.sep for top in tops))}


def add_asan_halts_counterexample(t):
    """A public counterexample of the approved fuzz target's asan_halts: the asan build aborts, the control is normal."""
    cx = "counterexamples/%s/asan_halts" % APPROVED
    t.put_yaml(cx + "/expect.yaml", {
        "schema": "oss-fuzz-theorems/counterexample/1", "statement": APPROVED + "/asan_halts",
        "input": "input.bin", "observed": {"build": "asan", "exit": 134, "signal": "SIGABRT"},
        "control": {"input": "control.bin", "exit": 0}, "disclosure": "public",
        "note": "A stand-in counterexample for these tests."})
    t.write(cx + "/input.bin", "x")
    t.write(cx + "/control.bin", "y")


def align_unpatched_pins(t, project="zlib"):
    """Pin the project's published binaries to the ones its findings run on: an enrolled project with an open finding
    publishes no patched build, so the statement hold applies (facts.hold)."""
    u = t.yaml(UNPATCHED)
    for harness, pins in u["harnesses"].items():
        for b, rec in t.yaml("projects/%s/%s/harness.yaml" % (project, harness))["builds"].items():
            pins[b].update(bytes=rec["bytes"], sha256=rec["sha256"])
    t.put_yaml(UNPATCHED, u)


def hold(t):
    return facts.hold(facts.load(t.root))


class Hold(unittest.TestCase):
    def test_a_finding_that_is_not_public_pruned_or_not_a_defect_holds_its_project_whole(self):
        with tree(render=False) as t:
            add_findings(t)
            rel = FINDING + "/finding.yaml"
            for state, held in (("open", True), ("patched", True), ("reported", True), ("public", False),
                                ("pruned", False), ("not-a-defect", False)):
                t.put_yaml(rel, dict(t.yaml(rel), state=state))
                self.assertEqual(hold(t), facts.Hold({"zlib"} if held else set(), set(), {}), state)

    def test_a_private_project_is_held_whole_and_never_by_statement(self):
        with tree(render=False) as t:
            make_private(t, "json")
            self.assertEqual(hold(t), facts.Hold(set(), {"json"}, {}))
            self.assertEqual(hold(t).whole, {"json"})


class HeldFixture:
    """Two projects: zlib, with a reported finding, and json, whose proof the release publishes.  The finding's patch
    and input are shaped like a real finding's (helpers.HELD_PATCH, HELD_PAYLOAD)."""

    def setUp(self):
        self.t = Tree()
        self.addCleanup(self.t.close)
        add_findings(self.t)
        self.set_state("reported", upstream="https://bugs.example.org/1")
        self.t.write(FINDING + "/" + PATCH, HELD_PATCH)
        self.t.write(FINDING + "/input.bin", HEADER + HELD_PAYLOAD.encode(), mode="wb")
        shutil.rmtree(self.t.path("counterexamples", "json"))
        add_proof(self.t, RELEASED + "/plain_halts")
        add_proof(self.t, APPROVED + "/plain_halts")
        add_proof(self.t, UNAPPROVED + "/ubsan_agrees")
        self.t.write("proofs/%s/lib/Shared.v" % APPROVED, "Definition one := 1.\n")
        self.t.write("proofs/%s/provenance/PROVENANCE.md" % APPROVED, "The build record.\n")
        self.t.write("proofs/%s/provenance/PROVENANCE.md" % RELEASED, "The build record.\n")
        add_asan_halts_counterexample(self.t)
        self.assertTrue(os.path.isfile(self.t.path("notes", "zlib.md")))
        approve(self.t, RELEASED)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)

    def restart(self):
        self.doCleanups()
        self.setUp()

    def set_state(self, state, **kw):
        y = self.t.yaml(FINDING + "/finding.yaml")
        y.update(state=state, **kw)
        self.t.put_yaml(FINDING + "/finding.yaml", y)

    def release(self):
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        return out

    def assertRefused(self, why):
        before = snapshot(self.t)
        rc, out = release(self.t)
        self.assertEqual(rc, 1, out)
        self.assertIn(why, out)
        self.assertEqual(snapshot(self.t), before)

    def hunk(self, k=1):
        """The label of the added side of hunk k of the held patch, as a refusal names it."""
        return "added lines of hunk %d of %s/%s" % (k, FINDING, PATCH)


class HeldBack(HeldFixture, unittest.TestCase):
    """A project with a finding that is open, patched or reported ships only as held."""

    def test_the_held_project_ships_only_its_held_project_yaml_and_its_readme(self):
        out = self.release()
        self.assertIn("held back by a finding that is not public: zlib", out)
        self.assertEqual(self.t.yaml("projects/zlib/project.yaml"), {
            "schema": "oss-fuzz-theorems/project/1", "project": "zlib", "homepage": "https://www.zlib.net/",
            "language": "c++", "oss_fuzz": {"path": "projects/zlib", "commit": "bd2ce21991a94a362b92fb1bf25f86d5a1a60842"},
            "status": "held", "reason": "held"})
        self.assertEqual(sorted(os.listdir(self.t.path("projects", "zlib"))), ["README.md", "project.yaml"])
        self.assertIn("Held from this release.", self.t.read("projects/zlib/README.md"))

    def test_every_other_path_of_the_held_project_is_gone(self):
        self.t.write("patches/zlib/" + PATCH, "A stand-in patch.\n")
        self.release()
        for rel in ("proofs/zlib", "counterexamples/zlib", "patches/zlib", "notes/zlib.md"):
            self.assertFalse(os.path.lexists(self.t.path(rel)), rel)

    def test_the_counts_are_recomputed_and_the_cut_passes_generate_check_and_lint(self):
        out = self.release()
        self.assertEqual(self.t.yaml("release.yaml")["counts"],
                         {"projects": 5, "available": 1, "harnesses": 1, "binaries": 4})
        self.assertEqual(self.t.generate(check=True), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        self.assertIn("the cut's statements, for its CHANGELOG.md section: %s\n"
                      % generate.counts_sentence(facts.load(self.t.root)), out)

    def test_releasing_a_hold_needs_no_release_yaml_change(self):
        """The tree's counts describe the tree, held project and all, and the cut writes the release's: a state change
        that releases the hold leaves release.yaml valid as it is."""
        self.assertEqual(self.t.yaml("release.yaml")["counts"], rules_counts(facts.load(self.t.root)))
        self.assertEqual([str(f) for f in self.t.lint()], [])
        self.set_state("public")
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_the_held_project_keeps_its_row_in_the_index_and_has_no_other_rows(self):
        self.release()
        rows = {}
        for name in ("projects", "harnesses", "statements", "binaries"):
            with open(self.t.path("index", name + ".tsv"), newline="") as f:
                rows[name] = list(csv.DictReader(f, delimiter="\t"))
        zlib = [r for r in rows["projects"] if r["project"] == "zlib"]
        self.assertEqual([(r["status"], r["reason"]) for r in zlib], [("held", "held")])
        self.assertEqual([r for r in rows["harnesses"] + rows["binaries"] if r["project"] == "zlib"], [])
        self.assertEqual([r for r in rows["statements"] if r["id"].startswith("zlib/")], [])
        self.assertIn("| [zlib](../projects/zlib/) | c++ | held |", self.t.read("index/STATUS.md"))

    def test_oft_approvals_omits_a_held_fuzz_target_and_says_so(self):
        os.remove(self.t.path("approvals.yaml"))
        rc, out = write_approvals(self.t, "%s\n%s\n" % (APPROVED, RELEASED))
        self.assertEqual(rc, 0, out)
        self.assertIn("held by a finding that is not public: %s\n" % APPROVED, out)
        self.assertEqual([e["fuzz_target"] for e in self.t.yaml("approvals.yaml")["fuzz_targets"]], [RELEASED])

    def test_a_private_project_oss_fuzz_has_that_a_finding_holds_gets_the_held_page(self):
        """b73257f8: a private project OSS-Fuzz has keeps its held page, finding or not."""
        make_private(self.t, "zlib")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.release()
        self.assertEqual(sorted(os.listdir(self.t.path("projects", "zlib"))), ["README.md", "project.yaml"])
        self.assertEqual(self.t.yaml("projects/zlib/project.yaml")["status"], "held")
        for gone in ("proofs/zlib", "counterexamples/zlib", "notes/zlib.md", "findings"):
            self.assertFalse(os.path.lexists(self.t.path(gone)), gone)
        self.assertEqual(self.t.generate(check=True), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def without_oss_fuzz(self):
        """zlib as a port-built project OSS-Fuzz does not have (no oss_fuzz), with its one harness, and release.yaml's
        counts as this tree has them."""
        rel = "projects/zlib/project.yaml"
        y = self.t.yaml(rel)
        del y["oss_fuzz"]
        y["harnesses"] = [dict(e, origin="oss-verify") for e in y["harnesses"] if e["name"] == "checksum_fuzzer"]
        y["build"]["oss_verify"] = dict(PORT, path="projects/zlib")
        y["assets"]["bin"].pop("recipe", None)   # the port built the archive, and no recipe
        y["assets"]["port"] = dict(PORT_ASSET, file="zlib-port.tar.zst")
        self.t.put_yaml(rel, y)
        hrel = "projects/%s/harness.yaml" % APPROVED
        self.t.put_yaml(hrel, dict(self.t.yaml(hrel), origin="oss-verify"))
        shutil.rmtree(self.t.path("projects", UNAPPROVED))
        shutil.rmtree(self.t.path("proofs", UNAPPROVED))
        u = self.t.yaml(UNPATCHED)
        del u["harnesses"]["api-driver"]
        self.t.put_yaml(UNPATCHED, u)
        recount(self.t)

    def assertZlibGone(self):
        for gone in ("projects/zlib", "proofs/zlib", "counterexamples/zlib", "notes/zlib.md", "findings"):
            self.assertFalse(os.path.lexists(self.t.path(gone)), gone)
        self.assertNotIn("zlib", self.t.read("index/projects.tsv"))
        self.assertEqual(self.t.yaml("release.yaml")["counts"], rules_counts(facts.load(self.t.root)))
        self.assertEqual(self.t.generate(check=True), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_a_private_project_oss_fuzz_lacks_that_a_finding_holds_is_removed_whole(self):
        self.without_oss_fuzz()
        make_private(self.t, "zlib")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.release()
        self.assertZlibGone()

    def test_a_project_a_finding_holds_that_oss_fuzz_lacks_is_removed_whole(self):
        """A held page for a seeded project that was never released would tell the reader a finding exists."""
        self.without_oss_fuzz()
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.assertEqual(hold(self.t).held, {"zlib"})
        out = self.release()
        self.assertNotIn("held back by an open finding", out)
        self.assertZlibGone()

    def test_what_only_the_held_project_needed_leaves_release_yaml(self):
        """An image_libraries entry that only the held project's builds link goes; release.yaml sets no size limit on
        plain binaries, so there is no admitted_above_limit list to cut."""
        def link(rel, lib):
            y = self.t.yaml(rel)
            for b in y["builds"].values():
                b["uninstrumented"] = [{"name": lib, "kind": "image-library"}]
            self.t.put_yaml(rel, y)
        link("projects/%s/harness.yaml" % APPROVED, "libgmp.a")
        link("projects/%s/harness.yaml" % RELEASED, "libyaml.a")
        r = self.t.yaml("release.yaml")
        r["image_libraries"] = {n: {"library": n, "licence": "MIT", "copyleft": False, "in_sysroot_src": True}
                                for n in ("libgmp.a", "libyaml.a")}
        self.t.put_yaml("release.yaml", r)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.release()
        r = self.t.yaml("release.yaml")
        self.assertEqual(list(r["image_libraries"]), ["libyaml.a"])
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_a_symbolic_link_at_an_ignored_path_the_cut_removes_is_refused_before_any_change(self):
        """internal #80's final review at 320061f9f6, finding 3: checkout_links reads no ignored path, and the cut
        removes projects/zlib/bin/ and projects/zlib/_build/ from the held page it keeps; a link there stopped rmtree
        after proofs/zlib was gone.  The cut refuses it before its first change, and leaves its target alone."""
        outside = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, outside)
        with open(os.path.join(outside, "kept"), "w") as f:
            f.write("kept\n")
        for rel in ("projects/zlib/bin", "projects/zlib/_build"):
            with self.subTest(rel=rel):
                if os.path.lexists(self.t.path(rel)):
                    shutil.rmtree(self.t.path(rel))
                os.symlink(outside, self.t.path(rel))
                self.assertRefused("error: %s: a symbolic link, which the cut could follow out of the checkout" % rel)
                self.assertTrue(os.path.isdir(self.t.path("proofs", "zlib")))
                self.assertEqual(os.listdir(outside), ["kept"])
                os.remove(self.t.path(rel))
        self.release()

    def test_no_shipped_text_names_a_held_finding(self):
        self.release()
        for rel, data in snapshot(self.t).items():
            for name in (SLUG, PATCH):
                self.assertNotIn(name, rel)
                self.assertNotIn(name.encode(), data, rel)

    def test_a_shipped_text_that_names_a_held_finding_is_refused_and_changes_nothing(self):
        for rel, text, why in (
                ("CHANGELOG.md", "Fixed the %s bug.\n" % SLUG.upper(), "%s, the slug of finding %s" % (SLUG, FINDING)),
                ("docs/notes.md", PATCH + "\n", "%s, a patch file name of finding %s" % (PATCH, FINDING))):
            with self.subTest(rel=rel):
                self.restart()
                self.t.write(rel, text)
                self.assertRefused("error: %s names %s" % (rel, why))

    def test_a_copy_of_the_patch_with_its_headers_changed_is_refused_wherever_it_ships(self):
        """#117's code-quality review, finding 1: a copy of the patch with `diff -u` header timestamps, or with another
        path prefix, in a document, in the build record of a fuzz target the release recipe built, and in the record of
        a port-built one written as UTF-32."""
        copies = patch_copies(HELD_PATCH)
        record = "proofs/%s/provenance/PROVENANCE.md" % RELEASED
        for rel, port_built, enc in (("docs/repair.md", False, None), (record, False, None),
                                     (record, True, "utf-32-le")):
            for how in ("header timestamps", "another path prefix"):
                with self.subTest(rel=rel, port_built=port_built, how=how):
                    self.restart()
                    if port_built:
                        port_build(self.t, "json")
                    data = copies[how]
                    self.t.write(rel, data.decode().encode(enc) if enc else data, mode="wb")
                    self.assertRefused("error: %s names %s" % (rel, self.hunk(2)))

    def test_a_hunk_of_the_patch_in_the_notes_of_a_project_the_release_keeps_is_refused(self):
        stamped = patch_copies(HELD_PATCH)["header timestamps"].decode()
        self.t.write("notes/json.md", "How zlib was fixed:\n\n" + stamped)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.assertRefused("error: notes/json.md names %s" % self.hunk(1))

    def test_a_hunk_of_the_patch_in_the_changelog_is_refused(self):
        self.t.write("CHANGELOG.md", "## 2026.11.0\n\n- crc32:\n\n" + "".join(
            "      " + line for line in patch_copies(HELD_PATCH)["only the hunks"].decode().splitlines(True)))
        self.assertRefused("error: CHANGELOG.md names %s" % self.hunk(1))

    def test_the_summary_folded_over_lines_is_refused(self):
        summary = self.t.yaml(FINDING + "/finding.yaml")["summary"]
        self.t.write("CHANGELOG.md", "## 2026.11.0\n\n- " + folded(summary, 60, "  ").lstrip())
        self.assertRefused("error: CHANGELOG.md names the summary of finding " + FINDING)

    def test_the_input_without_its_header_is_refused(self):
        self.t.write("docs/notes.md", "The input:\n\n```make\n%s```\n" % HELD_PAYLOAD)
        self.assertRefused("error: docs/notes.md names the payload of %s/input.bin" % FINDING)

    def test_a_byte_copy_of_the_input_is_refused(self):
        with open(self.t.path(FINDING, "input.bin"), "rb") as f:
            self.t.write("docs/repro.bin", f.read(), mode="wb")
        self.assertRefused("error: docs/repro.bin names the bytes of %s/input.bin" % FINDING)

    def test_a_link_out_of_the_checkout_at_a_build_record_is_refused_and_never_read(self):
        """#117's deep review, finding 3: a build record that is a link to a directory outside the checkout."""
        outside = tempfile.mkdtemp(prefix="oft-outside-")
        self.addCleanup(shutil.rmtree, outside)
        with open(os.path.join(outside, "elsewhere.txt"), "wb") as f:
            f.write(patch_copies(HELD_PATCH)["header timestamps"])
        record = "proofs/%s/provenance" % RELEASED
        shutil.rmtree(self.t.path(record))
        os.symlink(outside, self.t.path(record))
        self.assertRefused("error: %s: a symbolic link" % record)
        loaded = facts.load(self.t.root)
        hits = disclosure.search(self.t.root, disclosure.needles(loaded, facts.hold(loaded)), skip=(), writes={})
        self.assertEqual([h for h in hits if h[0].startswith(record)], [])

    def test_a_reference_that_is_no_character_is_read_and_ships(self):
        """Ordinary text the decoder cannot turn into a character is no error: it is read, and nothing held is in it."""
        self.t.write("docs/notes.md", "A replacement: &#x110000; &#99999999999999999999; %zz %4\n")
        self.release()
        self.assertTrue(os.path.isfile(self.t.path("docs", "notes.md")))

    def test_a_held_page_the_cut_renders_is_searched_as_well(self):
        """held_form keeps the project's homepage, and the cut renders the held page from it: the slug in a field the
        held page carries would ship, though the file it is written in is rewritten."""
        rel = "projects/zlib/project.yaml"
        self.t.put_yaml(rel, dict(self.t.yaml(rel), homepage="https://www.zlib.net/%s" % SLUG))
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.assertRefused("error: projects/zlib/README.md names %s, the slug of finding" % SLUG)

    def test_the_empty_output_digest_ships(self):
        """Every finding record holds the SHA-256 of empty output, and so do this repository's own tools: it reveals
        nothing, so a kept file that holds it ships."""
        self.t.write("tools/oft/sample.py", "EMPTY = %r\n" % disclosure.EMPTY_SHA256)
        self.release()
        self.assertTrue(os.path.isfile(self.t.path("tools", "oft", "sample.py")))

    def test_the_log_names_a_held_project_the_cut_removes_whole(self):
        """A finding that holds a project OSS-Fuzz lacks removes it whole; the log still says why."""
        self.without_oss_fuzz()
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.assertIn("held back by a finding that is not public: zlib\n", self.release())

    def test_a_symbolic_link_at_a_file_the_cut_rewrites_is_refused(self):
        """The cut writes a held project's project.yaml and README.md, and release.yaml: a link there would carry the
        write out of the checkout."""
        for rel in ("projects/zlib/project.yaml", "projects/zlib/README.md", "release.yaml"):
            with self.subTest(rel=rel):
                self.restart()
                outside = self.t.path("..", "outside-" + os.path.basename(rel))
                os.rename(self.t.path(rel), outside)
                os.symlink(outside, self.t.path(rel))
                self.assertRefused("error: %s: a symbolic link" % rel)

    def test_a_symbolic_link_on_the_way_to_a_held_path_is_refused(self):
        os.rename(self.t.path("counterexamples"), self.t.path("..", "other-counterexamples"))
        os.symlink(os.path.join("..", "other-counterexamples"), self.t.path("counterexamples"))
        self.assertRefused("counterexamples: a symbolic link")

    def test_the_other_project_is_unchanged(self):
        before = files_under(self.t, "projects/json", "proofs/json")
        self.release()
        self.assertEqual(files_under(self.t, "projects/json", "proofs/json"), before)

    def assertHoldsNothing(self):
        approve(self.t, RELEASED, APPROVED, entry(UNAPPROVED, statements=["ubsan_agrees"]))
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        kept = ("projects/zlib", "proofs/zlib", "counterexamples/zlib", "patches/zlib", "notes")
        before = files_under(self.t, *kept)
        out = self.release()
        self.assertNotIn("held back", out)
        self.assertEqual(files_under(self.t, *kept), before)
        self.assertFalse(os.path.lexists(self.t.path("findings")))

    def test_a_public_finding_holds_back_nothing(self):
        self.set_state("public")
        self.assertHoldsNothing()

    def test_a_pruned_finding_holds_back_nothing(self):
        self.set_state("pruned")
        self.t.write("findings/zlib/checksum_fuzzer/series", "")
        y = self.t.yaml(FINDING + "/finding.yaml")
        y["input"] = dict(y["control"])
        self.t.put_yaml(FINDING + "/finding.yaml", y)
        self.assertHoldsNothing()

    def test_a_not_a_defect_finding_holds_back_nothing(self):
        self.set_state("not-a-defect")
        self.t.write("findings/zlib/checksum_fuzzer/series", "")
        h = self.t.yaml("projects/%s/harness.yaml" % APPROVED)
        for s in ("asan_agrees", "asan_ubsan_agrees"):
            h["statements"][s].update(status="suspected-false", basis="reading",
                                      reason="A stand-in reason for these tests.")
        self.t.put_yaml("projects/%s/harness.yaml" % APPROVED, h)
        self.assertHoldsNothing()


def port_build(t, project):
    """project's binaries built by the OSS Verify port, not the release recipe."""
    rel = "projects/%s/project.yaml" % project
    y = t.yaml(rel)
    y["build"]["oss_verify"] = dict(PORT, path="projects/" + project)
    y["assets"]["bin"].pop("recipe", None)   # the port built the archive, and no recipe
    y["assets"]["port"] = dict(PORT_ASSET, file=project + "-port.tar.zst")
    y["assets"]["src"] = {"release": "v2026.11.0", "file": project + "-src.tar.zst", "bytes": 9000000,
                          "sha256": "5d" * 32}
    y["assets"]["src_manifest"] = {"release": "v2026.11.0", "file": project + "-src.MANIFEST.tsv", "bytes": 4000,
                                   "sha256": "5e" * 32}
    t.put_yaml(rel, y)
    assert t.generate() == 0, t.last_output


HELD_STATEMENTS = ("asan_agrees",)
# asan_agrees's pair's bound and decidability statements go with it (rules.py), so they are held too
HELD_WITH_PAIR = HELD_STATEMENTS + ("asan_disagrees_at_most", "asan_agreement_decidable")


class EnrolledHold(HeldFixture, unittest.TestCase):
    """An enrolled project whose unpublished findings are all open holds back only the statements they name."""

    def setUp(self):
        super().setUp()
        rel = "projects/zlib/project.yaml"
        self.t.put_yaml(rel, dict(self.t.yaml(rel), enrolled=True))
        shutil.rmtree(self.t.path("counterexamples", APPROVED, "asan_halts"))
        # a statement hold never keeps a shared proof library (see the test of it below)
        shutil.rmtree(self.t.path("proofs", APPROVED, "lib"))
        y = self.t.yaml(FINDING + "/finding.yaml")
        normal = y["control"]["plain"]
        different = dict(normal, stdout_sha256="c0595f8938f4c1b33f96d71df39e76f1dc58784e820217db6dbc0797eeecde70")
        y.update(state="open", statements=list(HELD_STATEMENTS),
                 input={"plain": dict(normal), "asan": different},
                 control={"plain": dict(normal), "asan": dict(normal)})
        self.t.put_yaml(FINDING + "/finding.yaml", y)
        self.t.write("findings/zlib/checksum_fuzzer/series", "")
        align_unpatched_pins(self.t)
        add_proof(self.t, APPROVED + "/ubsan_agrees")
        add_proof(self.t, APPROVED + "/asan_agrees")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.assertEqual(hold(self.t),
                         facts.Hold(set(), set(), {"zlib": {"checksum_fuzzer/" + s for s in HELD_WITH_PAIR}}))

    def assertHeldWhole(self):
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.assertEqual(hold(self.t), facts.Hold({"zlib"}, set(), {}))

    def test_a_project_that_is_not_enrolled_is_held_whole(self):
        """A seeded project publishes no statement of a project with an open finding: only enrollment holds per
        statement."""
        rel = "projects/zlib/project.yaml"
        y = self.t.yaml(rel)
        del y["enrolled"]
        self.t.put_yaml(rel, y)
        self.assertHeldWhole()

    def test_only_the_statements_the_open_finding_names_are_cut(self):
        approve(self.t, RELEASED, entry(APPROVED, statements=["plain_halts", "ubsan_agrees"]),
                entry(UNAPPROVED, statements=["ubsan_agrees"]))
        out = self.release()
        for s in HELD_WITH_PAIR:
            self.assertIn("held back by an open finding: %s/%s\n" % (APPROVED, s), out)
        self.assertEqual(self.t.yaml("projects/zlib/project.yaml")["status"], "available")
        self.assertEqual(sorted(set(HELD_WITH_PAIR) & set(self.t.yaml("projects/%s/harness.yaml" % APPROVED)
                                                          ["statements"])), [])
        for gone in ("proofs/%s/asan_agrees" % APPROVED, "findings"):
            self.assertFalse(os.path.lexists(self.t.path(gone)), gone)
        st = index_status(self.t)
        self.assertEqual([sid for sid in st if sid.rsplit("/", 1)[1] in HELD_WITH_PAIR and sid.startswith(APPROVED)],
                         [])
        self.assertEqual((st[APPROVED + "/plain_halts"], st[APPROVED + "/ubsan_agrees"]), ("proved", "proved"))
        self.assertEqual(st[UNAPPROVED + "/ubsan_agrees"], "proved")
        statements = self.t.read("projects/%s/Statements.v" % APPROVED)
        self.assertNotIn("asan_agrees", statements)
        self.assertIn("asan_halts", statements)
        self.assertEqual(self.t.generate(check=True), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_oft_approvals_omits_only_the_held_statements(self):
        os.remove(self.t.path("approvals.yaml"))
        rc, out = write_approvals(self.t, "%s\n%s\n" % (APPROVED, RELEASED))
        self.assertEqual(rc, 0, out)
        self.assertIn("held by an open finding: %s/asan_agrees\n" % APPROVED, out)
        got = {e["fuzz_target"]: e["statements"] for e in self.t.yaml("approvals.yaml")["fuzz_targets"]}
        self.assertEqual(got[APPROVED], ["plain_halts", "ubsan_agrees"])

    def test_oft_approvals_says_only_held_for_a_fuzz_target_whose_proofs_are_all_held(self):
        """internal #80's deep review, finding 9: no "listed, no proof yet" for a fuzz target with proofs."""
        for s in ("plain_halts", "ubsan_agrees"):
            shutil.rmtree(self.t.path("proofs", APPROVED, s))
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        os.remove(self.t.path("approvals.yaml"))
        rc, out = write_approvals(self.t, "%s\n%s\n" % (APPROVED, RELEASED))
        self.assertEqual(rc, 0, out)
        self.assertIn("held by an open finding: %s/asan_agrees\n" % APPROVED, out)
        self.assertNotIn("listed, no proof yet: %s" % APPROVED, out)
        self.assertEqual([e["fuzz_target"] for e in self.t.yaml("approvals.yaml")["fuzz_targets"]], [RELEASED])

    def test_an_approvals_entry_for_a_held_statement_is_refused(self):
        approve(self.t, RELEASED, entry(APPROVED, statements=["plain_halts", "asan_agrees"]))
        why = "%s/asan_agrees is held back by an open finding, so no release lists it" % APPROVED
        self.assertTrue(any(why in f.msg for f in self.t.lint()), [str(f) for f in self.t.lint()])
        self.assertRefused(why)

    def test_a_private_enrolled_projects_approvals_entry_is_refused_once(self):
        """The hold is one value: a private project is held whole, so its held statements add no error of their own."""
        make_private(self.t, "zlib")
        approve(self.t, RELEASED, entry(APPROVED, statements=["plain_halts", "asan_agrees"]))
        msgs = [f.msg for f in self.t.lint() if APPROVED in f.msg]
        self.assertTrue(any("is private" in m for m in msgs), msgs)
        self.assertFalse(any("held back by an open finding" in m for m in msgs), msgs)

    def test_a_private_enrolled_project_is_held_whole_by_its_finding(self):
        """internal #80's gates at 320061f9f6: a private project is held whole, so the open findings of an enrolled one
        hold it whole too (Hold.held), as any finding of a project that is not enrolled does.  So it may build from the
        port's internal copy, and the cut says a finding holds it back."""
        make_private(self.t, "zlib")
        port_build(self.t, "zlib")
        rel = "projects/zlib/project.yaml"
        y = self.t.yaml(rel)
        y["build"]["oss_verify"]["repository"] = schema.INTERNAL_PORT_REPOSITORY
        self.t.put_yaml(rel, y)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.assertEqual(hold(self.t), facts.Hold({"zlib"}, {"zlib"}, {}))
        self.assertEqual([str(f) for f in self.t.lint() if "build.oss_verify" in f.msg or f.rule == "private-data"], [])
        out = self.release()
        self.assertIn("held back by a finding that is not public: zlib\n", out)
        self.assertNotIn("held back by an open finding", out)
        self.assertEqual(self.t.yaml(rel)["status"], "held")

    def test_a_hold_that_would_empty_a_harness_holds_the_whole_project(self):
        """oft fetch refuses an archive with a harness's binaries the facts no longer list, and a one-harness project
        left with no build is rejected by rules.py: so the project is held whole, with its held page."""
        rel = "projects/%s/harness.yaml" % APPROVED
        h = self.t.yaml(rel)
        h["statements"] = {s: d for s, d in h["statements"].items() if s in HELD_WITH_PAIR}
        self.t.put_yaml(rel, h)
        for s in ("plain_halts", "ubsan_agrees", "asan_agrees"):
            shutil.rmtree(self.t.path("proofs", APPROVED, s))
        self.assertHeldWhole()
        self.release()
        self.assertEqual(sorted(os.listdir(self.t.path("projects", "zlib"))), ["README.md", "project.yaml"])
        self.assertEqual(self.t.yaml("projects/zlib/project.yaml")["status"], "held")
        self.assertEqual(self.t.generate(check=True), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_a_hold_that_would_leave_a_published_harness_only_withheld_statements_holds_the_whole_project(self):
        """rules.py refuses a harness that publishes a build while Statements.v carries none of its statements, unless
        it withdrew every one (internal main's #234): a statement hold that would leave only withheld statements holds
        the whole project, so the cut ships its held page instead of refusing the facts it would leave."""
        rel = "projects/%s/harness.yaml" % APPROVED
        h = self.t.yaml(rel)
        for name, st in h["statements"].items():
            if name not in HELD_WITH_PAIR:
                for k in ("basis", "reason", "witness", "withheld", "gap"):
                    st.pop(k, None)
                st.update(status="withheld", withheld="not-yet-published")
        self.t.put_yaml(rel, h)
        for s in ("plain_halts", "ubsan_agrees", "asan_agrees"):
            shutil.rmtree(self.t.path("proofs", APPROVED, s))
        self.assertHeldWhole()
        out = self.release()
        self.assertIn("held back by a finding that is not public: zlib\n", out)
        self.assertEqual(self.t.yaml("projects/zlib/project.yaml")["status"], "held")
        self.assertEqual(self.t.generate(check=True), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_a_build_record_that_says_a_held_statement_was_written_here_holds_the_whole_project(self):
        """A build record ships whole: proofs.written_here naming a held statement would leave that name in the
        release's PROVENANCE.yaml, where the cut's facts no longer have the statement (rules._written_here)."""
        self.t.write("proofs/%s/provenance/PROVENANCE.yaml" % APPROVED,
                     build_record(proofs={"origin": PACKAGE, "written_here": ["asan_agrees", "plain_halts"]}))
        self.assertHeldWhole()
        out = self.release()
        self.assertIn("held back by a finding that is not public: zlib\n", out)
        self.assertEqual(self.t.yaml("projects/zlib/project.yaml")["status"], "held")
        self.assertEqual(self.t.generate(check=True), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_a_build_record_that_says_only_statements_the_hold_leaves_were_written_here_keeps_the_statement_hold(self):
        """Only a held statement in proofs.written_here holds the project whole: plain_halts, which the hold leaves,
        keeps the hold per statement."""
        self.t.write("proofs/%s/provenance/PROVENANCE.yaml" % APPROVED,
                     build_record(proofs={"origin": PACKAGE, "written_here": ["plain_halts"]}))
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.assertEqual(hold(self.t),
                         facts.Hold(set(), set(), {"zlib": {"checksum_fuzzer/" + s for s in HELD_WITH_PAIR}}))

    def test_a_statement_the_recorded_input_shows_false_is_held_though_the_finding_does_not_name_it(self):
        """asan_halts allows exits 0 and 2; the recorded asan run exits 77, so it is false, though the finding names
        only asan_agrees."""
        y = self.t.yaml(FINDING + "/finding.yaml")
        y["input"]["asan"] = dict(y["input"]["asan"], exit=77)
        self.t.put_yaml(FINDING + "/finding.yaml", y)
        add_proof(self.t, APPROVED + "/asan_halts")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        held = HELD_WITH_PAIR + ("asan_halts",)
        self.assertEqual(hold(self.t).statements, {"zlib": {"checksum_fuzzer/" + s for s in held}})
        os.remove(self.t.path("approvals.yaml"))
        rc, out = write_approvals(self.t, "%s\n%s\n" % (APPROVED, RELEASED))
        self.assertEqual(rc, 0, out)
        self.assertIn("held by an open finding: %s/asan_halts\n" % APPROVED, out)
        self.release()
        self.assertNotIn("asan_halts", self.t.yaml("projects/%s/harness.yaml" % APPROVED)["statements"])
        self.assertNotIn(APPROVED + "/asan_halts", index_status(self.t))

    def test_a_signal_death_holds_every_statement_of_that_build(self):
        """A build killed by a signal makes its halts statements false and every agreement that names it
        (facts._refute_agreements), though the record has no run of the agreement's other build: a finding records
        only the builds its own statements name (rules.py)."""
        for build, statements in (("plain", ("plain_halts", "plain_halts_may_fail", "ubsan_agrees", "asan_agrees",
                                             "asan_ubsan_agrees")),
                                  ("asan", ("asan_halts", "asan_agrees"))):
            with self.subTest(build=build):
                self.restart()
                y = self.t.yaml(FINDING + "/finding.yaml")
                normal = y["control"]["plain"]
                y.update(statements=["%s_halts" % build],
                         input={build: dict(normal, exit=134, signal="SIGABRT")}, control={build: dict(normal)})
                self.t.put_yaml(FINDING + "/finding.yaml", y)
                for s in ("asan_agrees", "ubsan_agrees"):
                    shutil.rmtree(self.t.path("proofs", APPROVED, s), ignore_errors=True)
                self.assertEqual(self.t.generate(), 0, self.t.last_output)
                held = hold(self.t).statements["zlib"]
                self.assertEqual([s for s in statements if "checksum_fuzzer/" + s not in held], [])

    def test_a_published_build_that_is_not_the_one_the_finding_runs_on_holds_the_whole_project(self):
        """The statement hold ships the project's binaries.  A published build that differs from the unpatched pin
        the finding runs on may carry the fix, which a reader could find by comparing it with the source."""
        u = self.t.yaml(UNPATCHED)
        u["harnesses"]["checksum_fuzzer"]["plain"]["sha256"] = "7a" * 32
        self.t.put_yaml(UNPATCHED, u)
        self.assertHeldWhole()

    def test_a_published_build_with_no_unpatched_pin_holds_the_whole_project(self):
        """The pins say which binaries the findings run on; a build with no pin is not known to be unpatched."""
        u = self.t.yaml(UNPATCHED)
        del u["harnesses"]["checksum_fuzzer"]["ubsan"]
        self.t.put_yaml(UNPATCHED, u)
        self.assertHeldWhole()

    def test_a_withheld_build_needs_no_unpatched_pin(self):
        """A withheld build is not published, so the release ships no binary of it to compare: the hold stays per
        statement."""
        hrel = "projects/%s/harness.yaml" % UNAPPROVED
        h = self.t.yaml(hrel)
        h["builds"]["asan-ubsan"] = {"file": h["builds"]["asan-ubsan"]["file"], "withheld": "not-yet-published"}
        self.t.put_yaml(hrel, h)
        u = self.t.yaml(UNPATCHED)
        u["harnesses"]["api-driver"]["asan-ubsan"]["sha256"] = "7d" * 32
        self.t.put_yaml(UNPATCHED, u)
        recount(self.t)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.assertEqual(set(hold(self.t).statements), {"zlib"})
        self.assertEqual(hold(self.t).held, set())

    def test_a_harness_proof_library_with_a_held_statement_holds_the_whole_project(self):
        """A kept proofs/<p>/<h>/lib/ is shared by the harness's statements and ships unchecked: it may hold the held
        statement's proof or the finding's evidence, so the project is held whole."""
        self.t.write("proofs/%s/lib/HeldDetails.v" % APPROVED,
                     "(* held theorem: asan_agrees; observed stdout: c0595f8938f4c1b3 *)\n")
        self.assertHeldWhole()
        self.release()
        self.assertEqual(sorted(os.listdir(self.t.path("projects", "zlib"))), ["README.md", "project.yaml"])
        self.assertFalse(os.path.lexists(self.t.path("proofs", "zlib")))
        for rel, data in snapshot(self.t).items():
            self.assertNotIn(b"c0595f8938f4c1b3", data, rel)
            self.assertNotIn("HeldDetails", rel)

    def test_a_proof_library_of_another_harness_of_the_project_holds_the_whole_project(self):
        self.t.write("proofs/%s/lib/Disclosure.v" % UNAPPROVED, "(* nothing to see *)\n")
        self.assertHeldWhole()

    def test_a_patched_or_reported_finding_holds_the_whole_project(self):
        for state in ("patched", "reported"):
            with self.subTest(state=state):
                self.restart()
                self.set_state(state, upstream="https://bugs.example.org/1")
                self.t.write("findings/zlib/checksum_fuzzer/series", PATCH + "\n")
                self.assertHeldWhole()
                self.release()
                self.assertEqual(self.t.yaml("projects/zlib/project.yaml")["status"], "held")
                self.assertEqual(sorted(os.listdir(self.t.path("projects", "zlib"))), ["README.md", "project.yaml"])

    def test_a_held_statement_with_a_counterexample_is_cut_with_it(self):
        """asan_halts is held (the recorded asan run exits 77) and keeps the counterexample HeldFixture gave it: the
        cut removes that counterexample instead of refusing to ship it."""
        y = self.t.yaml(FINDING + "/finding.yaml")
        y["input"]["asan"] = dict(y["input"]["asan"], exit=77)
        self.t.put_yaml(FINDING + "/finding.yaml", y)
        add_asan_halts_counterexample(self.t)
        shutil.rmtree(self.t.path("proofs", APPROVED, "asan_agrees"))
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.assertIn("checksum_fuzzer/asan_halts", hold(self.t).statements["zlib"])
        self.release()
        self.assertFalse(os.path.lexists(self.t.path("counterexamples", APPROVED, "asan_halts")))
        self.assertEqual(self.t.generate(check=True), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_the_shipped_text_check_covers_the_statement_hold(self):
        self.t.write("CHANGELOG.md", "Fixed the %s bug.\n" % SLUG)
        self.assertRefused("names %s, the slug of finding" % SLUG)

    def test_a_shipped_file_whose_path_names_a_held_finding_is_refused(self):
        digest = self.t.yaml(FINDING + "/finding.yaml")["input"]["asan"]["stdout_sha256"]
        for rel, why in (("docs/%s.md" % digest, "%s, a digest finding %s records" % (digest, FINDING)),
                         ("docs/%s.md" % SLUG, "%s, the slug of finding %s" % (SLUG, FINDING))):
            with self.subTest(rel=rel):
                self.restart()
                self.t.write(rel, "nothing here\n")
                self.assertRefused("error: %s names %s" % (rel, why))

    def test_a_shipped_text_that_names_a_held_statement_or_its_recorded_evidence_is_refused(self):
        digest = self.t.yaml(FINDING + "/finding.yaml")["input"]["asan"]["stdout_sha256"]
        for text, why in (("%s/asan_agrees is false.\n" % APPROVED,
                           "%s/asan_agrees, a statement an open finding of zlib holds back" % APPROVED),
                          ("The ASan run printed %s.\n" % digest.upper(),
                           "%s, a digest finding %s records" % (digest, FINDING))):
            with self.subTest(why=why):
                self.restart()
                self.t.write("CHANGELOG.md", text)
                self.assertRefused("error: CHANGELOG.md names " + why)

    def test_a_kept_statements_file_may_still_name_its_own_statement(self):
        rel = "proofs/%s/ubsan_agrees/Proof.v" % APPROVED
        self.t.write(rel, self.t.read(rel) + "(* Statements.ubsan_agrees, which this release carries. *)\n")
        approve(self.t, RELEASED, entry(APPROVED, statements=["plain_halts", "ubsan_agrees"]))
        self.release()

    def test_a_held_statement_does_not_refuse_a_kept_statement_whose_name_it_begins(self):
        """The recorded plain run exits 77, so plain_halts (exits 0 or 2) is held; plain_halts_may_fail (any exit)
        holds and ships its proof, though its name begins with plain_halts, and so do texts that name it, in each
        encoding the search reads."""
        y = self.t.yaml(FINDING + "/finding.yaml")
        y["input"]["plain"] = dict(y["input"]["plain"], exit=77)
        self.t.put_yaml(FINDING + "/finding.yaml", y)
        add_proof(self.t, APPROVED + "/plain_halts_may_fail")
        shutil.rmtree(self.t.path("proofs", APPROVED, "plain_halts"))
        rel = "proofs/%s/plain_halts_may_fail/Proof.v" % APPROVED
        self.t.write(rel, self.t.read(rel) + "(* Statements.plain_halts_may_fail and plain_halts_may_fail_holds *)\n")
        for enc in ENCODINGS:
            self.t.write("docs/kept-%s.txt" % enc, ("see %s/plain_halts_may_fail\n" % APPROVED).encode(enc), mode="wb")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        held = hold(self.t).statements["zlib"]
        self.assertIn("checksum_fuzzer/plain_halts", held)
        self.assertNotIn("checksum_fuzzer/plain_halts_may_fail", held)
        approve(self.t, RELEASED, entry(APPROVED, statements=["ubsan_agrees", "plain_halts_may_fail"]))
        self.release()
        self.assertTrue(os.path.isfile(self.t.path(rel)))

    def test_a_held_name_inside_a_kept_name_is_no_mention(self):
        """A finding that names ubsan_agrees holds it, and the release keeps asan_ubsan_agrees, whose name contains
        it: the kept statement's own rendered files ship."""
        y = self.t.yaml(FINDING + "/finding.yaml")
        normal = y["control"]["plain"]
        y.update(statements=["ubsan_agrees"],
                 input={"plain": dict(normal), "ubsan": dict(normal, stdout_sha256="c0" * 32)},
                 control={"plain": dict(normal), "ubsan": dict(normal)})
        self.t.put_yaml(FINDING + "/finding.yaml", y)
        shutil.rmtree(self.t.path("proofs", APPROVED, "ubsan_agrees"))
        add_proof(self.t, APPROVED + "/asan_ubsan_agrees")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        held = hold(self.t).statements["zlib"]
        self.assertIn("checksum_fuzzer/ubsan_agrees", held)
        self.assertNotIn("checksum_fuzzer/asan_ubsan_agrees", held)
        approve(self.t, RELEASED, entry(APPROVED, statements=["plain_halts", "asan_ubsan_agrees"]))
        self.release()
        self.assertIn("asan_ubsan_agrees", self.t.yaml("projects/%s/harness.yaml" % APPROVED)["statements"])

    def test_a_kept_statement_of_another_project_with_the_same_harness_and_name_is_no_mention(self):
        """json/fuzzer-parse_bjdata/asan_agrees is kept: its own `fuzzer-parse_bjdata/asan_agrees` names no zlib
        statement, and a short `asan_agrees` in a file about json is about json."""
        self.t.write("docs/json.md", "json's fuzzer-parse_bjdata/asan_agrees is suspected false.\n")
        self.release()

    def add_v2(self):
        """A second fuzz target of zlib, checksum_fuzzer_v2, whose Rocq module begins with checksum_fuzzer's."""
        v2 = "checksum_fuzzer_v2"
        shutil.copytree(self.t.path("projects", APPROVED), self.t.path("projects", "zlib", v2))
        rel = "projects/zlib/%s/harness.yaml" % v2
        h = self.t.yaml(rel)
        h.update(harness=v2, rocq="OssFuzzTheorems.zlib." + v2)
        for b, rec in h["builds"].items():
            rec["file"] = "%s.%s" % (v2, b)
        self.t.put_yaml(rel, h)
        p = self.t.yaml("projects/zlib/project.yaml")
        p["harnesses"].append({"name": v2, "status": "included"})
        self.t.put_yaml("projects/zlib/project.yaml", p)
        u = self.t.yaml(UNPATCHED)
        u["harnesses"][v2] = {b: dict(rec, file="%s.%s" % (v2, b))
                              for b, rec in u["harnesses"]["checksum_fuzzer"].items()}
        self.t.put_yaml(UNPATCHED, u)
        align_unpatched_pins(self.t)
        recount(self.t)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)

    def test_a_fuzz_target_whose_module_begins_with_the_held_ones_ships(self):
        """internal #80's final review, finding 7: checksum_fuzzer_v2's rendered Statements.v names its own module,
        OssFuzzTheorems.zlib.checksum_fuzzer_v2, and its own asan_agrees; neither names the held one."""
        self.add_v2()
        self.assertEqual(set(hold(self.t).statements["zlib"]), {"checksum_fuzzer/" + s for s in HELD_WITH_PAIR})
        approve(self.t, RELEASED, entry(APPROVED, statements=["plain_halts", "ubsan_agrees"]))
        self.release()
        self.assertIn("Definition asan_agrees", self.t.read("projects/zlib/checksum_fuzzer_v2/Statements.v"))


if __name__ == "__main__":
    unittest.main()
