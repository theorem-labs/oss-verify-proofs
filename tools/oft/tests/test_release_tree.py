"""`oft release-tree`, `oft approvals` and approvals.yaml: a release carries the approved proofs and no other, no
findings/, and only the held form of a project a finding holds back."""
import contextlib
import csv
import io
import os
import shutil
import subprocess
import tempfile
import unittest

from oft import approvals, facts, release_tree, yamlio
from oft.tests.helpers import Tree, add_findings, build_record, rules_of
from oft.tests.test_oss_verify import add_standin

APPROVED = "zlib/checksum_fuzzer"
UNAPPROVED = "zlib/api-driver"
CODEOWNERS = "/approvals.yaml @approver\n"
# a build record's proofs.origin that names a package, in the shape of the real ones: the package and its sha256, then
# the submissions taken from it, the YAML folded over lines
PACKAGE = ("fixture-proofs-package-2026-10-21 (sha256 %s),\n  libraries/zlib/proofs/submission-1 and "
           "libraries/json/proofs/submission-2" % ("4c" * 32))
# a contribution's proofs.origin: it names the package's digest too, later, and is no package origin
CONTRIBUTED = ("contributed by A. Contributor in https://github.com/theorem-labs/oss-verify-proofs/pull/3 (commit %s), "
               "made from "
               "the library files of fixture-proofs-package-2026-10-21 (sha256 %s)" % ("1e" * 20, "4c" * 32))
RELEASED = "json/fuzzer-parse_bjdata"


def add_proof(t, sid):
    st = next(s for s in facts.load(t.root).statements() if s.id == sid)
    t.put_yaml("proofs/%s/proof.yaml" % sid, {
        "schema": "oss-fuzz-theorems/proof/1", "proves": sid, "fingerprint": st.fingerprint})
    t.write("proofs/%s/Proof.v" % sid, "Theorem holds : True. Proof. exact I. Qed.\n")


def entry(unit, statements=("plain_halts",), **kw):
    return dict({"fuzz_target": unit, "statements": list(statements), "approved_by": "approver", "date": "2026-10-19",
                 "origin": "this-repository"}, **kw)


def approve(t, *entries):
    t.put_yaml("approvals.yaml", {"schema": "oss-fuzz-theorems/approvals/1",
                                  "fuzz_targets": [e if isinstance(e, dict) else entry(e) for e in entries]})


def refute(t, sid):
    """Make the proof of sid a refutation."""
    st = next(x for x in facts.load(t.root).statements() if x.id == sid)
    t.put_yaml("proofs/%s/proof.yaml" % sid, {
        "schema": "oss-fuzz-theorems/proof/1", "refutes": sid, "fingerprint": st.fingerprint})
    t.write("proofs/%s/Refutation.v" % sid, "Theorem fails : True. Proof. exact I. Qed.\n")
    if os.path.exists(t.path("proofs", sid, "Proof.v")):
        os.remove(t.path("proofs", sid, "Proof.v"))


def make_private(t, project):
    """Mark project `release: private`.  release.yaml's counts still describe this tree, so they do not change: the
    cut writes the release's own."""
    rel = "projects/%s/project.yaml" % project
    t.put_yaml(rel, dict(t.yaml(rel), release="private"))


def index_status(t):
    """{statement id: status} as index/statements.tsv, the rendered index, says."""
    with open(t.path("index", "statements.tsv"), newline="") as f:
        return {r["id"]: r["status"] for r in csv.DictReader(f, delimiter="\t")}


def snapshot(t):
    """{path: bytes} of every file in the checkout (a symbolic link is not followed)."""
    out = {}
    for dp, _, fns in os.walk(t.root):
        for f in fns:
            full = os.path.join(dp, f)
            if os.path.islink(full):
                out[os.path.relpath(full, t.root)] = os.readlink(full)
            else:
                with open(full, "rb") as fh:
                    out[os.path.relpath(full, t.root)] = fh.read()
    return out


EXCEPTIONS = "tools/oft/lint-exceptions.yaml"
EXCEPTIONS_HEAD = "# the reviewed exceptions\n\n# a second paragraph\nschema: oss-fuzz-theorems/lint-exceptions/1\n"


def needed_exception(t, rel):
    """Write a host path into rel, an upstream copy, and return the lint exception that clears the one finding it
    makes there."""
    t.write(rel, "/* built in /" + "home/someone/src */\n", "a")
    found = [f for f in t.lint() if f.rule == "private-data" and f.where.startswith(rel + ":")]
    assert len(found) == 1, [str(f) for f in found]
    return {"path": rel, "rule": "private-data", "key": found[0].key, "count": 1, "reason": "a host path upstream"}


def put_exceptions(t, entries, head=EXCEPTIONS_HEAD):
    """Write lint-exceptions.yaml: head (a leading comment with a blank line in it, and the schema), then entries."""
    t.write(EXCEPTIONS, head + yamlio.dump({"exceptions": entries}))


def release(t):
    buf = io.StringIO()
    rc = release_tree.run(t.root, out=buf)
    return rc, buf.getvalue()


def write_approvals(t, listing):
    """`oft approvals` over t with FILE holding listing, written beside the checkout, not in it."""
    path = t.path("..", "launch.txt")
    with open(path, "w", encoding="utf-8") as f:
        f.write(listing)
    buf = io.StringIO()
    rc = approvals.write(t.root, path, approved_by="approver", date="2026-10-20", out=buf)
    return rc, buf.getvalue()


class ReleaseTree(unittest.TestCase):
    def setUp(self):
        self.t = Tree()
        self.addCleanup(self.t.close)
        add_proof(self.t, APPROVED + "/plain_halts")
        add_proof(self.t, UNAPPROVED + "/ubsan_agrees")
        self.t.write("proofs/%s/lib/Shared.v" % APPROVED, "Definition one := 1.\n")
        self.t.write("proofs/%s/lib/Shared.v" % UNAPPROVED, "Definition two := 2.\n")
        for u in (APPROVED, UNAPPROVED):
            self.t.write("proofs/%s/provenance/PROVENANCE.md" % u, "The build record.\n")
        self.t.write("proofs/lib/Common.v", "Definition zero := 0.\n")
        self.t.write(".github/CODEOWNERS", CODEOWNERS)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)

    def assertRefused(self, why):
        """release-tree refuses, says why, and leaves every file of the checkout byte for byte as it was."""
        before = snapshot(self.t)
        rc, out = release(self.t)
        self.assertEqual(rc, 1, out)
        self.assertIn(why, out)
        self.assertEqual(snapshot(self.t), before)

    def test_keeps_only_the_approved_proofs_and_renders_their_statuses(self):
        approve(self.t, APPROVED)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        self.assertEqual(index_status(self.t)[UNAPPROVED + "/ubsan_agrees"], "proved")
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertTrue(os.path.isfile(self.t.path("proofs", APPROVED, "plain_halts", "Proof.v")))
        self.assertTrue(os.path.isfile(self.t.path("proofs", APPROVED, "lib", "Shared.v")))
        self.assertTrue(os.path.isfile(self.t.path("proofs", APPROVED, "provenance", "PROVENANCE.md")))
        self.assertFalse(os.path.exists(self.t.path("proofs", UNAPPROVED)))
        self.assertFalse(os.path.exists(self.t.path("approvals.yaml")))
        self.assertFalse(os.path.exists(self.t.path(".github", "CODEOWNERS")))
        st = index_status(self.t)
        self.assertEqual(st[APPROVED + "/plain_halts"], "proved")
        self.assertEqual(st[UNAPPROVED + "/ubsan_agrees"], "open")
        self.assertEqual(self.t.generate(check=True), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_the_shared_library_and_counterexamples_stay(self):
        approve(self.t, APPROVED)
        cx = "counterexamples/json/fuzzer-parse_bjdata/plain_halts"
        self.assertTrue(os.path.isdir(self.t.path(cx)))
        self.assertEqual(release(self.t)[0], 0)
        self.assertTrue(os.path.isfile(self.t.path("proofs", "lib", "Common.v")))
        self.assertTrue(os.path.isdir(self.t.path(cx)))
        self.assertEqual(index_status(self.t)["json/fuzzer-parse_bjdata/plain_halts"], "counterexample")

    def test_only_the_approved_statements_of_a_fuzz_target_are_kept(self):
        add_proof(self.t, APPROVED + "/ubsan_agrees")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertTrue(os.path.isfile(self.t.path("proofs", APPROVED, "plain_halts", "Proof.v")))
        self.assertFalse(os.path.exists(self.t.path("proofs", APPROVED, "ubsan_agrees")))
        self.assertTrue(os.path.isfile(self.t.path("proofs", APPROVED, "lib", "Shared.v")))
        st = index_status(self.t)
        self.assertEqual(st[APPROVED + "/plain_halts"], "proved")
        self.assertEqual(st[APPROVED + "/ubsan_agrees"], "open")
        self.assertIn(release_tree.PARTIAL % APPROVED, out)

    def test_a_fuzz_target_with_all_its_proofs_kept_is_not_reported_for_its_lib(self):
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertNotIn("kept the lib/", out)

    def test_findings_never_ship(self):
        add_findings(self.t)
        make_private(self.t, "zlib")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, entry("json/fuzzer-parse_bjdata", statements=["plain_halts"]))
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.exists(self.t.path("findings")))
        self.assertEqual(sorted(os.listdir(self.t.path("projects", "zlib"))), ["README.md", "project.yaml"])
        self.assertEqual(self.t.yaml("projects/zlib/project.yaml")["status"], "held")
        self.assertIn("removed findings/ and approvals.yaml", out)
        self.assertEqual(self.t.generate(check=True), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_a_project_a_finding_holds_back_is_refused(self):
        add_findings(self.t)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, APPROVED)
        self.assertTrue(any("holds back project zlib" in f.msg for f in self.t.lint()))
        self.assertRefused("a finding holds back project zlib")

    def test_a_project_a_finding_holds_back_that_is_not_private_ships_held(self):
        """It was refused until the hold existed; it now ships in the held form (HeldBack covers the rest)."""
        add_findings(self.t)
        self.t.write("notes/zlib.md", "Notes on zlib.\n")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, entry("json/fuzzer-parse_bjdata", statements=["plain_halts"]))
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.t.yaml("projects/zlib/project.yaml")["status"], "held")
        self.assertFalse(os.path.lexists(self.t.path("notes", "zlib.md")))

    def test_a_held_project_attached_to_its_findings_release_ships_no_asset(self):
        add_findings(self.t)
        rel = "projects/zlib/project.yaml"
        y = self.t.yaml(rel)
        y["assets"]["bin"]["release"] = "findings-zlib"
        self.t.put_yaml(rel, y)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, entry("json/fuzzer-parse_bjdata", statements=["plain_halts"]))
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        for rel_, data in snapshot(self.t).items():
            self.assertNotIn(b"findings-zlib", data, rel_)

    def test_a_symbolic_link_under_findings_is_refused(self):
        add_findings(self.t)
        make_private(self.t, "zlib")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, entry("json/fuzzer-parse_bjdata", statements=["plain_halts"]))
        outside = self.t.path("..", "outside")
        os.makedirs(outside)
        os.symlink(outside, self.t.path("findings", "zlib", "linked"))
        self.assertRefused("findings/zlib/linked")

    def test_a_listed_refutation_is_refused(self):
        add_proof(self.t, APPROVED + "/asan_halts")
        refute(self.t, APPROVED + "/asan_halts")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, entry(APPROVED, statements=["plain_halts", "asan_halts"]))
        self.assertTrue(any("is a refutation" in f.msg for f in self.t.lint()))
        self.assertRefused("%s/asan_halts: its proof is a refutation" % APPROVED)

    def test_an_extra_file_in_a_kept_statement_directory_is_refused(self):
        approve(self.t, APPROVED)
        self.t.write("proofs/%s/plain_halts/Extra.v" % APPROVED, "Definition x := 0.\n")
        self.assertRefused("proofs/%s/plain_halts/Extra.v" % APPROVED)

    def test_each_file_of_the_shared_library_is_reported(self):
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertIn("as every release carries proofs/lib/: proofs/lib/Common.v", out)

    def test_a_private_project_oss_fuzz_has_keeps_only_its_held_page(self):
        before = self.t.yaml("projects/json/project.yaml")
        self.t.write("notes/json.md", "Notes on json.\n")
        make_private(self.t, "json")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, APPROVED)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertEqual(sorted(os.listdir(self.t.path("projects", "json"))), ["README.md", "project.yaml"])
        self.assertEqual(self.t.yaml("projects/json/project.yaml"), {
            "schema": before["schema"], "project": "json", "homepage": before["homepage"],
            "language": before["language"], "oss_fuzz": before["oss_fuzz"], "status": "held", "reason": "held"})
        for gone in ("counterexamples/json", "notes/json.md", "proofs/json"):
            self.assertFalse(os.path.lexists(self.t.path(gone)), gone)
        self.assertTrue(os.path.isfile(self.t.path("proofs", APPROVED, "plain_halts", "Proof.v")))
        self.assertIn("Held from this release", self.t.read("projects/json/README.md"))
        self.assertIn("\njson\t", self.t.read("index/projects.tsv"))
        for idx in ("harnesses", "statements", "binaries"):
            self.assertNotIn("\njson\t", self.t.read("index/%s.tsv" % idx), idx)
        r = self.t.yaml("release.yaml")
        self.assertEqual(r["counts"], {"projects": 5, "available": 1, "harnesses": 2, "binaries": 8})
        self.assertEqual(r["oss_fuzz"]["projects"], 5)
        for rel, data in snapshot(self.t).items():
            self.assertNotIn(b"fuzzer-parse_bjdata", data, rel)
            self.assertNotIn(b"fuzzer_parse_bjdata", data, rel)
        self.assertEqual(self.t.generate(check=True), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_a_private_projects_build_record_goes_with_its_proofs(self):
        """The recipe a private project's build record cites is no fact of the release: its held page pins none."""
        record = "proofs/json/fuzzer-parse_bjdata/provenance/PROVENANCE.yaml"
        self.t.write(record, build_record())
        make_private(self.t, "json")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, APPROVED)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.lexists(self.t.path("proofs", "json")))
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_a_private_projects_written_here_goes_with_its_build_record(self):
        """The cut checks the public facts again: a private project's build record, and what it says was written
        here, is gone from them with its harnesses."""
        record = "proofs/json/fuzzer-parse_bjdata/provenance/PROVENANCE.yaml"
        self.t.write(record, build_record(proofs={"origin": PACKAGE, "written_here": ["plain_halts"]}))
        make_private(self.t, "json")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, APPROVED)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_a_private_project_oss_fuzz_does_not_have_is_removed_whole(self):
        add_standin(self.t)
        self.t.write("notes/standin.md", "Notes on the stand-in.\n")
        make_private(self.t, "standin")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, APPROVED)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        for gone in ("projects/standin", "notes/standin.md"):
            self.assertFalse(os.path.lexists(self.t.path(gone)), gone)
        for rel, data in snapshot(self.t).items():
            self.assertNotIn(b"standin", data, rel)
        r = self.t.yaml("release.yaml")
        self.assertEqual(r["counts"], {"projects": 5, "available": 2, "harnesses": 3, "binaries": 12})
        self.assertEqual(r["oss_fuzz"]["projects"], 5)
        self.assertEqual(self.t.generate(check=True), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_an_image_library_only_a_private_project_links_leaves_release_yaml(self):
        h = "projects/json/fuzzer-parse_bjdata/harness.yaml"
        y = self.t.yaml(h)
        for b in y["builds"].values():
            b["uninstrumented"] = [{"name": "libgmp.a", "kind": "image-library"}]
        self.t.put_yaml(h, y)
        r = self.t.yaml("release.yaml")
        r["image_libraries"] = {"libgmp.a": {"library": "GMP", "licence": "LGPL-3.0-or-later OR GPL-2.0-or-later",
                                             "copyleft": False, "in_sysroot_src": True}}
        self.t.put_yaml("release.yaml", r)
        make_private(self.t, "json")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, APPROVED)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertNotIn("libgmp", self.t.read("release.yaml"))
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_shipped_text_that_names_a_private_fuzz_target_is_refused(self):
        make_private(self.t, "json")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, APPROVED)
        cases = [("CHANGELOG.md", "json/fuzzer-parse_bjdata", b"Proved json/fuzzer-parse_bjdata/plain_halts.\n"),
                 ("docs/notes.md", "json/fuzzer-parse_bjdata", b"see json/fuzzer-parse_bjdata\n"),
                 ("notes/zlib.md", "json/fuzzer-parse_bjdata", b"the path json%2Ffuzzer-parse_bjdata\n"),
                 ("docs/rocq.md", "OssFuzzTheorems.json.fuzzer_parse_bjdata",
                  b"Require OssFuzzTheorems.json.fuzzer_parse_bjdata.\n"),
                 ("docs/nul.md", "json/fuzzer-parse_bjdata", b"\0json/fuzzer-parse_bjdata\n"),
                 ("docs/wide.md", "json/fuzzer-parse_bjdata", "json/fuzzer-parse_bjdata\n".encode("utf-16")),
                 ("docs/blob.bin", "json/fuzzer-parse_bjdata", b"\x7fELF\0\0json/fuzzer-parse_bjdata\0")]
        for rel, needle, data in cases:
            with self.subTest(rel=rel):
                self.t.write(rel, data, mode="wb")
                self.assertRefused("error: %s names %s, " % (rel, needle))
                os.remove(self.t.path(rel))

    def test_a_private_name_inside_the_enrollment_tools_is_not_shipped_or_refused(self):
        # the cut removes tools/enroll/ whole, so a name it holds back there is neither shipped nor a refusal
        make_private(self.t, "json")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, APPROVED)
        self.t.write("tools/enroll/README.md", "enrolled json/fuzzer-parse_bjdata\n")
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.lexists(self.t.path("tools/enroll")))

    def test_shipped_text_that_names_a_holding_finding_is_refused(self):
        add_findings(self.t)
        make_private(self.t, "zlib")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, entry("json/fuzzer-parse_bjdata", statements=["plain_halts"]))
        for needle in ("stand-in-abort", "0001-stand-in.patch"):
            with self.subTest(needle=needle):
                self.t.write("CHANGELOG.md", "Fixed %s in adler32.\n" % needle)
                self.assertRefused("error: CHANGELOG.md names %s, " % needle)
                os.remove(self.t.path("CHANGELOG.md"))

    def test_a_file_git_tracks_at_an_ignored_path_is_refused(self):
        approve(self.t, APPROVED)
        self.t.write("docs/_build/page.html", "built\n")
        subprocess.run(["git", "init", "-q", self.t.root], check=True)
        subprocess.run(["git", "-C", self.t.root, "add", "-f", "docs/_build/page.html"], check=True)
        self.assertRefused("docs/_build/page.html (tracked by git at an ignored path)")

    def test_a_private_project_cannot_be_approved(self):
        make_private(self.t, "zlib")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, APPROVED)
        self.assertTrue(any("is private (release: private" in f.msg for f in self.t.lint()))
        self.assertRefused("project zlib is private (release: private in its project.yaml)")

    def test_counts_that_do_not_describe_this_tree_are_refused(self):
        r = self.t.yaml("release.yaml")
        r["counts"]["available"] = 1
        self.t.put_yaml("release.yaml", r)
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 1, out)
        self.assertNotIn("unknown key", out)
        self.assertNotIn("projects/json/project.yaml", out)
        self.assertIn("error: release.yaml: counts.available is 1 but the tree has 2\n", out)

    def test_a_private_project_leaves_this_tree_counts_as_they_are(self):
        """release.yaml and the rendering agree in this repository, private projects and all."""
        before = self.t.yaml("release.yaml")["counts"]
        make_private(self.t, "json")
        self.assertEqual(self.t.generate(check=True), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        self.assertEqual(self.t.yaml("release.yaml")["counts"], before)
        self.assertIn("The 2 available projects have 3 harnesses", self.t.read("README.md"))

    def test_a_statement_the_fuzz_target_does_not_have_is_refused(self):
        approve(self.t, entry(APPROVED, statements=["plain_halts", "no_such_statement"]))
        self.assertRefused("no_such_statement is not a statement of zlib/checksum_fuzzer")

    def test_a_project_left_with_no_proofs_leaves_no_directory(self):
        approve(self.t, entry("json/fuzzer-parse_bjdata", statements=["plain_halts"]))
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.exists(self.t.path("proofs", "zlib")))

    def test_the_facts_review_files_never_ship(self):
        self.t.write(".github/workflows/facts-review.yml", "name: facts-review\n")
        self.t.write(".claude/skills/review-facts/SKILL.md", "# review the facts\n")
        self.t.write("review.md", "# The facts review's checks\n")
        approve(self.t, APPROVED)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        for gone in (".github/workflows/facts-review.yml", ".claude/skills/review-facts/SKILL.md", "review.md"):
            self.assertFalse(os.path.lexists(self.t.path(gone)), gone)
        self.assertIn(".github/workflows/facts-review.yml", out)

    def test_the_enrollment_pipeline_never_ships(self):
        self.t.write(".github/workflows/enroll.yml", "name: enroll\n")
        self.t.write(".github/workflows/enroll-build.yml", "name: enroll-build\n")
        self.t.write("tools/enroll/README.md", "# tools/enroll\n")
        self.t.write("tools/enroll/ci/gate.py", "LIMIT = 3\n")
        approve(self.t, APPROVED)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        for gone in (".github/workflows/enroll.yml", ".github/workflows/enroll-build.yml", "tools/enroll"):
            self.assertFalse(os.path.lexists(self.t.path(gone)), gone)
        self.assertIn("tools/enroll", out)

    def test_the_proof_index_never_ships(self):
        self.t.write(".github/workflows/proof-index.yml", "name: proof-index\n")
        self.t.write(".github/proof-index.py", "RULES = 5\n")
        approve(self.t, APPROVED)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        for gone in (".github/workflows/proof-index.yml", ".github/proof-index.py"):
            self.assertFalse(os.path.lexists(self.t.path(gone)), gone)
            self.assertIn(gone, out)

    def test_without_codeowners_it_says_what_it_removed(self):
        os.remove(self.t.path(".github", "CODEOWNERS"))
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertIn("removed approvals.yaml;", out)
        self.assertNotIn("CODEOWNERS", out)

    def test_no_approvals_file_changes_nothing(self):
        self.assertRefused("no approvals.yaml")

    def test_an_entry_that_names_no_fuzz_target_is_refused_and_changes_nothing(self):
        approve(self.t, APPROVED, "zlib/no_such_fuzzer")
        self.assertTrue(any("not an included fuzz target" in f.msg for f in self.t.lint()))
        self.assertRefused("zlib/no_such_fuzzer is not an included fuzz target")

    def test_an_entry_without_its_approver_is_refused_and_changes_nothing(self):
        e = entry(APPROVED)
        del e["approved_by"]
        approve(self.t, e)
        self.assertIn("schema", rules_of(self.t.lint()))
        self.assertRefused("missing key 'approved_by'")

    def test_an_empty_list_is_refused(self):
        approve(self.t)
        self.assertIn("schema", rules_of(self.t.lint()))
        self.assertRefused("at least 1 item(s) required")

    def test_a_symbolic_link_under_proofs_is_refused_and_changes_nothing(self):
        approve(self.t, APPROVED)
        outside = self.t.path("..", "outside", "victim")
        os.makedirs(outside)
        os.symlink(os.path.dirname(outside), self.t.path("proofs", "zlib", "linked"))
        self.assertRefused("proofs/zlib/linked")
        self.assertTrue(os.path.isdir(outside))

    def test_a_stray_file_under_proofs_is_refused(self):
        approve(self.t, APPROVED)
        self.t.write("proofs/zlib/STRAY.v", "Definition x := 0.\n")
        self.assertRefused("proofs/zlib/STRAY.v")

    def test_a_stray_file_beside_the_statements_is_refused(self):
        approve(self.t, APPROVED)
        self.t.write("proofs/%s/STRAY.v" % APPROVED, "Definition x := 0.\n")
        self.assertRefused("proofs/%s/STRAY.v" % APPROVED)

    def test_a_listed_statement_with_no_proof_is_reported(self):
        approve(self.t, entry(APPROVED, statements=["plain_halts", "asan_halts"]))
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertIn("listed, but no proof in this checkout: %s/asan_halts" % APPROVED, out)
        self.assertIn("1 listed statement(s) with no proof", out)

    def test_a_stale_rendering_is_refused_before_anything_is_removed(self):
        approve(self.t, APPROVED)
        self.t.write("projects/zlib/checksum_fuzzer/README.md", "stale\n")
        self.assertRefused("the generated files are not current")

    def test_a_symbolically_linked_proofs_directory_is_refused(self):
        approve(self.t, APPROVED)
        os.rename(self.t.path("proofs"), self.t.path("..", "other-proofs"))
        os.symlink(os.path.join("..", "other-proofs"), self.t.path("proofs"))
        self.assertRefused("proofs: a symbolic link")
        self.assertTrue(os.path.isdir(self.t.path("..", "other-proofs", UNAPPROVED)))

    def test_a_symbolically_linked_directory_that_holds_an_internal_path_is_refused(self):
        """The cut removes .claude/skills/review-facts/SKILL.md and tools/enroll; through a linked .claude or tools it
        would remove them where the link points, outside the checkout."""
        approve(self.t, APPROVED)
        for top, inside in ((".claude", "skills/review-facts/SKILL.md"), ("tools", "enroll/build")):
            with self.subTest(directory=top):
                outside = self.t.path("..", "outside-" + top.strip("."))
                os.makedirs(os.path.dirname(os.path.join(outside, inside)), exist_ok=True)
                with open(os.path.join(outside, inside), "w") as f:
                    f.write("kept\n")
                if os.path.lexists(self.t.path(top)):
                    shutil.rmtree(self.t.path(top))
                os.symlink(os.path.join("..", "outside-" + top.strip(".")), self.t.path(top))
                self.assertRefused("%s: a symbolic link" % top)
                self.assertTrue(os.path.isfile(os.path.join(outside, inside)))
                os.remove(self.t.path(top))

    def test_an_entry_listed_twice(self):
        approve(self.t, APPROVED, APPROVED)
        self.assertTrue(any("listed twice" in f.msg for f in self.t.lint()))

    def test_a_statement_in_two_entries_is_listed_twice(self):
        approve(self.t, entry(APPROVED, statements=["plain_halts"], origin="submission", record="review-a"),
                entry(APPROVED, statements=["plain_halts"], origin="submission", record="review-b"))
        found = [f.msg for f in self.t.lint()]
        self.assertIn("approvals.fuzz_targets[1]: %s/plain_halts is listed twice: approvals.fuzz_targets[0] and [1]"
                      % APPROVED, found)
        self.assertNotIn("listed twice for one source", " ".join(found))

    def test_a_statement_listed_twice(self):
        approve(self.t, entry(APPROVED, statements=["plain_halts", "plain_halts"]))
        self.assertTrue(any("plain_halts is listed twice" in f.msg for f in self.t.lint()))

    def test_a_submission_names_its_review_record_and_only_a_submission_does(self):
        approve(self.t, entry(APPROVED, origin="submission", record="review-2026-10-18"))
        self.assertEqual([str(f) for f in self.t.lint()], [])
        for e in (entry(APPROVED, origin="submission"), entry(APPROVED, record="review-2026-10-18")):
            approve(self.t, e)
            self.assertTrue(any("names the record" in f.msg for f in self.t.lint()), e)

    def test_a_fuzz_target_with_an_entry_per_source(self):
        add_proof(self.t, APPROVED + "/ubsan_agrees")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, entry(APPROVED, statements=["ubsan_agrees"], origin="submission", record="review-2026-10-18"),
                entry(APPROVED, statements=["plain_halts"]))
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        for s in ("plain_halts", "ubsan_agrees"):
            self.assertTrue(os.path.isfile(self.t.path("proofs", APPROVED, s, "Proof.v")), s)
        self.assertNotIn(release_tree.PARTIAL % APPROVED, out)

    def test_a_statement_in_two_entries_of_its_fuzz_target(self):
        approve(self.t, entry(APPROVED, origin="submission", record="review-2026-10-18"), entry(APPROVED))
        self.assertIn("approvals.fuzz_targets[1]: %s/plain_halts is listed twice: approvals.fuzz_targets[0] and [1]"
                      % APPROVED,
                      [f.msg for f in self.t.lint()])

    def test_one_source_listed_twice(self):
        approve(self.t, entry(APPROVED, origin="submission", record="review-2026-10-18"),
                entry(APPROVED, statements=["ubsan_agrees"], origin="submission", record="review-2026-10-18"))
        self.assertIn("approvals.fuzz_targets[1]: %s is listed twice for one source (submission, record "
                      "review-2026-10-18): "
                      "approvals.fuzz_targets[0] and [1]" % APPROVED, [f.msg for f in self.t.lint()])

    def test_a_lint_exception_for_a_private_project_is_cut_with_it(self):
        make_private(self.t, "json")
        approve(self.t, APPROVED)
        private = needed_exception(self.t, "projects/json/fuzzer-parse_bjdata/source/fuzzer-parse_bjdata.cpp")
        kept = needed_exception(self.t, "projects/zlib/checksum_fuzzer/source/checksum_fuzzer.c")
        put_exceptions(self.t, [private, kept])
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertIn("rewrote %s without the exception(s) for %s" % (EXCEPTIONS, private["path"]), out)
        self.assertEqual(self.t.read(EXCEPTIONS), EXCEPTIONS_HEAD + yamlio.dump({"exceptions": [kept]}))
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_a_lint_exception_under_an_unapproved_fuzz_target_of_a_public_project_is_cut_with_it(self):
        """zlib is public, so only the removal of api-driver's unlisted proofs takes the entry out."""
        approve(self.t, APPROVED)
        cut = needed_exception(self.t, "proofs/%s/provenance/LICENSES/zlib-LICENSE" % UNAPPROVED)
        kept = needed_exception(self.t, "projects/zlib/checksum_fuzzer/source/checksum_fuzzer.c")
        put_exceptions(self.t, [cut, kept])
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.exists(self.t.path("proofs", UNAPPROVED)))
        self.assertEqual(self.t.read(EXCEPTIONS), EXCEPTIONS_HEAD + yamlio.dump({"exceptions": [kept]}))
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_a_rewritten_lint_exceptions_file_that_names_a_private_fuzz_target_is_refused(self):
        """The file is rewritten, so the scan of the files the release keeps skips it: its new text is read instead."""
        make_private(self.t, "json")
        approve(self.t, APPROVED)
        private = needed_exception(self.t, "projects/json/fuzzer-parse_bjdata/source/fuzzer-parse_bjdata.cpp")
        kept = needed_exception(self.t, "projects/zlib/checksum_fuzzer/source/checksum_fuzzer.c")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        named = dict(kept, reason="as json/fuzzer-parse_bjdata")
        cases = {"a kept entry's reason": (EXCEPTIONS_HEAD, [private, named]),
                 "the leading comment": ("# see json/fuzzer-parse_bjdata\n" + EXCEPTIONS_HEAD, [private, kept])}
        for where, (head, entries) in cases.items():
            with self.subTest(where=where):
                put_exceptions(self.t, entries, head)
                self.assertRefused("error: %s names %s" % (EXCEPTIONS, "json/fuzzer-parse_bjdata, a fuzz target of held project json"))


class WriteApprovals(unittest.TestCase):
    """`oft approvals` writes approvals.yaml from the proofs a checkout holds, for the fuzz targets a file lists."""

    def setUp(self):
        self.t = Tree()
        self.addCleanup(self.t.close)
        add_proof(self.t, APPROVED + "/plain_halts")
        add_proof(self.t, APPROVED + "/ubsan_agrees")
        add_proof(self.t, UNAPPROVED + "/ubsan_agrees")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)

    def write(self, listing):
        return write_approvals(self.t, listing)

    def test_each_listed_fuzz_target_with_the_statements_it_has_proofs_of(self):
        rc, out = self.write("# the launch set\n%s\n%s\treview-2026-10-18\tubsan_agrees\njson/fuzzer-parse_bjdata\n"
                             % (APPROVED, UNAPPROVED))
        self.assertEqual(rc, 0, out)
        self.assertIn("listed, no proof yet: json/fuzzer-parse_bjdata", out)
        doc = self.t.yaml("approvals.yaml")
        self.assertEqual(doc["fuzz_targets"], [
            {"fuzz_target": UNAPPROVED, "statements": ["ubsan_agrees"], "approved_by": "approver", "date": "2026-10-20",
             "origin": "submission", "record": "review-2026-10-18"},
            {"fuzz_target": APPROVED, "statements": ["plain_halts", "ubsan_agrees"], "approved_by": "approver",
             "date": "2026-10-20", "origin": "this-repository"}])
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_only_the_statements_a_record_covers(self):
        rc, out = self.write("%s\treview-2026-10-18\tubsan_agrees\n" % APPROVED)
        self.assertEqual(rc, 0, out)
        self.assertIn("a proof its record does not cover, not listed: %s/plain_halts" % APPROVED, out)
        self.assertEqual(self.t.yaml("approvals.yaml")["fuzz_targets"][0]["statements"], ["ubsan_agrees"])

    def test_a_refutation_is_never_listed(self):
        sid = APPROVED + "/asan_halts"
        refute(self.t, sid)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        rc, out = self.write("%s\n" % APPROVED)
        self.assertEqual(rc, 0, out)
        self.assertIn("a refutation, not listed: %s" % sid, out)
        self.assertNotIn("asan_halts", self.t.yaml("approvals.yaml")["fuzz_targets"][0]["statements"])

    def test_a_record_without_its_statements_writes_nothing(self):
        rc, out = self.write("%s\treview-2026-10-18\n" % APPROVED)
        self.assertEqual(rc, 1, out)
        self.assertIn("a record must name the statements it covers", out)
        self.assertFalse(os.path.exists(self.t.path("approvals.yaml")))

    def test_a_covered_name_that_is_no_statement_writes_nothing(self):
        rc, out = self.write("%s\treview-2026-10-18\tplain_halt\n" % APPROVED)
        self.assertEqual(rc, 1, out)
        self.assertIn("'plain_halt' is not a statement of %s" % APPROVED, out)
        self.assertFalse(os.path.exists(self.t.path("approvals.yaml")))

    def test_a_project_a_finding_holds_back_is_not_listed(self):
        add_findings(self.t)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        rc, out = self.write("%s\n" % APPROVED)
        self.assertEqual(rc, 1, out)
        self.assertIn("held by a finding that is not public: %s\n" % APPROVED, out)
        self.assertFalse(os.path.exists(self.t.path("approvals.yaml")))

    def test_a_private_project_is_not_listed(self):
        make_private(self.t, "zlib")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        rc, out = self.write("%s\n" % APPROVED)
        self.assertEqual(rc, 1, out)
        self.assertIn("its project is private (release: private), not listed: %s" % APPROVED, out)
        self.assertFalse(os.path.exists(self.t.path("approvals.yaml")))

    def test_an_unchanged_entry_keeps_its_approver_and_date(self):
        rc, out = self.write("%s\n" % APPROVED)
        self.assertEqual(rc, 0, out)
        path = self.t.path("..", "launch.txt")
        with open(path, "w", encoding="utf-8") as f:
            f.write("%s\n%s\treview-2026-10-18\tubsan_agrees\n" % (APPROVED, UNAPPROVED))
        rc = approvals.write(self.t.root, path, approved_by="bob", date="2026-10-25", out=io.StringIO())
        self.assertEqual(rc, 0)
        by = {e["fuzz_target"]: (e["approved_by"], e["date"]) for e in self.t.yaml("approvals.yaml")["fuzz_targets"]}
        self.assertEqual(by, {APPROVED: ("approver", "2026-10-20"), UNAPPROVED: ("bob", "2026-10-25")})
        with open(path, "w", encoding="utf-8") as f:
            f.write("%s\treview-2026-10-18\tplain_halts\n" % APPROVED)
        self.assertEqual(approvals.write(self.t.root, path, approved_by="bob", date="2026-10-26", out=io.StringIO()), 0)
        self.assertEqual(self.t.yaml("approvals.yaml")["fuzz_targets"][0]["approved_by"], "bob")

    def test_a_lib_kept_with_unlisted_proofs_is_reported(self):
        self.t.write("proofs/%s/lib/Shared.v" % APPROVED, "Definition one := 1.\n")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        rc, out = self.write("%s\treview-2026-10-18\tubsan_agrees\n" % APPROVED)
        self.assertEqual(rc, 0, out)
        self.assertIn(release_tree.PARTIAL % APPROVED, out)

    def test_a_tab_with_no_record_writes_nothing(self):
        rc, out = self.write("%s\t\n" % APPROVED)
        self.assertEqual(rc, 1, out)
        self.assertIn("an empty field", out)

    def test_a_fourth_field_writes_nothing(self):
        rc, out = self.write("%s\treview-2026-10-18\tubsan_agrees\textra\n" % APPROVED)
        self.assertEqual(rc, 1, out)
        self.assertIn("more than three fields", out)
        self.assertFalse(os.path.exists(self.t.path("approvals.yaml")))

    def test_an_outdated_approvals_file_does_not_stop_it(self):
        self.t.put_yaml("approvals.yaml", {"schema": "oss-fuzz-theorems/approvals/1",
                                           "fuzz_targets": [{"fuzz_target": APPROVED}]})
        rc, out = self.write("%s\n" % APPROVED)
        self.assertEqual(rc, 0, out)
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_a_list_with_no_proof_at_all_writes_nothing(self):
        rc, out = self.write("json/fuzzer-parse_bjdata\n")
        self.assertEqual(rc, 1, out)
        self.assertFalse(os.path.exists(self.t.path("approvals.yaml")))

    def test_a_target_listed_twice_writes_nothing(self):
        rc, out = self.write("%s\n%s\n" % (APPROVED, APPROVED))
        self.assertEqual(rc, 1, out)
        self.assertIn("listed twice", out)
        self.assertFalse(os.path.exists(self.t.path("approvals.yaml")))

    def test_a_name_that_is_no_fuzz_target_writes_nothing(self):
        rc, out = self.write("%s\nzlib/no_such_fuzzer\n" % APPROVED)
        self.assertEqual(rc, 1, out)
        self.assertIn("'zlib/no_such_fuzzer' is not an included fuzz target", out)
        self.assertFalse(os.path.exists(self.t.path("approvals.yaml")))

    def test_a_record_line_and_a_bare_line_write_an_entry_each(self):
        rc, out = self.write("%s\n%s\treview-2026-10-18\tubsan_agrees\n" % (APPROVED, APPROVED))
        self.assertEqual(rc, 0, out)
        self.assertNotIn("does not cover", out)
        self.assertEqual(self.t.yaml("approvals.yaml")["fuzz_targets"], [
            {"fuzz_target": APPROVED, "statements": ["ubsan_agrees"], "approved_by": "approver", "date": "2026-10-20",
             "origin": "submission", "record": "review-2026-10-18"},
            {"fuzz_target": APPROVED, "statements": ["plain_halts"], "approved_by": "approver", "date": "2026-10-20",
             "origin": "this-repository"}])
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_two_records_with_disjoint_statements(self):
        rc, out = self.write("%s\treview-b\tubsan_agrees\n%s\treview-a\tplain_halts\n" % (APPROVED, APPROVED))
        self.assertEqual(rc, 0, out)
        self.assertEqual([(e["record"], e["statements"]) for e in self.t.yaml("approvals.yaml")["fuzz_targets"]],
                         [("review-a", ["plain_halts"]), ("review-b", ["ubsan_agrees"])])

    def test_two_records_covering_one_statement_write_nothing(self):
        rc, out = self.write("%s\treview-a\tplain_halts\n%s\treview-b\tplain_halts,ubsan_agrees\n"
                             % (APPROVED, APPROVED))
        self.assertEqual(rc, 1, out)
        self.assertIn("%s: plain_halts covered by two records" % APPROVED, out)
        self.assertFalse(os.path.exists(self.t.path("approvals.yaml")))

    def test_one_record_twice_writes_nothing(self):
        rc, out = self.write("%s\treview-a\tplain_halts\n%s\treview-a\tubsan_agrees\n" % (APPROVED, APPROVED))
        self.assertEqual(rc, 1, out)
        self.assertIn("%s is listed twice with record review-a" % APPROVED, out)

    def test_a_record_line_with_no_proof_is_reported(self):
        rc, out = self.write("%s\n%s\treview-a\tasan_halts\n" % (APPROVED, APPROVED))
        self.assertEqual(rc, 0, out)
        self.assertIn("listed, no proof yet: %s, record review-a" % APPROVED, out)
        self.assertIn("1 line(s) with no proof yet", out)
        self.assertEqual([e["origin"] for e in self.t.yaml("approvals.yaml")["fuzz_targets"]], ["this-repository"])

    def test_a_bare_line_with_nothing_outside_the_records_is_reported(self):
        # UNAPPROVED has a proof of ubsan_agrees only, which the record line takes
        rc, out = self.write("%s\treview-a\tubsan_agrees\n%s\n" % (UNAPPROVED, UNAPPROVED))
        self.assertEqual(rc, 0, out)
        self.assertIn("listed, no proof yet: %s\n" % UNAPPROVED, out)
        self.assertIn("1 line(s) with no proof yet", out)
        self.assertEqual([e["origin"] for e in self.t.yaml("approvals.yaml")["fuzz_targets"]], ["submission"])

    def test_approver_and_date_are_kept_per_source(self):
        listing = "%s\treview-2026-10-18\tubsan_agrees\n%s\n" % (APPROVED, APPROVED)
        self.assertEqual(self.write(listing)[0], 0)
        add_proof(self.t, APPROVED + "/asan_halts")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        path = self.t.path("..", "launch.txt")
        rc = approvals.write(self.t.root, path, approved_by="bob", date="2026-10-25", out=io.StringIO())
        self.assertEqual(rc, 0)
        by = {(e["origin"], tuple(e["statements"])): (e["approved_by"], e["date"])
              for e in self.t.yaml("approvals.yaml")["fuzz_targets"]}
        self.assertEqual(by, {("submission", ("ubsan_agrees",)): ("approver", "2026-10-20"),
                              ("this-repository", ("asan_halts", "plain_halts")): ("bob", "2026-10-25")})



class WrittenHere(unittest.TestCase):
    """A build record whose proofs.origin names a package says which of its proofs were written here, and
    approvals.yaml lists each statement under the source that record gives it."""

    def setUp(self):
        self.t = Tree()
        self.addCleanup(self.t.close)
        add_proof(self.t, APPROVED + "/plain_halts")
        add_proof(self.t, APPROVED + "/ubsan_agrees")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)

    def record(self, origin, written_here=None, ok=True):
        proofs = {"origin": origin}
        if written_here is not None:
            proofs["written_here"] = written_here
        self.t.write("proofs/%s/provenance/PROVENANCE.yaml" % APPROVED, build_record(proofs=proofs))
        rc = self.t.generate()
        self.assertEqual(rc == 0, ok, self.t.last_output)

    def msgs(self):
        return [f.msg for f in self.t.lint()]

    def test_a_package_record_with_written_here_and_an_entry_per_source(self):
        self.record(PACKAGE, ["plain_halts"])
        approve(self.t, entry(APPROVED, statements=["ubsan_agrees"], origin="submission", record="final-package"),
                entry(APPROVED, statements=["plain_halts"]))
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_this_repository_may_list_only_what_written_here_names(self):
        self.record(PACKAGE, ["plain_halts"])
        approve(self.t, entry(APPROVED, statements=["plain_halts", "ubsan_agrees"]))
        self.assertIn("approvals.fuzz_targets[0]: %s/ubsan_agrees: the build record says the proofs of this fuzz target "
                      "came from a package and "
                      "proofs.written_here does not name it, so a this-repository entry may not list it" % APPROVED,
                      self.msgs())

    def test_a_submission_may_list_none_of_them(self):
        self.record(PACKAGE, ["plain_halts"])
        approve(self.t, entry(APPROVED, statements=["plain_halts"], origin="submission", record="final-package"))
        self.assertIn("approvals.fuzz_targets[0]: %s/plain_halts: the build record says the proofs of this fuzz target "
                      "came from a package and "
                      "proofs.written_here names it, so a submission entry may not list it" % APPROVED, self.msgs())

    def test_written_here_without_a_package_origin(self):
        self.record("written in this repository", ["plain_halts"], ok=False)
        approve(self.t, entry(APPROVED))
        self.assertIn("proofs.written_here: proofs.origin names no package, so every proof of %s was written here "
                      "and none is singled out" % APPROVED, self.msgs())

    def test_a_package_record_without_written_here_lists_nothing_as_ours(self):
        self.record(PACKAGE)
        approve(self.t, entry(APPROVED, statements=["plain_halts"]))
        self.assertIn("approvals.fuzz_targets[0]: %s/plain_halts: the build record says the proofs of this fuzz target "
                      "came from a package and "
                      "proofs.written_here does not name it, so a this-repository entry may not list it" % APPROVED,
                      self.msgs())
        approve(self.t, entry(APPROVED, statements=["plain_halts"], origin="submission", record="final-package"))
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_a_real_shaped_package_origin_is_a_package(self):
        self.assertIn("\n", PACKAGE)
        self.record(PACKAGE, ["plain_halts"])
        approve(self.t, entry(APPROVED, statements=["ubsan_agrees"]))
        self.assertIn("approvals.fuzz_targets[0]: %s/ubsan_agrees: the build record says the proofs of this fuzz target "
                      "came from a package and proofs.written_here does not name it, so a this-repository entry may "
                      "not list it" % APPROVED, self.msgs())

    def test_a_contribution_naming_the_package_later_imposes_nothing(self):
        self.record(CONTRIBUTED)
        approve(self.t, entry(APPROVED, statements=["plain_halts", "ubsan_agrees"]))
        self.assertEqual([str(f) for f in self.t.lint()], [])
        approve(self.t, entry(APPROVED, statements=["plain_halts", "ubsan_agrees"], origin="submission",
                              record="oss-verify-proofs-pull-3"))
        self.assertEqual([str(f) for f in self.t.lint()], [])
        self.record(CONTRIBUTED, ["plain_halts"], ok=False)
        self.assertIn("proofs.written_here: proofs.origin names no package, so every proof of %s was written here "
                      "and none is singled out" % APPROVED, self.msgs())

    def test_written_here_names_a_statement_of_the_fuzz_target(self):
        self.record(PACKAGE, ["plain_halt"], ok=False)
        self.assertIn("proofs.written_here: plain_halt is not a statement of %s" % APPROVED, self.msgs())

    def test_written_here_must_be_a_list_of_names(self):
        self.record(PACKAGE, "plain_halts", ok=False)
        self.assertIn("proofs.written_here must be a list of statement names", self.msgs())



class ToolsProblems(unittest.TestCase):
    """release_tree.tools_problems: whether tools/oft may be published on its own, as the runner image publishes it
    (.github/workflows/images.yml)."""

    def setUp(self):
        self.t = Tree()
        self.addCleanup(self.t.close)
        self.t.write("tools/oft/README.md", "The tools.\n")
        self.t.write("tools/other/notes.md", "Elsewhere under tools/.\n")

    def problems(self):
        return release_tree.tools_problems(facts.load(self.t.root))

    def test_the_fixture_tools_may_be_published(self):
        self.assertEqual(self.problems(), [])

    def test_a_private_fuzz_target_named_under_tools_oft_is_refused_and_elsewhere_is_not(self):
        make_private(self.t, "json")
        self.t.write("docs/notes.md", "see json/fuzzer-parse_bjdata\n")
        self.t.write("tools/other/notes.md", "see json/fuzzer-parse_bjdata\n")
        self.assertEqual(self.problems(), [])
        self.t.write("tools/oft/README.md", "see json/fuzzer-parse_bjdata\n")
        self.assertEqual(self.problems(), ["tools/oft/README.md names json/fuzzer-parse_bjdata, a fuzz target of held project json"])

    def test_a_private_fuzz_target_named_by_a_path_under_tools_oft_is_refused(self):
        make_private(self.t, "json")
        rocq = facts.load(self.t.root).projects["json"].harnesses["fuzzer-parse_bjdata"].data["rocq"]
        self.t.write("tools/oft/tests/fixtures/%s.txt" % rocq, "x\n")
        got = self.problems()
        self.assertEqual(len(got), 1, got)
        self.assertTrue(got[0].startswith("tools/oft/tests/fixtures/%s.txt names " % rocq), got)

    def test_a_holding_finding_named_under_tools_oft_is_refused(self):
        add_findings(self.t)
        make_private(self.t, "zlib")
        self.t.write("tools/oft/README.md", "fixed stand-in-abort\n")
        self.assertTrue(any(p.startswith("tools/oft/README.md names stand-in-abort, the slug of finding")
                            for p in self.problems()), self.problems())

    def test_a_project_a_finding_holds_back_is_searched_for_whether_or_not_it_is_private(self):
        """The cut holds a project a finding holds back whole, so tools/oft must not name it either."""
        add_findings(self.t)
        self.assertEqual(self.problems(), [])
        self.t.write("tools/oft/README.md", "see zlib/checksum_fuzzer\n")
        self.assertEqual(self.problems(), ["tools/oft/README.md names zlib/checksum_fuzzer, a fuzz target of held "
                                           "project zlib"])

    def test_facts_with_an_error_are_refused(self):
        self.t.write("projects/zlib/project.yaml", "status: [\n", "a")
        got = self.problems()
        self.assertTrue(got and all(p.startswith("the facts have an error") for p in got), got)

    def test_a_file_at_an_ignored_path_under_tools_oft_is_refused_and_elsewhere_is_not(self):
        self.t.write("tools/oft/_build/stale.txt", "x\n")
        self.t.write("docs/_build/page.html", "built\n")
        self.assertEqual(self.problems(), ["tools/oft/_build: an ignored path, so it is not read, and a copy of "
                                           "tools/oft takes it",
                                           "tools/oft/_build/stale.txt: an ignored path, so it is not read, and a copy "
                                           "of tools/oft takes it"])

    def other(self, stack):
        """A checkout of its own, with a tools/oft and a file outside it, as the public repository's is."""
        root = stack.enter_context(tempfile.TemporaryDirectory())
        os.makedirs(os.path.join(root, "tools", "oft"))
        os.makedirs(os.path.join(root, "docs"))
        self.write_to(root, "docs/notes.md", "see json/fuzzer-parse_bjdata\n")
        self.write_to(root, "tools/oft/README.md", "The tools.\n")
        return root

    @staticmethod
    def write_to(root, rel, text):
        path = os.path.join(root, *rel.split("/"))
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as f:
            f.write(text)

    def test_another_checkout_s_tools_oft_is_judged_by_this_tree_s_facts(self):
        # images.yml: the runner carries the public repository's tools/oft, judged by this repository's facts
        make_private(self.t, "json")
        rocq = facts.load(self.t.root).projects["json"].harnesses["fuzzer-parse_bjdata"].data["rocq"]
        # this tree's own tools/oft holds every problem; none of them may be reported for another checkout
        self.t.write("tools/oft/README.md", "see json/fuzzer-parse_bjdata\n")
        self.t.write("tools/oft/tests/fixtures/%s.txt" % rocq, "x\n")
        self.t.write("tools/oft/_build/stale.txt", "x\n")
        with contextlib.ExitStack() as stack:
            other = self.other(stack)
            self.assertEqual(release_tree.tools_problems(facts.load(self.t.root), checkout=other), [])
            # each rule reads the other checkout: its bytes, its paths, and an ignored path in it
            self.write_to(other, "tools/oft/README.md", "see json/fuzzer-parse_bjdata\n")
            self.write_to(other, "tools/oft/tests/fixtures/%s.txt" % rocq, "x\n")
            self.write_to(other, "tools/oft/_build/stale.txt", "x\n")
            self.assertEqual(release_tree.tools_problems(facts.load(self.t.root), checkout=other), [
                "tools/oft/README.md names json/fuzzer-parse_bjdata, a fuzz target of held project json",
                "tools/oft/tests/fixtures/%s.txt names OssFuzzTheorems.json.fuzzer_parse_bjdata, the Rocq module of "
                "held fuzz target json/fuzzer-parse_bjdata" % rocq,
                "tools/oft/_build: an ignored path, so it is not read, and a copy of tools/oft takes it",
                "tools/oft/_build/stale.txt: an ignored path, so it is not read, and a copy of tools/oft takes it",
            ])

if __name__ == "__main__":
    unittest.main()
