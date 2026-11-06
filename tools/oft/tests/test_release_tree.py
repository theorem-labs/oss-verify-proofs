"""`oft release-tree`, `oft approvals` and approvals.yaml: a release carries the approved proofs and no other, no
findings, and only the held form of a project a finding holds back; a tree ported to the per-project layout cuts to the
same release."""
import ast
import contextlib
import csv
import io
import os
import re
import shutil
import subprocess
import tempfile
import unittest

import yaml

from oft import approvals, disclosure, facts, generate, layout, lint, paths, port, release_tree, rules, yamlio
from oft.tests.helpers import (OTHER_OWN_RECIPE, REPO, Tree, add_findings, build_record, own_recipe, public_patch,
                               recipe_file, rules_of)
from oft.tests.test_oss_verify import add_standin

# a recipe file name as the disclosure search reads a name (escapes decoded, case folded, every dash read as `_`)
RECIPE_NAME = re.compile(r"recipe(_[0-9]+)?\.tar\.zst")


def recipe_names(data):
    """The recipe file names that the bytes data spell, in each reading the disclosure search makes of them."""
    return {m.group() for t in disclosure._readings(data)
            for m in RECIPE_NAME.finditer(disclosure._name_text(disclosure._decoded(t)))}


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


# the block of an entry the enrollment merge watcher writes: the merge of the project's enrollment pull request on the
# OSS Verify port, which approves the proofs of its fuzz targets (the approvals plan)
MERGE = {"pull_request": "https://github.com/theorem-labs/oss-verify/pull/41", "merged_by": "approver",
         "merged_at": "2026-10-29T17:04:11Z", "merge_commit": "5e" * 20}


def enrolled(unit, statements=("plain_halts",), **merge):
    """An entry from an enrollment merge: the statements its enrollment facts pull requests wrote (a ceiling), and
    MERGE with merge's fields in place of its own."""
    return entry(unit, statements, origin="enrollment", enrollment=dict(MERGE, **merge))



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


def port_tree(t):
    """oft port-layout over t, then its rendering, as L2 moves the tree and renders it again."""
    assert port.port_worktree(t.root, out=io.StringIO()) == 0
    assert t.generate() == 0, t.last_output


def ported_copy(test, t):
    """A copy of t ported to the per-project layout (port_tree), as a Tree of its own that the test closes."""
    u = Tree(render=False)
    test.addCleanup(u.close)
    shutil.rmtree(u.root)
    shutil.copytree(t.root, u.root, symlinks=True)
    port_tree(u)
    return u


def outside_keys(rel):
    """Whether rel is a generated file that no content key reads (README.md files, index/, analyses/): each names the
    folders of its own tree's layout, and the layout move renders it again."""
    return paths.is_gen(rel) and (rel.split("/")[0] in ("index", "analyses") or rel.rsplit("/", 1)[-1] == "README.md")


def a_finding(rel):
    """Whether rel, a per-project path, is a file of a fuzz target's findings or a project's unpatched.yaml."""
    parts = rel.split("/")
    return parts[0] == "projects" and ((len(parts) > 4 and parts[3] == "findings")
                                       or (len(parts) == 3 and parts[2] == "unpatched.yaml"))


def assert_ported_cut(test, t):
    """oft release-tree cuts t, and a copy of it ported to the per-project layout (ported_copy), to the same release:
    the ported cut holds each file of the old cut where layout.canonical puts it, with the same bytes, but a generated
    file outside every key (outside_keys), which only has the same path; beside them it holds the barrier dune of each
    proofs and counterexamples folder the cut keeps, which only the per-project layout has; and neither cut keeps a
    finding."""
    u = ported_copy(test, t)
    for tree in (t, u):
        rc, out = release(tree)
        test.assertEqual(rc, 0, out)
    old, new = snapshot(t), snapshot(u)
    moved = {layout.canonical(rel): data for rel, data in old.items()}
    barriers = {"/".join(rel.split("/")[:4] + ["dune"]) for rel in moved
                if rel.split("/")[0] == "projects" and len(rel.split("/")) > 4
                and rel.split("/")[3] in ("proofs", "counterexamples")}
    test.assertEqual(sorted(new), sorted(set(moved) | barriers))
    test.assertEqual({rel: new[rel] for rel in barriers}, {rel: generate.barrier_dune().encode() for rel in barriers})
    test.assertEqual({rel: data for rel, data in new.items() if rel not in barriers and not outside_keys(rel)},
                     {rel: data for rel, data in moved.items() if not outside_keys(rel)})
    test.assertEqual([rel for rel in moved if a_finding(rel) or rel.split("/")[0] == "findings"], [])
    test.assertEqual([rel for rel in new if layout.of_path(rel) == layout.OLD], [])


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

    def test_the_counterexamples_stay(self):
        approve(self.t, APPROVED)
        cx = "counterexamples/json/fuzzer-parse_bjdata/plain_halts"
        self.assertTrue(os.path.isdir(self.t.path(cx)))
        self.assertEqual(release(self.t)[0], 0)
        self.assertTrue(os.path.isdir(self.t.path(cx)))
        self.assertEqual(index_status(self.t)["json/fuzzer-parse_bjdata/plain_halts"], "counterexample")

    def test_a_ported_tree_cuts_to_the_ported_cut(self):
        """canonical(cut(old)) == cut(ported), as assert_ported_cut compares them, for a checkout with an approved proof,
        an unapproved proof of the same fuzz target and a fuzz target with none approved, the proof library and build
        record of each, a counterexample, and a finding that holds nothing back."""
        add_proof(self.t, APPROVED + "/ubsan_agrees")
        for u in (APPROVED, UNAPPROVED):
            self.t.write("proofs/%s/provenance/PROVENANCE.yaml" % u, build_record())
        add_findings(self.t)
        # public, with the patches entry that ships its patch, as a release has it (helpers.public_patch)
        public_patch(self.t)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, APPROVED)
        self.assertEqual(facts.hold(facts.load(self.t.root)), facts.Hold(set(), set(), {}))
        assert_ported_cut(self, self.t)

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
        # unpatched binaries `oft fetch --findings` unpacked into a checkout (untracked; a released project's too)
        self.t.write("projects/json/unpatched-bin/fuzzer-parse_bjdata/fuzzer-parse_bjdata.plain", "\x7fELF stand-in")
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.exists(self.t.path("findings")))
        self.assertFalse(os.path.exists(self.t.path("projects/json/unpatched-bin")))
        self.assertEqual(sorted(os.listdir(self.t.path("projects", "zlib"))), ["README.md", "project.yaml"])
        self.assertEqual(self.t.yaml("projects/zlib/project.yaml")["status"], "held")
        self.assertIn("removed findings/ and projects/json/unpatched-bin/ and approvals.yaml", out)
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

    def test_a_file_under_proofs_lib_is_refused(self):
        """No row admits proofs/lib/, and port-layout gives it no place, so no release carries it."""
        approve(self.t, APPROVED)
        self.t.write("proofs/lib/Common.v", "Definition zero := 0.\n")
        self.assertRefused("error: proofs/lib/Common.v: a file a release cannot carry there")

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

    def test_a_private_projects_own_recipe_leaves_no_trace_in_the_cut(self):
        """A private project's own recipe (a draft asset of this repository, which release.yaml does not list) is no
        fact of the release: its release tag, file name and sha256 are in no file of the cut, and the cut's counts
        are recounted without the project."""
        own_recipe(self.t, "json", OTHER_OWN_RECIPE, "proofs/json/fuzzer-parse_bjdata/provenance/PROVENANCE.yaml")
        traces = (OTHER_OWN_RECIPE["release"].encode(), OTHER_OWN_RECIPE["file"].encode(),
                  OTHER_OWN_RECIPE["sha256"].encode())
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, APPROVED)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        before = self.t.yaml("release.yaml")["counts"]
        self.assertTrue(any(traces[1] in data for data in snapshot(self.t).values()))
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        for rel, data in snapshot(self.t).items():
            for trace in traces:
                self.assertNotIn(trace, data, rel)
        r = self.t.yaml("release.yaml")
        self.assertEqual(r["counts"], {"projects": 5, "available": 1, "harnesses": 2, "binaries": 8})
        self.assertNotEqual(r["counts"], before)
        self.assertEqual(self.t.generate(check=True), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_shipped_text_that_names_a_private_projects_own_recipe_is_refused(self):
        """A kept file that names a private project's own recipe, by its SHA-256, its file name or its release tag (one
        no fact the release keeps names), is refused: the cut would publish what the project keeps private. The
        negative control: the release's own tag names no held recipe, so a file that names it is cut."""
        own_recipe(self.t, "json", OTHER_OWN_RECIPE, "proofs/json/fuzzer-parse_bjdata/provenance/PROVENANCE.yaml")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, APPROVED)
        sha, file, tag = OTHER_OWN_RECIPE["sha256"], OTHER_OWN_RECIPE["file"], OTHER_OWN_RECIPE["release"]
        for rel, needle, data in (("CHANGELOG.md", sha, "Built with the recipe %s.\n" % sha),
                                  ("docs/notes.md", file, "see %s\n" % file),
                                  ("notes/zlib.md", tag, "attached to %s\n" % tag)):
            with self.subTest(rel=rel):
                self.t.write(rel, data.encode(), mode="wb")
                self.assertRefused("error: %s names %s, " % (rel, needle))
                os.remove(self.t.path(rel))
        own_tag = "v%s-src" % self.t.yaml("release.yaml")["release"]
        self.t.write("docs/notes.md", ("attached to %s\n" % own_tag).encode(), mode="wb")
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertIn(own_tag, self.t.read("docs/notes.md"))

    def test_no_shipped_file_names_a_recipe_file_a_private_project_could_pin(self):
        """The cut ships tools/ (but tools/enroll/) and docs/ of this repository, the tests and their fixtures among
        them, and refuses a kept file that names a held project's own recipe file.  So none of them may name a recipe
        file other than one release.yaml lists, which no private project may take (rules.py): the fixtures build the
        names of theirs at run time (helpers.recipe_file).  The control: a file naming a recipe file that a held
        project pins is found by the same reading, and the cut's own needles refuse it."""
        own_recipe(self.t, "json", dict(OTHER_OWN_RECIPE, file=recipe_file(7)),
                   "proofs/json/fuzzer-parse_bjdata/provenance/PROVENANCE.yaml")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        control = ("see %s\n" % recipe_file(7)).encode()
        self.assertEqual(recipe_names(control), {recipe_file(7).replace("-", "_")})
        tree = facts.load(self.t.root)
        self.assertTrue(disclosure.found("docs/control.md", control, disclosure.needles(tree, facts.hold(tree))))
        with open(os.path.join(REPO, "release.yaml"), encoding="utf-8") as f:
            r = yaml.safe_load(f)
        listed = {x["file"].replace("-", "_") for x in (r.get("recipes") or [r.get("recipe") or {"file": ""}])}
        named = {}
        for top in ("tools", "docs"):
            for dp, dns, fns in os.walk(os.path.join(REPO, top)):
                rel = os.path.relpath(dp, REPO).replace(os.sep, "/")
                dns[:] = [d for d in dns if d != "__pycache__" and "%s/%s" % (rel, d) != "tools/enroll"]
                for fn in fns:
                    with open(os.path.join(dp, fn), "rb") as fh:
                        extra = recipe_names(fh.read()) - listed
                    if extra:
                        named["%s/%s" % (rel, fn)] = sorted(extra)
        self.assertEqual(named, {})

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
        # the two runs' workflows, the ones that start its redo runs, the one that re-runs a failed run, the one that
        # starts the approvals runs, and the scripts they all run
        pipeline = (".github/workflows/enroll.yml", ".github/workflows/enroll-build.yml",
                    ".github/workflows/facts-refresh.yml", ".github/workflows/hold-state.yml",
                    ".github/workflows/enroll-retry.yml", ".github/workflows/approvals-watch.yml")
        for path in pipeline:
            self.t.write(path, "name: %s\n" % os.path.basename(path)[:-4])
        self.t.write("tools/enroll/README.md", "# tools/enroll\n")
        self.t.write("tools/enroll/ci/gate.py", "LIMIT = 3\n")
        approve(self.t, APPROVED)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        for gone in pipeline + ("tools/enroll",):
            self.assertFalse(os.path.lexists(self.t.path(gone)), gone)
        self.assertIn("tools/enroll", out)

    def test_the_stream_s_operational_tools_never_ship(self):
        """dev/stream/ runs the OSS Verify stream rather than checks a proof, and names this company's machines,
        buckets and sessions: the cut removes the directory whole, and leaves what a release carries.  This is the
        fact lint.internal_only stands on, so the file here holds the text lint stops reading there."""
        self.t.write("dev/stream/README.md", "# stream\n")
        self.t.write("dev/stream/bin/ossv-tools",
                     "#!/bin/sh\n# runs from /" + "home/someone/src/oss-verifier on box-7.tailnet." + "ts.net\n")
        self.t.write("dev/stream/tests/test_tools.py", "def test_x():\n    assert True\n")
        approve(self.t, APPROVED)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.lexists(self.t.path("dev/stream")))
        self.assertIn("dev/stream", out)
        for kept in ("README.md", "release.yaml", "theories", "projects/%s/harness.yaml" % APPROVED):
            self.assertTrue(os.path.lexists(self.t.path(kept)), kept)

    def test_the_cut_completes_on_a_tree_holding_a_lane_link(self):
        """A link inside a directory the cut removes whole must not refuse the cut before it gets there.

        `checkout_links` runs before `facts.load`, so that no facts path the cut reads can point out of the
        checkout, and it used to walk `dev/stream/` too: with the three mirrored links of
        `dev/stream/lane/tools/` in the tree, `oft release-tree` printed "a symbolic link ... nothing changed"
        and exited 1, so the first release cut from a main carrying them would have failed, and no CI job runs
        this tool over the tree to say so (the review of pull request 669, B1).  A completing cut is the
        assertion; `shutil.rmtree` unlinks such a child rather than following it.
        """
        self.t.write("dev/stream/README.md", "# stream\n")
        self.t.write("dev/stream/lane/tools/cb-90203d09.sh", "#!/bin/sh\necho cb\n")
        os.symlink("cb-90203d09.sh", self.t.path("dev/stream/lane/tools/cb"))
        approve(self.t, APPROVED)
        self.assertEqual(release_tree.checkout_links(self.t.root), [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.lexists(self.t.path("dev/stream")))
        self.assertIn("dev/stream", out)

    def test_a_link_at_the_cut_itself_still_refuses_the_cut(self):
        """The entry is gated even though its contents are not: rmtree would follow a link AT dev/stream."""
        self.t.write("dev/stream-live/README.md", "# the tree the link names\n")
        os.symlink("dev/stream-live", self.t.path("dev/stream"))
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 1, out)
        self.assertIn("dev/stream: a symbolic link", out)

    def test_a_lane_link_under_a_cut_entry_written_with_its_trailing_slash_is_accepted(self):
        """INTERNAL writes a directory with its trailing / (dev/stream/, as INTERNAL in paths.py does), and a file
        inside it is inside the cut whatever the entry's last character: compared as `entry + "/"`, dev/stream/ became
        dev/stream//, no path was inside any directory entry, and the lane link under dev/stream/lane/ refused the
        whole cut.  Every directory entry of INTERNAL is checked, not only dev/stream/."""
        directories = [e for e in release_tree.INTERNAL if e.endswith("/")]
        self.assertIn("dev/stream/", directories)
        for entry in directories:
            with self.subTest(entry=entry):
                self.assertTrue(release_tree._inside_a_cut(entry + "lane/tools/cb"), entry)
                self.assertFalse(release_tree._inside_a_cut(entry.rstrip("/")), entry)
        self.t.write("dev/stream/lane/tools/cb-90203d09.sh", "#!/bin/sh\necho cb\n")
        os.symlink("cb-90203d09.sh", self.t.path("dev/stream/lane/tools/cb"))
        self.t.write("tools/publish/x/cb-1.sh", "#!/bin/sh\necho cb\n")
        os.symlink("cb-1.sh", self.t.path("tools/publish/x/cb"))
        approve(self.t, APPROVED)
        self.assertEqual(release_tree.checkout_links(self.t.root), [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        for gone in ("dev/stream", "tools/publish"):
            self.assertFalse(os.path.lexists(self.t.path(gone)), gone)

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

    def test_the_publishing_files_never_ship_and_never_refuse_the_cut(self):
        """tools/publish/ holds what the scanner looks for, a private project's fuzz target among it: the cut removes
        the directory whole, with the publishing workflows, and does not read it for what is held back."""
        make_private(self.t, "json")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, APPROVED)
        planted = {"tools/publish/needles.txt": "json/fuzzer-parse_bjdata\ninternal-codename\n",
                   "tools/publish/tests/test_scan.py": "NEEDLE = 'json/fuzzer-parse_bjdata'\n",
                   ".github/workflows/publish.yml": "name: publish  # json/fuzzer-parse_bjdata\n",
                   ".github/workflows/publish-gate.yml": "name: publish-gate\n",
                   ".github/workflows/publish-request.yml": "name: publish-request  # json/fuzzer-parse_bjdata\n"}
        for rel, text in planted.items():
            self.t.write(rel, text)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        for gone in ("tools/publish", ".github/workflows/publish.yml", ".github/workflows/publish-gate.yml",
                     ".github/workflows/publish-request.yml"):
            self.assertFalse(os.path.lexists(self.t.path(gone)), gone)
        self.assertIn("tools/publish/", out)
        for rel, data in snapshot(self.t).items():
            self.assertNotIn(b"internal-codename", data, rel)
            self.assertNotIn(b"fuzzer-parse_bjdata", data, rel)
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_a_symbolically_linked_internal_directory_is_refused(self):
        approve(self.t, APPROVED)
        os.makedirs(self.t.path("..", "elsewhere"))
        os.makedirs(self.t.path("tools"), exist_ok=True)
        os.symlink(os.path.join("..", "..", "elsewhere"), self.t.path("tools", "publish"))
        self.assertRefused("error: tools/publish: a symbolic link")
        self.assertTrue(os.path.isdir(self.t.path("..", "elsewhere")))

    def test_every_internal_path_is_one_the_cut_removes(self):
        # the cut's list is paths.py's, then the skill directories paths.py does not name, written out
        # (test_the_release_gate_reads_every_internal_path_from_release_tree_py)
        self.assertEqual(vars(release_tree)["INTERNAL"], vars(paths)["INTERNAL"] + release_tree.SKILLS)
        self.assertEqual(release_tree.SKILLS, (".claude/skills/porting-released-proofs/",
                                               ".claude/skills/clean-room-restatement/"))
        # each is a directory lint alone admits files under (lint.LINT_ONLY_HAND), and paths.py classifies nothing there
        for d in release_tree.SKILLS:
            self.assertTrue(any(p.startswith(d) for p in lint.LINT_ONLY_HAND), d)
            self.assertFalse(paths.is_internal(d + "SKILL.md"), d)
            self.assertEqual(paths.classify(d + "SKILL.md"), [], d)
        self.assertEqual(set(vars(paths)["INTERNAL"]), {
            "approvals.yaml", ".github/CODEOWNERS", ".github/workflows/facts-review.yml",
            ".claude/skills/review-facts/SKILL.md", "review.md", ".github/workflows/enroll.yml",
            ".github/workflows/enroll-build.yml", ".github/workflows/facts-refresh.yml",
            ".github/workflows/hold-state.yml", ".github/workflows/enroll-retry.yml",
            ".github/workflows/approvals-watch.yml", "tools/enroll/", ".github/workflows/proof-index.yml",
            ".github/proof-index.py", ".github/workflows/proof-index-trigger.yml", ".github/workflows/index.yml",
            ".github/workflows/publish-request.yml", ".github/workflows/publish.yml",
            ".github/workflows/publish-gate.yml", "tools/publish/", "tools/oft/ci/regenerate-shared.sh",
            "tools/oft/tests/test_regenerate_shared.py", "tools/oft/ci/prove-pr", "tools/oft/tests/test_prove_pr.py",
            "changes/", "docs/reference/", "dev/stream/"})
        for rel in ("approvals.yaml", ".github/CODEOWNERS", "review.md", ".github/workflows/index.yml",
                    ".github/workflows/publish-request.yml", "tools/publish/x", "tools/publish/a/b",
                    "tools/enroll/ci/gate.py", "tools/publish"):
            self.assertTrue(paths.is_internal(rel), rel)
            # one row, of the internal class: the class and INTERNAL's rows are one list
            self.assertEqual([cls for cls, _, _ in paths.classify(rel)], ["internal"], rel)
        # a file of INTERNAL_FILES keeps the one row of the directory it lies in
        for rel in vars(paths)["INTERNAL_FILES"]:
            self.assertTrue(paths.is_internal(rel), rel)
            self.assertEqual(len(paths.classify(rel)), 1, rel)
            self.assertNotIn("internal", [cls for cls, _, _ in paths.classify(rel)], rel)
        # a file under INTERNAL_DIRS keeps its own row too (hand), which lint reads it by
        for rel in ("changes/1/journal.md", "docs/reference/README.md", "dev/stream/bin/ossv-tools"):
            self.assertTrue(paths.is_internal(rel), rel)
            self.assertEqual([cls for cls, _, _ in paths.classify(rel)], ["hand"], rel)
        for rel in ("tools/publisher", "tools/enrollment/x", "tools/oft/paths.py", ".github/workflows/pr.yml",
                    "approvals.yaml.bak", "tools/oft/ci/regenerate-shared.sh.bak", "tools/oft/ci/check-units.sh"):
            self.assertFalse(paths.is_internal(rel), rel)
            self.assertNotIn("internal", [cls for cls, _, _ in paths.classify(rel)], rel)

    def test_the_release_gate_reads_every_internal_path_from_release_tree_py(self):
        """The release gate's R17 row (a published tree is a release-tree cut) reads release_tree.py's INTERNAL from its
        syntax tree: an assignment of a literal tuple of strings, never an import, which it skips without a word. Its
        loop, replayed here on this file, reads every path of paths.py's INTERNAL and of SKILLS and finds nothing it cannot
        read."""
        with open(release_tree.__file__, encoding="utf-8") as f:
            body = ast.parse(f.read()).body
        names, unread = set(), []
        for node in body:
            targets = node.targets if isinstance(node, ast.Assign) else [node.target] if isinstance(
                node, (ast.AnnAssign, ast.AugAssign)) else []
            if not any(isinstance(t, ast.Name) and t.id == "INTERNAL" for t in targets):
                continue
            try:
                value = ast.literal_eval(node.value) if not isinstance(node, ast.AugAssign) and node.value else None
            except (ValueError, TypeError, SyntaxError, RecursionError, MemoryError):
                value = None
            if isinstance(value, (tuple, list)) and all(isinstance(x, str) for x in value):
                names |= set(value)
            else:
                unread.append(node.lineno)
        self.assertEqual((names, unread), (set(vars(paths)["INTERNAL"] + release_tree.SKILLS), []))
        # and no import binds the name, which the gate would not read
        self.assertEqual([n.lineno for n in body if isinstance(n, ast.ImportFrom)
                          and any((a.asname or a.name) == "INTERNAL" for a in n.names)], [])

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

    def test_a_stray_file_in_a_per_project_proofs_folder_is_refused(self):
        """Beside the statement directories only the generated dune file may be; in a kept statement directory only
        STATEMENT_FILES."""
        approve(self.t, APPROVED)
        port_tree(self.t)
        for rel in ("projects/%s/proofs/STRAY.v" % APPROVED, "projects/%s/proofs/plain_halts/Extra.v" % APPROVED):
            self.t.write(rel, "Definition x := 0.\n")
            self.assertRefused("error: %s: a file a release cannot carry there" % rel)
            os.remove(self.t.path(rel))

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

    def test_a_stale_shared_file_does_not_stop_the_cut(self):
        """The shared generated files are the line's render's, so a line commit may carry a stale one; the cut's own
        final render writes them."""
        approve(self.t, APPROVED)
        self.t.write("index/statements.tsv", "stale\n")
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.t.generate(check=True), 0, self.t.last_output)

    def test_the_render_of_the_line_is_not_published(self):
        """release_tree.INTERNAL names index.yml and its script: a release has no line to render, and the public
        repository must not run the render on its own main."""
        internal = (".github/workflows/index.yml", "tools/oft/ci/regenerate-shared.sh")
        for rel in internal:
            self.t.write(rel, "# the render\n")
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        for rel in internal:
            self.assertFalse(os.path.lexists(self.t.path(rel)), rel)
            self.assertIn(rel, out)

    def test_the_change_ledgers_are_not_published(self):
        """release_tree.INTERNAL names changes/: a change's sessions, costs and journal (oft change-ledger) are this
        repository's own records, and no release carries them."""
        for rel in ("changes/libreac-35/sessions.tsv", "changes/libreac-35/ledger.tsv", "changes/tools/journal.md"):
            self.t.write(rel, "step\n")
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.lexists(self.t.path("changes")))
        self.assertIn("changes", out)

    def test_the_prove_job_s_script_and_its_test_are_not_published(self):
        """release_tree.INTERNAL names tools/oft/ci/prove-pr and its test: pr.yml's prove job posts this repository's
        pull request checks with it, and the public repository's pr.yml, which finds no such script, posts none."""
        internal = ("tools/oft/ci/prove-pr", "tools/oft/tests/test_prove_pr.py")
        for rel in internal:
            self.t.write(rel, "# theorem prove on a pull request\n")
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        for rel in internal:
            self.assertFalse(os.path.lexists(self.t.path(rel)), rel)
            self.assertIn(rel, out)

    def test_the_reference_book_is_not_published(self):
        """release_tree.INTERNAL names docs/reference/: the worker briefs and the rules a proof's author follows are
        written for the people and agents who prove, and no release carries them.  Its paths row stays, so lint
        reads the pages while they are here."""
        for rel in ("docs/reference/README.md", "docs/reference/choosing-a-donor.md"):
            self.t.write(rel, "a page\n")
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.lexists(self.t.path("docs/reference")))
        self.assertTrue(os.path.isdir(self.t.path("docs")))
        self.assertIn("docs/reference", out)

    def test_the_moved_skills_are_not_published(self):
        """release_tree.INTERNAL names .claude/skills/porting-released-proofs/ and
        .claude/skills/clean-room-restatement/: the first finds a port's source through unreleased branches and internal
        search tools, the second is the internal method of a clean-room rewrite, and no release carries either.  A
        skill beside them stays."""
        moved = (".claude/skills/porting-released-proofs", ".claude/skills/clean-room-restatement")
        for rel in (moved[0] + "/SKILL.md", moved[0] + "/references/search-tools.md", moved[1] + "/SKILL.md",
                    moved[1] + "/references/sizing-a-programme.md"):
            self.t.write(rel, "a skill\n")
        kept = ".claude/skills/adding-a-proof/SKILL.md"
        self.t.write(kept, "a skill\n")
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        for d in moved:
            self.assertFalse(os.path.lexists(self.t.path(d)), d)
            self.assertIn(d, out)
        self.assertTrue(os.path.isfile(self.t.path(kept)))

    def test_the_streams_operational_tools_are_not_published(self):
        """release_tree.INTERNAL names dev/stream/: the tools that run the stream name this company's machines,
        addresses and private repositories, and link to them, which lint.internal_only lets them do because the cut
        removes the directory before a release.  So the two hold each other up, and this is the cut's half: with a
        real file of that shape in the tree, lint reports nothing and the cut leaves none of it behind.

        Every shape is written in parts, as test_lint.InternalOnly writes them: this file is not under dev/stream/
        and every rule reads it, so the fixture must hold a host path and a private host name that its own source
        does not."""
        tree_path = "/" + "home/someone/work/ovpi"
        box = "box-7.tailnet." + "ts.net"
        tool = ("#!/bin/sh\n"
                "# the stream's own box and the tree it works in\n"
                "ssh %s 'ls %s'\n"
                "curl -fsS https://%s/ready\n" % (box, tree_path, box))
        for rel in ("dev/stream/bin/ossv-agent", "dev/stream/README.md"):
            self.t.write(rel, tool)
            self.assertTrue(lint.internal_only(rel), rel)
            # the fixture holds what the exemption is for: the shapes a release must not carry
            self.assertEqual(sorted({f.msg for f in lint.scan_shapes(tool, rel)}),
                             ["a host path", "a private host name"])
        self.assertEqual([str(f) for f in self.t.lint()], [])
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.lexists(self.t.path("dev/stream")))
        self.assertIn("dev/stream", out)

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

    def test_an_old_form_lint_exception_under_an_unapproved_fuzz_target_of_a_ported_tree_is_cut_with_it(self):
        """lint-exceptions.yaml keeps its entries in the old layout's form, and lint matches each through
        layout.canonical, so the cut takes out the old-form entry of a file it removes from the ported tree."""
        approve(self.t, APPROVED)
        cut = needed_exception(self.t, "proofs/%s/provenance/LICENSES/zlib-LICENSE" % UNAPPROVED)
        kept = needed_exception(self.t, "projects/zlib/checksum_fuzzer/source/checksum_fuzzer.c")
        put_exceptions(self.t, [cut, kept])
        port_tree(self.t)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.exists(self.t.path(layout.proofs_dir("zlib", "api-driver", layout.NEW))))
        self.assertIn("rewrote %s without the exception(s) for %s" % (EXCEPTIONS, cut["path"]), out)
        self.assertEqual(self.t.read(EXCEPTIONS), EXCEPTIONS_HEAD + yamlio.dump({"exceptions": [kept]}))

    def test_a_per_project_form_lint_exception_under_an_unapproved_fuzz_target_is_cut_with_it(self):
        """The converse: an entry in the per-project form, of a file under the whole proofs folder the cut removes
        from an old-layout tree."""
        approve(self.t, APPROVED)
        cut = needed_exception(self.t, "proofs/%s/provenance/LICENSES/zlib-LICENSE" % UNAPPROVED)
        cut["path"] = layout.canonical(cut["path"])
        kept = needed_exception(self.t, "projects/zlib/checksum_fuzzer/source/checksum_fuzzer.c")
        put_exceptions(self.t, [cut, kept])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.exists(self.t.path("proofs", UNAPPROVED)))
        self.assertEqual(self.t.read(EXCEPTIONS), EXCEPTIONS_HEAD + yamlio.dump({"exceptions": [kept]}))

    def licence_pending_cut(self, ported):
        """A release never carries a licence-pending entry: the cut drops every one, for a fuzz target it keeps and
        for one it removes."""
        approve(self.t, APPROVED)
        if ported:
            port_tree(self.t)
        pending = [{"unit": u, "rule": "licence-pending", "due": "2999-12-31", "series": s,
                    "reason": "its licence lines are applied in its own series"}
                   for u, s in ((APPROVED, "pending"), (UNAPPROVED, "#441"))]
        put_exceptions(self.t, pending)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertIn("rewrote %s without the exception(s) for licence-pending %s, licence-pending %s"
                      % (EXCEPTIONS, APPROVED, UNAPPROVED), out)
        self.assertEqual(self.t.read(EXCEPTIONS), EXCEPTIONS_HEAD + yamlio.dump({"exceptions": []}))
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_a_release_carries_no_licence_pending_entry(self):
        self.licence_pending_cut(ported=False)

    def test_a_release_cut_from_a_ported_tree_carries_no_licence_pending_entry(self):
        self.licence_pending_cut(ported=True)

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

    def test_a_per_project_lib_kept_with_unlisted_proofs_is_reported(self):
        port_tree(self.t)
        self.t.write("projects/%s/proofs/lib/Shared.v" % APPROVED, "Definition one := 1.\n")
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

    def test_a_per_project_build_record_is_named_where_it_is(self):
        port_tree(self.t)
        self.t.write(layout.record_path("zlib", "checksum_fuzzer", layout.NEW),
                     build_record(proofs={"origin": PACKAGE, "written_here": "plain_halts"}))
        tree = facts.load(self.t.root)
        rules.check(tree)
        self.assertIn("projects/%s/proofs/provenance/PROVENANCE.yaml: proofs.written_here must be a list of statement "
                      "names" % APPROVED, tree.errors)

    def test_an_enrollment_entry_for_a_package_fuzz_target_is_refused(self):
        """N4: a fuzz target whose build record names a package keeps its submission and this-repository entries; an
        enrollment entry of it is refused once, whatever proofs.written_here names (asan_halts is not in it)."""
        self.record(PACKAGE, ["plain_halts"])
        approve(self.t, entry(APPROVED, statements=["ubsan_agrees"], origin="submission", record="final-package"),
                enrolled(APPROVED, ["plain_halts", "asan_halts"]))
        tree = facts.load(self.t.root)
        self.assertEqual(rules.check(tree), [
            "approvals.yaml: approvals.fuzz_targets[1]: %s: its build record says its proofs came from a package "
            "(proofs.origin), so no enrollment entry lists it: its proofs keep their submission and this-repository "
            "entries" % APPROVED])
        # a contribution's origin names no package: its fuzz target may have an enrollment entry
        self.record(CONTRIBUTED)
        approve(self.t, enrolled(APPROVED, ["plain_halts", "ubsan_agrees"]))
        self.assertEqual([str(f) for f in self.t.lint()], [])


class EnrollmentEntry(unittest.TestCase):
    """An entry that the merge of a project's enrollment pull request on the OSS Verify port writes (origin enrollment)
    names that merge, and is a ceiling: it lists the statements its enrollment facts pull requests wrote, and a release
    carries the proofs of those statements that exist, that no hold keeps out and that do not refute (the approvals
    plan)."""

    def setUp(self):
        self.t = Tree()
        self.addCleanup(self.t.close)
        add_proof(self.t, APPROVED + "/plain_halts")
        add_proof(self.t, UNAPPROVED + "/ubsan_agrees")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)

    def errors(self):
        """The errors of the facts: schema (facts.load) and rules (rules.check)."""
        tree = facts.load(self.t.root)
        return rules.check(tree)

    def cut(self):
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        return out

    def test_an_enrollment_entry_names_its_merge(self):
        # a merge by a person, and one by an app, whose login GitHub gives with [bot]
        approve(self.t, enrolled(APPROVED), enrolled(UNAPPROVED, ["ubsan_agrees"], merged_by="ossv-merge[bot]"))
        self.assertEqual(self.errors(), [])
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_an_enrollment_entry_needs_its_block(self):
        bare = enrolled(APPROVED)
        del bare["enrollment"]
        approve(self.t, bare, entry(UNAPPROVED, statements=["ubsan_agrees"], enrollment=dict(MERGE)))
        why = "an enrollment entry names the merge that wrote it (enrollment), and only an enrollment entry does"
        self.assertEqual(self.errors(), ["approvals.yaml: approvals.fuzz_targets[0]: %s: %s" % (APPROVED, why),
                                         "approvals.yaml: approvals.fuzz_targets[1]: %s: %s" % (UNAPPROVED, why)])

    def test_an_enrollment_pull_request_must_be_on_oss_verify(self):
        approve(self.t, enrolled(APPROVED, pull_request="https://github.com/someone/else/pull/1"))
        errors = self.errors()
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("approvals.fuzz_targets[0].enrollment.pull_request", errors[0])
        self.assertIn("https://github.com/someone/else/pull/1", errors[0])

    def test_a_look_alike_pull_request_is_refused(self):
        # another repository whose name begins with oss-verify, http, a page under the pull request, and an issue
        for url in ("https://github.com/theorem-labs/" + "oss-verify-private/pull/1",
                    "http://github.com/theorem-labs/oss-verify/pull/1",
                    "https://github.com/theorem-labs/oss-verify/pull/1/files",
                    "https://github.com/theorem-labs/oss-verify/issues/1"):
            with self.subTest(url=url):
                approve(self.t, enrolled(APPROVED, pull_request=url))
                errors = self.errors()
                self.assertEqual(len(errors), 1, errors)
                self.assertIn("approvals.fuzz_targets[0].enrollment.pull_request", errors[0])

    def test_an_enrollment_block_needs_each_of_its_fields(self):
        for key in MERGE:
            with self.subTest(key=key):
                e = enrolled(APPROVED)
                del e["enrollment"][key]
                approve(self.t, e)
                errors = self.errors()
                self.assertEqual(len(errors), 1, errors)
                self.assertIn("approvals.fuzz_targets[0].enrollment: missing key %r" % key, errors[0])

    def test_oft_approvals_keeps_enrollment_entries(self):
        add_proof(self.t, APPROVED + "/ubsan_agrees")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        # json's enrollment merged before any proof of it, by an app; zlib's checksum_fuzzer has a proof of plain_halts,
        # which its entry lists, and one of ubsan_agrees, which its bare line below lists as this repository's
        approve(self.t, enrolled(APPROVED, ["asan_halts", "plain_halts"]),
                enrolled(RELEASED, merged_by="ossv-merge[bot]"))
        before = self.t.read("approvals.yaml")
        kept = self.t.yaml("approvals.yaml")["fuzz_targets"]
        rc, out = write_approvals(self.t, "%s\n%s\n" % (APPROVED, UNAPPROVED))
        self.assertEqual(rc, 0, out)
        after = self.t.read("approvals.yaml")
        # byte for byte: each enrollment entry's text in the file before is in the file oft approvals writes
        for e in kept:
            self.assertIn(yamlio.dump([e]), before)
            self.assertIn(yamlio.dump([e]), after)
        self.assertEqual([(e["fuzz_target"], e["origin"], e["statements"])
                          for e in self.t.yaml("approvals.yaml")["fuzz_targets"]],
                         [(RELEASED, "enrollment", ["plain_halts"]), (UNAPPROVED, "this-repository", ["ubsan_agrees"]),
                          (APPROVED, "enrollment", ["asan_halts", "plain_halts"]),
                          (APPROVED, "this-repository", ["ubsan_agrees"])])

    def test_oft_approvals_writes_nothing_when_it_cannot_keep_the_enrollment_entries(self):
        # an approvals.yaml that is not YAML may hold enrollment entries; one with a malformed enrollment entry does,
        # and an error in one names its index in the file, whether or not it names a fuzz target
        malformed = {"schema": "oss-fuzz-theorems/approvals/1",
                     "fuzz_targets": [enrolled(APPROVED, merged_at="yesterday")]}
        nameless = {"schema": "oss-fuzz-theorems/approvals/1",
                    "fuzz_targets": [entry(UNAPPROVED, ["ubsan_agrees"]),
                                     {k: v for k, v in enrolled(APPROVED).items() if k != "fuzz_target"}]}
        unreadable = ("approvals.yaml cannot be read, so its enrollment entries cannot be kept; nothing written: "
                      "repair it, or remove it when it holds no enrollment entry, and run oft approvals again")
        nameless_why = "approvals.yaml: approvals.fuzz_targets[1]: missing key 'fuzz_target'"
        for text, why in (("fuzz_targets: [\n", unreadable),
                          (yamlio.dump(malformed), "approvals.yaml: approvals.fuzz_targets[0].enrollment.merged_at"),
                          (yamlio.dump(nameless), nameless_why)):
            with self.subTest(why=why):
                self.t.write("approvals.yaml", text)
                rc, out = write_approvals(self.t, "%s\n" % UNAPPROVED)
                self.assertEqual(rc, 1, out)
                self.assertIn(why, out)
                self.assertIn("nothing written", out)
                self.assertEqual(self.t.read("approvals.yaml"), text)

    def test_a_bare_line_whose_proofs_its_enrollment_entry_lists_is_not_without_proof(self):
        # checksum_fuzzer's one proof, plain_halts, is in its enrollment entry; json has no proof at all
        approve(self.t, enrolled(APPROVED, ["asan_halts", "plain_halts"]), enrolled(RELEASED))
        rc, out = write_approvals(self.t, "%s\n%s\n%s\n" % (APPROVED, RELEASED, UNAPPROVED))
        self.assertEqual(rc, 0, out)
        self.assertNotIn("listed, no proof yet: %s" % APPROVED, out)
        self.assertIn("listed, no proof yet: %s\n" % RELEASED, out)
        self.assertIn("1 line(s) with no proof yet", out)

    def test_an_enrollment_entry_is_a_ceiling(self):
        approve(self.t, enrolled(APPROVED, ["plain_halts", "asan_halts"]))
        self.assertEqual(self.errors(), [])
        self.assertEqual([str(f) for f in self.t.lint()], [])
        self.cut()
        self.assertTrue(os.path.isfile(self.t.path("proofs", APPROVED, "plain_halts", "Proof.v")))
        self.assertEqual(index_status(self.t)[APPROVED + "/plain_halts"], "proved")

    def test_a_ceiling_statement_with_no_proof_is_counted_apart(self):
        """A ceiling's statements with no proof are its normal state: one line counts them.  A statement of an exact
        entry with no proof is still named."""
        approve(self.t, entry(RELEASED), enrolled(APPROVED, ["asan_halts", "plain_halts", "ubsan_agrees"]))
        out = self.cut()
        self.assertNotIn("listed, but no proof in this checkout: %s/" % APPROVED, out)
        self.assertIn("listed, but no proof in this checkout: %s/plain_halts\n" % RELEASED, out)
        self.assertIn("2 statement(s) that enrollment entries list have no proof in this checkout (an enrollment entry "
                      "is a ceiling)\n", out)
        self.assertIn("1 listed statement(s) with no proof", out)

    def test_a_refuting_proof_of_an_enrollment_entry_is_not_kept(self):
        add_proof(self.t, APPROVED + "/asan_halts")
        refute(self.t, APPROVED + "/asan_halts")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, enrolled(APPROVED, ["plain_halts", "asan_halts"]))
        self.assertEqual(self.errors(), [])
        self.cut()
        self.assertTrue(os.path.isfile(self.t.path("proofs", APPROVED, "plain_halts", "Proof.v")))
        self.assertFalse(os.path.lexists(self.t.path("proofs", APPROVED, "asan_halts")))

    def test_an_unlisted_proof_is_still_removed(self):
        add_proof(self.t, APPROVED + "/ubsan_agrees")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, enrolled(APPROVED, ["plain_halts"]))
        self.cut()
        self.assertTrue(os.path.isfile(self.t.path("proofs", APPROVED, "plain_halts", "Proof.v")))
        for gone in ("proofs/%s/ubsan_agrees" % APPROVED, "proofs/" + UNAPPROVED):
            self.assertFalse(os.path.lexists(self.t.path(gone)), gone)

    def test_a_statement_added_after_the_merge_ships_no_proof(self):
        # the merge's enrollment facts pull requests added plain_halts; a later change added asan_halts, and its proof
        approve(self.t, enrolled(APPROVED, ["plain_halts"]))
        add_proof(self.t, APPROVED + "/asan_halts")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.assertEqual(self.errors(), [])
        self.cut()
        self.assertTrue(os.path.isfile(self.t.path("proofs", APPROVED, "plain_halts", "Proof.v")))
        self.assertFalse(os.path.lexists(self.t.path("proofs", APPROVED, "asan_halts")))
        self.assertNotEqual(index_status(self.t).get(APPROVED + "/asan_halts"), "proved")

    def test_an_enrollment_entry_naming_a_removed_fuzz_target_or_statement_is_not_an_error(self):
        """N3: a new build removed zlib/gone_fuzzer, and checksum_fuzzer's gone_halts, after their enrollment merge;
        the approvals pull request comes after the new build's facts merge, so the cut keeps only proofs that exist."""
        approve(self.t, entry("zlib/gone_fuzzer"), entry(APPROVED, statements=["gone_halts", "plain_halts"]))
        self.assertEqual(self.errors(), [
            "approvals.yaml: approvals.fuzz_targets[0]: zlib/gone_fuzzer is not an included fuzz target",
            "approvals.yaml: approvals.fuzz_targets[1]: gone_halts is not a statement of %s" % APPROVED])
        approve(self.t, enrolled("zlib/gone_fuzzer"), enrolled(APPROVED, ["gone_halts", "plain_halts"]))
        self.assertEqual(self.errors(), [])
        self.assertEqual([str(f) for f in self.t.lint()], [])
        self.cut()
        self.assertTrue(os.path.isfile(self.t.path("proofs", APPROVED, "plain_halts", "Proof.v")))


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


def internal_paths(module, internal):
    """(the paths of internal, release_tree.INTERNAL split at '/', that the parsed test module names, those of them it
    checks the existence of), each joined with '/'.  It names one by an os.path.join of literal parts on a name bound at
    its top level or on an expression of __file__ (the repository's own tree, not a test's temporary one) whose parts
    begin with the path's last parts, and a workflow by its file name alone (as test_workflow_verdicts.load takes it);
    it checks one by os.path.exists, isdir, isfile or lexists of such a join, or of a name such a join is bound to."""
    top = set()
    for node in module.body:
        if isinstance(node, ast.Assign):
            top.update(t.id for t in node.targets if isinstance(t, ast.Name))
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            top.update((a.asname or a.name).split(".")[0] for a in node.names)

    def os_path(call, names):
        f = call.func
        return (isinstance(f, ast.Attribute) and f.attr in names and isinstance(f.value, ast.Attribute)
                and f.value.attr == "path" and isinstance(f.value.value, ast.Name) and f.value.value.id == "os")

    def joined(node):
        if not (isinstance(node, ast.Call) and os_path(node, ("join",)) and node.args):
            return set()
        base, parts = node.args[0], node.args[1:]
        if not parts or not all(isinstance(p, ast.Constant) and isinstance(p.value, str) for p in parts):
            return set()
        if not ((isinstance(base, ast.Name) and base.id in top)
                or any(isinstance(n, ast.Name) and n.id == "__file__" for n in ast.walk(base))):
            return set()
        tail = "/".join(p.value for p in parts).split("/")
        return {"/".join(p) for p in internal if any(tail[:k] == p[-k:] for k in range(1, len(p) + 1))}

    workflows = {p[-1]: "/".join(p) for p in internal if p[:2] == [".github", "workflows"]}
    bound, named, checked = {}, set(), set()
    for node in ast.walk(module):
        named |= joined(node)
        if isinstance(node, ast.Constant) and node.value in workflows:
            named.add(workflows[node.value])
        if isinstance(node, ast.Assign) and joined(node.value):
            for t in node.targets:
                if isinstance(t, ast.Name):
                    bound.setdefault(t.id, set()).update(joined(node.value))
    for node in ast.walk(module):
        if isinstance(node, ast.Call) and os_path(node, ("exists", "isdir", "isfile", "lexists")) and node.args:
            arg = node.args[0]
            checked |= bound.get(arg.id, set()) if isinstance(arg, ast.Name) else joined(arg)
    return named, checked


class ReleasedTests(unittest.TestCase):
    """A test module the release keeps finds the files it needs in the release: one that names a path
    release_tree.INTERNAL removes either goes with it (INTERNAL names the module too) or checks that the path exists and
    skips without it, as test_enroll_tools and test_workflow_verdicts' FACTS_REVIEW do.  Limits: any existence call on
    the path counts as that check, whether or not a skip follows from it, so this does not prove the guard works; and
    a path reached through a name imported from another module, or a join with a part that is not a literal, is not
    seen (internal_paths)."""

    def test_every_released_test_s_required_files_are_released(self):
        internal = [p.split("/") for p in release_tree.INTERNAL]
        tests = os.path.join(REPO, "tools", "oft", "tests")
        problems = []
        for name in sorted(os.listdir(tests)):
            rel = "tools/oft/tests/" + name
            if not name.endswith(".py") or any(rel == p or rel.startswith(p + "/") for p in release_tree.INTERNAL):
                continue
            with open(os.path.join(tests, name), encoding="utf-8") as f:
                named, checked = internal_paths(ast.parse(f.read()), internal)
            problems += ["%s needs %s, which the release removes: release_tree.INTERNAL must name the test too, or the "
                         "test must check that the path exists" % (rel, p) for p in sorted(named - checked)]
        self.assertEqual(problems, [])

    def test_the_check_sees_each_way_a_test_names_a_path(self):
        internal = [p.split("/") for p in ("tools/oft/ci/prove-pr", "tools/enroll", ".github/workflows/index.yml")]
        for text, named, checked in (
                ('import os\nfrom x import REPO\nP = os.path.join(REPO, "tools", "oft", "ci", "prove-pr")\n',
                 {"tools/oft/ci/prove-pr"}, set()),
                ('import os\nS = os.path.join(os.path.dirname(__file__), "..", "ci/prove-pr")\n', set(), set()),
                ('import os\nS = os.path.join(os.path.dirname(__file__), "ci", "prove-pr")\n',
                 {"tools/oft/ci/prove-pr"}, set()),
                ('import os\nT = "t"\nE = os.path.join(T, "enroll", "tests")\nif os.path.isdir(E): pass\n',
                 {"tools/enroll"}, {"tools/enroll"}),
                ('import os\ndef f(d):\n    return os.path.join(d, "tools", "oft", "ci", "prove-pr")\n', set(), set()),
                ('def f():\n    return load("index.yml")\n', {".github/workflows/index.yml"}, set()),
                ('import os\nW = "w"\nI = os.path.join(W, "index.yml")\nok = os.path.exists(I)\nload("index.yml")\n',
                 {".github/workflows/index.yml"}, {".github/workflows/index.yml"})):
            with self.subTest(text=text):
                self.assertEqual(internal_paths(ast.parse(text), internal), (named, checked))


if __name__ == "__main__":
    unittest.main()
