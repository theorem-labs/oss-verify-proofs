"""`oft release-tree`, `oft approvals` and approvals.yaml: a release carries the proofs of each fuzz target that is not
held, whatever approvals.yaml lists, and no proof that a hold or a refutation keeps out (KeepRule), no findings, and
only the held form of a project a finding holds back; a tree ported to the per-project layout cuts to the same
release.  approvals.yaml is still a fact file: the rules check it while it exists (rules._approvals), so the cut
refuses a tree whose approvals.yaml they refuse."""
import ast
import contextlib
import csv
import hashlib
import io
import os
import re
import shutil
import subprocess
import tempfile
import unittest

import yaml

from oft import approvals, disclosure, facts, generate, layout, lint, paths, port, release_tree, rules, schema, yamlio
from oft.tests.helpers import (HELD_PATCH, OTHER_OWN_RECIPE, REPO, Tree, add_findings, align_unpatched_pins,
                               build_record, own_recipe, port_built, public_patch, recipe_file, recount, rules_of)
from oft.tests.test_oss_verify import add_json_oss_verify_target, add_standin

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
# release.yaml is at the root of a checkout; tools/oft alone, as the runner image carries it, has no such file, and
# the test that reads this repository's own release.yaml says so instead of ending in FileNotFoundError (images.yml
# run 42574457306, 2026-11-09).
RELEASE_YAML = os.path.join(REPO, "release.yaml")
HAVE_RELEASE_YAML = os.path.exists(RELEASE_YAML)
NO_RELEASE_YAML = "no release.yaml: tools/oft without the checkout around it"
# tools/publish/ is the internal repository's alone (INTERNAL list): a release's cut removes it, the publication gate's
# reader tools/publish/verify with it, so a tree without it is a release's.  A test that reads a file of it skips there,
# and fails in the internal tree where the file is missing.
INTERNAL_TREE = os.path.isdir(os.path.join(REPO, "tools", "publish"))
NOT_INTERNAL = "no tools/publish/ beside tools/oft: a release's tree, whose cut removes it"


def cut_list():
    """What release_tree.INTERNAL writes out: each entry of lint.LINT_ONLY_INTERNAL, a directory (a /** entry) with its
    trailing / (as paths.py writes a /** row there) and any other entry, a file, as it is, then the INTERNAL of
    paths.py, then release_tree.SKILLS, in the order they are defined (SKILLS last, where the publishing scan's
    reviewed exceptions read them).  Past a directory's /**, no entry holds a pattern: the cut removes literal paths."""
    entries = tuple(p[:-len("**")] if p.endswith("/**") else p for p in lint.LINT_ONLY_INTERNAL)
    assert not any(c in e for e in entries for c in "*?[{"), lint.LINT_ONLY_INTERNAL
    return entries + vars(paths)["INTERNAL"] + release_tree.SKILLS


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


def hold_fuzz_target(t, unit):
    """Name the fuzz target unit, <project>/<harness>, in its project's private_harnesses: the fuzz target is held while
    the rest of the project publishes (facts.hold, Hold.entries)."""
    p, h = unit.split("/")
    rel = "projects/%s/project.yaml" % p
    t.put_yaml(rel, dict(t.yaml(rel), private_harnesses=[h]))


def finding_hold(t, state="open", enrolled=True):
    """Lay down zlib's one finding (add_findings) as test_hold.EnrolledHold shapes it: in state, naming asan_agrees
    alone (its asan run differs from the plain one, and no run dies), with a patch zlib's own patches do not hold
    (test_hold.HeldFixture's), and with zlib's unpatched pins the binaries it publishes; zlib enrolled when enrolled.
    Open, of enrolled zlib with no proof library (the caller removes any), it holds back asan_agrees of checksum_fuzzer
    with its pair's bound and decidability statements (facts.hold, Hold.ids).  Open and not enrolled, or patched or
    reported (then reported upstream, and its patch in the series), it holds zlib whole (Hold.held)."""
    add_findings(t)
    if enrolled:
        rel = "projects/zlib/project.yaml"
        t.put_yaml(rel, dict(t.yaml(rel), enrolled=True))
    finding = "findings/zlib/checksum_fuzzer/stand-in-abort"
    t.write(finding + "/0001-stand-in.patch", HELD_PATCH)
    normal = t.yaml(finding + "/finding.yaml")["control"]["plain"]
    fields = dict(state=state, statements=["asan_agrees"],
                  input={"plain": normal, "asan": dict(normal, stdout_sha256="c0" * 32)},
                  control={"plain": normal, "asan": normal})
    if state != "open":
        fields["upstream"] = "https://bugs.example.org/1"
    t.put_yaml(finding + "/finding.yaml", dict(t.yaml(finding + "/finding.yaml"), **fields))
    t.write("findings/zlib/checksum_fuzzer/series", "" if state == "open" else "0001-stand-in.patch\n")
    align_unpatched_pins(t)


def index_status(t):
    """{statement id: status} as index/statements.tsv, the rendered index, says."""
    with open(t.path("index", "statements.tsv"), newline="") as f:
        return {r["id"]: r["status"] for r in csv.DictReader(f, delimiter="\t")}


def proof_folders(t):
    """The id of each proof folder of the checkout, a statement folder that holds proof.yaml, in either layout:
    proofs/<p>/<h>/<s>/ or projects/<p>/<h>/proofs/<s>/."""
    out = set()
    for rel in t.files():
        parts = layout.canonical(rel).split("/")
        if len(parts) == 6 and parts[0] == "projects" and parts[3] == "proofs" and parts[5] == "proof.yaml":
            out.add("/".join(parts[1:3] + parts[4:5]))
    return out


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


# OSSV-668's block of the shared generated files, as it appends it to .gitignore right after the last line, .venv/, with
# no blank line: the marker line, then "/" and each pattern of paths.SHARED, a project's folder as *.  It is written out
# here, not taken from release_tree, so these tests hold the cut's constants to that text.
GITIGNORE_BLOCK = ("# The shared generated files (tools/oft/paths.py SHARED): main holds none; ./oft generate "
                   "--shared-only renders them, and oft release-tree drops these lines from a release's copy.\n"
                   "/README.md\n"
                   "/index/STATUS.md\n"
                   "/index/PROOFS.md\n"
                   "/index/*.tsv\n"
                   "/analyses/harness-checks/checks.tsv\n"
                   "/analyses/known-issues.md\n"
                   "/projects/*/README.md\n")
# a .gitignore before the block (four lines, so a marker right after them is line 5), and a line after the block
GITIGNORE_HEAD = "_build/\nprojects/*/bin/\n__pycache__/\n.venv/\n"
GITIGNORE_TAIL = "dist/\n"
REWROTE_GITIGNORE = ("rewrote .gitignore without the block of the shared generated files (8 lines), which the release "
                     "commits")
NOT_THE_BLOCK = ("oft release-tree: .gitignore's block of the shared generated files is not the one the cut removes; "
                 "nothing changed")


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

    def test_a_private_projects_notice_goes_with_it(self):
        """projects/<project>/NOTICE, the licence of a `release: private` project's proof files (lint.PROJECT_NOTICE),
        goes with the rest of the project: the held page and project.yaml are all of it that the cut keeps."""
        self.t.write("projects/json/NOTICE", "Copyright Theorem Labs. All rights reserved.\n")
        make_private(self.t, "json")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, APPROVED)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertEqual(sorted(os.listdir(self.t.path("projects", "json"))), ["README.md", "project.yaml"])
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

    def test_a_private_projects_failure_handler_rows_are_cut(self):
        """facts.py writes a row of failure_handlers.tsv for a private project's fuzz target too: the cut takes it out,
        and every other row of that project, a fuzz target the tree no longer has included, since facts.py never
        removes a row and the publication gate refuses any row of a project held back whole.  It keeps a public
        project's rows, that project's absent fuzz target among them.  A row names no fuzz target as a path, so the
        disclosure search alone would let it through."""
        header = "project\tharness\tvalue\tevidence\n"
        private_row = "json\tfuzzer-parse_bjdata\tnone\tthe scan of handlers/fuzzer-parse_bjdata.txt\n"
        private_gone_row = "json\tremoved_bjdata_fuzzer\tnone\tthe scan of handlers/removed_bjdata_fuzzer.txt\n"
        public_row = "zlib\tchecksum_fuzzer\tnone\tthe scan of handlers/checksum_fuzzer.txt\n"
        gone_row = "zlib\tremoved_fuzzer\tnone\tthe scan of handlers/removed_fuzzer.txt\n"
        self.t.write(release_tree.HANDLERS, header + private_row + private_gone_row + public_row + gone_row)
        make_private(self.t, "json")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.t.read(release_tree.HANDLERS), header + public_row + gone_row)
        self.assertIn("wrote %s as the release has it" % release_tree.HANDLERS, out)

    def test_internal_block_of_agents_md_is_cut(self):
        """AGENTS.md ships without its marked block, which is text for this repository only, and every other byte of
        it stays as it is, its CRLF line ends among them."""
        approve(self.t, APPROVED)
        kept = b"# Agents\r\n\r\nA kept line.\r\n"
        self.t.write(release_tree.AGENTS, kept + b"<!-- BEGIN-INTERNAL: for this repository only -->\r\n\r\n"
                     b"## Only here\r\n\r\nNot for a release.\r\n<!-- END-INTERNAL -->\r\n", mode="wb")
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        with open(self.t.path(release_tree.AGENTS), "rb") as f:
            self.assertEqual(f.read(), kept)
        self.assertIn("wrote AGENTS.md as the release has it\n", out)

    def test_internal_block_with_no_end_is_refused(self):
        """A start that no line ends is a marker line with no partner: the cut refuses, and changes nothing."""
        approve(self.t, APPROVED)
        self.t.write(release_tree.AGENTS, b"A kept line.\n<!-- BEGIN-INTERNAL -->\nNot for a release.\n", mode="wb")
        self.assertRefused("error: AGENTS.md: line 2 starts a block that no line ends\noft release-tree: the cut cannot "
                           "take the marked blocks out of AGENTS.md; nothing changed\n")

    def test_internal_block_in_agents_md_that_is_not_utf8_is_refused(self):
        """A file that holds a marked block and a byte that is not UTF-8 is one the cut cannot write as UTF-8 text: it
        refuses before the first change, and names that byte by its offset, counted from 0."""
        approve(self.t, APPROVED)
        self.t.write(release_tree.AGENTS, b"A kept line \xff.\n<!-- BEGIN-INTERNAL -->\nNot for a release.\n"
                     b"<!-- END-INTERNAL -->\n", mode="wb")
        self.assertRefused("error: AGENTS.md: it holds a marked block and is not UTF-8 text (byte 12), so the cut "
                           "cannot write it\noft release-tree: the cut cannot take the marked blocks out of AGENTS.md; "
                           "nothing changed\n")

    def test_internal_block_is_cut_before_the_disclosure_search(self):
        """The disclosure search reads AGENTS.md as the release has it: a marked block that names this internal
        repository does not stop the cut, which writes the file without the block."""
        approve(self.t, APPROVED)
        kept = b"# Agents\n\nA kept line.\n"
        internal = schema.INTERNAL_PORT_REPOSITORY.encode()
        self.t.write(release_tree.AGENTS, kept + b"<!-- BEGIN-INTERNAL -->\nBuilt in " + internal + b".\n"
                     b"<!-- END-INTERNAL -->\n", mode="wb")
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        with open(self.t.path(release_tree.AGENTS), "rb") as f:
            self.assertEqual(f.read(), kept)

    def test_agents_md_with_no_internal_block_is_left_as_it_is(self):
        """With no marked block the cut does not write AGENTS.md: every byte of it stays, a lone CR, a byte that is not
        UTF-8 and a last line with no line end among them."""
        approve(self.t, APPROVED)
        data = b"# Agents\r\rA kept line about begin-internal \xff.\rThe last line"
        self.t.write(release_tree.AGENTS, data, mode="wb")
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        with open(self.t.path(release_tree.AGENTS), "rb") as f:
            self.assertEqual(f.read(), data)
        self.assertNotIn("wrote AGENTS.md", out)

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

    @unittest.skipUnless(HAVE_RELEASE_YAML, NO_RELEASE_YAML)
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
        with open(RELEASE_YAML, encoding="utf-8") as f:
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
        """zlib is private, so the cut removes the proofs folder of each of its fuzz targets, and proofs/zlib/, which
        they leave empty, goes with them."""
        make_private(self.t, "zlib")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
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
        # a tree with tools/publish/ has the list `oft generate` renders there: empty, since nothing is held
        self.t.write("tools/publish/private-harnesses.txt", "")
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
        # with the list `oft generate` renders in a tree with tools/publish/: empty, since no fuzz target is held
        planted = {"tools/publish/private-harnesses.txt": "",
                   "tools/publish/needles.txt": "json/fuzzer-parse_bjdata\ninternal-codename\n",
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

    def test_the_public_checks_ship_byte_for_byte(self):
        """The three public checks and the files they read run on the public repository alone, so a release must
        carry each of them as this repository holds it: the cut keeps each of them, with the same bytes.  They are the
        `.github/` entries of lint.LINT_ONLY_HAND.  The test, and not the class, skips where one of them is absent
        (tools/oft alone, as the runner image carries it)."""
        files = [p for p in lint.LINT_ONLY_HAND if p.startswith(".github/")]
        # each is an exact path, so a pattern cannot read as a file that is absent and skip the test
        self.assertTrue(files)
        self.assertEqual([p for p in files if set(p) & set("*?[")], [])
        sources = {rel: os.path.join(REPO, *rel.split("/")) for rel in files}
        missing = [rel for rel in files if not os.path.exists(sources[rel])]
        if missing:
            self.skipTest("no %s beside tools/oft" % ", ".join(missing))
        for rel in files:
            os.makedirs(os.path.dirname(self.t.path(rel)), exist_ok=True)
            shutil.copyfile(sources[rel], self.t.path(rel))
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        kept = snapshot(self.t)
        for rel in files:
            with open(sources[rel], "rb") as f:
                self.assertEqual(kept.get(rel), f.read(), rel)

    def test_a_symbolically_linked_internal_directory_is_refused(self):
        approve(self.t, APPROVED)
        os.makedirs(self.t.path("..", "elsewhere"))
        os.makedirs(self.t.path("tools"), exist_ok=True)
        os.symlink(os.path.join("..", "..", "elsewhere"), self.t.path("tools", "publish"))
        self.assertRefused("error: tools/publish: a symbolic link")
        self.assertTrue(os.path.isdir(self.t.path("..", "elsewhere")))

    def test_every_internal_path_is_one_the_cut_removes(self):
        # the cut's list is the entries lint alone holds internal (lint.LINT_ONLY_INTERNAL, since a row of paths.TABLE
        # re-keys every unit), then paths.py's, then the skill directories paths.py does not name, written out
        # (test_the_release_gate_reads_every_internal_path_from_release_tree_py)
        self.assertEqual(vars(release_tree)["INTERNAL"], cut_list())
        self.assertEqual(release_tree.SKILLS, (".claude/skills/porting-released-proofs/",
                                               ".claude/skills/clean-room-restatement/"))
        # each skill directory is one lint alone admits files under (lint.LINT_ONLY_HAND), and paths.py classifies
        # nothing there
        for d in release_tree.SKILLS:
            self.assertTrue(any(p.startswith(d) for p in lint.LINT_ONLY_HAND), d)
            self.assertFalse(paths.is_internal(d + "SKILL.md"), d)
            self.assertEqual(paths.classify(d + "SKILL.md"), [], d)
        for rel in ("dev/enroll/build", "dev/enroll/ci/gate.py", "dev/enroll/tests/fixtures/x.yaml"):
            self.assertTrue(lint.is_internal(rel), rel)
            self.assertFalse(paths.is_internal(rel), rel)
            self.assertEqual([cls for cls, _, _ in lint.classify_path(rel)], ["internal"], rel)
        for rel in ("dev/enrollment/x", "dev/other/x.py", ".github/workflows/pr.yml", "dev/licence/made_from.py"):
            self.assertFalse(lint.is_internal(rel), rel)
        # dev/gateway-model/, the model gateway's formal model (OSSV-498), and the workflow that builds it: internal to
        # lint alone, like dev/enroll/, and no sibling of the directory with it
        for rel in ("dev/gateway-model/theories/Json.v", "dev/gateway-model/tests/run.sh", "dev/gateway-model/NOTICE",
                    ".github/workflows/gateway-model.yml"):
            self.assertTrue(lint.is_internal(rel), rel)
            self.assertFalse(paths.is_internal(rel), rel)
            self.assertEqual([cls for cls, _, _ in lint.classify_path(rel)], ["internal"], rel)
        for rel in ("dev/gateway-models/x", "dev/gateway-model.md", ".github/workflows/gateway-model.yml.bak"):
            self.assertFalse(lint.is_internal(rel), rel)
        # dev/evals/, the tools that run the evals (OSSV-643), and the paired run's workflow: internal to lint alone,
        # like dev/gateway-model/, and no sibling of the directory with it
        for rel in ("dev/evals/paired-run/runner.py", "dev/evals/paired-run/tests/test_runner.py",
                    "dev/evals/README.md", ".github/workflows/paired-run.yml"):
            self.assertTrue(lint.is_internal(rel), rel)
            self.assertFalse(paths.is_internal(rel), rel)
            self.assertEqual([cls for cls, _, _ in lint.classify_path(rel)], ["internal"], rel)
        for rel in ("dev/evalsx/x", "dev/evals.md", ".github/workflows/paired-run.yml.bak"):
            self.assertFalse(lint.is_internal(rel), rel)
        # the build service's release test and its table of memory classes (OSSV-299): internal to lint alone, like the
        # paired run's workflow, and no sibling of either file with them
        for rel in (".github/workflows/rocq-release.yml", ".github/theorem-rule-classes.tsv"):
            self.assertTrue(lint.is_internal(rel), rel)
            self.assertFalse(paths.is_internal(rel), rel)
            self.assertEqual([cls for cls, _, _ in lint.classify_path(rel)], ["internal"], rel)
        for rel in (".github/workflows/rocq-release.yaml", ".github/workflows/rocq-release.yml.bak",
                    ".github/rocq-release.yml", ".github/workflows/rocq-release/x.yml",
                    ".github/theorem-rule-classes.tsv.bak", ".github/theorem-rule-classes.csv",
                    ".github/workflows/theorem-rule-classes.tsv", "theorem-rule-classes.tsv",
                    ".github/x/theorem-rule-classes.tsv"):
            self.assertFalse(lint.is_internal(rel), rel)
            self.assertEqual(lint.classify_path(rel), [], rel)
        # .github/README.md, the page GitHub shows on this repository's front page (OSSV-668): internal to lint alone,
        # like .github/rekey-window, and named by its exact path, so that no neighbour of it is internal
        rel = ".github/README.md"
        self.assertTrue(lint.is_internal(rel), rel)
        self.assertFalse(paths.is_internal(rel), rel)
        self.assertEqual([cls for cls, _, _ in lint.classify_path(rel)], ["internal"], rel)
        for rel in (".github/README", ".github/x/README.md", ".github/README.md.bak"):
            self.assertFalse(lint.is_internal(rel), rel)
        self.assertEqual(set(vars(paths)["INTERNAL"]), {
            "approvals.yaml", ".github/CODEOWNERS", ".github/workflows/facts-review.yml",
            ".claude/skills/review-facts/SKILL.md", "review.md", ".github/workflows/enroll.yml",
            ".github/workflows/enroll-build.yml", ".github/workflows/facts-refresh.yml",
            ".github/workflows/hold-state.yml", ".github/workflows/enroll-retry.yml",
            ".github/workflows/approvals-watch.yml", "tools/enroll/", ".github/workflows/proof-index.yml",
            ".github/proof-index.py", ".github/workflows/proof-index-trigger.yml", ".github/workflows/index.yml",
            ".github/workflows/prove.yml", ".github/workflows/publish-request.yml", ".github/workflows/publish.yml",
            ".github/workflows/publish-gate.yml", "tools/publish/", ".github/workflows/store-retention.yml",
            "tools/oft/ci/regenerate-shared.sh", "tools/oft/tests/test_regenerate_shared.py",
            "tools/oft/tests/test_held_match.py", "tools/oft/ci/prove-pr", "tools/oft/tests/test_prove_pr.py",
            "tools/oft/tests/test_prove_workflow.py", "changes/", "docs/reference/", "dev/stream/"})
        for rel in ("approvals.yaml", ".github/CODEOWNERS", "review.md", ".github/workflows/index.yml",
                    ".github/workflows/publish-request.yml", ".github/workflows/store-retention.yml", "tools/publish/x",
                    "tools/publish/a/b", "tools/enroll/ci/gate.py", "tools/publish"):
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
        loop, replayed here on this file, reads every path the cut removes (cut_list) and finds nothing it cannot read."""
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
        self.assertEqual((names, unread), (set(cut_list()), []))
        # and no import binds the name, which the gate would not read
        self.assertEqual([n.lineno for n in body if isinstance(n, ast.ImportFrom)
                          and any((a.asname or a.name) == "INTERNAL" for a in n.names)], [])

    def test_without_codeowners_it_says_what_it_removed(self):
        os.remove(self.t.path(".github", "CODEOWNERS"))
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertIn("; removed approvals.yaml", out)
        self.assertNotIn("CODEOWNERS", out)

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

    def test_the_witness_record_beside_a_kept_proof_is_carried(self):
        """OSSV-360: the record of which term discharged the statement goes with the proof it is of, in
        both layouts.  STATEMENT_FILES is a second allowlist, independent of paths.py: without the suffix here the
        first release after the first land would refuse the cut, and a release that dropped the record instead would
        leave the audit reading "no record" for a proof that has one.  A record whose stem is not the statement's is
        still a file the release carries, as paths.py's `*.witness.json` row admits it: the two readers of this one
        file agree, and land.py is what holds the stem to the node."""
        record = ('{\n "schema": "oss-verify/witness-record/1",\n "node": "plain_halts",\n'
                  ' "term": "OSSVerify.Proofs.zlib.checksum_fuzzer.lib.A.Sched.plain_halts.plain_halts_holds",\n'
                  ' "require": [\n  [\n   "OSSVerify.Proofs.zlib.checksum_fuzzer.lib.A.Sched",\n'
                  '   "plain_halts"\n  ]\n ]\n}\n')
        for ported in (False, True):
            with self.subTest(layout="per-project" if ported else "old"):
                self.setUp()
                approve(self.t, APPROVED)
                if ported:
                    port_tree(self.t)
                    rel = "projects/%s/proofs/plain_halts/plain_halts.witness.json" % APPROVED
                else:
                    rel = "proofs/%s/plain_halts/plain_halts.witness.json" % APPROVED
                self.t.write(rel, record)
                rc, out = release(self.t)
                self.assertEqual(rc, 0, out)
                self.assertEqual(self.t.read(rel), record)
                self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_the_witness_record_of_a_cut_statement_goes_with_it(self):
        """A record is kept where its proof is kept and goes where its proof goes.  Both statements here are of the
        fuzz target the release keeps, so the cut reaches each statement directory separately and the test tells the
        two apart: an open finding of enrolled zlib holds back asan_agrees (finding_hold), so the record of plain_halts
        is carried, and the record of asan_agrees is removed with its directory and is named in the cut's own `removed`
        output."""
        for unit in (APPROVED, UNAPPROVED):
            shutil.rmtree(self.t.path("proofs", unit, "lib"))
        finding_hold(self.t)
        add_proof(self.t, APPROVED + "/asan_agrees")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.assertIn(APPROVED + "/asan_agrees", facts.hold(facts.load(self.t.root)).ids)
        approve(self.t, entry(APPROVED, statements=["plain_halts"]))
        kept = "proofs/%s/plain_halts/plain_halts.witness.json" % APPROVED
        cut = "proofs/%s/asan_agrees/asan_agrees.witness.json" % APPROVED
        self.t.write(kept, '{"node": "plain_halts"}\n')
        self.t.write(cut, '{"node": "asan_agrees"}\n')
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.t.read(kept), '{"node": "plain_halts"}\n')
        self.assertFalse(os.path.exists(self.t.path(cut)))
        self.assertFalse(os.path.exists(self.t.path("proofs", APPROVED, "asan_agrees")))
        self.assertIn("removed proofs/%s/asan_agrees" % APPROVED, out)

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
        repository's own records, and no release carries them.  A fuzz target's ledger is under changes/ too
        (changes/targets/<project>/<harness>/), and goes with them."""
        for rel in ("changes/libreac-35/sessions.tsv", "changes/libreac-35/ledger.tsv", "changes/tools/journal.md",
                    "changes/targets/libreac/fuzz_hts/sessions.tsv",
                    "changes/targets/libreac/fuzz_hts/ledger.tsv"):
            self.t.write(rel, "step\n")
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.lexists(self.t.path("changes")))
        self.assertIn("changes", out)

    def test_the_rekey_window_file_is_not_published(self):
        """release_tree.INTERNAL names .github/rekey-window (lint.LINT_ONLY_INTERNAL, OSSV-413): the file
        that opens a re-key window on this repository's main, which a release has no use for.  The rest of .github/
        stays."""
        self.t.write(".github/rekey-window", "open\n")
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.lexists(self.t.path(".github/rekey-window")))
        self.assertTrue(os.path.isdir(self.t.path(".github")))
        self.assertIn(".github/rekey-window", out)

    def test_the_repository_page_readme_is_not_published(self):
        """release_tree.INTERNAL names .github/README.md (lint.LINT_ONLY_INTERNAL, OSSV-668): the page GitHub shows on
        this repository's front page in place of the root README.md.  A release has no use for that page, since it keeps
        its own rendered README.md.  The rest of .github/ stays."""
        self.t.write(".github/README.md", "# OSS Verify proofs\n")
        self.t.write(".github/workflows/pr.yml", "name: pr\n")
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.lexists(self.t.path(".github/README.md")))
        self.assertIn(".github/README.md", out)
        self.assertTrue(os.path.isfile(self.t.path(".github/workflows/pr.yml")))

    def test_the_gateway_model_and_its_workflow_are_not_published(self):
        """release_tree.INTERNAL names dev/gateway-model/ (lint.LINT_ONLY_INTERNAL, OSSV-498), the model gateway's
        formal model, which no release carries, and .github/workflows/gateway-model.yml, which builds and checks it.
        The directory goes whole, NOTICE with it; the rest of .github/workflows/ stays."""
        model = ("dev/gateway-model/NOTICE", "dev/gateway-model/build.sh", "dev/gateway-model/theories/Json.v",
                 "dev/gateway-model/tests/run.sh")
        for rel in model + (".github/workflows/gateway-model.yml",):
            self.t.write(rel, "# the gateway model\n")
        self.t.write(".github/workflows/pr.yml", "name: pr\n")
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.lexists(self.t.path("dev/gateway-model")))
        self.assertFalse(os.path.lexists(self.t.path(".github/workflows/gateway-model.yml")))
        self.assertIn("dev/gateway-model/", out)
        self.assertIn(".github/workflows/gateway-model.yml", out)
        self.assertTrue(os.path.isfile(self.t.path(".github/workflows/pr.yml")))

    def test_the_evals_tools_and_their_workflow_are_not_published(self):
        """release_tree.INTERNAL names dev/evals/ (lint.LINT_ONLY_INTERNAL, OSSV-643), the tools that run the evals,
        which no release carries, and .github/workflows/paired-run.yml, which runs the paired run's tests.  The
        directory goes whole; the rest of .github/workflows/ stays."""
        evals = ("dev/evals/paired-run/README.md", "dev/evals/paired-run/runner.py",
                 "dev/evals/paired-run/tests/test_runner.py")
        for rel in evals + (".github/workflows/paired-run.yml",):
            self.t.write(rel, "# the paired run\n")
        self.t.write(".github/workflows/pr.yml", "name: pr\n")
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.lexists(self.t.path("dev/evals")))
        self.assertFalse(os.path.lexists(self.t.path(".github/workflows/paired-run.yml")))
        self.assertIn("dev/evals/", out)
        self.assertIn(".github/workflows/paired-run.yml", out)
        self.assertTrue(os.path.isfile(self.t.path(".github/workflows/pr.yml")))

    def test_the_build_service_release_test_and_its_class_table_are_not_published(self):
        """release_tree.INTERNAL names .github/workflows/rocq-release.yml, the shared Rocq build service's release test,
        and .github/theorem-rule-classes.tsv, the table of memory classes that the service's client `theorem check`
        reads (lint.LINT_ONLY_INTERNAL, OSSV-299): no release carries them.  The rest of .github/ and of
        .github/workflows/ stays."""
        self.t.write(".github/workflows/rocq-release.yml", "name: rocq-release\n")
        self.t.write(".github/theorem-rule-classes.tsv", "*\tstd\n")
        self.t.write(".github/workflows/pr.yml", "name: pr\n")
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        for rel in (".github/workflows/rocq-release.yml", ".github/theorem-rule-classes.tsv"):
            self.assertFalse(os.path.lexists(self.t.path(rel)), rel)
            self.assertIn(rel, out)
        self.assertTrue(os.path.isfile(self.t.path(".github/workflows/pr.yml")))

    def test_the_ci_review_caller_and_its_rules_file_are_not_published(self):
        """release_tree.INTERNAL names .github/workflows/ci-review.yaml, the caller of agent-infra's CI reviewer, and
        .github/ci-review.md, the rules file that holds this repository's own check for that reviewer
        (lint.LINT_ONLY_INTERNAL).  The pull request of Dispatch issue OSSV-774 adds them, and no release carries them.
        The cut removes those two files.  A workflow beside them and files with names near theirs stay."""
        gone = (".github/workflows/ci-review.yaml", ".github/ci-review.md")
        kept = (".github/workflows/pr.yml", ".github/workflows/ci-review.yml", ".github/ci-review.md.bak")
        self.t.write(gone[0], "name: ci-review\n")
        self.t.write(gone[1], "# What the CI review checks\n")
        for k in kept:
            self.t.write(k, "x\n")
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        for rel in gone:
            self.assertFalse(os.path.lexists(self.t.path(rel)), rel)
            self.assertIn(rel, out)
        for k in kept:
            self.assertTrue(os.path.isfile(self.t.path(k)), k)

    def test_the_held_refscan_workflow_is_not_published(self):
        """release_tree.INTERNAL names .github/workflows/held-refscan.yml (lint.LINT_ONLY_INTERNAL): the daily scan
        of the public refs for held fuzz targets (Dispatch issue OSSV-377), which no release carries.  The cut removes
        that one file: a workflow beside it, and a file whose name starts with its name, stay."""
        rel = ".github/workflows/held-refscan.yml"
        kept = (".github/workflows/pr.yml", ".github/workflows/held-refscan.yml.txt")
        self.t.write(rel, "on:\n  schedule:\n    - cron: '0 6 * * *'\n")
        for k in kept:
            self.t.write(k, "on: push\n")
        approve(self.t, APPROVED)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.lexists(self.t.path(rel)))
        self.assertIn(rel, out)
        for k in kept:
            self.assertTrue(os.path.isfile(self.t.path(k)), k)

    def test_the_prove_workflow_its_script_and_their_tests_are_not_published(self):
        """release_tree.INTERNAL names prove.yml, tools/oft/ci/prove-pr and their tests: the workflow posts a check on
        this repository's own pull requests with the workflow's own token, and a reader of a proof never needs it."""
        internal = (".github/workflows/prove.yml", "tools/oft/ci/prove-pr", "tools/oft/tests/test_prove_pr.py",
                    "tools/oft/tests/test_prove_workflow.py")
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

    def test_a_lint_exception_under_the_proofs_folder_of_a_held_fuzz_target_is_cut_with_it(self):
        """zlib is private, and of its paths under proofs/ the cut removes only its fuzz targets' proofs folders (the
        rest of a project held whole goes from projects/, counterexamples/, patches/ and notes/): so only the removal of
        api-driver's proofs folder takes the entry out."""
        make_private(self.t, "zlib")
        approve(self.t, entry(RELEASED, statements=["plain_halts"]))
        cut = needed_exception(self.t, "proofs/%s/provenance/LICENSES/zlib-LICENSE" % UNAPPROVED)
        kept = needed_exception(self.t, "projects/%s/source/fuzzer-parse_bjdata.cpp" % RELEASED)
        put_exceptions(self.t, [cut, kept])
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.assertEqual([str(f) for f in self.t.lint()], [])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.exists(self.t.path("proofs", UNAPPROVED)))
        self.assertEqual(self.t.read(EXCEPTIONS), EXCEPTIONS_HEAD + yamlio.dump({"exceptions": [kept]}))
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_an_old_form_lint_exception_under_a_held_fuzz_target_of_a_ported_tree_is_cut_with_it(self):
        """lint-exceptions.yaml keeps its entries in the old layout's form, and lint matches each through
        layout.canonical, so the cut takes out the old-form entry of a file it removes from the ported tree."""
        make_private(self.t, "zlib")
        approve(self.t, entry(RELEASED, statements=["plain_halts"]))
        cut = needed_exception(self.t, "proofs/%s/provenance/LICENSES/zlib-LICENSE" % UNAPPROVED)
        kept = needed_exception(self.t, "projects/%s/source/fuzzer-parse_bjdata.cpp" % RELEASED)
        put_exceptions(self.t, [cut, kept])
        port_tree(self.t)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.exists(self.t.path(layout.proofs_dir("zlib", "api-driver", layout.NEW))))
        self.assertIn("rewrote %s without the exception(s) for %s" % (EXCEPTIONS, cut["path"]), out)
        self.assertEqual(self.t.read(EXCEPTIONS), EXCEPTIONS_HEAD + yamlio.dump({"exceptions": [kept]}))

    def test_a_per_project_form_lint_exception_under_a_held_fuzz_target_is_cut_with_it(self):
        """The converse: an entry in the per-project form, of a file under the whole proofs folder the cut removes
        from an old-layout tree."""
        make_private(self.t, "zlib")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        approve(self.t, entry(RELEASED, statements=["plain_halts"]))
        cut = needed_exception(self.t, "proofs/%s/provenance/LICENSES/zlib-LICENSE" % UNAPPROVED)
        cut["path"] = layout.canonical(cut["path"])
        kept = needed_exception(self.t, "projects/%s/source/fuzzer-parse_bjdata.cpp" % RELEASED)
        put_exceptions(self.t, [cut, kept])
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertFalse(os.path.exists(self.t.path("proofs", UNAPPROVED)))
        self.assertEqual(self.t.read(EXCEPTIONS), EXCEPTIONS_HEAD + yamlio.dump({"exceptions": [kept]}))

    def licence_pending_cut(self, ported):
        """A release never carries a licence-pending entry: the cut drops every one, of each fuzz target, whether or not
        it keeps that fuzz target's proofs."""
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

    def test_a_kept_file_that_names_this_internal_repository_is_refused_in_every_cut(self):
        """Decision 15 of Dispatch issue OSSV-424: no project holds a fuzz target and nothing is held back, and the cut
        still refuses a kept CHANGELOG.md that names this repository in full, in any case, with "nothing changed".  Its
        bare name is no needle (test_oss_verify.py names it), and a longer name that begins with the full name is the
        name of another repository."""
        approve(self.t, APPROVED)
        self.assertFalse(os.path.lexists(self.t.path("tools", "publish")))
        internal = schema.INTERNAL_PORT_REPOSITORY
        for text in ("Built in %s.\n" % internal, "See https://github.com/%s/pull/1.\n" % internal.title()):
            with self.subTest(text=text):
                self.t.write("CHANGELOG.md", text)
                before = snapshot(self.t)
                rc, out = release(self.t)
                self.assertEqual(rc, 1, out)
                self.assertIn("error: CHANGELOG.md names %s, the name of this internal repository" % internal, out)
                self.assertIn("nothing changed", out)
                self.assertEqual(snapshot(self.t), before)
        text = "Built in %s-mirror and in %s.\n" % (internal, internal.split("/")[1])
        self.t.write("CHANGELOG.md", text)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.t.read("CHANGELOG.md"), text)

    def gitignore_block_cut(self, data):
        """The cut of this checkout with .gitignore holding the bytes data, or with no .gitignore when data is None:
        (the bytes of .gitignore after the cut, None when there is none, and the cut's output)."""
        approve(self.t, APPROVED)
        if data is None:
            self.assertFalse(os.path.lexists(self.t.path(".gitignore")))
        else:
            self.t.write(".gitignore", data, mode="wb")
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        if not os.path.lexists(self.t.path(".gitignore")):
            return None, out
        with open(self.t.path(".gitignore"), "rb") as f:
            return f.read(), out

    def test_the_gitignore_block_goes_and_every_other_byte_stays(self):
        """OSSV-668 appends the block of the shared generated files to .gitignore, so main commits none of them; a
        release commits the files its last render writes, so the cut writes .gitignore as it was before the block."""
        after, out = self.gitignore_block_cut((GITIGNORE_HEAD + GITIGNORE_BLOCK).encode())
        self.assertEqual(after, GITIGNORE_HEAD.encode())
        self.assertIn(REWROTE_GITIGNORE, out)

    def test_a_gitignore_block_in_the_middle_leaves_no_blank_line(self):
        after, out = self.gitignore_block_cut((GITIGNORE_HEAD + GITIGNORE_BLOCK + GITIGNORE_TAIL).encode())
        self.assertEqual(after, (GITIGNORE_HEAD + GITIGNORE_TAIL).encode())
        self.assertIn(REWROTE_GITIGNORE, out)

    def test_a_blank_line_next_to_the_gitignore_block_stays(self):
        """The cut removes the eight lines of the block alone."""
        after, _ = self.gitignore_block_cut((GITIGNORE_HEAD + "\n" + GITIGNORE_BLOCK + "\n" + GITIGNORE_TAIL).encode())
        self.assertEqual(after, (GITIGNORE_HEAD + "\n\n" + GITIGNORE_TAIL).encode())

    def test_a_gitignore_with_no_gitignore_block_stays_as_it_is(self):
        """No marker in the bytes of .gitignore: the cut leaves the file as it is, whatever its bytes (these are not
        UTF-8), and its output does not name it."""
        data = GITIGNORE_HEAD.encode() + b"caf\xe9/\n"
        after, out = self.gitignore_block_cut(data)
        self.assertEqual(after, data)
        self.assertNotIn(".gitignore", out)

    def test_with_no_gitignore_the_gitignore_block_cut_writes_none(self):
        after, out = self.gitignore_block_cut(None)
        self.assertIsNone(after)
        self.assertNotIn(".gitignore", out)

    def test_a_gitignore_block_that_is_the_whole_file_leaves_it_empty(self):
        after, out = self.gitignore_block_cut(GITIGNORE_BLOCK.encode())
        self.assertEqual(after, b"")
        self.assertIn(REWROTE_GITIGNORE, out)

    def test_a_gitignore_block_last_with_no_final_line_feed_goes_the_same_way(self):
        after, out = self.gitignore_block_cut((GITIGNORE_HEAD + GITIGNORE_BLOCK[:-1]).encode())
        self.assertEqual(after, GITIGNORE_HEAD.encode())
        self.assertIn(REWROTE_GITIGNORE, out)

    def test_a_gitignore_block_the_cut_does_not_remove_is_refused(self):
        """Each refusal names its line of .gitignore and changes nothing: fewer lines under the marker line than the
        block has (at the marker line), a line that is not the block's next one (at that line, with the line read and
        the line wanted), a second marker line (at it), and the marker in a file that is not UTF-8 (at the first byte
        that is not)."""
        approve(self.t, APPROVED)
        marker, *ignores = GITIGNORE_BLOCK.splitlines(True)
        wrong = ignores[:2] + ["/index/*.md\n"] + ignores[3:]
        cases = {
            "a short block": ((GITIGNORE_HEAD + marker + "".join(ignores[:3])).encode(),
                              ".gitignore:5: the marker line of the shared generated files has 3 line(s) under it, "
                              "not the 7 of the block"),
            "a wrong line": ((GITIGNORE_HEAD + marker + "".join(wrong)).encode(),
                             ".gitignore:8: '/index/*.md' is under the marker line of the shared generated files, "
                             "where the block has '/index/PROOFS.md'"),
            "a second marker line": ((GITIGNORE_HEAD + GITIGNORE_BLOCK + GITIGNORE_TAIL + GITIGNORE_BLOCK).encode(),
                                     ".gitignore:14: a second marker line of the shared generated files (the first is "
                                     "line 5)"),
            "not UTF-8": (GITIGNORE_HEAD.encode() + b"caf\xe9/\n" + GITIGNORE_BLOCK.encode(),
                          ".gitignore:5: byte 0xe9 is not UTF-8, in a file that holds the marker of the shared "
                          "generated files")}
        for case, (data, why) in cases.items():
            with self.subTest(case=case):
                self.t.write(".gitignore", data, mode="wb")
                self.assertRefused("error: %s\n%s" % (why, NOT_THE_BLOCK))

    def test_the_cut_keeps_the_mode_of_each_file_it_rewrites(self):
        """The cut writes each file it rewrites over the file that is there, so the file keeps its mode, an executable
        one too: tools/publish/verify refuses a release in which a file the cut changes, a generated one apart, changed
        its mode (check_changes).  One tree holds a file of each kind the cut rewrites but the edits for a fuzz target
        of private_harnesses: json is private (its held page, release.yaml's counts, its lint exception, and its rows of
        pack.py and failure_handlers.tsv), an open finding of enrolled zlib holds back asan_agrees (the harness.yaml of
        that fuzz target, as test_hold.EnrolledHold makes the hold), AGENTS.md holds a marked block, and .gitignore
        holds the block."""
        # the hold per statement (finding_hold): zlib enrolled and with no proof library
        for unit in (APPROVED, UNAPPROVED):
            shutil.rmtree(self.t.path("proofs", unit, "lib"))
        finding_hold(self.t)
        make_private(self.t, "json")
        approve(self.t, APPROVED)
        private = needed_exception(self.t, "projects/json/fuzzer-parse_bjdata/source/fuzzer-parse_bjdata.cpp")
        put_exceptions(self.t, [private])
        self.t.write(release_tree.PACK,
                     '"""a stand-in packer."""\nSWEEP_TIMES = (\n'
                     '    ("%s", "r1", 10, "finished"),\n'
                     '    ("%s", "r1", 20, "finished"),\n)\n' % (APPROVED, RELEASED))
        self.t.write(release_tree.HANDLERS,
                     "project\tharness\tvalue\tevidence\n"
                     "json\tfuzzer-parse_bjdata\tnone\tthe scan of handlers/fuzzer-parse_bjdata.txt\n"
                     "zlib\tchecksum_fuzzer\tnone\tthe scan of handlers/checksum_fuzzer.txt\n")
        self.t.write(".gitignore", GITIGNORE_HEAD + GITIGNORE_BLOCK)
        self.t.write(release_tree.AGENTS, "# Agents\n\nA kept line.\n<!-- BEGIN-INTERNAL -->\nNot for a release.\n"
                     "<!-- END-INTERNAL -->\n")
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        rewrites = sorted([".gitignore", "release.yaml", EXCEPTIONS, release_tree.PACK, release_tree.HANDLERS,
                           "projects/json/project.yaml", "projects/%s/harness.yaml" % APPROVED, release_tree.AGENTS])
        for rel in rewrites:
            os.chmod(self.t.path(rel), 0o755)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        named = sorted(line.split(" ", 2)[1] for line in out.splitlines() if line.startswith(("wrote ", "rewrote ")))
        self.assertEqual(named, rewrites)
        for rel in named:
            self.assertEqual(os.stat(self.t.path(rel)).st_mode & 0o777, 0o755, rel)


# A fuzz target that private_harnesses holds while the rest of its project publishes (Dispatch issue OSSV-424, K11 and
# K15): zlib/held_target, a copy of checksum_fuzzer, which the release keeps.  zlib enrolled through this repository, so
# build.oss_verify and the port of each build record name the port's internal copy, and the approvals entries name the
# facts pull request on this repository.  Each name of this repository is built at run time from
# schema.INTERNAL_PORT_REPOSITORY: no file of a release may spell it.
HELD = "zlib/held_target"
HELD_NAME = HELD.split("/")[1]
KEPT_NAME = APPROVED.split("/")[1]
PORT_COMMIT = "d" * 40   # helpers.port_built's
BUILT = "b" * 40         # the commit the port's tools/check built (oss_verifier.commit)
LIBRARY_COMMIT = "51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf"
FACTS_PR = "https://github.com/" + schema.INTERNAL_PORT_REPOSITORY + "/pull/52"


def copy_harness(t, name):
    """A second fuzz target of zlib, name, a copy of checksum_fuzzer with its own name and binaries' file names."""
    shutil.copytree(t.path("projects", APPROVED), t.path("projects", "zlib", name))
    rel = "projects/zlib/%s/harness.yaml" % name
    h = t.yaml(rel)
    h.update(harness=name, rocq="OssFuzzTheorems.zlib." + name)
    for b, rec in h["builds"].items():
        rec["file"] = "%s.%s" % (name, b)
    t.put_yaml(rel, h)


def commented(text, held=None):
    """zlib's project.yaml text, as yamlio.dump wrote it, with comments as a person writes them: one at the top, one
    above build, one above the entry of held_target, and the field private_harnesses (when held, its names) in flow
    style, with a comment on its line and one above it.  The cut keeps the first two."""
    out = "# zlib as an enrollment through this repository writes it, with the comments of a person\n" + text
    if held is not None:
        out = out.replace("private_harnesses:\n" + "".join("- %s\n" % n for n in held),
                          "# The fuzz targets that no public repository may hold.\n"
                          "private_harnesses: [%s]  # until the stand-in issue is closed\n" % ", ".join(held))
    out = out.replace("- name: %s\n" % HELD_NAME, "# %s: its files stay in this repository\n- name: %s\n"
                      % (HELD_NAME, HELD_NAME))
    return out.replace("\nbuild:\n", "\n# The OSS Verify port built every binary.\nbuild:\n")


def manifest_text(names):
    """port/manifest.yaml, the manifest tools/check wrote for a build of the fuzz targets names, less its host keys:
    each fuzz target in fuzz_targets, and under its own key in targets, layout and binary_checks."""
    man = {"schema": "oss-verifier/build-manifest/1", "project": "zlib", "repo": "https://github.com/madler/zlib",
           "commit": LIBRARY_COMMIT, "oss_verifier": {"commit": BUILT, "modified": False},
           "builds": list(schema.BUILDS), "fuzz_targets": list(names),
           "targets": {n: {"builds": {b: {"file": "%s.%s" % (n, b), "bytes": 1000,
                                          "sha256": hashlib.sha256(("%s.%s" % (n, b)).encode()).hexdigest()}
                                      for b in schema.BUILDS}} for n in names},
           "layout": {n: {b: {"text_bytes": 900, "static": True} for b in schema.BUILDS} for n in names},
           "binary_checks": {"inputs": {n: ["(the empty input)"] for n in names},
                             "targets": {n: {"plain": {"elf": {"result": "pass"}}} for n in names}}}
    return "# Generated by tools/check; do not edit.\n" + yamlio.dump(man)


def port_files(names):
    """{path under port/projects/zlib/: text} of the port's files for zlib, for a build of the fuzz targets names: the
    maintainers' project.yaml, build.sh, the Dockerfile, the sources table, and each fuzz target's own files."""
    files = {
        "project.yaml": ("# zlib's port, a stand-in of these tests\nrepo: https://github.com/madler/zlib#%s\n"
                         "primary_contact: n/a\nhomepage: https://www.zlib.net/\nlanguage: c\n"
                         "sanitizers: [address, undefined]\nfuzz_targets:\n%s"
                         % (LIBRARY_COMMIT, "".join("  - %s\n" % n for n in names))),
        "build.sh": "#!/bin/bash -eu\n# Builds the fuzz targets of zlib.\n./configure --static && make libz.a\n"
                    + "".join('$CC $CFLAGS -c "$SRC/%s.c" -o "$WORK/%s.o"\n' % (n, n)
                              + '$CC $CFLAGS "$WORK/%s.o" -o "$OUT/%s" $LIB_FUZZING_ENGINE libz.a\n' % (n, n)
                              for n in names),
        "Dockerfile": "RUN fetch-commit $SRC/zlib\n",
        "sources": "git\tzlib\thttps://github.com/madler/zlib\t%s\n" % LIBRARY_COMMIT + "".join(
            "link\ttargets/zlib-%s/%s.c\t%s.c\n" % (n, n, n) for n in names if n != KEPT_NAME),
    }
    for n in names:
        files["%s.c" % n] = "int LLVMFuzzerTestOneInput(const unsigned char *d, unsigned long n) { return 0; }\n"
        if n != KEPT_NAME:
            files["%s.options" % n] = "[libfuzzer]\nmax_len = 4096\n"
    return files


def port_record(t, h, names):
    """{path under provenance/: text} of the build record of zlib's fuzz target h that tools/enroll/facts.py writes for
    an enrollment through this repository whose port built the fuzz targets names: PROVENANCE.yaml and PROVENANCE.md,
    port/manifest.yaml, the port's files under port/projects/zlib/, and LICENSES/."""
    harness = t.yaml("projects/zlib/%s/harness.yaml" % h)
    assets = t.yaml("projects/zlib/project.yaml")["assets"]
    pin = {k: {"file": assets[k]["file"], "sha256": assets[k]["sha256"]}
           for k in ("bin", "src", "src_manifest", "port")}
    record = {
        "schema": "oss-verify-proofs build record v1",
        "entry_point": {"project": "zlib", "harness": h, "function": "LLVMFuzzerTestOneInput",
                        "records": ["projects/zlib/project.yaml", "projects/zlib/%s/harness.yaml" % h]},
        "upstream": {"name": "zlib", "repository": "https://github.com/madler/zlib", "commit": LIBRARY_COMMIT,
                     "licence": "Zlib", "patch_count": 0, "licence_evidence": "a stand-in of these tests"},
        "harness": {"origin": harness["origin"], "source": harness["source"]},
        "port": {"repository": schema.INTERNAL_PORT_REPOSITORY, "commit": PORT_COMMIT, "path": "projects/zlib",
                 "tools": {"commit": "c" * 40, "paths": ["infra/", "tools/"], "built": BUILT,
                           "how": "a stand-in of these tests"},
                 "asset": pin["port"], "files": "port/projects/zlib/ and port/manifest.yaml", "patches": [],
                 "build_system": "cmake", "how_to_rebuild": "a stand-in of these tests"},
        "toolchain": {"clang": "20.1.8", "builder_image": t.yaml("release.yaml")["images"]["builder"][0]},
        "binaries": [{"build": b, "file": r["file"], "bytes": r["bytes"], "sha256": r["sha256"]}
                     for b, r in harness["builds"].items()],
        "binary_asset": pin["bin"], "source_asset": {"src": pin["src"], "src_manifest": pin["src_manifest"]},
        "rebuild": ["all %d binaries of the %d harnesses identical in the second build" % (4 * len(names), len(names))],
        "licence": {"components": [{"component": "zlib", "files": "-", "licence": "Zlib",
                                    "evidence": "a stand-in of these tests", "texts": ["LICENSES/zlib-LICENSE"]}],
                    "not_in_binaries": [], "source_bundle": [pin["src"], pin["src_manifest"], pin["port"]]},
    }
    md = ("# How the binaries of `zlib/%s` were built\n\n| | |\n|---|---|\n"
          "| Port | the internal copy of the OSS Verify port `projects/zlib` at `%s` |\n" % (h, PORT_COMMIT))
    out = {"PROVENANCE.yaml": yamlio.dump(record), "PROVENANCE.md": md, "port/manifest.yaml": manifest_text(names),
           "LICENSES/zlib-LICENSE": "A stand-in for zlib's licence text, for the tests of tools/oft.\n"}
    out.update({"port/projects/zlib/" + rel: text for rel, text in port_files(names).items()})
    return out


class HeldFuzzTarget(unittest.TestCase):
    """oft release-tree and a fuzz target that private_harnesses holds while the rest of its project publishes (Dispatch
    issue OSSV-424, K11 and K15).  zlib enrolled through this repository, with two fuzz targets: checksum_fuzzer, whose
    proof the release keeps, and held_target, held, with a proof that approvals.yaml lists, a counterexample, a lint
    exception, and a build record of each.  The build record of each fuzz target holds the port's files of zlib and
    tools/check's manifest, and both name held_target."""

    PROJECT_YAML = "projects/zlib/project.yaml"

    def setUp(self):
        self.t = Tree()
        self.addCleanup(self.t.close)

    def build(self, held=(HELD_NAME,), record_names=(KEPT_NAME, HELD_NAME)):
        """zlib as above, with private_harnesses held (names), each build record's port naming the fuzz targets
        record_names; rendered, with tools/publish/ as the internal tree has it.  Returns the data of project.yaml
        that the cut keeps."""
        t = self.t
        copy_harness(t, HELD_NAME)
        port_built(t, "zlib")
        data = {}
        for k, v in t.yaml(self.PROJECT_YAML).items():
            data[k] = v
            if k == "harnesses":
                v.append({"name": HELD_NAME, "status": "included"})
                data["private_harnesses"] = list(held)
        data["build"]["oss_verify"]["repository"] = schema.INTERNAL_PORT_REPOSITORY
        t.write(self.PROJECT_YAML, commented(yamlio.dump(data), held))
        for h in (KEPT_NAME, HELD_NAME):
            for rel, text in port_record(t, h, record_names).items():
                t.write("%s/%s" % (layout.provenance_dir("zlib", h, layout.OLD), rel), text)
        for sid in (APPROVED + "/plain_halts", HELD + "/plain_halts"):
            add_proof(t, sid)
        cx = layout.counterexample_dir("zlib", HELD_NAME, "asan_halts", layout.OLD)
        t.put_yaml(cx + "/expect.yaml", {
            "schema": "oss-fuzz-theorems/counterexample/1", "statement": HELD + "/asan_halts", "input": "input.bin",
            "observed": {"build": "asan", "exit": 134, "signal": "SIGABRT"},
            "control": {"input": "control.bin", "exit": 0}, "disclosure": "public",
            "note": "A stand-in counterexample of these tests."})
        t.write(cx + "/input.bin", "x")
        t.write(cx + "/control.bin", "y")
        approve(t, enrolled(APPROVED, pull_request=FACTS_PR), enrolled(HELD, pull_request=FACTS_PR))
        os.makedirs(t.path("tools", "publish"))
        t.write("CHANGELOG.md", "# Changelog\n\n## Unreleased\n\n- Proofs of zlib.\n")
        recount(t)
        self.assertEqual(t.generate(), 0, t.last_output)
        put_exceptions(t, [needed_exception(t, "projects/%s/source/checksum_fuzzer.c" % HELD)])
        self.assertEqual([str(f) for f in t.lint()], [])
        cut = {k: v for k, v in data.items() if k != "private_harnesses"}
        cut["harnesses"] = [e for e in data["harnesses"] if e["name"] not in held]
        if held:
            cut["build"] = dict(cut["build"], oss_verify=dict(cut["build"]["oss_verify"],
                                                              repository=schema.NO_PORT_REPOSITORY))
        return cut

    def assertRefused(self, why):
        """release-tree refuses, says why, and leaves every file of the checkout byte for byte as it was."""
        t = self.t
        before = snapshot(t)
        rc, out = release(t)
        self.assertEqual(rc, 1, out)
        self.assertIn(why, out)
        self.assertIn("nothing changed", out)
        self.assertEqual(snapshot(t), before)

    def test_the_cut_keeps_nothing_of_the_held_fuzz_target_in_either_layout(self):
        """K11 and K15: no folder of zlib/held_target in either layout, no proof of it that approvals.yaml listed, no
        counterexample, no lint exception, no entry or field or comment of either in project.yaml, which keeps every
        other byte, and no tools/publish/private-harnesses.txt.  In the kept build record the port's files of
        held_target are gone, and the manifest, the maintainers' project.yaml, build.sh and the sources table lose
        exactly the lines that name it.  The port reads `none` with the port commit's id in project.yaml and in the
        kept build record.  No file of the cut names held_target (by the rule of disclosure.held_match, which its Rocq
        module and generated files also match) or this repository, and `oft lint` and `oft generate --check` pass."""
        cut = self.build()
        before = snapshot(self.t)
        for where, t in ((layout.OLD, self.t), (layout.NEW, ported_copy(self, self.t))):
            with self.subTest(layout=where):
                record = layout.provenance_dir("zlib", KEPT_NAME, where)
                rc, out = release(t)
                self.assertEqual(rc, 0, out)
                self.assertIn("held back by private_harnesses: %s\n" % HELD, out)
                for rel in [layout.statement_dir("zlib", HELD_NAME), "tools/publish"] + [
                        kind("zlib", HELD_NAME, lay) for lay in layout.LAYOUTS
                        for kind in (layout.proofs_dir, layout.counterexamples_dir, layout.findings_dir)]:
                    self.assertFalse(os.path.lexists(t.path(rel)), rel)
                files = snapshot(t)
                internal = schema.INTERNAL_PORT_REPOSITORY.casefold()
                for rel, data in files.items():
                    text = data.decode("utf-8", "replace")
                    self.assertEqual(disclosure.held_match(rel, [HELD]) + disclosure.held_match(text, [HELD]), [], rel)
                    self.assertNotIn(internal, text.casefold(), rel)
                self.assertEqual(t.read(self.PROJECT_YAML), commented(yamlio.dump(cut)))
                self.assertEqual(t.yaml(self.PROJECT_YAML)["build"]["oss_verify"],
                                 {"repository": "none", "commit": PORT_COMMIT, "path": "projects/zlib"})
                old = yamlio.load(before[layout.record_path("zlib", KEPT_NAME, layout.OLD)].decode(), "record")
                old["port"]["repository"] = "none"
                self.assertEqual(t.yaml(record + "/PROVENANCE.yaml"), old)
                kept_port = {"port/manifest.yaml": manifest_text([KEPT_NAME])}
                kept_port.update({"port/projects/zlib/" + rel: text for rel, text in port_files([KEPT_NAME]).items()})
                self.assertEqual({rel[len(record) + 1:]: data.decode() for rel, data in files.items()
                                  if rel.startswith(record + "/port/")}, kept_port)
                self.assertEqual(t.yaml(EXCEPTIONS)["exceptions"], [])
                self.assertEqual([str(f) for f in t.lint()], [])
                self.assertEqual(t.generate(check=True), 0, t.last_output)

    def test_a_kept_file_that_names_the_held_fuzz_target_its_module_or_this_repository_is_refused(self):
        """K11's refusals, each of a kept CHANGELOG.md, with "nothing changed": the held entry in each form of the rule
        of disclosure.held_match, the Rocq module of held_target in any case, and this repository's full name in any
        case."""
        self.build()
        internal = schema.INTERNAL_PORT_REPOSITORY
        held = "%s, a held fuzz target (private_harnesses of zlib)" % HELD
        module = "OssFuzzTheorems.zlib.held_target, the Rocq module of held fuzz target %s" % HELD
        repository = "%s, the name of this internal repository, which no release names" % internal
        for text, why in (("Fixed %s.\n" % HELD, held), ("See projects/%s/harness.yaml.\n" % HELD, held),
                          ("The held_target build.\n", held),
                          ("Require OssFuzzTheorems.zlib.held_target.Statements.\n", module),
                          ("Require ossfuzztheorems.ZLIB.HELD_TARGET.\n", module),
                          ("Built from %s.\n" % internal, repository),
                          ("Built from https://github.com/%s/pull/52.\n" % internal.upper(), repository)):
            with self.subTest(text=text):
                self.t.write("CHANGELOG.md", text)
                self.assertRefused("error: CHANGELOG.md names %s" % why)

    def test_an_s_whose_private_harnesses_txt_is_missing_or_differs_from_its_fields_is_refused(self):
        """The readers of the held entries outside oft read the file, and the cut reads the fields: an S in which the
        two disagree is refused, with "nothing changed"."""
        self.build()
        rel = generate.PRIVATE_HARNESSES
        os.remove(self.t.path(rel))
        self.assertRefused("error: %s is missing, and the private_harnesses fields hold %s" % (rel, HELD))
        other = "zlib/held_target_other"
        for text, lists in (("", "no fuzz target"), ("%s\n%s\n" % (HELD, other), "%s, %s" % (HELD, other)),
                            (other + "\n", other)):
            with self.subTest(text=text):
                self.t.write(rel, text)
                self.assertRefused("error: %s lists %s, and the private_harnesses fields hold %s" % (rel, lists, HELD))

    def test_a_name_with_no_harness_keeps_the_fuzz_target_and_its_port(self):
        """The negative control of K11: private_harnesses names held_target_unheld, which no harness has.  held_target
        ships with its folder, its proof, its entry and its files in each build record's copy of the port, byte for
        byte.  zlib still holds a fuzz target, so its port reads `none` and the field goes."""
        cut = self.build(held=("%s_unheld" % HELD_NAME,))
        before = snapshot(self.t)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertIn("held back by private_harnesses: %s_unheld\n" % HELD, out)
        self.assertTrue(os.path.isfile(self.t.path(layout.proof_dir("zlib", HELD_NAME, "plain_halts", layout.OLD),
                                                   "Proof.v")))
        self.assertTrue(os.path.isfile(self.t.path(layout.statement_dir("zlib", HELD_NAME), "harness.yaml")))
        self.assertEqual(self.t.read(self.PROJECT_YAML), commented(yamlio.dump(cut)))
        self.assertIn({"name": HELD_NAME, "status": "included"}, self.t.yaml(self.PROJECT_YAML)["harnesses"])
        after = snapshot(self.t)
        for h in (KEPT_NAME, HELD_NAME):
            port = layout.provenance_dir("zlib", h, layout.OLD) + "/port/"
            self.assertEqual({rel: data for rel, data in after.items() if rel.startswith(port)},
                             {rel: data for rel, data in before.items() if rel.startswith(port)}, h)
        self.assertEqual([str(f) for f in self.t.lint()], [])

    def test_a_kept_file_that_names_another_fuzz_target_ships(self):
        """The negative control of K11's search: names that the rule of disclosure.held_match tells from
        zlib/held_target (another project's held_target_other, a longer harness name) are no disclosure."""
        self.build()
        text = "Proofs of json/held_target_other and of zlib/held_target_v2 come later.\n"
        self.t.write("CHANGELOG.md", text)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.t.read("CHANGELOG.md"), text)

    def test_a_kept_record_whose_port_copy_names_no_held_fuzz_target_is_left_as_it_is(self):
        """The negative control of K15: the build records hold a port built before held_target existed, so the copy
        of the port names checksum_fuzzer alone.  The cut leaves every file of it byte for byte, and writes only the
        port repository `none` into the record itself."""
        self.build(record_names=(KEPT_NAME,))
        port = layout.provenance_dir("zlib", KEPT_NAME, layout.OLD) + "/port/"
        before = {rel: data for rel, data in snapshot(self.t).items() if rel.startswith(port)}
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertEqual({rel: data for rel, data in snapshot(self.t).items() if rel.startswith(port)}, before)
        self.assertEqual(self.t.yaml(layout.record_path("zlib", KEPT_NAME, layout.OLD))["port"]["repository"], "none")

    def test_a_kept_fuzz_target_whose_name_continues_the_held_name_ships(self):
        """zlib/held_target_v2 is no held fuzz target, though its name starts with held_target's: its folder, its proof,
        its build record and its entry in project.yaml ship.  A cut that matched a held name as a prefix of a path would
        take them out."""
        t, sibling = self.t, HELD_NAME + "_v2"
        self.build()
        copy_harness(t, sibling)
        t.write(self.PROJECT_YAML, t.read(self.PROJECT_YAML).replace(
            "# The fuzz targets", "- name: %s\n  status: included\n# The fuzz targets" % sibling, 1))
        for rel, text in port_record(t, sibling, (KEPT_NAME, HELD_NAME, sibling)).items():
            t.write("%s/%s" % (layout.provenance_dir("zlib", sibling, layout.OLD), rel), text)
        add_proof(t, "zlib/%s/plain_halts" % sibling)
        approve(t, enrolled(APPROVED, pull_request=FACTS_PR), enrolled(HELD, pull_request=FACTS_PR),
                enrolled("zlib/" + sibling, pull_request=FACTS_PR))
        recount(t)
        self.assertEqual(t.generate(), 0, t.last_output)
        rc, out = release(t)
        self.assertEqual(rc, 0, out)
        for rel in (layout.statement_dir("zlib", sibling) + "/harness.yaml",
                    layout.proof_dir("zlib", sibling, "plain_halts", layout.OLD) + "/Proof.v",
                    layout.record_path("zlib", sibling, layout.OLD)):
            self.assertTrue(os.path.isfile(t.path(rel)), rel)
        self.assertIn(sibling, [e["name"] for e in t.yaml(self.PROJECT_YAML)["harnesses"]])

    def test_an_empty_field_of_another_project_goes_from_the_cut_with_its_comments(self):
        """json holds nothing: its `private_harnesses: []` and the comment line above it are no part of the release
        either, and every other byte of json's project.yaml stays."""
        self.build()
        rel = "projects/json/project.yaml"
        before = self.t.read(rel)
        self.t.write(rel, before + "# nothing of json is held yet\nprivate_harnesses: []  # empty\n")
        self.assertEqual(self.t.generate(check=True), 0, self.t.last_output)
        rc, out = release(self.t)
        self.assertEqual(rc, 0, out)
        self.assertEqual(self.t.read(rel), before)


class KeepRule(unittest.TestCase):
    """R1's keep rule, the inventory of its class (OSSV-844, D1 of its plan): `oft release-tree` keeps each
    proof folder of each fuzz target that is not held, whatever approvals.yaml lists and whether or not there is one,
    and leaves out each proof that a hold or a refutation keeps out.  ROWS is the table: each member of the class, the
    fixture that makes it, and how the cut leaves it.  A hold reason added later gets a row."""

    def tree(self):
        t = Tree()
        self.addCleanup(t.close)
        return t

    def render(self, t):
        """Give t the CODEOWNERS of this repository, which the cut removes, and render it."""
        t.write(".github/CODEOWNERS", CODEOWNERS)
        self.assertEqual(t.generate(), 0, t.last_output)

    # The fixtures.  Each returns the checkouts to cut, as [(layout, Tree)].

    def no_approvals_held_by_rules(self):
        """No approvals.yaml.  zlib publishes: checksum_fuzzer holds a proof of plain_halts that no entry lists and a
        refuting proof of asan_halts, beside its proof library and its build record; api-driver's proofs folder holds
        only lib/ and provenance/ (and, in the per-project layout, its barrier dune); held_target, a copy of
        checksum_fuzzer with a proof, is held by private_harnesses.  standin is `release: private`, with a proof.  json
        has curl's shape: it is `release: private`, and its private_harnesses holds fuzz-extra, a second fuzz target
        of it, with a proof.  The tree is cut as it is, in the old layout, and as a copy ported to the per-project
        layout."""
        t = self.tree()
        add_proof(t, APPROVED + "/plain_halts")
        add_proof(t, APPROVED + "/asan_halts")
        refute(t, APPROVED + "/asan_halts")
        for p, h in (unit.split("/") for unit in (APPROVED, UNAPPROVED)):
            t.write(layout.proof_lib_dir(p, h, layout.OLD) + "/Shared.v", "Definition one := 1.\n")
            t.write(layout.provenance_dir(p, h, layout.OLD) + "/PROVENANCE.md", "The build record.\n")
        copy_harness(t, HELD_NAME)
        rel = "projects/zlib/project.yaml"
        y = t.yaml(rel)
        y["harnesses"].append({"name": HELD_NAME, "status": "included"})
        t.put_yaml(rel, y)
        hold_fuzz_target(t, HELD)
        add_proof(t, HELD + "/plain_halts")
        add_standin(t)
        make_private(t, "standin")
        add_proof(t, "standin/standin_eval_fuzzer/plain_halts")
        add_json_oss_verify_target(t)
        make_private(t, "json")
        hold_fuzz_target(t, "json/fuzz-extra")
        add_proof(t, "json/fuzz-extra/plain_halts")
        recount(t)
        self.render(t)
        self.assertFalse(os.path.lexists(t.path("approvals.yaml")))
        held = facts.hold(facts.load(t.root))
        self.assertEqual((held.whole, held.entries, held.ids), ({"json", "standin"}, {HELD, "json/fuzz-extra"}, set()))
        u = ported_copy(self, t)
        self.assertEqual(sorted(os.listdir(u.path(layout.proofs_dir("zlib", "api-driver", layout.NEW)))),
                         ["dune", "lib", "provenance"])
        return [(layout.OLD, t), (layout.NEW, u)]

    def a_sibling_listed(self):
        """approvals.yaml lists plain_halts of checksum_fuzzer, with asan_halts, which has no proof, and json's
        enrollment entry (a ceiling) lists plain_halts, which has none either.  checksum_fuzzer's proof of ubsan_agrees
        and api-driver's of ubsan_agrees are in no entry."""
        t = self.tree()
        for sid in (APPROVED + "/plain_halts", APPROVED + "/ubsan_agrees", UNAPPROVED + "/ubsan_agrees"):
            add_proof(t, sid)
        self.render(t)
        approve(t, entry(APPROVED, statements=["plain_halts", "asan_halts"]), enrolled(RELEASED))
        self.assertEqual(rules.check(facts.load(t.root)), [])
        return [(layout.OLD, t)]

    def finding(self, state, enrolled=True):
        """No approvals.yaml.  checksum_fuzzer holds proofs of plain_halts, ubsan_agrees and asan_agrees, and api-driver
        one of ubsan_agrees, with no proof library; zlib's finding is in state (finding_hold)."""
        t = self.tree()
        for sid in (APPROVED + "/plain_halts", APPROVED + "/ubsan_agrees", APPROVED + "/asan_agrees",
                    UNAPPROVED + "/ubsan_agrees"):
            add_proof(t, sid)
        finding_hold(t, state, enrolled)
        self.render(t)
        return t

    def held_whole(self, state, enrolled=True):
        """finding, whose finding holds zlib whole."""
        t = self.finding(state, enrolled)
        self.assertEqual(facts.hold(facts.load(t.root)), facts.Hold({"zlib"}, set(), {}))
        return [(layout.OLD, t)]

    def open_finding_not_enrolled(self):
        return self.held_whole("open", enrolled=False)

    def patched_finding(self):
        return self.held_whole("patched")

    def reported_finding(self):
        return self.held_whole("reported")

    def open_finding_enrolled(self):
        """finding, whose open finding of enrolled zlib holds back asan_agrees and its pair's statements alone."""
        t = self.finding("open")
        self.assertEqual(facts.hold(facts.load(t.root)), facts.Hold(set(), set(), {"zlib": {
            "checksum_fuzzer/asan_agrees", "checksum_fuzzer/asan_disagrees_at_most",
            "checksum_fuzzer/asan_agreement_decidable"}}))
        return [(layout.OLD, t)]

    # The fates.  Each asserts how the cut, in layout where and with output out, left t's subject.

    def assertKept(self, t, where, out, sid):
        """The proof folder of sid is in the cut, and the index the cut renders says that sid is proved."""
        self.assertIn(sid, proof_folders(t))
        self.assertEqual(index_status(t).get(sid), "proved")

    def assertLibKept(self, t, where, out, unit):
        """The fuzz target's proof library and build record stay with its kept proofs, and the cut names the library
        it keeps while it removes a statement folder beside it (release_tree.PARTIAL)."""
        p, h = unit.split("/")
        for rel in (layout.proof_lib_dir(p, h, where) + "/Shared.v",
                    layout.provenance_dir(p, h, where) + "/PROVENANCE.md"):
            self.assertTrue(os.path.isfile(t.path(rel)), rel)
        self.assertIn(release_tree.PARTIAL % unit + "\n", out)

    def assertGone(self, t, where, out, subject):
        """No proof folder of subject, a statement id, a fuzz target or a project, is in the cut."""
        self.assertEqual(sorted(sid for sid in proof_folders(t) if (sid + "/").startswith(subject + "/")), [])

    def assertNothingOf(self, t, where, out, unit):
        """No proof folder of the fuzz target unit is in the cut, nor any folder of it in either layout."""
        self.assertGone(t, where, out, unit)
        p, h = unit.split("/")
        for rel in [layout.statement_dir(p, h)] + [kind(p, h, lay) for lay in layout.LAYOUTS for kind in (
                layout.proofs_dir, layout.counterexamples_dir, layout.findings_dir)]:
            self.assertFalse(os.path.lexists(t.path(rel)), rel)

    def assertRefuted(self, t, where, out, sid):
        """The refuting proof of sid is not in the cut, and the output names it."""
        self.assertGone(t, where, out, sid)
        self.assertIn("held back as a refutation: %s\n" % sid, out)

    def assertRemovedWhole(self, t, where, out, unit):
        """The fuzz target's proofs folder is not in the cut, in either layout, and its statement folder is."""
        p, h = unit.split("/")
        for lay in layout.LAYOUTS:
            self.assertFalse(os.path.lexists(t.path(layout.proofs_dir(p, h, lay))), lay)
        self.assertTrue(os.path.isfile(t.path(layout.statement_dir(p, h), "harness.yaml")))

    # (member, fixture, fate, subjects)
    ROWS = (
        ("unheld, listed by no approvals.yaml entry, with no approvals.yaml", no_approvals_held_by_rules, assertKept,
         (APPROVED + "/plain_halts",)),
        ("the proof library and build record of a kept fuzz target whose refuting proof goes",
         no_approvals_held_by_rules, assertLibKept, (APPROVED,)),
        ("unheld, its fuzz target listed with another statement: both", a_sibling_listed, assertKept,
         (APPROVED + "/plain_halts", APPROVED + "/ubsan_agrees")),
        ("unheld, its fuzz target in no entry of an approvals.yaml", a_sibling_listed, assertKept,
         (UNAPPROVED + "/ubsan_agrees",)),
        ("project release: private", no_approvals_held_by_rules, assertGone, ("standin",)),
        ("project held whole by an open finding of a project that is not enrolled", open_finding_not_enrolled,
         assertGone, ("zlib",)),
        ("project held whole by a patched finding", patched_finding, assertGone, ("zlib",)),
        ("project held whole by a reported finding", reported_finding, assertGone, ("zlib",)),
        ("statement held by an open finding of an enrolled project", open_finding_enrolled, assertGone,
         (APPROVED + "/asan_agrees",)),
        ("the siblings of that statement", open_finding_enrolled, assertKept,
         (APPROVED + "/plain_halts", APPROVED + "/ubsan_agrees")),
        ("fuzz target of private_harnesses, curl's shape (its project release: private)", no_approvals_held_by_rules,
         assertNothingOf, ("json/fuzz-extra",)),
        ("fuzz target of private_harnesses, of a project that publishes", no_approvals_held_by_rules, assertNothingOf,
         (HELD,)),
        ("refuting proof", no_approvals_held_by_rules, assertRefuted, (APPROVED + "/asan_halts",)),
        ("fuzz target whose proofs folder holds only lib/, provenance/, dune", no_approvals_held_by_rules,
         assertRemovedWhole, (UNAPPROVED,)),
    )

    def test_each_proof_folder_is_kept_or_left_out_by_its_hold(self):
        """N1: each row of ROWS, after the cut of its fixture, which completes (run returns 0), counts in its summary
        line the proof folders it keeps and no other, and leaves a release that `oft generate --check` and `oft lint`
        pass."""
        for fixture in dict.fromkeys(row[1] for row in self.ROWS):
            with self.subTest(fixture=fixture.__name__):
                for where, t in fixture(self):
                    rc, out = release(t)
                    self.assertEqual(rc, 0, out)
                    for member, of, fate, subjects in self.ROWS:
                        for subject in subjects if of is fixture else ():
                            with self.subTest(member=member, subject=subject, layout=where):
                                fate(self, t, where, out, subject)
                    self.assertIn("oft release-tree: kept %d proof(s) of " % len(proof_folders(t)), out)
                    self.assertEqual(t.generate(check=True), 0, t.last_output)
                    self.assertEqual([str(x) for x in t.lint()], [])

    def test_the_output_names_no_listed_statement_and_no_ceiling(self):
        """N2: the cut no longer reads approvals.yaml for the proofs it keeps, so it names no listed statement that has
        no proof and counts none of an enrollment entry (a ceiling).  After the cut of the fixture of ROWS that has an
        approvals.yaml (a_sibling_listed, whose entries list such statements), no line of the output says `listed` or
        `ceiling`, and the summary line ends with the paths the cut removed."""
        [(_, t)] = self.a_sibling_listed()
        rc, out = release(t)
        self.assertEqual(rc, 0, out)
        self.assertEqual([line for line in out.splitlines() if "listed" in line or "ceiling" in line], [])
        self.assertEqual([line for line in out.splitlines() if line.startswith("oft release-tree: ")],
                         ["oft release-tree: kept 3 proof(s) of 2 fuzz target(s); removed 0 path(s) of proofs folders; "
                          "removed approvals.yaml and .github/CODEOWNERS"])


class CutLineEdits(unittest.TestCase):
    """The line edits of the cut for a held fuzz target (release_tree.cut_project_yaml, cut_port_text): each removes
    whole lines and keeps every other byte, in the shapes a person or a tool writes."""

    def test_the_field_goes_with_the_comments_above_on_and_under_it(self):
        text = ("project: p1\n# kept: the comment of harnesses\nharnesses:\n- name: kept_target\n"
                "# about held_target, above its entry\n- {name: held_target, status: included}\n"
                "# kept: directly above an empty line\n\n"
                "# the hold, above the field\nprivate_harnesses:   # on the field's line\n"
                "- held_target  # on an item\n  # under the field\nbuild:\n  oss_verify:\n"
                "    repository: \"%s\"  # the port\n    commit: %s\n" % (schema.INTERNAL_PORT_REPOSITORY, "d" * 40))
        self.assertEqual(release_tree.cut_project_yaml(text, ("held_target",), True),
                         "project: p1\n# kept: the comment of harnesses\nharnesses:\n- name: kept_target\n"
                         "# kept: directly above an empty line\n\nbuild:\n  oss_verify:\n"
                         "    repository: none  # the port\n    commit: %s\n" % ("d" * 40))

    def test_a_yaml_key_or_item_that_names_a_held_fuzz_target_goes_whole(self):
        """Each block that names it goes whole, as a key with its value or as a list item; the first key of a list
        item takes the item; a line that is no part of the YAML structure (a comment) goes alone."""
        text = ("fuzz_targets:\n- kept_target\n- held_target\ntargets:\n  held_target:\n    builds:\n"
                "      plain: {file: held_target.plain}\n  kept_target:\n    builds: {}\n"
                "uninstrumented:\n- name: held_target.o\n  kind: libc\n- name: kept.o\n  kind: libc\n"
                "# built with held_target\nnote: |\n  the build of\n  held_target too\nend: true\n")
        self.assertEqual(release_tree.cut_port_text("manifest.yaml", text, ["p1/held_target"]),
                         "fuzz_targets:\n- kept_target\ntargets:\n  kept_target:\n    builds: {}\n"
                         "uninstrumented:\n- name: kept.o\n  kind: libc\nend: true\n")

    def test_a_line_of_any_other_file_that_names_a_held_fuzz_target_goes_alone(self):
        text = "make held_target\nmake kept_target held_target_v2\nrow\tp1/held_target\tx\n"
        self.assertEqual(release_tree.cut_port_text("build.sh", text, ["p1/held_target"]),
                         "make kept_target held_target_v2\n")


class CutPackReadings(unittest.TestCase):
    """release_tree.cut_pack_readings: the packer's measured tables name one unit a row, so the cut takes out the
    rows of the units it does not carry.  A row for a held project's fuzz target would say in the release that the
    target exists, which is the one thing a hold withholds."""

    def tree_with(self, text):
        t = Tree(render=False)
        self.addCleanup(t.close)
        t.write(release_tree.PACK, text)
        return t

    TABLE = ('"""a stand-in packer."""\n'
             "SWEEP_TIMES = (\n"
             '    ("a/one", "r1", 10, "finished"),\n'
             '    ("held/two", "r1", 20, "finished"),\n'
             ")\n"
             "\n"
             "FARM_CHECKS = (\n"
             '    ("a/one", "farm/20261107t181007z-ad5fe9", "2026-11-07"),\n'
             '    ("held/two", "farm/20261107t222300z-b2f735", "2026-11-07"),\n'
             ")\n"
             "\n"
             'OTHER = (("not a row", 1),)\n')

    def test_the_rows_of_a_unit_the_cut_does_not_carry_go_and_the_rest_stay(self):
        t = self.tree_with(self.TABLE)
        text, gone = release_tree.cut_pack_readings(t, {"a/one"})
        self.assertEqual(gone, ["held/two"])
        self.assertNotIn("held/two", text)
        self.assertIn('    ("a/one", "r1", 10, "finished"),\n', text)
        self.assertIn('    ("a/one", "farm/20261107t181007z-ad5fe9", "2026-11-07"),\n', text)
        # everything outside the two tables is kept as written, the tuple that is no row among it
        self.assertIn('OTHER = (("not a row", 1),)\n', text)
        self.assertTrue(text.startswith('"""a stand-in packer."""\n'))

    def test_nothing_is_rewritten_when_the_cut_carries_every_unit(self):
        t = self.tree_with(self.TABLE)
        self.assertIsNone(release_tree.cut_pack_readings(t, {"a/one", "held/two"}))

    def test_a_table_line_that_is_no_row_stops_the_cut(self):
        """A table nobody can read row by row would ship rows nobody filtered, so it is an error and not a file
        copied through."""
        t = self.tree_with(self.TABLE.replace('    ("held/two", "r1", 20, "finished"),\n', "    # a comment\n"))
        with self.assertRaises(ValueError) as e:
            release_tree.cut_pack_readings(t, {"a/one"})
        self.assertIn("is no row naming a unit", str(e.exception))

    def test_the_tracked_packer_is_read_row_by_row_and_keeps_every_unit_it_carries(self):
        """The real tools/oft/pack.py: with every unit it names carried, no row drops; with one held, that one
        unit's rows drop and nothing else moves."""
        from oft import pack
        t = Tree(render=False)
        self.addCleanup(t.close)
        with open(os.path.join(REPO, release_tree.PACK), encoding="utf-8") as f:
            t.write(release_tree.PACK, f.read())
        units = set(pack.sweep()) | set(pack.farm_checks())
        self.assertIsNone(release_tree.cut_pack_readings(t, units))
        # one of its own units, chosen from the table rather than named here: a test ships too
        held = sorted(units)[0]
        kept = sorted(units)[-1]
        text, gone = release_tree.cut_pack_readings(t, units - {held})
        self.assertEqual(gone, [held])
        self.assertNotIn(held, text)
        self.assertIn(kept, text)


class CutHandlerRows(unittest.TestCase):
    """release_tree.cut_handler_rows: failure_handlers.tsv names one unit a row, so the cut takes out the rows of the
    tree's units it does not carry and every row of a project held back whole, and keeps every other row; it reads the
    table as the publication gate does, and refuses what the gate would."""

    TABLE = "project\tharness\tvalue\tevidence\na\tone\tnone\tread\nheld\ttwo\tnone\tread\ngone\tthree\tnone\tread\n"

    def tree_with(self, text):
        t = Tree(render=False)
        self.addCleanup(t.close)
        t.write(release_tree.HANDLERS, text)
        return t

    def test_the_rows_of_a_withheld_unit_go_and_the_rest_stay(self):
        text, gone = release_tree.cut_handler_rows(self.tree_with(self.TABLE), {"held/two"}, set())
        self.assertEqual((text, gone), ("project\tharness\tvalue\tevidence\na\tone\tnone\tread\n"
                                        "gone\tthree\tnone\tread\n", ["held/two"]))
        self.assertIsNone(release_tree.cut_handler_rows(self.tree_with(self.TABLE), set(), set()))

    def test_every_row_of_a_project_held_back_whole_goes_even_a_fuzz_target_the_tree_no_longer_has(self):
        # facts.py never removes a row, so a held project may have rows of fuzz targets the tree no longer lists,
        # and the publication gate refuses a release that keeps any row of a project held back whole (#2647's review
        # of record, S1)
        table = self.TABLE + "held\told_one\tnone\tread\n"
        text, gone = release_tree.cut_handler_rows(self.tree_with(table), {"held/two"}, {"held"})
        self.assertEqual((text, gone), ("project\tharness\tvalue\tevidence\na\tone\tnone\tread\n"
                                        "gone\tthree\tnone\tread\n", ["held/old_one", "held/two"]))
        # with no unit of the tree withheld, the held project's rows still go
        self.assertEqual(release_tree.cut_handler_rows(self.tree_with(table), set(), {"held"})[1],
                         ["held/old_one", "held/two"])

    def test_a_table_the_gate_would_refuse_stops_the_cut(self):
        # the cut refuses each table the publication gate refuses (tools/publish/verify's handler_rows_held), so a
        # tree the cut accepts makes a release the gate accepts
        for text in (self.TABLE + "a line\n", self.TABLE + "\n", self.TABLE.replace("project\t", "who\t", 1),
                     self.TABLE.replace("held\ttwo", "\ufeffheld\ttwo"), self.TABLE.replace("held\ttwo", "Held\ttwo"),
                     self.TABLE.replace("held\ttwo", " held\ttwo"), self.TABLE.replace("\n", "\r\n"),
                     self.TABLE.replace("\n", "\r"), self.TABLE.replace("\n", "\u2028")):
            with self.subTest(text=text), self.assertRaises(ValueError):
                release_tree.cut_handler_rows(self.tree_with(text), {"held/two"}, {"held"})

    @unittest.skipUnless(INTERNAL_TREE, NOT_INTERNAL)
    def test_the_gate_accepts_every_table_the_cut_writes(self):
        # the cut's output, through the gate's own reader: no held row, no malformed line
        import importlib.machinery
        import importlib.util
        verify_path = os.path.join(REPO, "tools", "publish", "verify")
        loader = importlib.machinery.SourceFileLoader("publish_verify", verify_path)
        spec = importlib.util.spec_from_loader("publish_verify", loader)
        verify = importlib.util.module_from_spec(spec)
        loader.exec_module(verify)
        table = self.TABLE + "held\told_one\tnone\tread\n"
        text, _ = release_tree.cut_handler_rows(self.tree_with(table), {"held/two"}, {"held"})
        self.assertEqual(verify.handler_rows_held(text.encode(), {"held"}), ([], []))
        # and the control: the uncut table holds held rows the gate refuses
        self.assertEqual(len(verify.handler_rows_held(table.encode(), {"held"})[0]), 2)


class StripInternalBlocks(unittest.TestCase):
    """release_tree.strip_internal_blocks: a marked block of AGENTS.md is text for this repository only, so the cut
    takes out each line from one that holds BEGIN-INTERNAL through the next one that holds END-INTERNAL, each with its
    own line end, and keeps every other line as it is.  It refuses a marker line with no partner."""

    START, END = "<!-- BEGIN-INTERNAL: for this repository only -->", "<!-- END-INTERNAL -->"

    def test_internal_block_none_leaves_the_text_as_it_is(self):
        for text in ("", "A kept line.\nAnother kept line.\n",
                     "A kept line about begin-internal and end-internal, in lower case.\n",
                     "A kept line.\nThe last line, with no line end"):
            with self.subTest(text=text):
                self.assertEqual(release_tree.strip_internal_blocks(text), text)

    def test_internal_block_at_the_end_goes_with_its_line_ends(self):
        # the shape AGENTS.md has: the block after the last paragraph, a blank line after its start, its end the last
        # line
        kept = "# Agents\n\nA kept paragraph line.\n"
        text = (kept + self.START + "\n\n## Only here\n\nA line for this repository only.\nAnother one.\n" + self.END
                + "\n")
        self.assertEqual(release_tree.strip_internal_blocks(text), kept)

    def test_internal_block_end_line_with_no_line_end_goes_too(self):
        text = "A kept line.\n" + self.START + "\nNot for a release.\n" + self.END
        self.assertEqual(release_tree.strip_internal_blocks(text), "A kept line.\n")

    def test_internal_block_that_is_the_whole_text_leaves_an_empty_text(self):
        # an empty text, not None: the release keeps the file, empty
        for text in (self.START + "\nNot for a release.\n" + self.END + "\n", self.START + "\n" + self.END):
            with self.subTest(text=text):
                self.assertEqual(release_tree.strip_internal_blocks(text), "")

    def test_internal_blocks_two_are_both_taken_out(self):
        text = ("before\n" + self.START + "\none\n" + self.END + "\nbetween\n" + self.START + "\ntwo\n" + self.END
                + "\nafter\n")
        self.assertEqual(release_tree.strip_internal_blocks(text), "before\nbetween\nafter\n")

    def test_internal_block_line_ends_other_than_lf(self):
        """Every line break that str.splitlines knows ends a line, and each kept line keeps its own."""
        b, e = self.START, self.END
        for name, text, want in (
                ("CRLF", "kept\r\n" + b + "\r\nbody\r\n" + e + "\r\nafter\r\n", "kept\r\nafter\r\n"),
                ("a lone CR", "kept\r" + b + "\rbody\r" + e + "\rafter\r", "kept\rafter\r"),
                ("a form feed", "kept\x0c" + b + "\x0cbody\n" + e + "\x0cafter\n", "kept\x0cafter\n"),
                ("U+0085", "kept\x85" + b + "\x85body\x85" + e + "\x85after\x85", "kept\x85after\x85"),
                ("U+2028", "kept\u2028" + b + "\u2028body\u2028" + e + "\u2028after\u2028", "kept\u2028after\u2028"),
                ("a marker after a U+0085 and a CR", "a\x85b\rBEGIN-INTERNAL\rx END-INTERNAL y\n", "a\x85b\r"),
                ("each kept line end as it is", "one\r\ntwo\rthree\n" + b + "\r\nbody\x85" + e + "\u2028four",
                 "one\r\ntwo\rthree\nfour")):
            with self.subTest(name):
                self.assertEqual(release_tree.strip_internal_blocks(text), want)

    def test_internal_block_refusals(self):
        b, e = self.START, self.END
        for text, why in (
                ("one\n<!-- BEGIN-INTERNAL END-INTERNAL -->\ntwo\n",
                 "line 2 holds both BEGIN-INTERNAL and END-INTERNAL"),
                (b + "\none\n" + b + "\ntwo\n" + e + "\n", "line 3 starts a block inside the block that line 1 starts"),
                ("one\ntwo\n" + e + "\n", "line 3 ends a block that no line starts"),
                (b + "\none\n" + e + "\n" + e + "\n", "line 4 ends a block that no line starts"),
                ("one\n" + b + "\ntwo\n", "line 2 starts a block that no line ends"),
                (b + "\none\n" + e + "\ntwo\n" + b + "\nthree", "line 5 starts a block that no line ends"),
                ("one\r" + b + "\rtwo\r", "line 2 starts a block that no line ends")):
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, "^%s$" % re.escape(why)):
                release_tree.strip_internal_blocks(text)


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
    names that merge, and is a ceiling: it lists the statements its enrollment facts pull requests wrote (the approvals
    plan).  The rules still check it (rules._approvals), and a cut with such entries completes; which proofs the cut
    keeps is KeepRule's, whatever an entry lists."""

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
