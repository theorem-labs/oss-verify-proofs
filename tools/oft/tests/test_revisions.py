"""oft revisions: each statement against the previous release, both fingerprinted by today's tools."""
import contextlib
import io
import os
import shutil
import unittest
from unittest import mock

import yaml

from oft import facts, revisions, shapes, yamlio
from oft.tests.helpers import recount, tree

HARNESS = "projects/zlib/checksum_fuzzer/harness.yaml"
STATEMENTS = "projects/zlib/checksum_fuzzer/Statements.v"
PROVED = "zlib/checksum_fuzzer/plain_halts"
WITHHELD = "zlib/api-driver/asan_ubsan_agrees"   # the fixture's withheld statement: no fingerprint to compare


def fingerprints(t, tag=facts.FINGERPRINT_TAG):
    with mock.patch.object(facts, "FINGERPRINT_TAG", tag):
        return {s.id: s.fingerprint for s in facts.load(t.root).statements()}


def prove(t, sid, pin):
    d = "proofs/%s/" % sid
    t.put_yaml(d + "proof.yaml", {"schema": "oss-fuzz-theorems/proof/1", "proves": sid, "fingerprint": pin})
    t.write(d + "Proof.v", "Theorem holds : True. Proof. exact I. Qed.\n")


def raw(t, rel):
    with open(t.path(rel), encoding="utf-8", newline="") as f:
        return f.read()


def drop_project(t, name):
    """Remove a project from a release tree, as a release that holds it back leaves it out, and write the counts of
    what is left (what `oft release-tree` does, rules.counts)."""
    for rel in (("projects", name), ("counterexamples", name), ("proofs", name)):
        shutil.rmtree(t.path(*rel), ignore_errors=True)
    note = t.path("notes", name + ".md")
    if os.path.isfile(note):
        os.remove(note)
    recount(t)
    assert t.generate() == 0, t.last_output


def run(cur, prev, **kw):
    """(exit status, output, {id: the other columns}) of `oft revisions` in cur against prev."""
    buf = io.StringIO()
    rc = revisions.run(cur.root, prev.root, out=buf, **kw)
    out = buf.getvalue()
    return rc, out, {r[0]: r[1:] for r in (line.split("\t") for line in out.splitlines()[1:]) if len(r) > 1}


def dated(t, release, date):
    """Make t the checkout of release, published on date."""
    r = t.yaml("release.yaml")
    r.update(release=release, date=date)
    t.put_yaml("release.yaml", r)


UBSAN = ("ubsan_agrees", "ubsan_halts", "ubsan_halts_may_fail")   # the statements the ubsan build's bytes are part of


def hold_back(t, names=UBSAN):
    """Leave names out of t, as a release that holds them back does (facts.cut)."""
    y = t.yaml(HARNESS)
    y["statements"] = {k: v for k, v in y["statements"].items() if k not in names}
    t.put_yaml(HARNESS, y)
    assert t.generate() == 0, t.last_output


def rebuild(t, sha, revision, names=UBSAN):
    """Give t's ubsan build other bytes, so names mean something else, at revision."""
    y = t.yaml(HARNESS)
    y["builds"]["ubsan"]["sha256"] = sha
    for name in names:
        y["statements"][name]["revision"] = revision
    t.put_yaml(HARNESS, y)
    assert t.generate() == 0, t.last_output


HARNESSES = (HARNESS, "projects/zlib/api-driver/harness.yaml", "projects/json/fuzzer-parse_bjdata/harness.yaml")
SHAPES_CODE = "\nDefinition a_new_definition := 0.\n"   # a change to the code of Shapes.v: every fingerprint moves


def block(t, rels=HARNESSES):
    """Write each harness.yaml of rels in block style, as every harness.yaml of the repository is (the fixture's are in
    flow style)."""
    for rel in rels:
        t.put_yaml(rel, t.yaml(rel))


def with_revisions(data, revisions_by_name):
    """data, a harness.yaml's, with each named statement's revision set, right after its status, or no revision for
    revision 1."""
    for name, revision in revisions_by_name.items():
        st = {}
        for k, v in data["statements"][name].items():
            if k != "revision":
                st[k] = v
            if k == "status" and revision != 1:
                st["revision"] = revision
        data["statements"][name] = st
    return data


def new_model(t):
    """Give t another LPS commit: every statement's meaning may have changed, and no fingerprint did."""
    r = t.yaml("release.yaml")
    r["semantics"]["commit"] = "0" * 40
    t.put_yaml("release.yaml", r)


class Revisions(unittest.TestCase):
    def test_a_new_way_of_fingerprinting_changes_no_revision_and_retires_no_proof(self):
        """The previous release pinned its proof under another version of the fingerprint: every fingerprint
        differs from the one it published, and no statement's meaning does."""
        with tree() as prev, tree() as cur:
            old = fingerprints(prev, "oss-fuzz-theorems/statement/0")
            self.assertNotEqual(old[PROVED], fingerprints(prev)[PROVED])
            for t in (prev, cur):
                prove(t, PROVED, old[PROVED])
            rc, out, rows = run(cur, prev, write_pins=True)
            self.assertEqual(rc, 0, out)
            self.assertEqual(sorted(k for k, r in rows.items() if r[3] != "same"), [WITHHELD])
            self.assertEqual(rows[WITHHELD], ["1", "1", "-", "unfingerprinted", "-"])
            self.assertTrue(all(r[0] == r[1] == r[2] for k, r in rows.items() if k != WITHHELD), out)
            self.assertEqual(rows[PROVED][4], "carried-forward")
            self.assertIn("1 pins rewritten", out)
            self.assertEqual(cur.yaml("proofs/%s/proof.yaml" % PROVED)["fingerprint"], fingerprints(cur)[PROVED])
            self.assertEqual(cur.generate(), 0, cur.last_output)
            self.assertEqual([str(f) for f in cur.lint() if "proof.yaml" in str(f)], [])

    def test_a_comment_or_layout_edit_in_the_shapes_changes_no_revision(self):
        with tree() as prev, tree() as cur:
            cur.write("theories/Shapes.v", "\n\n(* a comment (* nested *) \"*)\" *)\n", "a")
            cur.write("theories/Images.v", "(** a docstring *)\n", "a")
            rc, out, rows = run(cur, prev)
        self.assertEqual(rc, 0, out)
        self.assertEqual(sorted(k for k, r in rows.items() if r[3] != "same"), [WITHHELD])

    def test_a_change_of_meaning_needs_the_next_revision(self):
        sid = "zlib/checksum_fuzzer/ubsan_halts"
        with tree() as prev, tree() as cur:
            for t in (prev, cur):
                prove(t, sid, fingerprints(prev)[sid])
            y = cur.yaml(HARNESS)
            y["builds"]["ubsan"]["sha256"] = "0" * 63 + "a"
            cur.put_yaml(HARNESS, y)
            rc, out, rows = run(cur, prev, write_pins=True)
            self.assertEqual(rc, 1)
            self.assertEqual(sorted(k for k, r in rows.items() if r[3] == "changed"),
                             [sid.replace("halts", "agrees"), sid, sid + "_may_fail"])
            self.assertIn("error: %s: revision 1, expected 2: its meaning changed" % sid, out)
            self.assertEqual(rows[sid][4], "re-check")
            self.assertIn("0 pins rewritten", out)
            for name in ("ubsan_agrees", "ubsan_halts", "ubsan_halts_may_fail"):
                y["statements"][name]["revision"] = 2
            cur.put_yaml(HARNESS, y)
            rc, out, _rows = run(cur, prev)
        self.assertEqual(rc, 0, out)

    def test_a_change_of_model_commit_or_rocq_version_needs_the_next_revision(self):
        """The fingerprint hashes only the model's version, which reads `unreleased` until the model is released: a
        new model commit or Rocq version changes no fingerprint, and still every statement's meaning."""
        for section, key, label, value in (("semantics", "commit", "commit", "0" * 40),
                                           ("rocq", "version", "rocq version", "9.3.0")):
            with self.subTest(key=key), tree() as prev, tree() as cur:
                for t in (prev, cur):
                    prove(t, PROVED, fingerprints(prev)[PROVED])
                r = cur.yaml("release.yaml")
                r[section][key] = value
                cur.put_yaml("release.yaml", r)
                self.assertEqual(fingerprints(cur), fingerprints(prev))
                rc, out, rows = run(cur, prev, write_pins=True)
                self.assertEqual(rc, 1, out)
                self.assertIn("note: the model changed: %s is %s" % (label, value), out)
                self.assertEqual(sorted(k for k, r in rows.items() if r[3] != "model-changed"), [WITHHELD])
                self.assertEqual(rows[PROVED][2:], ["2", "model-changed", "re-check"])
                self.assertIn("the model it is stated in changed", out)
                self.assertIn("0 pins rewritten", out)

    def test_a_retired_proof_and_a_new_one(self):
        with tree() as prev, tree() as cur:
            prove(prev, PROVED, fingerprints(prev)[PROVED])
            _rc, _out, rows = run(cur, prev)
            self.assertEqual(rows[PROVED][4], "retired")
            _rc, _out, rows = run(prev, cur)
        self.assertEqual(rows[PROVED][4], "new")

    def test_a_change_to_the_renderer_is_a_change_of_meaning(self):
        """Today's tools render the previous release's facts with another halts budget: the previous release's own
        Statements.v says what its statements meant, so they changed, though both fingerprints, taken by today's
        tools, are the same."""
        pin = "proofs/%s/proof.yaml" % PROVED
        with tree() as prev, tree() as cur:
            for t in (prev, cur):
                prove(t, PROVED, fingerprints(prev)[PROVED])
            before = raw(cur, pin)
            with mock.patch.object(shapes, "HALTS_BUDGET", ("Budgets.Asan.lim_source", "2 GiB")):
                rc, out, rows = run(cur, prev, write_pins=True)
            self.assertEqual(rc, 1, out)
            self.assertEqual(rows[PROVED], ["1", "1", "2", "re-rendered", "re-check"])
            self.assertIn("error: %s: revision 1, expected 2: these tools render it otherwise" % PROVED, out)
            rerendered = sorted(k for k, r in rows.items() if r[3] == "re-rendered")
            self.assertTrue(rerendered and all(k.endswith("_halts") for k in rerendered), rerendered)
            self.assertIn("0 pins rewritten", out)
            self.assertEqual(raw(cur, pin), before)

    def test_the_previous_releases_generated_code_is_its_meaning(self):
        """A comment or layout edit in the previous release's Statements.v changes nothing; an edit to its code does:
        to a statement's Definition, that statement; to any other sentence, or to the code of its Images.v, every
        statement of the harness."""
        images = "projects/zlib/checksum_fuzzer/Images.v"
        cases = [
            (STATEMENTS, ("Definition plain_halts :", "(* a comment *) Definition\n\tplain_halts :"), "none"),
            (STATEMENTS, ("halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused Images.plain.",
                          "halts_within_budget Budgets.Asan.lim_source Exits.ok_or_refused Images.plain."), "one"),
            (STATEMENTS, ("From Stdlib Require Import QArith.", "From Stdlib Require Import QArith ZArith."), "all"),
            (STATEMENTS, ("\n(** ** Proving", "\nDefinition helper := 0.\n(** ** Proving"), "all"),
            (images, ("\nLemma ", "\nDefinition helper := 0.\nLemma "), "all"),
        ]
        for rel, (old, new), which in cases:
            with self.subTest(rel=rel, new=new), tree() as prev, tree() as cur:
                text = raw(prev, rel)
                self.assertIn(old, text)
                prev.write(rel, text.replace(old, new, 1))
                _rc, out, rows = run(cur, prev)
                found = sorted(k for k, r in rows.items() if r[3] == "re-rendered")
                harness = sorted(k for k, r in rows.items()
                                 if k.startswith("zlib/checksum_fuzzer/") and r[3] != "unfingerprinted")
                self.assertEqual(found, {"none": [], "one": [PROVED], "all": harness}[which], out)

    def test_a_sentence_that_moves_across_a_definition_changes_every_statement_of_the_harness(self):
        """The same sentences in another order are other code: a scope or import that the previous release opened
        after a Definition, and today's tools open before it, can change how that Definition parses."""
        moved = "From OssFuzzTheorems.zlib.checksum_fuzzer Require Images Distribution.\n"
        after = "halts_within_budget Budgets.Standard.lim_source Exits.ok_or_refused Images.plain.\n"
        with tree() as prev, tree() as cur:
            text = raw(prev, STATEMENTS)
            self.assertIn(moved, text)
            self.assertIn(after, text)
            prev.write(STATEMENTS, text.replace(moved, "", 1).replace(after, after + moved, 1))
            _rc, out, rows = run(cur, prev)
            found = sorted(k for k, r in rows.items() if r[3] == "re-rendered")
            harness = sorted(k for k, r in rows.items()
                             if k.startswith("zlib/checksum_fuzzer/") and r[3] != "unfingerprinted")
            self.assertEqual(found, harness, out)

    def test_write_pins_keeps_the_quotes_comments_and_line_ends_of_a_pin(self):
        y = "proofs/%s/proof.yaml" % PROVED
        for spelling in ('"%s"   # the pin of release 2026.10.0', "'%s'", "%s  # pinned"):
            with self.subTest(spelling=spelling), tree() as prev, tree() as cur:
                old = fingerprints(prev, "oss-fuzz-theorems/statement/0")[PROVED]
                text = "schema: oss-fuzz-theorems/proof/1\r\nproves: %s\r\nfingerprint: %s\r\n" % (
                    PROVED, spelling % old)
                for t in (prev, cur):
                    prove(t, PROVED, old)
                    t.write(y, text)
                rc, out, _rows = run(cur, prev, write_pins=True)
                self.assertEqual(rc, 0, out)
                self.assertIn("1 pins rewritten", out)
                self.assertEqual(raw(cur, y), text.replace(old, fingerprints(cur)[PROVED]))

    def test_write_pins_writes_no_pin_when_one_cannot_be_written(self):
        """A pin written as a block scalar is valid, but has no one-line value to replace: no pin is written."""
        other = "zlib/checksum_fuzzer/ubsan_halts"
        with tree() as prev, tree() as cur:
            old = fingerprints(prev, "oss-fuzz-theorems/statement/0")
            for t in (prev, cur):
                prove(t, PROVED, old[PROVED])
                prove(t, other, old[other])
                t.write("proofs/%s/proof.yaml" % other, "schema: oss-fuzz-theorems/proof/1\nproves: %s\n"
                        "fingerprint: >-\n  %s\n" % (other, old[other]))
            before = {sid: raw(cur, "proofs/%s/proof.yaml" % sid) for sid in (PROVED, other)}
            rc, out, _rows = run(cur, prev, write_pins=True)
            self.assertEqual(rc, 1, out)
            self.assertIn("ubsan_halts/proof.yaml: no plain or quoted top-level fingerprint: no pin written", out)
            self.assertEqual({sid: raw(cur, "proofs/%s/proof.yaml" % sid) for sid in (PROVED, other)}, before)

    def test_a_statement_a_release_held_back_keeps_its_revision_when_it_returns(self):
        """A release leaves out what a finding or `release: private` holds back.  The statement comes back in a later
        release, and its identifier is never reused: --earlier gives it the revision of the newest release that has
        it, plus one when its meaning changed since."""
        sid = "zlib/checksum_fuzzer/ubsan_halts"
        with tree() as older, tree() as prev, tree() as cur:
            dated(older, "2026.10.0", "2026-10-01")
            # prev held these statements back (facts.cut); cur publishes them again, rebuilt, so their meaning changed
            hold_back(prev)
            rebuild(cur, "0" * 63 + "a", 2)
            rc, out, rows = run(cur, prev)
            self.assertEqual(rc, 1, out)
            self.assertEqual(rows[sid][1:4], ["2", "1", "new"])
            self.assertIn("error: %s: revision 2, expected 1: it is new" % sid, out)
            rc, out, rows = run(cur, prev, earlier=[older.root])
            self.assertEqual(rc, 0, out)
            for name in UBSAN:
                self.assertEqual(rows["zlib/checksum_fuzzer/" + name][:4], ["1", "2", "2", "changed"], name)
            self.assertEqual(rows[PROVED][:4], ["1", "1", "1", "same"])

    def test_a_statement_no_named_release_has_is_new(self):
        sid = "zlib/checksum_fuzzer/asan_ubsan_halts"
        with tree() as older, tree() as prev, tree() as cur:
            dated(older, "2026.10.0", "2026-10-01")
            for t in (older, prev):
                y = t.yaml(HARNESS)
                del y["statements"][sid.rsplit("/", 1)[1]]
                t.put_yaml(HARNESS, y)
                self.assertEqual(t.generate(), 0, t.last_output)
            rc, out, rows = run(cur, prev, earlier=[older.root])
        self.assertEqual(rc, 0, out)
        self.assertEqual(rows[sid][:4], ["-", "1", "1", "new"])

    def test_a_private_projects_statement_is_compared_with_the_release_that_had_it(self):
        """#2's case, already on main: a `release: private` project is left out of a release the same way."""
        sid = "json/fuzzer-parse_bjdata/plain_halts"
        with tree() as older, tree() as prev, tree() as cur:
            dated(older, "2026.10.0", "2026-10-01")
            drop_project(prev, "json")
            rc, out, rows = run(cur, prev)
            self.assertEqual((rc, rows[sid][1:4]), (0, ["1", "1", "new"]), out)
            rc, out, rows = run(cur, prev, earlier=[older.root])
        self.assertEqual(rc, 0, out)
        self.assertEqual(rows[sid][:4], ["1", "1", "1", "same"])

    def test_earlier_releases_named_out_of_order_are_refused(self):
        """--earlier names the releases newest first, so that a statement is compared with the newest one that has
        it: a list in another order is refused, and nothing is compared."""
        with tree() as older, tree() as prev, tree() as cur:
            dated(older, "2026.12.0", "2026-12-01")
            rc, out, _rows = run(cur, prev, earlier=[older.root])
        self.assertEqual(rc, 1, out)
        self.assertIn("error: earlier %s is 2026.12.0 of 2026-12-01, not older than 2026.11.0 of 2026-11-02 before it "
                      "in the list: name them newest first" % older.root, out)
        self.assertIn("nothing compared", out)

    def test_two_releases_of_one_day_are_named_newest_first_and_compared_with_the_newest(self):
        """rc.1 and rc.2 are of one day, rc.2 changed the meaning of the ubsan
        statements (revision 2), the release after them held them back, and this tree changes their meaning again but
        keeps revision 2.  Named newest first, they are compared with rc.2 and need revision 3; named oldest first, or
        the same release twice, nothing is compared."""
        sid = "zlib/checksum_fuzzer/ubsan_halts"
        with tree() as rc1, tree() as rc2, tree() as prev, tree() as cur:
            dated(rc1, "2026.11.0-rc.1", "2026-11-02")
            dated(rc2, "2026.11.0-rc.2", "2026-11-02")
            rebuild(rc2, "0" * 63 + "a", 2)
            hold_back(prev)
            rebuild(cur, "0" * 63 + "b", 2)
            rc, out, rows = run(cur, prev, earlier=[rc2.root, rc1.root])
            self.assertEqual(rc, 1, out)
            self.assertEqual(rows[sid][:4], ["2", "2", "3", "changed"])
            self.assertIn("error: %s: revision 2, expected 3" % sid, out)
            for order in ([rc1.root, rc2.root], [rc2.root, rc2.root]):
                rc, out, rows = run(cur, prev, earlier=order)
                self.assertEqual((rc, rows), (1, {}), out)
                self.assertIn("is 2026.11.0-rc.2 of 2026-11-02, not older than", out)
                self.assertIn("nothing compared", out)

    def test_a_tree_that_does_not_load_is_not_compared(self):
        with tree() as prev, tree() as cur:
            prev.write(HARNESS, "schema: [\n")
            rc, out, rows = run(cur, prev)
        self.assertEqual((rc, rows), (1, {}))
        self.assertIn("error: previous: " + HARNESS, out)
        self.assertIn("nothing compared", out)

    def test_write_revisions_sets_the_expected_revision(self):
        """A statement whose meaning changed goes from revision 1 to 2, whether its fingerprint changed (a rebuild) or
        the model did (a new LPS commit); a statement whose meaning is the same goes back to its previous revision,
        here 1, which is no `revision:` line; a new statement stays at revision 1 with no line.  Nothing else in
        harness.yaml changes."""
        new = "zlib/checksum_fuzzer/asan_ubsan_halts"
        for case in ("changed", "model-changed"):
            with self.subTest(case=case), tree() as prev, tree() as cur:
                y = prev.yaml(HARNESS)
                del y["statements"][new.rsplit("/", 1)[1]]
                prev.put_yaml(HARNESS, y)
                self.assertEqual(prev.generate(), 0, prev.last_output)
                block(cur)
                y = cur.yaml(HARNESS)
                y["statements"]["plain_halts"]["revision"] = 2
                if case == "changed":
                    y["builds"]["ubsan"]["sha256"] = "0" * 63 + "a"
                else:
                    new_model(cur)
                cur.put_yaml(HARNESS, y)
                self.assertEqual(cur.generate(), 0, cur.last_output)
                before = {rel: cur.yaml(rel) for rel in HARNESSES}
                rc, out, rows = run(cur, prev, write_revisions=True)
                self.assertEqual(rc, 0, out)
                bumped = sorted(k for k, r in rows.items() if r[3] == case)
                want = {sid: 2 for sid in bumped}
                if case == "changed":
                    self.assertEqual(bumped, ["zlib/checksum_fuzzer/" + n for n in sorted(UBSAN)])
                    self.assertEqual(rows[PROVED][:4], ["1", "2", "1", "same"])
                    self.assertIn("written: %s: revision 1, was 2: its meaning is the same as in the previous release"
                                  % PROVED, out)
                    want[PROVED] = 1
                else:
                    self.assertEqual(sorted(k for k, r in rows.items() if r[3] not in (case, "new")), [WITHHELD])
                    self.assertEqual(rows[PROVED][:4], ["1", "2", "2", "model-changed"])
                self.assertEqual(rows[new][:4], ["-", "1", "1", "new"])
                written = [sid for sid, r in want.items() if rows[sid][1] != str(r)]
                self.assertIn("%d with a wrong revision" % len(written), out)
                self.assertIn("%d revisions written" % len(written), out)
                for rel in HARNESSES:
                    names = {sid.rsplit("/", 1)[1]: r for sid, r in want.items()
                             if rel == "projects/%s/harness.yaml" % sid.rsplit("/", 1)[0]}
                    self.assertEqual(raw(cur, rel), yamlio.dump(with_revisions(before[rel], names)), rel)
                rc, out, _rows = run(cur, prev)
                self.assertEqual(rc, 0, out)
                self.assertIn("0 with a wrong revision", out)
                # without --write-revisions the summary line ends as it did before the flag existed
                self.assertTrue(out.splitlines()[-1].endswith("pins to rewrite (--write-pins)"), out)

    def test_write_revisions_never_lowers_a_new_statement_s_revision(self):
        """Review of #429 by the CI/CD lead, N1.  A statement released at revision 2, held back by the previous release
        and back here at revision 2, is new unless --earlier names the release that has it: --write-revisions does
        not write it down to 1, it writes nothing and fails, and with that release named the statement is the same."""
        sid = "zlib/checksum_fuzzer/ubsan_halts"
        with tree() as older, tree() as prev, tree() as cur:
            dated(older, "2026.10.0", "2026-10-01")
            rebuild(older, "0" * 63 + "a", 2)
            hold_back(prev)
            rebuild(cur, "0" * 63 + "a", 2)
            before = {rel: raw(cur, rel) for rel in HARNESSES}
            rc, out, rows = run(cur, prev, write_revisions=True)
            self.assertEqual(rc, 1, out)
            self.assertEqual(rows[sid][1:4], ["2", "1", "new"])
            self.assertIn("error: %s: revision 2, expected 1: it is new" % sid, out)
            self.assertIn("error: zlib/checksum_fuzzer/ubsan_agrees: revision 2, and it is new (and 2 more new "
                          "statements like it): --write-revisions never lowers a new statement's revision; if a "
                          "release before the previous one has it, name that release with --earlier; if no release "
                          "has it, remove its revision: line: no revision written", out)
            self.assertNotIn("written: ", out)
            self.assertEqual({rel: raw(cur, rel) for rel in HARNESSES}, before)
            rc, out, rows = run(cur, prev, earlier=[older.root], write_revisions=True)
            self.assertEqual(rc, 0, out)
            self.assertEqual(rows[sid][:4], ["2", "2", "2", "same"])
            self.assertIn("0 revisions written", out)

    def test_write_revisions_says_to_render_again_as_the_tree_s_own_tools_do(self):
        """Review of #429 by the CI/CD lead, N2.  index/statements.tsv lists each revision, so after a write the run
        names the render that comes next: with --skip-shared when the tree's own tools offer it (the shared
        files are rendered after the merge), read as port-branch reads it (port.offers_skip_shared; review of #438): an
        option line of their `generate --help`, not the flag named in prose.  Nothing written, nothing to render."""
        usage = "usage: oft generate [-h] [--check]%s\n\noptions:\n  -h, --help     show this help message and exit\n"
        helps = (("no tools", None, "./oft generate"),
                 ("an option line", usage % " [--skip-shared]" + "  --check        compare instead of writing\n"
                  "  --skip-shared  leave the shared generated files to the line's render\n",
                  "./oft generate --skip-shared"),
                 ("prose only", usage % "" + "  --check        compare instead of writing (--skip-shared is not "
                  "taken here)\n", "./oft generate"))
        for name, help_text, command in helps:
            with self.subTest(name), tree() as prev, tree() as cur:
                y = cur.yaml(HARNESS)
                y["builds"]["ubsan"]["sha256"] = "0" * 63 + "a"
                cur.put_yaml(HARNESS, y)
                self.assertEqual(cur.generate(), 0, cur.last_output)
                if help_text is not None:
                    cur.write("tools/oft/__init__.py", "")
                    cur.write("tools/oft/__main__.py", "import sys\nsys.stdout.write(%r)\n" % help_text)
                rc, out, _rows = run(cur, prev, write_revisions=True)
                self.assertEqual(rc, 0, out)
                self.assertIn("\noft revisions: harness.yaml changed: now run %s\noft revisions: " % command, out)
                rc, out, _rows = run(cur, prev, write_revisions=True)
                self.assertEqual(rc, 0, out)
                self.assertNotIn("now run", out)

    def test_write_revisions_refuses_a_tree_that_is_not_a_release(self):
        """Review of #429 by the CI/CD lead, N5.  A release is what `oft release-tree` makes, and it removes every file
        of release_tree.INTERNAL: a previous or earlier checkout that holds one is a commit of this repository, and
        the revisions it gives are not a release's.  --write-revisions compares nothing then; --repin-changed alone
        still runs against such a commit (plan C4)."""
        with tree() as older, tree() as prev, tree() as cur:
            dated(older, "2026.10.0", "2026-10-01")
            block(cur)
            new_model(cur)
            before = {rel: raw(cur, rel) for rel in HARNESSES}
            # Task 5A runs --write-revisions alone; a run that also re-pins is refused all the same
            for t, rel, name, kw in ((prev, "review.md", "previous", {"write_revisions": True}),
                                     (older, ".github/CODEOWNERS", "earlier",
                                      {"earlier": [older.root], "write_revisions": True, "repin_changed": True})):
                with self.subTest(name=name):
                    t.write(rel, "only in this repository\n")
                    rc, out, rows = run(cur, prev, **kw)
                    self.assertEqual((rc, rows), (1, {}), out)
                    self.assertIn("error: %s %s is not a release: it holds %s, which `oft release-tree` removes from "
                                  "every release" % (name, t.root, rel), out)
                    self.assertIn("oft revisions: --write-revisions needs checkouts of releases: nothing compared", out)
                    self.assertEqual({rel: raw(cur, rel) for rel in HARNESSES}, before)
                    os.remove(t.path(rel))
            prev.write("review.md", "only in this repository\n")
            rc, out, _rows = run(cur, prev, repin_changed=True)
            self.assertEqual(rc, 1, out)   # every revision is wrong against prev, and only the pins count here
            self.assertIn("0 pins rewritten", out)

    def test_the_cli_passes_both_flags(self):
        """Review of #429 by the CI/CD lead, N3: `oft revisions` hands --write-revisions and --repin-changed on."""
        from oft import __main__ as cli
        with tree() as prev, tree() as cur:
            old = fingerprints(prev)
            for t in (prev, cur):
                prove(t, PROVED, old[PROVED])
            block(cur)
            cur.write("theories/Shapes.v", SHAPES_CODE, "a")
            with contextlib.redirect_stdout(io.StringIO()) as out:
                rc = cli.main(["--root", cur.root, "revisions", prev.root, "--write-revisions", "--repin-changed"])
            self.assertEqual(rc, 0, out.getvalue())
            self.assertIn("1 pins rewritten; ", out.getvalue())
            self.assertEqual(cur.yaml("proofs/%s/proof.yaml" % PROVED)["fingerprint"], fingerprints(cur)[PROVED])
            self.assertEqual(cur.yaml(HARNESS)["statements"]["plain_halts"]["revision"], 2)

    def test_write_revisions_keeps_comments_and_line_ends(self):
        with tree() as prev, tree() as cur:
            y = cur.yaml(HARNESS)
            y["builds"]["ubsan"]["sha256"] = "0" * 63 + "a"
            cur.put_yaml(HARNESS, y)
            self.assertEqual(cur.generate(), 0, cur.last_output)

            def spelled(text):
                """text with a comment on ubsan_halts's status line, the line a revision goes after, and CRLF ends."""
                i = text.index("    status: open\n", text.index("  ubsan_halts:\n"))
                text = text[:i] + "    status: open  # the ubsan build\n" + text[i + len("    status: open\n"):]
                return text.replace("\n", "\r\n")

            cur.write(HARNESS, spelled(yamlio.dump(y)))
            rc, out, _rows = run(cur, prev, write_revisions=True)
            self.assertEqual(rc, 0, out)
            self.assertEqual(raw(cur, HARNESS), spelled(yamlio.dump(with_revisions(y, {n: 2 for n in UBSAN}))))

    def test_write_revisions_is_idempotent(self):
        with tree() as prev, tree() as cur:
            block(cur)
            new_model(cur)
            rc, out, _rows = run(cur, prev, write_revisions=True)
            self.assertEqual(rc, 0, out)
            written = {rel: raw(cur, rel) for rel in HARNESSES}
            rc, out, _rows = run(cur, prev, write_revisions=True)
            self.assertEqual(rc, 0, out)
            self.assertIn("0 with a wrong revision", out)
            self.assertIn("0 revisions written", out)
            self.assertNotIn("written: ", out)
            self.assertEqual({rel: raw(cur, rel) for rel in HARNESSES}, written)

    def test_write_revisions_after_a_model_change_needs_nothing_more_after_a_code_change(self):
        """The W2 sitting: the LPS pin PR bumps every statement for its new LPS commit, then the statements PR changes
        the code of Shapes.v.  Each change alone needs the previous release's revision plus one, so the second run
        writes nothing."""
        with tree() as prev, tree() as cur:
            block(cur)
            new_model(cur)
            rc, out, _rows = run(cur, prev, write_revisions=True)
            self.assertEqual(rc, 0, out)
            cur.write("theories/Shapes.v", SHAPES_CODE, "a")
            bumped = {rel: raw(cur, rel) for rel in HARNESSES}
            rc, out, rows = run(cur, prev, write_revisions=True)
            self.assertEqual(rc, 0, out)
            self.assertEqual(sorted(k for k, r in rows.items() if r[3] != "changed"), [WITHHELD])
            self.assertEqual(rows[PROVED][:4], ["1", "2", "2", "changed"])
            self.assertIn("0 with a wrong revision", out)
            self.assertIn("0 revisions written", out)
            self.assertEqual({rel: raw(cur, rel) for rel in HARNESSES}, bumped)

    def test_write_revisions_writes_no_file_when_one_cannot_be_written(self):
        """A statement written as a flow mapping has no `status:` line to put a revision after: no file is written,
        though the other harnesses' could be."""
        with tree() as prev, tree() as cur:
            block(cur, HARNESSES[1:])
            new_model(cur)
            before = {rel: raw(cur, rel) for rel in HARNESSES}
            rc, out, _rows = run(cur, prev, write_revisions=True)
            self.assertEqual(rc, 1, out)
            self.assertIn("checksum_fuzzer/harness.yaml: statement asan_agreement_decidable is not a block mapping: "
                          "no revision written", out)
            self.assertEqual({rel: raw(cur, rel) for rel in HARNESSES}, before)

    def test_write_revisions_keeps_a_comment_on_an_edited_line_and_replaces_a_revision(self):
        """A revision line is added after a `status:` line that has a comment, and the value of an existing
        `revision:` is replaced, its comment kept (review of #429, finding 2)."""
        with tree() as prev, tree() as cur:
            y = prev.yaml(HARNESS)
            y["statements"]["ubsan_agrees"]["revision"] = 2
            prev.put_yaml(HARNESS, y)
            self.assertEqual(prev.generate(), 0, prev.last_output)
            y = cur.yaml(HARNESS)
            y["builds"]["ubsan"]["sha256"] = "0" * 63 + "a"
            y["statements"]["ubsan_agrees"]["revision"] = 2
            cur.put_yaml(HARNESS, y)
            self.assertEqual(cur.generate(), 0, cur.last_output)
            text = yamlio.dump(y)
            i = text.index("    status: open\n", text.index("  ubsan_halts:\n"))
            text = text[:i] + "    status: open  # c\n" + text[i + len("    status: open\n"):]
            cur.write(HARNESS, text.replace("    revision: 2\n", "    revision: 2  # r\n"))
            rc, out, _rows = run(cur, prev, write_revisions=True)
            self.assertEqual(rc, 0, out)
            self.assertIn("    status: open  # c\n    revision: 2\n", raw(cur, HARNESS))
            self.assertIn("    revision: 3  # r\n", raw(cur, HARNESS))

    def test_write_revisions_refuses_a_status_that_is_not_one_line(self):
        with tree() as prev, tree() as cur:
            block(cur)
            new_model(cur)
            cur.write(HARNESS, raw(cur, HARNESS).replace("    status: open\n", "    status:\n      open\n", 1))
            before = {rel: raw(cur, rel) for rel in HARNESSES}
            rc, out, _rows = run(cur, prev, write_revisions=True)
            self.assertEqual(rc, 1, out)
            self.assertIn("its status is not one line of its own: no revision written", out)
            self.assertEqual({rel: raw(cur, rel) for rel in HARNESSES}, before)

    def test_no_pin_is_written_when_a_revision_cannot_be(self):
        """Pins and revisions are all computed before any file is written (review of #429, finding 3)."""
        with tree() as prev, tree() as cur:
            old = fingerprints(prev, "oss-fuzz-theorems/statement/0")
            y = cur.yaml(HARNESS)
            y["builds"]["ubsan"]["sha256"] = "0" * 63 + "a"
            cur.put_yaml(HARNESS, y)
            self.assertEqual(cur.generate(), 0, cur.last_output)
            cur.write(HARNESS, yaml.safe_dump(y, default_flow_style=True, sort_keys=False, width=100000))
            for t in (prev, cur):
                prove(t, PROVED, old[PROVED])
            pin = raw(cur, "proofs/%s/proof.yaml" % PROVED)
            rc, out, rows = run(cur, prev, write_pins=True, write_revisions=True)
            self.assertEqual(rows[PROVED][4], "carried-forward", out)
            self.assertEqual(rc, 1, out)
            self.assertIn("is not a block mapping: nothing written", out)
            self.assertNotIn("written: ", out)
            self.assertIn("error: zlib/checksum_fuzzer/ubsan_halts: revision 1, expected 2", out)
            self.assertEqual(raw(cur, "proofs/%s/proof.yaml" % PROVED), pin)

    def test_repin_changed_rewrites_only_pins_that_held_the_old_fingerprint(self):
        """A change of the code of Shapes.v changes every fingerprint, and its proofs are re-checked by the next corpus
        run: --repin-changed sets the pin of a re-checked proof that held its statement's fingerprint in PREVIOUS, and
        no other.  --write-pins alone sets none of them."""
        other = "zlib/checksum_fuzzer/ubsan_halts"
        with tree() as prev, tree() as cur:
            old = fingerprints(prev)
            for t in (prev, cur):
                prove(t, PROVED, old[PROVED])
                prove(t, other, "0" * 64)
            cur.write("theories/Shapes.v", SHAPES_CODE, "a")
            before = {sid: raw(cur, "proofs/%s/proof.yaml" % sid) for sid in (PROVED, other)}
            rc, out, rows = run(cur, prev, write_pins=True)
            self.assertEqual(rc, 1, out)   # every revision is wrong: the code of Shapes.v changed
            self.assertEqual((rows[PROVED][3:], rows[other][3:]), (["changed", "re-check"], ["changed", "re-check"]))
            self.assertIn("0 pins rewritten", out)
            self.assertEqual({sid: raw(cur, "proofs/%s/proof.yaml" % sid) for sid in (PROVED, other)}, before)
            rc, out, rows = run(cur, prev, repin_changed=True)
            self.assertEqual(rc, 1, out)
            self.assertIn("1 pins rewritten", out)
            self.assertEqual(raw(cur, "proofs/%s/proof.yaml" % PROVED),
                             before[PROVED].replace(old[PROVED], fingerprints(cur)[PROVED]))
            self.assertEqual(raw(cur, "proofs/%s/proof.yaml" % other), before[other])

    def test_repin_changed_rewrites_a_new_proof_pinned_to_the_previous_fingerprint(self):
        """A proof branch made before the change, merged with the base that has it, and compared with the base before
        it: PREVIOUS has none of its proofs, so they are new, and --repin-changed sets the pin of each one that holds
        its statement's fingerprint in PREVIOUS.  A pin that is neither fingerprint is never rewritten."""
        other = "zlib/checksum_fuzzer/ubsan_halts"
        with tree() as prev, tree() as cur:
            old = fingerprints(prev)
            prove(cur, PROVED, old[PROVED])
            prove(cur, other, "0" * 64)
            cur.write("theories/Shapes.v", SHAPES_CODE, "a")
            before = {sid: raw(cur, "proofs/%s/proof.yaml" % sid) for sid in (PROVED, other)}
            rc, out, rows = run(cur, prev, repin_changed=True)
            self.assertEqual(rc, 1, out)
            self.assertEqual((rows[PROVED][3:], rows[other][3:]), (["changed", "new"], ["changed", "new"]))
            self.assertIn("1 pins rewritten", out)
            self.assertEqual(raw(cur, "proofs/%s/proof.yaml" % PROVED),
                             before[PROVED].replace(old[PROVED], fingerprints(cur)[PROVED]))
            self.assertEqual(raw(cur, "proofs/%s/proof.yaml" % other), before[other])


if __name__ == "__main__":
    unittest.main()
