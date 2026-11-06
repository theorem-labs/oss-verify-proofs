"""tools/oft/tests/comment_sweep.py: the plan, apply and check of the comment sweep, over a scratch git repository
whose main releases one Rocq file of a fuzz target and whose head adds new ones with every shape the rule names.

Each must-fail control plants one change the rule does not allow into a correct sweep, commits it, and requires the
check to fail on it: a deleted code line, a deleted trailing or mid-line comment, a deleted timeout-ok line, header
line, Modified-by line or released line, a deleted blank line outside comments, a wrong citation number, a missing,
moved or extra notice, a changed file that is not a .v file, and a line the rule deletes left in place.  ReviewFindings
holds the shapes the reviews of pull request 639 found: a licence line on line 9 or 10 (Rev639), a cited line beside
an equal one, and a swept file that no longer lexes (ThermoDeep639)."""
import contextlib
import io
import os
import subprocess
import tempfile
import unittest

from oft import keys, lint
from oft.tests import comment_sweep as cs

GIT = ["git", "-c", "user.name=oft-tests", "-c", "user.email=oft-tests" + "@" + "example.invalid",
       "-c", "commit.gpgsign=false"]
GIT_ENV = dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")
UNIT = "demo/fuzz_x"
LIB = "projects/demo/fuzz_x/proofs/lib/"
COPYRIGHT = "(* Copyright 2026 Anthropic PBC *)"
SPDX = "(* SPDX-License-Identifier: Apache-2.0 OR MIT *)"

OLD = "\n".join([
    COPYRIGHT,
    SPDX,
    "Definition old := 0.",
    "(* A released comment line, copied below. *)",
    "",
])
OLD2 = "\n".join(["Definition o2 := 0."] + ["Definition o2_%d := %d." % (k, k) for k in range(2, 12)]
                 + ["(* a comment of a released file that is moved *)", ""])

# New.v, a file from a donor: its line numbers are the ones the tests name
NEW = [
    COPYRIGHT,                                                                       # 1
    SPDX,                                                                            # 2
    "(* Modified by Theorem Labs, 2026-10: copied from proofs/other/fuzz_y/lib/New.v. *)",  # 3
    "(* A doc comment that starts in the header",                                    # 4
    "   and runs on",                                                                # 5
    "   past line ten,",                                                             # 6
    "   line 7",                                                                     # 7
    "",                                                                              # 8: blank, inside the comment
    "   line 9",                                                                     # 9
    "   line 10",                                                                    # 10
    "   line 11 is past the header",                                                 # 11
    "   and line 12 closes it. *)",                                                  # 12
    "Definition a := 1. (* a trailing comment *)",                                   # 13
    "Definition b := (* a mid-line comment *) 2.",                                   # 14
    "Definition t := 5. (* timeout-ok: the other branch is a proof step *)",        # 15
    "(* timeout-ok: a whole-line justification *)",                                  # 16
    "(* A released comment line, copied below. *)",                                  # 17
    "(* An unverified comment to delete. *)",                                        # 18
    "(* A multi-line comment",                                                       # 19
    "   to delete",                                                                  # 20
    "   (* with a nested one *)",                                                    # 21
    '   and a string "*)" inside. *)',                                               # 22
    'Definition c := "(* not a comment *)".',                                        # 23
    "(* Modified by Theorem Labs, 2026-10: a second notice past the header,",        # 24
    "   on two lines. *)",                                                           # 25
    "Definition d := 3. (* see New2.v:12 *)",                                        # 26
    "Definition e := 4. (* as fuzz_y's New2.v:13 *)",                                # 27
    "(* last deletable line *)",                                                     # 28
    "",                                                                              # 29: a blank line outside comments
    "Definition f := 5.",                                                            # 30
    "",
]
# New2.v, a file written here (no licence lines, no notice)
NEW2 = (["Definition n2 := 0."] + ["Definition n2_%d := %d." % (k, k) for k in range(2, 11)] + [
    "(* deletable A *)",                                                             # 11
    "(* cited comment line *)",                                                      # 12: New.v:26 cites it
    "(* deletable B *)",                                                             # 13: only a foreign citation
    "Definition z := 0. (* see New.v:23 *)",                                         # 14: Definition c
    "",
])
REFUSED = (["Definition r0 := 0."] * 10 + ["Definition r := x.(* L1 *) 1.", "(* would be deleted *)", ""])

SWEPT_NEW = "\n".join(NEW[:3] + [cs.NOTICE] + NEW[3:10] + NEW[11:17] + [NEW[22]] + NEW[23:25] + [
    "Definition d := 3. (* see New2.v:11 *)",
    NEW[26],
] + NEW[28:])
SWEPT_NEW2 = "\n".join(NEW2[:10] + [NEW2[11], "Definition z := 0. (* see New.v:18 *)", ""])

# ReviewFindings' files; ten code lines first, so that every line the tests name is past the header
CODE10 = ["Definition h%d := %d." % (k, k) for k in range(10)]
# a cited line beside an equal one: a citation range that ends on a blank line inside a comment next to another, and
# two equal comment lines of which the first is cited
DUPS = CODE10 + [
    "(* cited start",                                                                # 11
    "",                                                                              # 12: cited, inside the comment
    "",                                                                              # 13: equal to 12, deletable
    "   end *)",                                                                     # 14: closes the comment
    "Definition d := 0. (* see Dups.v:11-12 *)",                                     # 15
    "(* dup *)",                                                                     # 16: cited
    "(* dup *)",                                                                     # 17: equal to 16, deletable
    "Definition e := 0. (* see Dups.v:16 *)",                                        # 18
    "",
]
SWEPT_DUPS = "\n".join(CODE10 + DUPS[10:12] + DUPS[13:16] + ["Definition e := 0. (* see Dups.v:15 *)", ""])
# a comment at the end of the file, whose closing line alone must not go
TAIL = CODE10 + ["Definition g := 1.", "(* junk a", "   junk b *)", ""]
SWEPT_TAIL = "\n".join(CODE10 + ["Definition g := 1.", ""])
# a deletable last line with no line feed after it
NOLF = CODE10 + ["(* the last line *)"]
SWEPT_NOLF = "\n".join(CODE10)
MODBY = "(* Modified by Theorem Labs, 2026-10: copied from proofs/other/fuzz_y/lib/L.v. *)"
RESTATED = "(* The proofs here are Copyright 2026 Anthropic PBC. *)"    # a licence line past Anthropic's two
# a donor file whose last licence line is line 9: the notice goes under it, at line 10
L9 = ([COPYRIGHT, SPDX, MODBY] + ["Definition l%d := %d." % (k, k) for k in range(5)]
      + [RESTATED, "(* a header note *)", "(* delete me *)", "Definition z := 0.", ""])
SWEPT_L9 = "\n".join(L9[:9] + [cs.NOTICE] + L9[9:10] + L9[11:])
# a donor file whose last licence line is line 10: no notice fits in its header, so the rule refuses it
L10 = ([COPYRIGHT, SPDX, MODBY] + ["Definition l%d := %d." % (k, k) for k in range(6)]
       + [RESTATED, "(* delete me *)", "Definition z := 0.", ""])
# ThermoDeep639-2's probe639j: X.v is a donor file with a licence line on line 10, whose one deletable line, 11, only
# Z.v's line 11 cites, a line the sweep deletes; so the plan refuses X.v, and X.v's citation of Y.v:13 keeps its
# number though Y.v loses two lines and gains the notice
PAD8 = ["Definition p%d := %d." % (k, k) for k in range(8)]
X = ([COPYRIGHT, SPDX] + PAD8[:7] + ["(* Copyright 2026 Anthropic PBC: adapted here *)", "(* junk x *)",
                                     "Definition zx := 0. (* see lib/Y.v:13 *)", ""])
Y = [COPYRIGHT, SPDX] + PAD8 + ["(* junk y1 *)", "(* junk y2 *)", "(* junk y3 *)", "Definition zy := 0.", ""]
Z = [COPYRIGHT, SPDX] + PAD8 + ["(* see lib/X.v:11 *)", "Definition zz := 0.", ""]
SWEPT_Y = "\n".join(Y[:2] + [cs.NOTICE] + Y[2:10] + Y[12:])
SWEPT_Z = "\n".join(Z[:2] + [cs.NOTICE] + Z[2:10] + Z[11:])


def run(cwd, *args):
    done = subprocess.run(GIT + list(args), cwd=cwd, env=GIT_ENV, capture_output=True, text=True)
    if done.returncode != 0:
        raise AssertionError("git %s: %s" % (" ".join(args), done.stderr))
    return done.stdout.strip()


def write(root, rel, text):
    path = os.path.join(root, rel)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="") as f:
        f.write(text)


class Repo:
    """main: the fuzz target's released Old.v and Old2.v; head: by default New.v, New2.v, Refused.v, a script, and
    Old2.v moved to Moved.v with a comment added; else the files given ({path: text})."""

    def __init__(self, files=None):
        self._tmp = tempfile.TemporaryDirectory(prefix="comment-sweep-")
        self.root = os.path.join(self._tmp.name, "repo")
        os.makedirs(self.root)
        run(self.root, "init", "-q", "-b", "main")
        write(self.root, "projects/demo/fuzz_x/harness.yaml", "statements: {}\n")
        write(self.root, "projects/other/fuzz_y/harness.yaml", "statements: {}\n")
        write(self.root, LIB + "Old.v", OLD)
        write(self.root, LIB + "Old2.v", OLD2)
        write(self.root, "tools/oft/lint-exceptions.yaml",
              "exceptions:\n  - unit: demo/fuzz_x\n    rule: licence-pending\n    due: '2026-11-02'\n"
              "    series: pending\n    reason: its licence lines are applied in its own series\n")
        run(self.root, "add", "-A")
        run(self.root, "commit", "-q", "-m", "main")
        run(self.root, "checkout", "-q", "-b", "head")
        if files is None:
            write(self.root, LIB + "New.v", "\n".join(NEW))
            write(self.root, LIB + "New2.v", "\n".join(NEW2))
            write(self.root, LIB + "Refused.v", "\n".join(REFUSED))
            write(self.root, "projects/demo/fuzz_x/proofs/provenance/run.py", "# a script's comment, not swept\n")
            os.remove(os.path.join(self.root, LIB + "Old2.v"))
            write(self.root, LIB + "Moved.v", OLD2 + "(* a comment the move added *)\n")
        else:
            for rel, text in files.items():
                write(self.root, rel, text)
        run(self.root, "add", "-A")
        run(self.root, "commit", "-q", "-m", "head")
        self.head = run(self.root, "rev-parse", "HEAD")

    def unit(self):
        return cs.Unit(self.root, UNIT, self.head, "main")

    def commit(self, files, message="swept"):
        """A commit on top of head with files ({path: text}) written; head stays checked out."""
        run(self.root, "checkout", "-q", "--detach", self.head)
        for rel, text in files.items():
            write(self.root, rel, text)
        run(self.root, "add", "-A")
        run(self.root, "commit", "-q", "-m", message)
        sha = run(self.root, "rev-parse", "HEAD")
        run(self.root, "checkout", "-q", "--detach", self.head)
        return sha

    def close(self):
        self._tmp.cleanup()


class CommentSweep(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        cls.repo = Repo()
        cls.plan = cs.Plan(cls.repo.unit())

    @classmethod
    def tearDownClass(cls):
        cls.repo.close()

    def reasons(self, name):
        return self.plan.files[LIB + name].reasons

    def check(self, files, keep_rows=()):
        bad, _notes = cs.check(self.repo.unit(), self.repo.commit(files), keep_rows)
        return bad

    def correct(self, **changes):
        out = {LIB + "New.v": SWEPT_NEW, LIB + "New2.v": SWEPT_NEW2}
        out.update({LIB + k.replace("_v", ".v"): v for k, v in changes.items()})
        return out

    # ---------------------------------------------------------------------------------------------------- plan

    def test_new_files_leave_out_rename_pairs_and_sweep_only_rocq(self):
        self.assertEqual(self.plan.pairs, {LIB + "Moved.v": LIB + "Old2.v"})
        self.assertEqual(self.plan.new_v, [LIB + "New.v", LIB + "New2.v", LIB + "Refused.v"])
        self.assertIn("projects/demo/fuzz_x/proofs/provenance/run.py", self.plan.new)

    def test_reasons(self):
        r = self.reasons("New.v")
        self.assertEqual({r[i] for i in range(10)}, {"header"})
        self.assertEqual(r[10], "deleted")
        self.assertEqual(r[11], "structural", "line 12 closes a comment whose start the header keeps")
        self.assertEqual(r[15], "timeout-ok")
        self.assertEqual(r[16], "released")
        self.assertEqual([r[i] for i in range(17, 22)], ["deleted"] * 5)
        self.assertEqual([r[i] for i in (23, 24)], ["modified-by"] * 2)
        self.assertEqual(r[27], "deleted")
        r2 = self.reasons("New2.v")
        self.assertEqual((r2[10], r2[11], r2[12]), ("deleted", "cited", "deleted"))

    def test_never_deleted(self):
        """The controls: a trailing comment, a mid-line comment, a timeout-ok line (on code and alone), the header
        block, both Modified-by notices, a released line, code lines and a blank line outside comments."""
        fp = self.plan.files[LIB + "New.v"]
        for line in (13, 14, 15, 16, 17, 23, 24, 25, 26, 27, 29, 30) + tuple(range(1, 11)):
            self.assertNotIn(line - 1, fp.deleted, "New.v:%d" % line)
        for line in (13, 14, 15):            # a comment on a line with code: in no block the sweep touches
            self.assertNotIn(line - 1, self.reasons("New.v"), "New.v:%d" % line)

    def test_refused_file(self):
        fp = self.plan.files[LIB + "Refused.v"]
        self.assertTrue(fp.refused and "non-blank" in fp.refused[0], fp.refused)
        self.assertFalse(fp.changed())

    def test_swept_text(self):
        self.assertEqual(self.plan.files[LIB + "New.v"].swept_text(), SWEPT_NEW)
        self.assertEqual(self.plan.files[LIB + "New2.v"].swept_text(), SWEPT_NEW2)
        self.assertEqual(self.plan.files[LIB + "New.v"].notice_at, 3, "under the header, after the notice there")
        self.assertIsNone(self.plan.files[LIB + "New2.v"].notice_at, "New2.v came from no donor")

    def test_citations(self):
        self.assertEqual(sorted((p.rsplit("/", 1)[1], i + 1, old, new) for p, i, _r, old, new in self.plan.resolutions),
                         [("New.v", 26, [12], [11]), ("New2.v", 14, [23], [18])])
        self.assertEqual([(p.rsplit("/", 1)[1], i + 1, why, line) for p, i, _r, why, line in self.plan.left],
                         [("New.v", 27, "another fuzz target's file (fuzz_y's)", NEW[26])])

    def test_summary_names_the_follow_ups(self):
        text = self.plan.summary()
        self.assertIn("condition 22", text)
        self.assertIn("condition 23", text)
        self.assertIn("at main, a licence-pending entry (due 2026-11-02, series pending)", text)

    # --------------------------------------------------------------------------------------------- apply, check

    def test_apply_then_check(self):
        wt = os.path.join(self.repo._tmp.name, "wt")
        run(self.repo.root, "worktree", "add", "-q", "--detach", wt, self.repo.head)
        try:
            changed = cs.apply(self.plan, wt)
            self.assertEqual(changed, [LIB + "New.v", LIB + "New2.v"])
            with open(os.path.join(wt, LIB + "New.v"), encoding="utf-8") as f:
                self.assertEqual(f.read(), SWEPT_NEW)
            run(wt, "commit", "-q", "-am", "swept")
            bad, notes = cs.check(self.repo.unit(), run(wt, "rev-parse", "HEAD"))
            self.assertEqual(bad, [])
            self.assertIn("lines deleted: 9 in 2 files; notices: 1; citations re-resolved: 2", notes[1])
            with self.assertRaises(cs.SweepError):
                cs.apply(self.plan, wt)                     # no longer at head
        finally:
            run(self.repo.root, "worktree", "remove", "--force", wt)

    def test_check_passes_the_correct_sweep(self):
        self.assertEqual(self.check(self.correct()), [])

    def test_check_fails_on_each_planted_change(self):
        """Each control: (the planted file or files, a phrase the check's first finding must hold)."""
        new, without_notice = SWEPT_NEW.split("\n"), [l for l in SWEPT_NEW.split("\n") if l != cs.NOTICE]
        less = "not HEAD's file less whole comment lines the rule deletes"
        cases = {
            "a code line": ("\n".join(l for l in new if l != NEW[22]), "its code changed"),
            "the line that closes a comment the header keeps": ("\n".join(l for l in new if l != NEW[11]),
                                                                "does not lex"),
            "a trailing comment": (SWEPT_NEW.replace(NEW[12], "Definition a := 1."), less),
            "a mid-line comment": (SWEPT_NEW.replace(NEW[13], "Definition b := 2."), less),
            "the timeout-ok comment of a code line": (SWEPT_NEW.replace(NEW[14], "Definition t := 5."), less),
            "a whole timeout-ok line": ("\n".join(l for l in new if l != NEW[15]), less),
            "a header line": ("\n".join(l for l in new if l != NEW[5]), less),
            "a Modified-by line in the header": ("\n".join(l for l in new if l != NEW[2]), "notice is not at line 4"),
            "a Modified-by notice past the header": ("\n".join(l for l in new if l not in NEW[23:25]), less),
            "a released line": ("\n".join(l for l in new if l != NEW[16]), less),
            "a blank line outside comments": ("\n".join(new[:-3] + new[-2:]), less),
            "a wrong citation number": (SWEPT_NEW.replace("New2.v:11", "New2.v:12"), "New2.v reads [12]"),
            "no notice": ("\n".join(without_notice), "no notice at line 4"),
            "the notice in another place": ("\n".join(without_notice[:5] + [cs.NOTICE] + without_notice[5:]),
                                            "notice is not at line 4"),
            "a line the rule deletes left in place": (
                SWEPT_NEW.replace(NEW[26] + "\n", NEW[26] + "\n" + NEW[27] + "\n"), "line(s) 28 are still there"),
        }
        for what, (text, phrase) in cases.items():
            with self.subTest(what):
                bad = self.check(self.correct(New_v=text))
                self.assertTrue(bad and phrase in bad[0], (what, bad))
        others = {
            "a cited line deleted": (self.correct(New2_v=SWEPT_NEW2.replace(NEW2[11] + "\n", "")),
                                     "the sweep deleted one of them"),
            "a notice in a file from no donor": (
                self.correct(New2_v="\n".join(NEW2[:1] + [cs.NOTICE] + SWEPT_NEW2.split("\n")[1:])),
                "notice is not at line 1"),
            "a file the rule refuses": (self.correct(Refused_v="\n".join(REFUSED[:11] + [""])), "the rule refuses it"),
            "a script": (dict(self.correct(), **{"projects/demo/fuzz_x/proofs/provenance/run.py": "\n"}),
                         "not a .v file"),
            "a moved file (released)": (self.correct(Moved_v=OLD2), less),
        }
        for what, (files, phrase) in others.items():
            with self.subTest(what):
                bad = self.check(files)
                self.assertTrue(any(phrase in b for b in bad), (what, bad))

    def test_check_of_an_unswept_head_names_what_is_left(self):
        bad, _notes = cs.check(self.repo.unit(), self.repo.head)
        self.assertTrue(any("still there" in b and "New.v" in b for b in bad), bad)

    # ---------------------------------------------------------------------------------------------- KEEP file

    def keep_file(self, rows):
        path = os.path.join(self.repo._tmp.name, "keep.tsv")
        with open(path, "w", encoding="utf-8") as f:
            f.write("# path\tselector\twhy\n" + "".join("\t".join(r) + "\n" for r in rows))
        return path

    def test_keep_list(self):
        rows = cs.read_keep(self.keep_file([(LIB + "New2.v", "13", "tools/gen.py, table out/t.tsv")]))
        plan = cs.Plan(self.repo.unit(), rows, count_other=False)
        self.assertEqual(plan.files[LIB + "New2.v"].reasons[12], "keep-list")
        kept = "\n".join(NEW2[:10] + [NEW2[11], NEW2[12], "Definition z := 0. (* see New.v:18 *)", ""])
        self.assertEqual(plan.files[LIB + "New2.v"].swept_text(), kept)
        self.assertEqual(self.check(self.correct(New2_v=kept), rows), [])
        self.assertNotEqual(self.check(self.correct(New2_v=kept)), [], "without the row, line 13 must go")

    def test_keep_row_that_names_no_comment_line_stops_the_run(self):
        for row in [(LIB + "New2.v", "14", "a code line"), (LIB + "New2.v", "sha256:" + "0" * 64, "no such line"),
                    (LIB + "Old.v", "4", "a released file")]:
            with self.subTest(row):
                rows = cs.read_keep(self.keep_file([row]))
                with self.assertRaises(cs.SweepError):
                    cs.Plan(self.repo.unit(), rows, count_other=False)
        with self.assertRaises(cs.SweepError):
            cs.read_keep(self.keep_file([(LIB + "New2.v", "13", "")]))

    def test_this_tool_is_in_no_key(self):
        """It lives under tools/oft/tests/ because keys.NOT_THE_CHECKER names oft/tests/: anywhere else under tools/
        it would be the checker, whose id is in every unit's key, and adding it would re-check every fuzz target."""
        self.assertTrue(keys.not_the_checker("tools/oft/tests/comment_sweep.py"))
        self.assertTrue(cs.__file__.endswith(os.path.join("tools", "oft", "tests", "comment_sweep.py")))

    def test_cli(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(cs.main(["plan", "--repo", self.repo.root, "--unit", UNIT, "--head", self.repo.head,
                                      "--main", "main"]), 0)
        self.assertIn("%s\t11\tdelete\tno reason keeps it" % (LIB + "New.v"), out.getvalue())
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(cs.main(["check", "--repo", self.repo.root, "--unit", UNIT, "--head", self.repo.head,
                                      "--main", "main", "--swept", self.repo.commit(self.correct())]), 0)
        self.assertIn("check: PASS", out.getvalue())
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(cs.main(["check", "--repo", self.repo.root, "--unit", "nounit", "--head", "main"]), 2)

    def test_the_citation_rows_go_to_the_approval(self):
        """The CI/CD lead's ruling on pull request 639: each approval carries the edit and citation-left rows, each
        marked checked or deleted by the owner; --citations writes them with an empty owner column."""
        path = os.path.join(self.repo._tmp.name, "citations.tsv")
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(cs.main(["plan", "--repo", self.repo.root, "--unit", UNIT, "--head", self.repo.head,
                                      "--main", "main", "--tsv", os.devnull, "--citations", path]), 0)
        with open(path, encoding="utf-8") as f:
            rows = f.read().split("\n")
        self.assertEqual(rows, [
            cs.ROWS_HEADER + "\towner",
            "%sNew.v\t26\tedit\tcitation re-resolved: New2.v:12 -> 11\tDefinition d := 3. (* see New2.v:11 *)\t" % LIB,
            "%sNew2.v\t14\tedit\tcitation re-resolved: New.v:23 -> 18\tDefinition z := 0. (* see New.v:18 *)\t" % LIB,
            "%sNew.v\t27\tcitation-left\tNew2.v: another fuzz target's file (fuzz_y's)\t%s\t" % (LIB, NEW[26]),
            ""])


class ReviewFindings(unittest.TestCase):
    """The shapes the reviews of pull request 639 found, each with a correct sweep that the check must pass and the
    planted sweeps it must fail."""

    FILES = {"Dups.v": DUPS, "Tail.v": TAIL, "NoLf.v": NOLF, "L9.v": L9, "L10.v": L10}
    SWEPT = {"Dups.v": SWEPT_DUPS, "Tail.v": SWEPT_TAIL, "NoLf.v": SWEPT_NOLF, "L9.v": SWEPT_L9}

    @classmethod
    def setUpClass(cls):
        cls.repo = Repo({LIB + name: "\n".join(lines) for name, lines in cls.FILES.items()})
        cls.plan = cs.Plan(cls.repo.unit(), count_other=False)

    @classmethod
    def tearDownClass(cls):
        cls.repo.close()

    def check(self, **changes):
        """The check's findings on the correct sweep with changes ({name with _v for .v: text}) laid over it."""
        files = {LIB + name: text for name, text in self.SWEPT.items()}
        files.update({LIB + k.replace("_v", ".v"): v for k, v in changes.items()})
        bad, self.notes = cs.check(self.repo.unit(), self.repo.commit(files))
        return bad

    def test_the_plan_sweeps_each_file_as_the_rule_says(self):
        for name, text in self.SWEPT.items():
            with self.subTest(name):
                self.assertEqual(self.plan.files[LIB + name].swept_text(), text)
        dups = self.plan.files[LIB + "Dups.v"].reasons
        self.assertEqual([dups[i] for i in range(10, 14)], ["cited", "cited", "deleted", "structural"])
        self.assertEqual([dups[i] for i in (15, 16)], ["cited", "deleted"])

    def test_the_check_passes_the_correct_sweep(self):
        self.assertEqual(self.check(), [])
        self.assertIn("lines deleted: 6 in 4 files; notices: 1; citations re-resolved: 1; new files the rule "
                      "refuses, unchanged: 1", self.notes[1])

    # ---- Rev639 finding 1: a licence line on line 9 or 10

    def test_the_notice_goes_under_a_licence_line_on_line_9(self):
        fp = self.plan.files[LIB + "L9.v"]
        self.assertEqual(fp.notice_at, 9)
        self.assertEqual(lint.scan_licence(SWEPT_L9, LIB + "L9.v", None), [])

    def test_a_licence_line_on_line_10_refuses_the_file(self):
        fp = self.plan.files[LIB + "L10.v"]
        self.assertEqual(fp.refused, [cs.LICENCE_REFUSAL])
        self.assertFalse(fp.changed())
        self.assertIn("%s: %s" % (LIB + "L10.v", cs.LICENCE_REFUSAL), self.plan.summary())

    def test_check_fails_a_notice_that_moves_a_licence_line(self):
        """The notice where the reviewed head put it, under Anthropic's two lines and the notice there, moves L10.v's
        licence line to line 11, which lint refuses; and any sweep of L10.v is refused."""
        old_place = "\n".join(L10[:3] + [cs.NOTICE] + L10[3:10] + L10[11:])
        self.assertNotEqual(lint.scan_licence(old_place, LIB + "L10.v", None), [])
        cases = {
            "L9.v, the notice under Anthropic's lines": (
                {"L9_v": "\n".join(L9[:3] + [cs.NOTICE] + L9[3:10] + L9[11:])}, "notice is not at line 10"),
            "L10.v, the notice under Anthropic's lines": ({"L10_v": old_place}, "notice is not at line 11"),
            "L10.v, the notice under its last licence line": (
                {"L10_v": "\n".join(L10[:10] + [cs.NOTICE] + L10[11:])}, "the rule refuses the file"),
            "L10.v, no notice": ({"L10_v": "\n".join(L10[:10] + L10[11:])}, "the rule refuses the file"),
        }
        for what, (changes, phrase) in cases.items():
            with self.subTest(what):
                bad = self.check(**changes)
                self.assertTrue(any(phrase in b for b in bad), (what, bad))

    # ---- ThermoDeep639 finding 1: a cited line beside an equal one

    def test_check_fails_a_sweep_that_deletes_a_cited_line_beside_its_equal(self):
        swept = SWEPT_DUPS.split("\n")
        cases = {
            "both blank lines": "\n".join(swept[:11] + swept[12:]),
            "both equal comment lines": "\n".join(swept[:14] + swept[15:]),
        }
        for what, text in cases.items():
            with self.subTest(what):
                bad = self.check(Dups_v=text)
                self.assertTrue(any("the sweep deleted one of them" in b for b in bad), (what, bad))

    # ---- ThermoDeep639 finding 2 and Rev639 findings 3 and 4: what lexes, to the end of the file

    def test_check_fails_a_swept_file_that_no_longer_lexes(self):
        """Deleting only the closing line of the last comment leaves it open to the end: rocq.code is unchanged, but
        Rocq cannot compile the file."""
        text = "\n".join(TAIL[:12] + TAIL[13:])
        self.assertEqual(cs.rocq.code(text), cs.rocq.code("\n".join(TAIL)))
        bad = self.check(Tail_v=text)
        self.assertTrue(bad and "does not lex" in bad[0], bad)

    def test_check_fails_a_deletable_last_line_with_no_line_feed_left_in_place(self):
        bad = self.check(NoLf_v="\n".join(NOLF))
        self.assertTrue(any("NoLf.v: line(s) 11 are still there" in b for b in bad), bad)

    def test_plan_and_check_refuse_the_same_open_ends(self):
        for text in ('Definition s := "abc', 'Definition s := "a""', "(* open", 'Definition s := "a""b".\n',
                     'Definition s := "".'):
            with self.subTest(text):
                self.assertEqual(bool(cs.Lexed(text).refused), bool(cs.Seen(text).bad))
        self.assertTrue(cs.Seen('Definition s := "a""').bad)
        self.assertEqual(cs.Seen("a.\n(* b *)").state_after[-1], (0, False))


class RefusedFileCitedOnlyByDeletedLines(unittest.TestCase):
    """ThermoDeep639-2: the check knows a file the rule refuses for its licence line by the lines the rule would
    delete, whatever cites them at HEAD, as the plan does; before, it skipped every line a citation at HEAD names, so
    it did not know X.v as refused and held X.v's citation to a number the plan, rightly, did not write."""

    def test_plan_and_check_agree(self):
        repo = Repo({LIB + "X.v": "\n".join(X), LIB + "Y.v": "\n".join(Y), LIB + "Z.v": "\n".join(Z)})
        self.addCleanup(repo.close)
        plan = cs.Plan(repo.unit(), count_other=False)
        self.assertEqual(plan.files[LIB + "X.v"].refused, [cs.LICENCE_REFUSAL])
        self.assertEqual([(p, i + 1, ref, why) for p, i, ref, why, _line in plan.left],
                         [(LIB + "X.v", 12, "lib/Y.v", "in a file the rule refuses, so 13 stays (the sweep gives 12)")])
        texts = {p: fp.swept_text() for p, fp in plan.files.items() if fp.changed()}
        self.assertEqual(texts, {LIB + "Y.v": SWEPT_Y, LIB + "Z.v": SWEPT_Z})
        bad, notes = cs.check(repo.unit(), repo.commit(texts))
        self.assertEqual(bad, [])
        self.assertIn("lines deleted: 3 in 2 files; notices: 2; citations re-resolved: 0; new files the rule refuses, "
                      "unchanged: 1", notes[1])
        # must fail: a sweep that deletes the refused file's line anyway
        bad, _notes = cs.check(repo.unit(), repo.commit(dict(texts, **{LIB + "X.v": "\n".join(X[:10] + X[11:])})))
        self.assertTrue(any("X.v: lines deleted, but the rule refuses the file" in b for b in bad), bad)


if __name__ == "__main__":
    unittest.main()
