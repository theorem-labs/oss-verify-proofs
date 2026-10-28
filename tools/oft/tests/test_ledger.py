"""oft ledger: the findings ledger over a change's history, in git repositories made for each test."""
import contextlib
import copy
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

from oft import ledger, names, schema, yamlio
from oft.tests.helpers import FINDINGS, FIXTURE

KEY = "zlib/checksum_fuzzer/stand-in-abort"
DIR = "findings/" + KEY
YAML = DIR + "/finding.yaml"
UNPATCHED = "findings/zlib/unpatched.yaml"
HARNESS = "projects/zlib/checksum_fuzzer/harness.yaml"
SECOND = "zlib/checksum_fuzzer/second"
# a record's files, in the order the ledger reports them
RECORD = ("0001-stand-in.patch", "control.bin", "finding.yaml", "input.bin")

GIT = ["git", "-c", "user.name=oft-tests", "-c", "user.email=oft-tests" + "@" + "example.invalid",
       "-c", "commit.gpgsign=false", "-c", "init.defaultBranch=main"]
GIT_ENV = dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")


class Repo:
    """A git repository in a temporary directory.  Its first commit, tagged base, holds the fixture's harness.yaml of
    zlib/checksum_fuzzer, which a record is judged with, and the fixture's findings/ (one patched record,
    findings/zlib/checksum_fuzzer/stand-in-abort, and the unpatched pins), or no findings/."""

    def __init__(self, findings=True):
        self._tmp = tempfile.TemporaryDirectory(prefix="oft-ledger-")
        self.root = os.path.join(self._tmp.name, "repo")
        os.mkdir(self.root)
        self.git("init", "-q")
        os.makedirs(os.path.dirname(self.path(HARNESS)))
        shutil.copyfile(os.path.join(FIXTURE, HARNESS), self.path(HARNESS))
        if findings:
            self.add_findings()
        self.base = self.commit("base")
        self.git("tag", "base")

    def close(self):
        self._tmp.cleanup()

    def git(self, *args, check=True):
        r = subprocess.run(GIT + ["-C", self.root] + list(args), env=GIT_ENV, capture_output=True, text=True)
        if check and r.returncode != 0:
            raise AssertionError("git %s: %s" % (" ".join(args), r.stderr))
        return r.stdout.strip()

    def path(self, *p):
        return os.path.join(self.root, *p)

    def write(self, rel, data):
        os.makedirs(os.path.dirname(self.path(rel)), exist_ok=True)
        with open(self.path(rel), "wb" if isinstance(data, bytes) else "w") as f:
            f.write(data)

    def read(self, rel):
        with open(self.path(rel), "rb") as f:
            return f.read()

    def edit(self, rel, change):
        y = yamlio.load_file(self.path(rel))
        change(y)
        self.write(rel, yamlio.dump(y))

    def remove(self, rel):
        p = self.path(rel)
        shutil.rmtree(p) if os.path.isdir(p) else os.remove(p)

    def add_findings(self):
        shutil.copytree(FINDINGS, self.path("findings"), dirs_exist_ok=True)

    def add_record(self, key):
        """A copy of the fixture's record at findings/<key>/."""
        shutil.copytree(os.path.join(FINDINGS, KEY), self.path("findings", key))

    def commit(self, msg):
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", msg)
        return self.git("rev-parse", "HEAD")

    def ledger(self, tip="HEAD"):
        return [str(f) for f in ledger.run(self.root, "base", tip)]


@contextlib.contextmanager
def repo(findings=True):
    r = Repo(findings)
    try:
        yield r
    finally:
        r.close()


def deleted(key, commit, names=RECORD):
    return ["paths findings/%s/%s: a finding is never deleted: findings/%s/%s, which %s had"
            % (key, n, key, n, commit[:10]) for n in names]


def changed(name, commit):
    rel = DIR + "/" + name
    return ["paths %s: a finding's %s is never changed: %s, since %s" % (rel, name, rel, commit[:10])]


def runs_changed(commit, builds=("asan", "asan-ubsan"), which=("input",)):
    return ["paths %s: a finding's recorded runs are never changed: %s %s.%s, since %s"
            % (YAML, YAML, w, b, commit[:10]) for w in which for b in builds]


def onto_control(commit):
    """What prune_onto_control changes of a record anchored at commit: its input.bin, and its input's runs of the
    builds where the control's differ (the fixture's input and control agree on plain)."""
    return changed("input.bin", commit) + runs_changed(commit)


def set_runner(r, digest):
    """Pin release.yaml's images.runner, the image CI re-runs findings in, to an image whose digest repeats digest,
    adding the fixture's release.yaml if the tree has none."""
    if not os.path.exists(r.path("release.yaml")):
        shutil.copyfile(os.path.join(FIXTURE, "release.yaml"), r.path("release.yaml"))
    r.edit("release.yaml", lambda y: y["images"].update(
        runner="ghcr.io/theorem-labs/oss-fuzz-theorems-runner@sha256:" + digest * 64))


def retag_base(r, msg):
    """Commit the tree as the new base: the history before it is what CI already judged."""
    r.base = r.commit(msg)
    r.git("tag", "-f", "base")


def repinned(commit, builds=("asan", "asan-ubsan")):
    return ["paths %s: a finding's unpatched pins are never changed: %s harnesses.checksum_fuzzer.%s, since %s"
            % (UNPATCHED, UNPATCHED, b, commit[:10]) for b in builds]


def drop_pins(r, builds=("asan", "asan-ubsan")):
    r.edit(UNPATCHED, lambda y: [y["harnesses"]["checksum_fuzzer"].pop(b) for b in builds])


def pin_fixed(r, builds=("asan", "asan-ubsan")):
    """Pin these builds to the binaries built with the patch, on which the input aborts nothing, adding
    unpatched.yaml with the fixture's other pins if the tree has none."""
    fixture = os.path.join(FINDINGS, "zlib", "unpatched.yaml")
    if not os.path.exists(r.path(UNPATCHED)):
        with open(fixture, "rb") as f:
            r.write(UNPATCHED, f.read())
    pins = yamlio.load_file(fixture)["harnesses"]["checksum_fuzzer"]
    r.edit(UNPATCHED, lambda y: y["harnesses"]["checksum_fuzzer"].update(
        {b: dict(pins[b], sha256="e%d" % i * 32) for i, b in enumerate(builds)}))


def prune_keeping_input(r):
    """The gate's release of a hold: the finding pruned with its input.bin kept and its input's runs recorded as what
    the fixed binaries do with it (its control's runs), and its patch out of the series."""
    r.edit(YAML, lambda y: y.update(state="pruned", input={b: dict(run) for b, run in y["control"].items()}))
    r.write("findings/zlib/checksum_fuzzer/series", "")


def prune_onto_control(r):
    """The adversarial gate's rewrite: the control copied over the input, its runs recorded as the input's, the
    finding pruned and its patch out of the series.  The record is evidence: it loads and meets every rule."""
    shutil.copyfile(r.path(DIR, "control.bin"), r.path(DIR, "input.bin"))
    r.edit(YAML, lambda y: y.update(state="pruned", input={b: dict(run) for b, run in y["control"].items()}))
    r.write("findings/zlib/checksum_fuzzer/series", "")


def narrow(y):
    """asan_agrees alone, with the asan-ubsan runs dropped beside it: a record that is evidence."""
    y["statements"] = ["asan_agrees"]
    for runs in (y["input"], y["control"]):
        del runs["asan-ubsan"]


class Deletion(unittest.TestCase):
    def test_a_file_paths_py_does_not_list_may_go_and_a_record_may_not(self):
        """The rule is net and protects records: a format change may drop the run.sh and VERDICT.md beside a record,
        and a branch that then deletes the record's directory is refused."""
        with repo() as r:
            r.write(DIR + "/run.sh", "#!/bin/sh\n")
            r.write(DIR + "/VERDICT.md", "reproduces\n")
            r.commit("the record, with an old run.sh and verdict beside it")
            r.remove(DIR + "/run.sh")
            r.remove(DIR + "/VERDICT.md")
            r.commit("the new format drops them")
            self.assertEqual(r.ledger(), [])
            r.remove(DIR)
            r.commit("the record goes")
            self.assertEqual(r.ledger(), deleted(KEY, r.base))

    def test_through_a_merge_parent(self):
        """Each parent of a merge counts.  A side branch that adds a record and drops its run.sh merges clean; one
        that adds a record and deletes its directory before the merge is refused, though neither parent of the merge
        has the record; so is a merge that keeps only its first parent's tree, which drops what its second parent
        had while it changes nothing of its first parent's tree."""
        third = "zlib/checksum_fuzzer/third"
        with repo() as r:
            r.git("checkout", "-q", "-b", "side")
            r.add_record(SECOND)
            r.write("findings/%s/run.sh" % SECOND, "#!/bin/sh\n")
            r.commit("a second record, with its run.sh")
            r.remove("findings/%s/run.sh" % SECOND)
            r.commit("the run.sh goes")
            r.git("checkout", "-q", "main")
            r.commit("main moves on")
            r.git("merge", "-q", "--no-edit", "side")
            self.assertEqual(r.ledger(), [])
        with repo() as r:
            r.git("checkout", "-q", "-b", "side")
            r.add_record(third)
            added = r.commit("a third record")
            r.remove("findings/" + third)
            r.commit("and its directory goes")
            r.git("checkout", "-q", "main")
            r.commit("main moves on")
            r.git("merge", "-q", "--no-edit", "side")
            self.assertEqual(r.ledger(), deleted(third, added))
        with repo() as r:
            r.git("checkout", "-q", "-b", "side")
            r.add_record(third)
            added = r.commit("a third record")
            r.git("checkout", "-q", "main")
            r.commit("main moves on")
            r.git("merge", "-q", "--no-edit", "-s", "ours", "side")
            self.assertEqual(r.git("diff", "--name-only", "HEAD^1", "HEAD"), "")
            self.assertEqual(r.ledger(), deleted(third, added))

    def test_a_record_added_and_removed_on_the_branch(self):
        """The case two trees miss: the base and the tip have the same findings/."""
        with repo() as r:
            r.add_record(SECOND)
            added = r.commit("a second record")
            r.remove("findings/" + SECOND)
            r.commit("and it goes")
            self.assertEqual(r.git("diff", "--name-only", "base", "HEAD"), "")
            self.assertEqual(r.ledger(), deleted(SECOND, added))

    def test_restoring_a_deleted_record_clears_the_finding(self):
        with repo() as r:
            r.remove(DIR)
            gone = r.commit("the record goes")
            self.assertEqual(r.ledger(), deleted(KEY, r.base))
            r.git("checkout", "base", "--", DIR)
            r.commit("the record is back")
            self.assertEqual(r.ledger(), [])
            self.assertEqual(r.ledger(tip=gone), deleted(KEY, r.base))

    def test_a_record_s_patch_is_one_of_its_files(self):
        with repo() as r:
            r.remove(DIR + "/0001-stand-in.patch")
            r.commit("the patch goes")
            self.assertEqual(r.ledger(), deleted(KEY, r.base, names=RECORD[:1]))

    def test_unpatched_pins_are_never_deleted(self):
        with repo() as r:
            r.remove(UNPATCHED)
            r.commit("the pins go")
            self.assertEqual(r.ledger(), ["paths %s: a finding's unpatched pins are never deleted: %s, which %s had"
                                          % (UNPATCHED, UNPATCHED, r.base[:10])])

    def test_a_replace_ref_or_a_graft_hides_no_deletion(self):
        """A graft that makes the tip a child of base hides the commit that added the record, so a walk that honoured
        it would see neither the record nor its deletion."""
        for how in ("replace", "grafts"):
            with self.subTest(how=how), repo() as r:
                r.add_record(SECOND)
                added = r.commit("a second record")
                r.remove("findings/" + SECOND)
                tip = r.commit("and it goes")
                if how == "replace":
                    r.git("replace", "--graft", tip, r.base)
                else:
                    r.write(".git/info/grafts", "%s %s\n" % (tip, r.base))
                self.assertEqual(r.git("-c", "advice.graftFileDeprecated=false", "rev-list", "--count", "base..HEAD"),
                                 "1", "the graft is in force for git itself")
                self.assertEqual(r.ledger(), deleted(SECOND, added))


class Drafts(unittest.TestCase):
    """Before its anchor, its first version whose input.bin and control.bin are regular files that begin with a
    complete driver header, each of whose statements is an agreement or halts statement by its name, and whose input
    and control each hold a run of every build those name in the shape `oft check --record` prints, a record is a
    draft that CI never re-ran: it may change in any way, and be renamed or deleted.  Nothing outside the record
    decides it, so no other file and no change to the tools makes a draft."""

    def test_a_draft_corrected_before_its_anchor_is_clean(self):
        """The final gate's case at b5dac6d61e, its runs recorded in the draft: one statement too few, an input.bin
        shorter than its driver header and a patch file name, then corrected."""
        with repo(findings=False) as r:
            r.add_findings()
            r.edit(YAML, lambda y: y.update(statements=["asan_agrees"], patch="0001-draft.patch"))
            os.rename(r.path(DIR, "0001-stand-in.patch"), r.path(DIR, "0001-draft.patch"))
            r.write(DIR + "/input.bin", b"\0\0\0")
            r.write("findings/zlib/checksum_fuzzer/series", "0001-draft.patch\n")
            self.assertIn("input", yamlio.load_file(r.path(YAML)), "the draft has its runs")
            r.commit("a draft")
            r.remove("findings")
            r.add_findings()
            r.commit("corrected")
            self.assertEqual(r.ledger(), [])

    def test_a_control_shorter_than_its_driver_header_is_a_draft(self):
        with repo(findings=False) as r:
            r.add_findings()
            r.write(DIR + "/control.bin", b"\0")
            r.commit("a draft, its runs recorded")
            r.remove(DIR)
            r.commit("dropped")
            self.assertEqual(r.ledger(), [])

    def test_a_draft_slug_renamed_before_its_anchor_is_clean(self):
        """A slug mistyped in a record with no runs yet may be renamed; once the record has its runs, it may not."""
        typo = "zlib/checksum_fuzzer/stand-in-abrot"
        for runs in (False, True):
            with self.subTest(runs=runs), repo(findings=False) as r:
                r.add_findings()
                shutil.move(r.path(DIR), r.path("findings", typo))
                if not runs:
                    r.edit("findings/%s/finding.yaml" % typo, lambda y: (y.pop("input"), y.pop("control")))
                first = r.commit("the record, under a mistyped slug")
                r.remove("findings")
                r.add_findings()
                r.commit("renamed")
                self.assertEqual(r.ledger(), deleted(typo, first) if runs else [])

    def test_a_draft_may_be_deleted(self):
        with repo(findings=False) as r:
            r.add_findings()
            r.edit(YAML, lambda y: (y.pop("input"), y.pop("control")))
            r.commit("a draft, with no runs")
            r.remove(DIR)
            r.commit("dropped")
            self.assertEqual(r.ledger(), [])

    def test_a_broken_harness_yaml_or_missing_unpatched_yaml_makes_no_draft(self):
        """The adversarial gate's cases: commit A has the finding with its runs while a file outside the record is
        broken; commit B mends that file and pruned the finding onto its control.  A is the anchor all the same."""
        def unknown_key(r):
            with open(r.path(HARNESS), "a") as f:
                f.write("colour: blue\n")

        def lacks_statement(r):
            r.edit(HARNESS, lambda y: y["statements"].pop("asan_ubsan_agrees"))
        for name, breaks in (("an unknown key in harness.yaml", unknown_key),
                             ("harness.yaml lacks a statement", lacks_statement),
                             ("no harness.yaml", lambda r: r.remove(HARNESS)),
                             ("no unpatched.yaml", lambda r: r.remove(UNPATCHED))):
            with self.subTest(name), repo(findings=False) as r:
                r.add_findings()
                breaks(r)
                anchor = r.commit("the finding, with its runs, beside a broken file")
                r.git("checkout", "base", "--", "projects")
                r.add_findings()
                prune_onto_control(r)
                r.commit("the file mended, and the finding pruned onto its control")
                self.assertEqual(r.ledger(), onto_control(anchor))

    def assert_a_draft(self, first_version):
        """A commit has first_version of the record; the next records every run, as the fixture has them; the next
        repins asan and asan-ubsan to the fixed binaries and prunes the finding with its input.bin kept.  The first is
        a draft, so the second is the anchor, and the repin and the runs of the prune are refused."""
        with repo(findings=False) as r:
            r.add_findings()
            first_version(r)
            r.commit("the record's first version")
            r.add_findings()
            anchor = r.commit("every run recorded")
            pin_fixed(r)
            prune_keeping_input(r)
            r.commit("asan and asan-ubsan pinned to the fixed binaries, and pruned")
            self.assertEqual(r.ledger(), runs_changed(anchor) + repinned(anchor))

    def test_runs_that_do_not_cover_the_builds_its_statements_name_are_a_draft(self):
        """The adversarial gate's 1a, 1b, 1c and 2d: the statements name plain, asan and asan-ubsan, and the runs are
        of another build only, or of a build of no name; and its 1e, a statement of another kind named beside them."""
        def runs_of(*builds):
            def first(r):
                r.edit(YAML, lambda y: y.update(input={b: dict(y["input"]["plain"]) for b in builds},
                                                control={b: dict(y["control"]["plain"]) for b in builds}))
            return first
        for name, first in (("1a: runs of a build bogus only", runs_of("bogus")),
                            ("1b: runs of ubsan only", runs_of("ubsan")),
                            ("1c: runs of plain only", runs_of("plain")),
                            ("asan-ubsan's runs missing", lambda r: r.edit(YAML, lambda y: (
                                y["input"].pop("asan-ubsan"), y["control"].pop("asan-ubsan")))),
                            ("2d: one run, of an empty key", lambda r: r.edit(YAML, lambda y: y.update(
                                input={"": ""}, control={"": ""}))),
                            ("1e: a bound statement named beside them", lambda r: r.edit(YAML, lambda y: (
                                y["statements"].append("asan_disagrees_at_most"),
                                y.update(input={"bogus": y["input"]["plain"]}, control={"bogus": y["control"]["plain"]})))),
                            ("a statement no harness has", lambda r: r.edit(
                                YAML, lambda y: y["statements"].append("asan_agrees_always")))):
            with self.subTest(name):
                self.assert_a_draft(first)

    def test_a_statement_s_builds_come_from_its_name_as_harness_yaml_gives_them(self):
        """names.statement_builds gives each agreement and halts statement of the fixture's harness.yaml the builds
        its fields give, and no builds for a statement of another kind."""
        for name, st in yamlio.load_file(os.path.join(FIXTURE, HARNESS))["statements"].items():
            with self.subTest(name):
                want = tuple(st["builds"]) if st["kind"] in ("agreement", "halts") else None
                self.assertEqual(names.statement_builds(name), want)

    def test_a_run_not_of_the_shape_oft_check_record_prints_is_a_draft(self):
        """The adversarial gate's 2a, 2b and 2c, and further: the run of asan is not one `oft check --record` prints."""
        sha = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        for name, run in (("2a: empty strings", {"exit": "", "stdout_sha256": "", "stderr_sha256": ""}),
                          ("2b: an empty map", {}),
                          ("2c: a string", ""),
                          ("exit missing", {"stdout_sha256": sha, "stderr_sha256": sha}),
                          ("exit a boolean", {"exit": True, "stdout_sha256": sha, "stderr_sha256": sha}),
                          ("exit 256", {"exit": 256, "stdout_sha256": sha, "stderr_sha256": sha}),
                          ("exit null", {"exit": None, "stdout_sha256": sha, "stderr_sha256": sha}),
                          ("a signal of no name the schema has", {"exit": 134, "signal": "SIGKILL",
                                                                  "stdout_sha256": sha, "stderr_sha256": sha}),
                          ("a signal by number", {"exit": 134, "signal": 6, "stdout_sha256": sha, "stderr_sha256": sha}),
                          ("a hash in capitals", {"exit": 0, "stdout_sha256": sha.upper(), "stderr_sha256": sha}),
                          ("a hash too short", {"exit": 0, "stdout_sha256": sha[:63], "stderr_sha256": sha}),
                          ("another key", {"exit": 0, "stdout_sha256": sha, "stderr_sha256": sha, "seconds": 1})):
            for which in ("input", "control"):
                with self.subTest(name, which=which):
                    self.assert_a_draft(lambda r: r.edit(YAML, lambda y: y[which].update(asan=run)))

    def test_runs_of_empty_strings_on_every_build_are_a_draft_that_may_be_corrected(self):
        """The adversarial gate's 2e: every named build has a run of empty strings, which the loader refuses; the
        author then corrects input.bin and records real runs."""
        empty = {"exit": "", "stdout_sha256": "", "stderr_sha256": ""}
        with repo(findings=False) as r:
            r.add_findings()
            r.edit(YAML, lambda y: y.update(input={b: dict(empty) for b in y["input"]},
                                            control={b: dict(empty) for b in y["control"]}))
            r.write(DIR + "/input.bin", r.read(DIR + "/input.bin") + b"before it was corrected\n")
            r.commit("runs of empty strings")
            r.add_findings()
            r.commit("input.bin corrected, and its runs recorded")
            self.assertEqual(r.ledger(), [])

    def test_a_run_of_a_build_its_statements_do_not_name_beside_them_is_no_draft(self):
        """A run of ubsan beside the runs of the builds the statements name, which lint refuses in the tree: the
        version is evidence all the same, so no extra key turns evidence into a draft."""
        with repo(findings=False) as r:
            r.add_findings()
            r.edit(YAML, lambda y: (y["input"].update(ubsan=dict(y["input"]["plain"])),
                                    y["control"].update(ubsan=dict(y["control"]["plain"]))))
            anchor = r.commit("every run, and one of ubsan")
            prune_onto_control(r)
            r.commit("pruned onto its control")
            self.assertEqual(r.ledger(), onto_control(anchor))

    def test_a_required_field_added_to_the_schemas_makes_no_draft(self):
        """A later release of the tools adds a required field to a schema, so a record anchored under the old one
        no longer loads; its deletion is refused all the same."""
        schemas = {kind: copy.deepcopy(schema.load_schema(kind)) for kind in ("finding", "harness", "unpatched")}
        for kind, s in schemas.items():
            s["defs"][s["root"]["name"]]["fields"]["added_later"] = {"type": "str"}
        with repo() as r, mock.patch.dict(schema._SCHEMAS, schemas):
            self.assertTrue(any("missing key 'added_later'" in e for e in schema.validate(
                "finding", yamlio.load_file(r.path(YAML)))), "the record no longer meets the finding schema")
            r.remove(DIR)
            r.commit("the record goes")
            self.assertEqual(r.ledger(), deleted(KEY, r.base))

    def test_an_input_of_a_full_payload_and_its_header_is_evidence(self):
        """A finding of a harness that reads 64 KiB: a 64 KiB payload after the six-byte header, 65,542 bytes.  Such a
        record is anchored, so its deletion is refused, and so is one of exactly the 1 MiB finding input cap; one byte
        over that cap it is a draft, which may go.  input.bin and control.bin alike."""
        for name in ledger.FIXED_FILES:
            for size, anchored in (((64 << 10) + 6, True), (1 << 20, True), ((1 << 20) + 1, False)):
                with self.subTest(name=name, size=size), repo(findings=False) as r:
                    r.add_findings()
                    rel = DIR + "/" + name
                    head = r.read(rel)
                    r.write(rel, head + b"x" * (size - len(head)))
                    added = r.commit("a record with a long " + name)
                    r.remove(DIR)
                    r.commit("the record goes")
                    self.assertEqual(r.ledger(), deleted(KEY, added) if anchored else [])


class Evidence(unittest.TestCase):
    def test_what_a_finding_s_runs_are_of_never_changes_and_a_restore_clears_it(self):
        """A record added on the branch and its input or control rewritten in a later commit: the tip's tree is a
        new record that lint's base comparison accepts.  Restoring it clears the finding."""
        for name in ("input.bin", "control.bin"):
            with self.subTest(name=name), repo(findings=False) as r:
                r.add_findings()
                added = r.commit("a finding")
                rel = DIR + "/" + name
                first = r.read(rel)
                r.write(rel, b"\0\0\0\0\0\0another run\n")
                r.commit("its %s is rewritten" % name)
                self.assertEqual(r.ledger(), changed(name, added))
                r.write(rel, first)
                r.commit("and put back")
                self.assertEqual(r.ledger(), [])

    def test_a_state_never_returns_to_open_over_the_history(self):
        """A record added on the branch as patched and set back to open in a later commit: the base has no record, so
        lint's base comparison sees nothing.  For an enrolled project an open finding holds back only its statements,
        while the pinned build still carries the patch."""
        with repo(findings=False) as r:
            r.add_findings()
            added = r.commit("a patched finding")
            r.edit(YAML, lambda y: y.update(state="open"))
            r.commit("and open again")
            self.assertEqual(r.ledger(), ["paths %s: a finding's state never returns to open: %s was patched at %s"
                                          % (YAML, YAML, added[:10])])
            r.edit(YAML, lambda y: y.update(state="patched"))
            r.commit("patched once more")
            self.assertEqual(r.ledger(), [])

    def test_a_finding_that_was_open_all_along_is_no_finding(self):
        with repo(findings=False) as r:
            r.add_findings()
            r.edit(YAML, lambda y: [y.update(state="open"), y.pop("patch", None)])
            r.commit("an open finding")
            r.edit(YAML, lambda y: y.update(summary="A stand-in finding for these tests; its summary changed."))
            r.commit("its summary changes")
            self.assertEqual(r.ledger(), [])

    def test_statements_may_grow(self):
        with repo(findings=False) as r:
            r.add_findings()
            r.edit(YAML, narrow)
            r.commit("asan_agrees")
            r.remove("findings")
            r.add_findings()
            r.commit("asan_ubsan_agrees too")
            self.assertEqual(r.ledger(), [])

    def test_statements_never_shrink_and_their_order_does_not_count(self):
        with repo() as r:
            r.edit(YAML, lambda y: y.update(statements=list(reversed(y["statements"]))))
            r.commit("the same statements, in another order")
            self.assertEqual(r.ledger(), [])
            r.edit(YAML, narrow)
            r.commit("narrowed")
            self.assertEqual(r.ledger(), ["paths %s: a finding's statements only grow: %s no longer names "
                                          "asan_ubsan_agrees, which %s recorded" % (YAML, YAML, r.base[:10])]
                             + runs_changed(r.base, builds=("asan-ubsan",), which=("input", "control")))

    def test_the_unpatched_pins_of_a_harness_with_a_finding_never_change(self):
        with repo() as r:
            r.edit(UNPATCHED, lambda y: y["harnesses"]["checksum_fuzzer"]["asan"].update(sha256="8" * 64))
            r.commit("repinned")
            self.assertEqual(r.ledger(), ["paths %s: a finding's unpatched pins are never changed: %s "
                                          "harnesses.checksum_fuzzer.asan, since %s"
                                          % (UNPATCHED, UNPATCHED, r.base[:10])])

    def test_a_pin_for_a_build_no_anchor_ran_may_be_added_or_changed(self):
        """The adversarial gate's Low: the record runs plain, asan and asan-ubsan, so its anchor freezes those pins
        only.  A ubsan pin, which a second finding naming ubsan_agrees needs, may be added and then changed."""
        with repo(findings=False) as r:
            r.add_findings()
            r.edit(UNPATCHED, lambda y: y["harnesses"]["checksum_fuzzer"].pop("ubsan"))
            r.commit("the finding, with no ubsan pin")
            r.git("checkout", "base", "--", "projects")
            shutil.copyfile(os.path.join(FINDINGS, "zlib", "unpatched.yaml"), r.path(UNPATCHED))
            r.commit("a ubsan pin")
            self.assertEqual(r.ledger(), [])
            r.edit(UNPATCHED, lambda y: y["harnesses"]["checksum_fuzzer"]["ubsan"].update(sha256="9" * 64))
            r.commit("the ubsan pin changed")
            self.assertEqual(r.ledger(), [])

    def test_a_prune_or_a_correction_with_no_runner_change_is_refused(self):
        """Every build the record runs is pinned at its anchor, and its anchor is in the base, but the runner image is
        the same: the same binaries in the same runner give the same runs, so a prune that changes them, or any other
        change to them, is refused."""
        with repo(findings=False) as r:
            r.add_findings()
            set_runner(r, "1")
            retag_base(r, "base: the record, run in runner 1")
            prune_keeping_input(r)
            r.commit("pruned, its input's runs those of the control")
            self.assertEqual(r.ledger(), runs_changed(r.base))
            r.add_findings()
            r.edit(YAML, lambda y: y["input"]["asan"].update(stdout_sha256="0" * 64))
            r.commit("instead, one run recorded again")
            self.assertEqual(r.ledger(), runs_changed(r.base, builds=("asan",)))

    def test_a_new_runner_may_record_the_runs_of_a_record_from_the_base_again(self):
        """The record is anchored in the base, so the checked merge that brought it there re-ran its runs against its
        pins.  A commit that pins another runner image may record a run again, and a prune whose runs are what the new
        runner gives is clean too (CI's re-run then checks that the input shows no statement false).  Back on the
        anchor's runner, the anchor's runs hold again."""
        with repo(findings=False) as r:
            r.add_findings()
            set_runner(r, "1")
            retag_base(r, "base: the record, run in runner 1")
            set_runner(r, "2")
            r.edit(YAML, lambda y: [run.update(stdout_sha256="0" * 64) for run in y["control"].values()])
            r.commit("runner 2, and the control's runs, which it prints otherwise, recorded again")
            self.assertEqual(r.ledger(), [])
            r.add_findings()
            prune_keeping_input(r)
            r.commit("pruned, its input's runs those of the control")
            self.assertEqual(r.ledger(), [])
            set_runner(r, "1")
            r.commit("back to runner 1")
            self.assertEqual(r.ledger(), runs_changed(r.base))

    def test_a_base_record_is_judged_against_the_base_s_runner_and_runs(self):
        """The final gate's P3: the record anchored under runner 1, then main moves to runner 2.  A proof-branch push
        on runner 2 that prunes it is refused, as lint refuses it: the base's runner is the tip's.  When main's move to
        runner 2 also recorded the runs again, the base's runs are the ones that hold, and a later change on runner 2
        must keep them."""
        for rerecorded in (False, True):
            with self.subTest(rerecorded=rerecorded), repo(findings=False) as r:
                r.add_findings()
                set_runner(r, "1")
                anchor = r.commit("the record, run in runner 1")
                set_runner(r, "2")
                if rerecorded:
                    r.edit(YAML, lambda y: [run.update(stdout_sha256="0" * 64) for run in y["control"].values()])
                retag_base(r, "main moves to runner 2" + (", the runs recorded again" if rerecorded else ""))
                rerun = yamlio.load_file(r.path(YAML))
                prune_keeping_input(r)
                r.commit("pruned on runner 2")
                # with the base's runs recorded again, the control's plain run copied into the input differs from the
                # base's input plain run too
                self.assertEqual(r.ledger(), runs_changed(anchor, builds=("plain", "asan", "asan-ubsan")
                                                          if rerecorded else ("asan", "asan-ubsan")))
                r.edit(YAML, lambda y: y.update(input=rerun["input"], control=rerun["control"]))
                r.commit("the base's runs back")
                self.assertEqual(r.ledger(), [])

    def test_the_adversarial_gate_s_runner_fixtures(self):
        """The adversarial gate's three fixtures at 4e04590e0d, each with the record in the base.  1: a release moves
        the base to runner 2 and records the runs again; a push on runner 2 that changes them again is refused.  2: the
        anchor commit had runner 2, set back to 1 before the merge; a push that records the runs again on runner 1 is
        refused.  3: from the same anchor, the release that moves the base from runner 1 to 2 and records the runs
        again is clean."""
        def control_again(digit):
            return lambda y: [run.update(stdout_sha256=digit * 64) for run in y["control"].values()]
        with self.subTest(fixture=1), repo(findings=False) as r:
            r.add_findings()
            set_runner(r, "1")
            anchor = r.commit("the record, run in runner 1")
            set_runner(r, "2")
            r.edit(YAML, control_again("0"))
            retag_base(r, "a release: runner 2, the runs recorded again")
            r.edit(YAML, control_again("9"))
            r.commit("the runs changed again, on runner 2")
            self.assertEqual(r.ledger(), runs_changed(anchor, builds=("plain", "asan", "asan-ubsan"), which=("control",)))
        for fixture in (2, 3):
            with self.subTest(fixture=fixture), repo(findings=False) as r:
                r.add_findings()
                set_runner(r, "2")
                anchor = r.commit("the lane's anchor, on runner 2")
                set_runner(r, "1")
                retag_base(r, "back to runner 1, and merged")
                if fixture == 3:
                    set_runner(r, "2")
                r.edit(YAML, control_again("0"))
                r.commit("the runs recorded again" + (", in the release that moves to runner 2" if fixture == 3 else ""))
                self.assertEqual(r.ledger(), [] if fixture == 3 else runs_changed(
                    anchor, builds=("plain", "asan", "asan-ubsan"), which=("control",)))

    def stale_branch(self, r, main_moves):
        """main has the record, run in runner 1; a proof branch is cut there; main then moves on (main_moves), and
        the branch never merges it.  Returns the record's anchor, with the branch checked out."""
        r.add_findings()
        set_runner(r, "1")
        anchor = r.commit("main: the record, run in runner 1")
        r.git("checkout", "-q", "-b", "proofs/zlib")
        r.git("checkout", "-q", "main")
        main_moves(r)
        r.commit("main moves on")
        r.git("tag", "-f", "base")
        r.base = r.git("rev-parse", "HEAD")
        r.git("checkout", "-q", "proofs/zlib")
        return anchor

    def test_a_push_from_a_branch_that_lags_main_is_judged_against_what_it_has(self):
        """The adversarial gate's four push fixtures at ce17e78dbe: BASE is main's head, which the branch never merged.
        The ledger takes the runner and the runs from git merge-base BASE TIP, the newest commit of main the branch
        has: 1, main moves to runner 2 and the branch, still on runner 1, prunes; 2, the same with main also recording
        the runs again; 3, main moves to runner 2 and the branch changes the control's runs; 4, main grows the record's
        statements to ubsan_agrees with the ubsan runs, and the branch pushes a commit that touches no finding."""
        def runner2(again=False):
            def move(r):
                set_runner(r, "2")
                if again:
                    r.edit(YAML, lambda y: [run.update(stdout_sha256="0" * 64) for run in y["control"].values()])
            return move

        def ubsan(r):
            """ubsan_agrees, with the ubsan runs: the fixture pins the unpatched ubsan binary already."""
            r.edit(YAML, lambda y: (y["statements"].append("ubsan_agrees"),
                                    y["input"].update(ubsan=dict(y["input"]["plain"])),
                                    y["control"].update(ubsan=dict(y["control"]["plain"]))))
        cases = ((1, runner2(), prune_keeping_input, ("input",), ("asan", "asan-ubsan")),
                 (2, runner2(again=True), prune_keeping_input, ("input",), ("asan", "asan-ubsan")),
                 (3, runner2(), lambda r: r.edit(YAML, lambda y: [run.update(stdout_sha256="9" * 64)
                                                                  for run in y["control"].values()]),
                  ("control",), ("plain", "asan", "asan-ubsan")),
                 (4, ubsan, lambda r: r.write("notes.txt", "a commit that touches no finding\n"), (), ()))
        for fixture, main_moves, push, which, builds in cases:
            with self.subTest(fixture=fixture), repo(findings=False) as r:
                anchor = self.stale_branch(r, main_moves)
                push(r)
                r.commit("the branch's push")
                self.assertEqual(r.ledger(), runs_changed(anchor, builds=builds, which=which))

    def released_branch(self, r, main_moves, branch_commits=None):
        """main has the record, run in runner 1; proof branch P is cut there and commits q (branch_commits, or a commit
        that touches no finding); main moves on (main_moves, if any), and a release pull request merges q into main
        with a merge commit.  P carries on from q without merging main.  Returns the record's anchor, with P checked
        out."""
        r.add_findings()
        set_runner(r, "1")
        anchor = r.commit("main: the record, run in runner 1")
        r.git("checkout", "-q", "-b", "proofs/zlib")
        (branch_commits or (lambda r: r.write("notes-q.txt", "q\n")))(r)
        r.commit("q")
        r.git("checkout", "-q", "main")
        if main_moves:
            main_moves(r)
            r.commit("M1: main moves on")
        r.git("merge", "-q", "--no-ff", "--no-edit", "proofs/zlib")
        r.git("tag", "-f", "base")
        r.base = r.git("rev-parse", "HEAD")
        r.git("checkout", "-q", "proofs/zlib")
        return anchor

    def test_a_push_from_a_branch_a_merge_commit_released_is_judged_against_what_it_has(self):
        """The adversarial gate's four merge-commit fixtures at d026d80fd4: the merge base is q, and the merge commit
        that brought q into main also holds main's M1, which the branch never had, so the ledger reads the newest
        commit of main's first-parent line the branch has.  1, M1 moves main to runner 2 and the branch, still on
        runner 1, prunes; 2, the same with M1 also recording the runs again; 3, M1 moves main to runner 2 and the
        branch changes the control's runs; 4, M1 grows the record's statements to ubsan_agrees with the ubsan runs,
        and the branch pushes a commit that touches no finding."""
        def runner2(again=False):
            def move(r):
                set_runner(r, "2")
                if again:
                    r.edit(YAML, lambda y: [run.update(stdout_sha256="0" * 64) for run in y["control"].values()])
            return move

        def ubsan(r):
            r.edit(YAML, lambda y: (y["statements"].append("ubsan_agrees"),
                                    y["input"].update(ubsan=dict(y["input"]["plain"])),
                                    y["control"].update(ubsan=dict(y["control"]["plain"]))))
        cases = ((1, runner2(), prune_keeping_input, ("input",), ("asan", "asan-ubsan")),
                 (2, runner2(again=True), prune_keeping_input, ("input",), ("asan", "asan-ubsan")),
                 (3, runner2(), lambda r: r.edit(YAML, lambda y: [run.update(stdout_sha256="9" * 64)
                                                                  for run in y["control"].values()]),
                  ("control",), ("plain", "asan", "asan-ubsan")),
                 (4, ubsan, lambda r: r.write("notes.txt", "a commit that touches no finding\n"), (), ()))
        for fixture, main_moves, push, which, builds in cases:
            with self.subTest(fixture=fixture), repo(findings=False) as r:
                anchor = self.released_branch(r, main_moves)
                q = r.git("rev-parse", "HEAD")
                push(r)
                tip = r.commit("the branch's push")
                self.assertEqual(r.git("merge-base", "--all", r.base, tip), q, "the merge base is q, off main's line")
                self.assertEqual(r.ledger(), runs_changed(anchor, builds=builds, which=which))

    def test_a_merge_commit_that_kept_the_branch_s_state_vouches_for_it(self):
        """The branch records the control's runs again on runner 2 at q, and a release merges q into main with a
        merge commit that keeps q's runner and record.  That merge commit vouches for q, so the branch's later push
        that changes the control's runs again, still on runner 2, is refused.  Reading the newest commit of main the
        branch had before q, on runner 1, would constrain nothing and pass it."""
        def rerecord(r):
            set_runner(r, "2")
            r.edit(YAML, lambda y: [run.update(stdout_sha256="0" * 64) for run in y["control"].values()])
        with repo(findings=False) as r:
            anchor = self.released_branch(r, None, branch_commits=rerecord)
            r.edit(YAML, lambda y: [run.update(stdout_sha256="9" * 64) for run in y["control"].values()])
            r.commit("the control's runs changed again, on runner 2")
            self.assertEqual(r.ledger(), runs_changed(anchor, builds=("plain", "asan", "asan-ubsan"), which=("control",)))

    def test_a_release_that_rewords_the_finding_still_vouches_for_its_runs(self):
        """The adversarial gate's three cases at f7c98e5509: the branch records the control's runs again on runner 2 at
        q, and a release merges q into main keeping q's runner and runs, but the finding's summary changes: in the
        release's merge commit, or on main before it.  A finding's text may change, so the merge commit still vouches
        for q's runs, and the branch's later push is refused: 1 and 2, it changes the control's runs again; 3, it
        prunes with input.bin kept."""
        def rerecord(r):
            set_runner(r, "2")
            r.edit(YAML, lambda y: [run.update(stdout_sha256="0" * 64) for run in y["control"].values()])

        def reword(r):
            r.edit(YAML, lambda y: y.update(summary="A stand-in finding, worded again."))

        def change_control(r):
            r.edit(YAML, lambda y: [run.update(stdout_sha256="9" * 64) for run in y["control"].values()])
        every = ("plain", "asan", "asan-ubsan")
        cases = (("the release merge rewords it", "merge", change_control, ("control",), every),
                 ("main rewords it before the release", "main", change_control, ("control",), every),
                 ("the release merge rewords it, then a prune", "merge", prune_keeping_input, ("input",), every))
        for name, where, push, which, builds in cases:
            with self.subTest(name), repo(findings=False) as r:
                r.add_findings()
                set_runner(r, "1")
                anchor = r.commit("main: the record, run in runner 1")
                r.git("checkout", "-q", "-b", "proofs/zlib")
                rerecord(r)
                q = r.commit("q: runner 2, the control's runs recorded again")
                r.git("checkout", "-q", "main")
                if where == "main":
                    reword(r)
                    r.commit("main rewords the finding")
                r.git("merge", "-q", "--no-ff", "--no-commit", "proofs/zlib", check=False)
                # the release keeps q's runner and runs, with the finding reworded
                r.git("checkout", q, "--", YAML, "release.yaml")
                reword(r)
                self.assertEqual(yamlio.load_file(r.path(YAML))["control"],
                                 yamlio.load(r.git("show", q + ":" + YAML), where=YAML)["control"])
                r.commit("the release merges q")
                r.git("tag", "-f", "base")
                r.base = r.git("rev-parse", "HEAD")
                r.git("checkout", "-q", "proofs/zlib")
                push(r)
                r.commit("the branch's push")
                self.assertEqual(r.ledger(), runs_changed(anchor, builds=builds, which=which))

    def test_a_criss_cross_history_is_judged_against_every_merge_base(self):
        """Two merge bases of BASE and TIP after a criss-cross merge, a on main's first-parent line and b merged by
        main's next commit, which keeps b's runs: the two commits where they entered main disagree in a control run,
        so TIP agrees with each of them or is refused, whichever runs it keeps.  With one merge base only, one of the
        two tips would pass."""
        with repo(findings=False) as r:
            r.add_findings()
            set_runner(r, "1")
            anchor = r.commit("the record, run in runner 1")
            r.git("checkout", "-q", "-b", "a")
            r.write("notes-a.txt", "a\n")
            a = r.commit("a")
            r.git("checkout", "-q", "-b", "b", anchor)
            r.edit(YAML, lambda y: y["control"]["plain"].update(stdout_sha256="0" * 64))
            b = r.commit("b: a control run recorded otherwise")
            ma = r.git("commit-tree", b + "^{tree}", "-p", a, "-p", b, "-m", "main merges b, keeping b's runs")
            r.git("tag", "-f", "base", ma)
            r.base = ma
            for kept in (a, b):
                with self.subTest(kept="a's runs" if kept == a else "b's runs"):
                    tip = r.git("commit-tree", kept + "^{tree}", "-p", b, "-p", a, "-m", "b merges a")
                    self.assertEqual(sorted(r.git("merge-base", "--all", ma, tip).split()), sorted((a, b)))
                    self.assertEqual(r.ledger(tip=tip), runs_changed(anchor, builds=("plain",), which=("control",)))

    def test_a_merge_base_no_check_judged_is_read_where_it_entered_main(self):
        """A merge base of main and the tip can be a proof-branch commit no check ever judged, since main checked
        only the merge that brought it in.  The reference is the commit of main's first-parent line where it entered.
        The cross-model review's case: branch P prunes the record at p, restores it at q, and main merges q; branch T,
        cut at p, pushes a commit that touches no finding, still holding p's prune.  The final gate's case: branch P
        pins runner 2 at p and runner 1 again at q, and main merges q; branch Q, cut at p, pins runner 1 and prunes."""
        for case in ("unchecked runs", "unchecked runner"):
            with self.subTest(case), repo(findings=False) as r:
                r.add_findings()
                set_runner(r, "1")
                anchor = r.commit("main: the record, run in runner 1")
                r.git("checkout", "-q", "-b", "p")
                if case == "unchecked runs":
                    prune_keeping_input(r)
                    p = r.commit("p: pruned, on runner 1")
                    r.add_findings()
                    r.commit("q: the record restored")
                else:
                    set_runner(r, "2")
                    p = r.commit("p: runner 2")
                    set_runner(r, "1")
                    r.commit("q: runner 1 again")
                r.git("checkout", "-q", "main")
                r.git("merge", "-q", "--no-ff", "--no-edit", "p")
                r.git("tag", "-f", "base")
                r.base = r.git("rev-parse", "HEAD")
                r.git("checkout", "-q", "-b", "t", p)
                if case == "unchecked runs":
                    r.write("notes.txt", "a commit that touches no finding\n")
                else:
                    set_runner(r, "1")
                    prune_keeping_input(r)
                tip = r.commit("the branch's push")
                self.assertEqual(r.git("merge-base", "--all", r.base, tip), p, "the merge base is p, which no check judged")
                self.assertEqual(r.ledger(), runs_changed(anchor))

    def test_a_runner_change_frees_no_run_of_a_record_anchored_on_the_branch(self):
        """The record's anchor is in BASE..TIP, a push no check ran, so its runs are not known to be what any runner
        gave on its pins: a new runner image frees none of them."""
        with repo(findings=False) as r:
            set_runner(r, "1")
            retag_base(r, "base: runner 1, no findings")
            r.add_findings()
            anchor = r.commit("the finding, with its runs")
            set_runner(r, "2")
            prune_keeping_input(r)
            r.commit("runner 2, and pruned")
            self.assertEqual(r.ledger(), runs_changed(anchor))

    def test_a_fixed_pin_in_the_anchor_commit_itself_prunes_nothing(self):
        """The adversarial gate's P1 and P2: the anchor commit records the runs and also pins asan and asan-ubsan to
        the fixed binaries (P2: the record was a draft with no runs before it).  A later commit prunes the finding
        with the runs `--record` prints on those pins, the control's.  P2 again with the anchor commit also pinning
        another runner image, and the later commit restoring the base's."""
        for name in ("P1", "P2", "P2 with a runner edit"):
            with self.subTest(name), repo(findings=False) as r:
                set_runner(r, "1")
                retag_base(r, "base: runner 1, no findings")
                r.add_findings()
                if name != "P1":
                    r.edit(YAML, lambda y: (y.pop("input"), y.pop("control")))
                    r.commit("W: the finding, with no runs yet")
                    r.add_findings()
                pin_fixed(r)
                if name == "P2 with a runner edit":
                    set_runner(r, "2")
                anchor = r.commit("X: the runs, and the fixed binaries pinned")
                set_runner(r, "1")
                prune_keeping_input(r)
                r.commit("Z: pruned with the runs --record prints on the fixed binaries")
                self.assertEqual(r.ledger(), runs_changed(anchor))

    def test_a_statement_added_later_frees_no_run(self):
        """The adversarial gate's N4: after the anchor, the statements gain ubsan_agrees, ubsan is pinned to the
        fixed binary, and the finding is pruned.  The anchor's runs of asan and asan-ubsan still hold."""
        with repo(findings=False) as r:
            r.add_findings()
            anchor = r.commit("the finding, with its runs")
            pin_fixed(r, builds=("ubsan",))
            r.edit(YAML, lambda y: (y["statements"].append("ubsan_agrees"),
                                    y["input"].update(ubsan=dict(y["control"]["plain"])),
                                    y["control"].update(ubsan=dict(y["control"]["plain"]))))
            prune_keeping_input(r)
            r.commit("ubsan_agrees, ubsan pinned to its fixed binary, and pruned")
            self.assertEqual(r.ledger(), runs_changed(anchor))

    def test_a_pin_added_after_the_anchor_must_reproduce_its_runs(self):
        """The adversarial gate's M2lin, M5 and M6: the anchor commit pins no asan or asan-ubsan binary (M2lin), or
        has no unpatched.yaml (M5).  A later commit pins those builds to the fixed binaries and prunes the finding
        with its input.bin kept (M2lin, M5), or only rewrites the stdout of their runs (M6).  No binary checked the
        anchor's runs of those builds, so they are frozen, and each case is refused."""
        def m6(r):
            pin_fixed(r)
            r.edit(YAML, lambda y: [y["input"][b].update(stdout_sha256=c * 64) for b, c in (("asan", "a"),
                                                                                             ("asan-ubsan", "b"))])
        for name, at_anchor, later in (("M2lin", drop_pins, lambda r: (pin_fixed(r), prune_keeping_input(r))),
                                       ("M5", lambda r: r.remove(UNPATCHED),
                                        lambda r: (pin_fixed(r), prune_keeping_input(r))),
                                       ("M6", drop_pins, m6)):
            with self.subTest(name), repo(findings=False) as r:
                r.add_findings()
                at_anchor(r)
                anchor = r.commit("the finding, with its runs, its asan builds not pinned yet")
                later(r)
                r.commit("its asan builds pinned to the fixed binaries")
                self.assertEqual(r.ledger(), runs_changed(anchor))

    def test_a_pin_added_by_a_merge_must_reproduce_the_anchor_s_runs(self):
        """The adversarial gate's M2: the proof branch anchors the record with no asan pins; a branch from main pins
        them to the fixed binaries, and its merge keeps those pins and prunes the finding."""
        with repo(findings=False) as r:
            r.git("checkout", "-q", "-b", "proofs/zlib")
            r.add_findings()
            drop_pins(r)
            anchor = r.commit("the finding, with its runs, its asan builds not pinned yet")
            r.git("checkout", "-q", "-b", "pins", "base")
            pin_fixed(r)
            r.commit("the pins, its asan builds the fixed binaries")
            r.git("checkout", "-q", "proofs/zlib")
            r.git("merge", "-q", "--no-edit", "pins", check=False)
            r.git("checkout", "pins", "--", UNPATCHED)
            prune_keeping_input(r)
            r.commit("merged, with its pins, and pruned")
            self.assertEqual(r.ledger(), runs_changed(anchor))

    def test_runs_that_oft_check_record_prints_on_fixed_binaries_pinned_later_are_refused(self):
        """The adversarial gate's M8, which writes no run by hand: X has the finding with its runs and no
        unpatched.yaml; Y pins the fixed binaries, drops the runs and prunes; Z commits the runs `oft check --record`
        prints on Y, where the input aborts nothing, so its runs are those of the control."""
        with repo(findings=False) as r:
            r.add_findings()
            r.remove(UNPATCHED)
            anchor = r.commit("X: the finding, with its runs, and no unpatched.yaml")
            pin_fixed(r)
            recorded = yamlio.load_file(r.path(YAML))
            r.edit(YAML, lambda y: (y.pop("input"), y.pop("control"), y.update(state="pruned")))
            r.write("findings/zlib/checksum_fuzzer/series", "")
            r.commit("Y: the fixed binaries pinned, the runs dropped, pruned")
            r.edit(YAML, lambda y: y.update(input=recorded["control"], control=recorded["control"]))
            r.commit("Z: the runs --record printed")
            self.assertEqual(r.ledger(), runs_changed(anchor))

    def test_a_pin_added_after_the_anchor_that_reproduces_its_runs_is_clean(self):
        """The adversarial gate's M5-legit: the record anchored with no unpatched.yaml, which a later commit adds with
        the unpatched binaries, the runs kept.  Those pins are then frozen in turn."""
        with repo(findings=False) as r:
            r.add_findings()
            r.remove(UNPATCHED)
            r.commit("the finding, with its runs, and no unpatched.yaml")
            r.add_findings()
            pinned = r.commit("unpatched.yaml, the unpatched binaries")
            self.assertEqual(r.ledger(), [])
            pin_fixed(r)
            r.commit("repinned")
            self.assertEqual(r.ledger(), repinned(pinned))

    def test_what_a_record_says_of_its_runs_may_change(self):
        """State, summary, upstream, recorded runs and the archive's pin: CI re-runs the record against fixed
        inputs and binaries, so these may change, as may the pins of a harness with no finding."""
        def rearchive(y):
            y["asset"]["sha256"] = "5" * 64
            y["harnesses"]["other_fuzzer"] = {"plain": {"file": "other_fuzzer.plain", "bytes": 1, "sha256": "6" * 64}}
        with repo() as r:
            r.edit(YAML, lambda y: y.update(state="reported", upstream="https://bugs.example.org/1",
                                            summary="A stand-in finding, reported."))
            r.edit(UNPATCHED, rearchive)
            r.commit("reported")
            r.edit(UNPATCHED, lambda y: y["harnesses"]["other_fuzzer"]["plain"].update(sha256="7" * 64))
            r.commit("another harness repinned")
            self.assertEqual(r.ledger(), [])

    def test_a_history_that_only_adds_records_is_clean(self):
        with repo(findings=False) as r:
            r.add_findings()
            r.commit("a finding")
            r.add_record(SECOND)
            r.commit("another")
            self.assertEqual(r.ledger(), [])


class Anchors(unittest.TestCase):
    """The anchors of a record are found by ancestry: two branches that each record the slug have two, and two that
    differ are refused whichever way the branches merge."""

    def assert_two_anchors(self, found, a, b, what):
        self.assertEqual(len(found), 1, found)
        prefix = "paths %s: a finding is first recorded once: %s was first recorded by " % (DIR, DIR)
        self.assertTrue(found[0].startswith(prefix), found[0])
        self.assertIn(found[0][len(prefix):], ["%s and by %s, which differ in its %s" % (x[:10], y[:10], what)
                                               for x, y in ((a, b), (b, a))])

    def test_the_gate_s_porcelain_merge_in_all_four_parent_orders(self):
        """A branch from main records the slug with the control copied over the input and the finding pruned, and
        merges the proof branch: by `git merge -s ours` either way round, and by a merge whose tree is its second
        parent's either way round."""
        with repo(findings=False) as r:
            r.git("checkout", "-q", "-b", "proofs/zlib")
            r.add_findings()
            proof = r.commit("the finding")
            r.git("checkout", "-q", "-b", "side", "base")
            r.add_findings()
            prune_onto_control(r)
            side = r.commit("the same slug, pruned onto its control")
            for first, second in ((side, proof), (proof, side)):
                with self.subTest(first=first == proof and "proof" or "side", tree="first parent's"):
                    r.git("checkout", "-q", "--detach", first)
                    r.git("merge", "-q", "--no-edit", "-s", "ours", second)
                    self.assert_two_anchors(r.ledger(), proof, side, "input.bin and recorded runs")
                with self.subTest(first=first == proof and "proof" or "side", tree="second parent's"):
                    merge = r.git("commit-tree", second + "^{tree}", "-p", first, "-p", second, "-m", "merge")
                    self.assert_two_anchors(r.ledger(tip=merge), proof, side, "input.bin and recorded runs")

    def test_an_add_add_conflict_resolved_either_way(self):
        """A lane from main records the slug with a re-minimized input and merges the proof branch; git reports an
        add/add conflict on input.bin."""
        for side in ("--ours", "--theirs"):
            with self.subTest(side=side), repo(findings=False) as r:
                r.git("checkout", "-q", "-b", "proofs/zlib")
                r.add_findings()
                proof = r.commit("the finding")
                r.git("checkout", "-q", "-b", "lane", "base")
                r.add_findings()
                r.write(DIR + "/input.bin", b"\0\0\0\0\0\0\nasan: abort\nasan-ubsan: abort\nminimized\n")
                lane = r.commit("the same slug, re-minimized")
                r.git("merge", "-q", "--no-edit", "proofs/zlib", check=False)
                self.assertIn("input.bin", r.git("diff", "--name-only", "--diff-filter=U"))
                r.git("checkout", side, "--", DIR + "/input.bin")
                r.commit("merged")
                self.assert_two_anchors(r.ledger(), proof, lane, "input.bin")

    def test_a_merge_with_s_ours_that_keeps_the_original_is_clean(self):
        """A branch from the proof branch rewrites the input; one anchor, so a merge that keeps the original is clean
        and one that keeps the rewrite is refused."""
        with repo() as r:
            r.git("checkout", "-q", "-b", "side")
            prune_onto_control(r)
            r.commit("rewritten")
            r.git("checkout", "-q", "main")
            r.commit("main moves on")
            r.git("merge", "-q", "--no-edit", "-s", "ours", "side")
            self.assertEqual(r.ledger(), [])
            r.git("checkout", "-q", "side")
            r.git("merge", "-q", "--no-edit", "-s", "ours", "main")
            self.assertEqual(r.ledger(), onto_control(r.base))

    def test_two_anchors_that_differ_in_runs_are_refused(self):
        """Two branches from main each record the slug, one with the input's asan runs those of the control: either
        tree kept is refused, whether or not either anchor pinned the builds."""
        for pinned in (False, True):
            with self.subTest(pinned=pinned), repo(findings=False) as r:
                r.git("checkout", "-q", "-b", "proofs/zlib")
                r.add_findings()
                drop_pins(r)
                proof = r.commit("the finding")
                r.git("checkout", "-q", "-b", "side", "base")
                r.add_findings()
                if not pinned:
                    drop_pins(r)
                r.edit(YAML, lambda y: y["input"].update(asan=y["control"]["asan"], **{
                    "asan-ubsan": y["control"]["asan-ubsan"]}))
                side = r.commit("the same slug, other runs of its asan builds")
                merge = r.git("commit-tree", side + "^{tree}", "-p", proof, "-p", side, "-m", "merge")
                self.assert_two_anchors(r.ledger(tip=merge), proof, side, "recorded runs")


class Errors(unittest.TestCase):
    def test_a_shallow_clone_or_an_unknown_commit_is_an_error(self):
        with repo() as r:
            r.commit("one more")
            shallow = os.path.join(r._tmp.name, "shallow")
            subprocess.run(GIT + ["clone", "-q", "--depth=1", "file://" + r.root, shallow], env=GIT_ENV, check=True)
            with self.assertRaisesRegex(ledger.LedgerError, "a shallow clone"):
                ledger.run(shallow, "HEAD")
            with self.assertRaisesRegex(ledger.LedgerError, "not a commit: nosuch"):
                ledger.run(r.root, "nosuch")

    def test_the_command(self):
        tools = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

        def oft(r, *args):
            return subprocess.run([sys.executable, "-B", "-m", "oft", "--root", r.root, "ledger"] + list(args),
                                  cwd=tools, env=dict(GIT_ENV, PYTHONPATH=tools), capture_output=True, text=True)
        with repo() as r:
            ok = oft(r, "--base", "base")
            self.assertEqual((ok.returncode, ok.stdout), (0, "oft ledger: 0 finding(s)\n"))
            r.remove(DIR)
            r.commit("the record goes")
            bad = oft(r, "--base", "base")
            self.assertEqual((bad.returncode, bad.stdout), (1, "\n".join(deleted(KEY, r.base))
                                                            + "\noft ledger: 4 finding(s)\n"))
            self.assertEqual(oft(r, "--base", "base", "--tip", "base").returncode, 0)
            err = oft(r, "--base", "nosuch")
            self.assertEqual((err.returncode, err.stdout), (1, "FAIL not a commit: nosuch\n"))


if __name__ == "__main__":
    unittest.main()
