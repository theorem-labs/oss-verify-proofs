"""keys.py and plan.py: a part's key changes exactly when what its check reads changes, and a plan checks a part only
when, judged against a base, its key differs from the base's, and when its key has no recorded pass."""
import hashlib
import io
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

from oft import check, facts, generate, keys, layout, names, pack, paths, plan, port, rules, unitpaths, yamlio
from oft.tests.helpers import NEW_NAMESPACE, NEW_OPAM_STEM, REPO, add_findings, rename_namespace, tree
from oft.tests.test_fetch_check import HAVE_ZSTD, make_release, withdraw_every_statement, withhold_checksum_fuzzer
from oft.tests.test_layout import old_layout_tree

GIT = ["git", "-c", "user.name=oft-tests", "-c", "user.email=oft-tests" + "@" + "example.invalid",
       "-c", "commit.gpgsign=false"]
GIT_ENV = dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")
TOOLS = os.path.dirname(os.path.dirname(os.path.abspath(keys.__file__)))
UNIT = "zlib/checksum_fuzzer"
CX_UNIT = "json/fuzzer-parse_bjdata"


def git(t, *args):
    r = subprocess.run(GIT + ["-C", t.root, *args], env=GIT_ENV, capture_output=True, text=True)
    if r.returncode != 0:
        raise AssertionError("git %s: %s" % (" ".join(args), r.stderr))
    return r.stdout.strip()


def commit(t):
    git(t, "add", "-A")
    git(t, "commit", "-q", "--allow-empty", "-m", "x")
    return git(t, "rev-parse", "HEAD")


def repo(t):
    """t as a git repository with a checker (tools/oft/check.py) and a file no check opens (tools/oft/lint.py), a
    counterexample and a finding; its first commit."""
    add_findings(t)
    t.write("tools/oft/check.py", "check\n")
    t.write("tools/oft/lint.py", "lint\n")
    # the shared actions pr.yml's base step requires on the base before a workflow uses them
    t.write(".github/actions/plan-drafts/action.yml", "name: plan-drafts\nruns:\n  using: composite\n  steps: []\n")
    t.write(".github/actions/place-drafts/action.yml", "name: place-drafts\nruns:\n  using: composite\n  steps: []\n")
    t.write(".gitattributes", "* text=auto eol=lf\n")
    git(t, "init", "-q")
    return commit(t)


def all_keys(t, facts_commit, change=None, tools=None):
    """{(unit, part): key} of every part the tree at t has to check."""
    change = change or facts_commit
    got = keys.keys(t.root, keys.wanted(facts.load(t.root)), facts_commit, change, tools or change)
    return {up: k for up, (k, _c) in got.items()}


def all_comps(t, facts_commit, change=None, tools=None):
    """{(unit, part): {component: id}} of every part the tree at t has to check."""
    change = change or facts_commit
    got = keys.keys(t.root, keys.wanted(facts.load(t.root)), facts_commit, change, tools or change)
    return {up: c for up, (_k, c) in got.items()}


def changed(a, b):
    return sorted(up for up in a if a[up] != b.get(up))


def tree_digest(t, rev):
    """The tree a deferred check's pin names (tools/oft/migration-pin.yaml): the SHA-256 of `git ls-tree -r REV`
    without the line of that file."""
    r = subprocess.run(GIT + ["-C", t.root, "ls-tree", "-r", rev], env=GIT_ENV, capture_output=True, check=True)
    lines = r.stdout.decode().splitlines(True)
    return hashlib.sha256("".join(l for l in lines if not l.endswith("\ttools/oft/migration-pin.yaml\n")).encode()
                          ).hexdigest()


def deferred_pin(tree_sha, check="deferred"):
    """A migration pin that defers the check of the tree tree_sha to a check of record, as the re-pin writes it."""
    return yamlio.dump({"schema": "oss-fuzz-theorems/migration-pin/1", "digest": "", "tree": tree_sha,
                        "check": check, "check_of_record": "a VM run of every part at the merge commit",
                        "pull_request": "release/join"})


def parts_of(all_of, parts, under=""):
    """[(unit, part)] of all_of with a part in parts, of a unit whose name starts with under."""
    return sorted(up for up in all_of if up[1] in parts and up[0].startswith(under))


def dune_case(test, t, before, rel, want):
    """Write a dune file at rel (a comment added to one that is there), commit, and check that the keys that moved
    against `before` are want; then put the tree back as it was and check that no key moved.  Every case is
    measured against the one baseline, so a regression in one does not cascade into the cases after it."""
    had = t.read(rel) if os.path.exists(t.path(rel)) else None
    try:
        t.write(rel, (had + "; a comment\n") if had is not None else "(dirs :standard)\n")
        git(t, "add", "-f", rel)
        test.assertEqual(changed(before, all_keys(t, commit(t))), want)
    finally:
        if had is None:
            os.remove(t.path(rel))
        else:
            t.write(rel, had)
        back = commit(t)
    test.assertEqual(changed(before, all_keys(t, back)), [])


# the attributes the repository's .gitattributes gives every file and a counterexample's inputs, in both layouts
LAYOUT_ATTRIBUTES = ("* text=auto eol=lf\ncounterexamples/**/*.bin binary\n"
                     "projects/*/*/counterexamples/**/*.bin binary\n")


def old_layout_repo(t):
    """t as test_layout.old_layout_tree lays it out (a proof with a proof library and a build record, a fuzz target
    with only a build record, a counterexample and a finding, all in the old layout) with a project's patch, rendered,
    with a checker and the repository's checkout attributes, as a git repository; its first commit."""
    old_layout_tree(t)
    t.write("patches/zlib/0001-stand-in.patch", "a stand-in patch\n")
    assert t.generate() == 0, t.last_output
    t.write("tools/oft/check.py", "check\n")
    t.write("tools/oft/lint.py", "lint\n")
    t.write(".gitattributes", LAYOUT_ATTRIBUTES)
    git(t, "init", "-q")
    return commit(t)


def port_layout(t):
    """`oft port-layout` and `oft generate` on t's working tree, committed: the new commit."""
    assert port.port_worktree(t.root, out=io.StringIO()) == 0
    assert t.generate() == 0, t.last_output
    return commit(t)

class Keys(unittest.TestCase):
    def test_the_fixture_has_every_part(self):
        with tree() as t:
            repo(t)
            wanted = set(keys.wanted(facts.load(t.root)))
            self.assertLessEqual({(UNIT, "build"), (UNIT, "findings"), (CX_UNIT, "counterexamples")}, wanted)

    def test_the_shared_generated_files_are_in_no_key(self):
        """The rule for the shared generated files rests on this: a commit that renders only them re-keys
        nothing, so the line's render after a merge voids no check."""
        with tree() as t:
            c1 = repo(t)
            edited = [rel for rel in generate.existing_generated(t.root) if paths.is_shared(rel)]
            self.assertTrue(all(any(paths.match(p, r) is not None for r in edited) for p in paths.SHARED))
            for rel in edited:
                t.write(rel, "stale\n")
            c2 = commit(t)
            self.assertEqual(changed(all_keys(t, c1), all_keys(t, c2, tools=c1)), [])

    def test_a_change_to_the_render_script_changes_no_key(self):
        """keys.NOT_THE_CHECKER names ci/regenerate-shared.sh: no check opens it, and the line's render after a
        merge must not re-key every unit."""
        with tree() as t:
            first = repo(t)
            t.write("tools/oft/ci/regenerate-shared.sh", "#!/bin/bash\necho changed\n")
            second = commit(t)
            self.assertEqual(changed(all_keys(t, first), all_keys(t, second)), [])

    def test_a_change_to_a_file_no_check_opens_changes_no_key(self):
        with tree() as t:
            first = repo(t)
            t.write("tools/oft/lint.py", "lint, changed\n")
            t.write("docs/x.md", "docs\n")
            t.write(".github/workflows/pr.yml", "on: push\n")
            # the images are keyed by the digests release.yaml pins, not by the files they are built from
            t.write("toolchain/runner.Dockerfile", "FROM scratch\n")
            t.write("toolchain/toolchain.lock", "checker: x\n")
            second = commit(t)
            self.assertEqual(changed(all_keys(t, first), all_keys(t, second)), [])

    def test_a_change_to_the_planner_changes_no_key(self):
        """plan.py holds images_differ, which pr.yml's reach step runs, because keys.NOT_THE_CHECKER names it: a
        change to it re-checks no fuzz target."""
        self.assertTrue(keys.not_the_checker("tools/oft/plan.py"))
        with tree() as t:
            t.write("tools/oft/plan.py", "plan\n")
            first = repo(t)
            t.write("tools/oft/plan.py", "plan, changed\n")
            second = commit(t)
            self.assertEqual(changed(all_keys(t, first), all_keys(t, second)), [])

    def test_the_packer_and_its_table_change_no_key(self):
        """pack.py and proof-times.tsv are the planner's: keys.NOT_THE_CHECKER names them, so adding or changing them
        re-checks no fuzz target."""
        for name in ("pack.py", "proof-times.tsv"):
            self.assertTrue(keys.not_the_checker("tools/oft/" + name), name)
        with tree() as t:
            first = repo(t)
            t.write("tools/oft/pack.py", "pack\n")
            t.write("tools/oft/proof-times.tsv", "unit\tminutes\tpeak_gib\tcpus\n")
            second = commit(t)
            before = all_keys(t, first)
            self.assertEqual(changed(before, all_keys(t, second)), [])
            t.write("tools/oft/pack.py", "pack, changed\n")
            t.write("tools/oft/proof-times.tsv", "unit\tminutes\tpeak_gib\tcpus\n%s\t1\t1.0\t8\n" % UNIT)
            third = commit(t)
            self.assertEqual(changed(before, all_keys(t, third)), [])

    def test_the_shipped_text_search_and_the_migration_pin_change_no_key(self):
        """disclosure.py is the release cut's and the lint's, since only lint.py and release_tree.py import it and
        both are named too, and migration-pin.yaml is read by pr.yml's plan step alone: keys.NOT_THE_CHECKER names
        them, so setting the pin or changing the search re-checks no fuzz target."""
        for name in ("disclosure.py", "migration-pin.yaml"):
            self.assertTrue(keys.not_the_checker("tools/oft/" + name), name)
        with tree() as t:
            t.write("tools/oft/disclosure.py", "disclosure\n")
            t.write("tools/oft/migration-pin.yaml", "digest: ''\n")
            first = repo(t)
            t.write("tools/oft/disclosure.py", "disclosure, changed\n")
            t.write("tools/oft/migration-pin.yaml", "digest: '%s'\n" % ("a" * 64))
            second = commit(t)
            self.assertEqual(changed(all_keys(t, first), all_keys(t, second)), [])

    def test_the_enrollment_scripts_change_no_key(self):
        """tools/enroll/ is the enrollment pipeline enroll.yml and enroll-build.yml run, and `oft release-tree`
        removes it from a release: keys.NOT_THE_CHECKER names the directory, so adding a file to it or changing
        one re-checks no fuzz target."""
        self.assertTrue(keys.not_the_checker("tools/enroll/build"))
        with tree() as t:
            first = repo(t)
            t.write("tools/enroll/build", "build\n")
            t.write("tools/enroll/tests/test_build.py", "import unittest\n")
            second = commit(t)
            before = all_keys(t, first)
            self.assertEqual(changed(before, all_keys(t, second)), [])
            t.write("tools/enroll/build", "build, changed\n")
            third = commit(t)
            self.assertEqual(changed(before, all_keys(t, third)), [])

    def test_a_change_to_port_layout_changes_no_key(self):
        """port.py and ci/port-check.sh move a tree to the per-project layout and check the moved tree; no check opens
        them (Checker says so), so a change to them re-checks no fuzz target."""
        ported = ("tools/oft/port.py", "tools/oft/ci/port-check.sh")
        with tree() as t:
            for rel in ported:
                t.write(rel, "port\n")
            first = repo(t)
            for rel in ported:
                t.write(rel, "port, changed\n")
            self.assertEqual(changed(all_keys(t, first), all_keys(t, commit(t))), [])

    def test_the_version_names_the_formula_of_the_key(self):
        """Each raise of it changed what a key reads or how it is computed, so that no key of an earlier formula
        equals one of this one: 2 for the first step of the layout move (a component is the entries of a folder and
        the attributes of its files by their paths in it), 3 for the dune files of the build path (the lead's ruling
        of 2026-10-30)."""
        with tree() as t:
            head = repo(t)
            got = keys.keys(t.root, keys.wanted(facts.load(t.root)), head, head, head)
            self.assertEqual({c["version"] for _k, c in got.values()}, {"3"})

    def test_a_component_reads_only_a_path_its_commit_s_listing_covers(self):
        """Attributes lists some paths of a commit once and serves every component from that listing: a path
        outside it raises instead of reading as "-", which would give a tree that holds the file the key of one
        that does not."""
        with tree() as t:
            head = repo(t)
            at = keys.Attributes(t.root, head, ("projects",))
            self.assertNotEqual(at.id("projects/%s" % UNIT), "-")
            with self.assertRaisesRegex(ValueError, "^theories: no path of the listing"):
                at.id("theories")

    def test_a_test_repository_runs_no_background_git(self):
        """git's automatic maintenance after a commit could write into .git/objects while tree() deletes it."""
        with tree() as t:
            repo(t)
            for key, value in (("maintenance.auto", "false"), ("gc.auto", "0")):
                with self.subTest(key=key):
                    self.assertEqual(git(t, "config", "--get", key), value)

    def test_a_change_to_the_checker_changes_every_key(self):
        """The checker is every file of tools/ a check job puts on PYTHONPATH, with its checkout attributes."""
        changes = {"tools/oft/check.py": ("tools/oft/check.py", "check, changed\n"),
                   "a module beside oft/": ("tools/sitecustomize.py", "import os\n"),
                   "an attribute of a checker file": (".gitattributes",
                                                      "* text=auto eol=lf\ntools/oft/check.py -text\n"),
                   # oft check renders a statement folder's dune file and a proof library's with these templates
                   "the statement dune template": ("tools/oft/templates/harness-dune.tmpl", "@@ file\n"),
                   "the proof dune template": ("tools/oft/templates/proof-dune.tmpl", "@@ file\n")}
        for name, (path, text) in changes.items():
            with self.subTest(change=name), tree() as t:
                first = repo(t)
                t.write(path, text)
                second = commit(t)
                before, after = all_keys(t, first), all_keys(t, second)
                self.assertEqual(changed(before, after), sorted(before))

    def test_a_proof_changes_the_build_of_its_unit_alone(self):
        with tree() as t:
            first = repo(t)
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem x : True. Proof. exact I. Qed.\n")
            second = commit(t)
            self.assertEqual(changed(all_keys(t, first), all_keys(t, second)), [(UNIT, "build")])

    def test_a_file_under_proofs_lib_changes_no_key(self):
        """proofs/lib/ has no place in either layout (no row admits a file there, and oft port-layout refuses one),
        and no build reads it: no proof's dune file names a theory there."""
        with tree() as t:
            first = repo(t)
            t.write("proofs/lib/Common.v", "Definition zero := 0.\n")
            self.assertEqual(changed(all_keys(t, first), all_keys(t, commit(t))), [])

    def test_dune_project_changes_the_builds_whose_bytes_of_it_change(self):
        """dune-project is the one file of a build path that dune_path_files leaves out: dune_project keys every
        byte of it a build reads, so a comment or another project's stanzas re-check no build, a project's own
        stanza re-checks that project's builds, and a form every build reads re-checks them all."""
        with tree() as t:
            first = repo(t)
            before, before_comps = all_keys(t, first), all_comps(t, first)
            builds = sorted(up for up in before if up[1] == "build")
            text = t.read("dune-project")
            t.write("dune-project", text + '\n(package\n (name rocq-oss-fuzz-theorems-newproj)\n'
                                           ' (synopsis "Theorem statements about newproj (a project)")\n'
                                           ' (depends rocq-oss-fuzz-theorems-core))\n; a comment with a ( in it\n')
            self.assertEqual(changed(before, all_keys(t, commit(t))), [])
            t.write("dune-project", text + "; a comment, and nothing else, changed\n")
            self.assertEqual(changed(before, all_keys(t, commit(t))), [])
            self.assertIn("(name rocq-oss-fuzz-theorems-zlib)", text)
            t.write("dune-project", text.replace("(name rocq-oss-fuzz-theorems-zlib)",
                                                 "(name rocq-oss-fuzz-theorems-zlib)\n (tags (zlib))"))
            now = commit(t)
            zlib_builds = parts_of(builds, ("build",), "zlib/")
            self.assertEqual(changed(before, all_keys(t, now)), zlib_builds)
            zlib = all_comps(t, now)
            self.assertEqual(sorted(up for up in before_comps
                                    if before_comps[up].get("dune-project") != zlib[up].get("dune-project")),
                             zlib_builds)
            t.write("dune-project", text.replace("(using rocq", "(using  rocq", 1))
            self.assertEqual(changed(before, all_keys(t, commit(t))), builds)

    def test_dune_project_ids_follow_the_opam_stem(self):
        """In a tree whose release.yaml names another opam stem, a build reads the stanzas of the packages that stem
        names: each is found, and a change to the project's own stanza re-keys that project's builds alone."""
        with tree(render=False) as t:
            rename_namespace(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            first = repo(t)
            self.assertEqual(keys.release_names(t.root, first), (NEW_NAMESPACE, NEW_OPAM_STEM))
            _shared, package, _ordered = unitpaths.dune_project_forms(unitpaths.forms(t.read("dune-project")), "zlib",
                                                                      NEW_OPAM_STEM)
            self.assertEqual(sorted(package), sorted(unitpaths.dune_packages("zlib", NEW_OPAM_STEM)))
            self.assertIn("rocq-oss-verify-zlib", package)
            before = all_keys(t, first)
            builds = sorted(up for up in before if up[1] == "build")
            text = t.read("dune-project")
            t.write("dune-project", text.replace("(name rocq-oss-verify-zlib)", "(name rocq-oss-verify-zlib)\n (tags (z))"))
            self.assertEqual(changed(before, all_keys(t, commit(t))), parts_of(builds, ("build",), "zlib/"))

    def test_a_dune_file_of_an_old_layout_build_path_changes_the_builds_under_it(self):
        """In the old layout a unit's build path is the repository root, projects/, projects/<p>/, its statement
        folder, proofs/, proofs/<p>/, its proofs folder, and the counterexamples and findings folders the new
        layout would put in the statement folder.  `dune build` of the statements and the proofs reads the files of
        that path, and no key held them before the lead's ruling of 2026-10-30: a dune file in any of them, under
        any of the names dune reads, now changes the build keys under it.  A dune file inside a unit's
        counterexamples or findings folder is in that folder's id as well, so it changes that part's key too, as
        any other file of the folder does; the barrier name, dune, is the one the folder's id drops.  The folders
        above the old layout's counterexamples and findings folders are on no build path, and a dune file there
        changes no key at all."""
        with tree() as t:
            first = repo(t)
            before = all_keys(t, first)
            self.assertTrue(len({up[0].split("/")[0] for up in before if up[1] == "build"}) > 1, sorted(before))
            for rel, parts, under in (("dune", ("build",), ""), ("dune-workspace", ("build",), ""),
                                      ("proofs/dune", ("build",), ""), ("proofs/dune-file", ("build",), ""),
                                      ("proofs/zlib/dune", ("build",), "zlib/"),
                                      ("proofs/zlib/dune-workspace", ("build",), "zlib/"),
                                      ("proofs/%s/dune" % UNIT, ("build",), UNIT),
                                      ("counterexamples/%s/dune" % CX_UNIT, ("build", "counterexamples"), CX_UNIT),
                                      ("findings/%s/dune-workspace" % UNIT, ("build", "findings"), UNIT),
                                      ("counterexamples/dune-workspace", (), ""),
                                      ("counterexamples/json/dune-file", (), ""),
                                      ("findings/dune", (), "")):
                with self.subTest(rel=rel):
                    dune_case(self, t, before, rel, parts_of(before, parts, under))

    def test_a_hand_written_dune_file_that_could_shadow_a_theory_gives_no_key(self):
        """A dune file oft generate does not write, wherever lint admits one, could declare a theory a build finds
        before the installed one, or bring in what this reader cannot see.  So could one under projects/<p>/bin/,
        which lint never reads (paths.IGNORED_PATTERNS) and a pattern of two name segments would take for a
        harness's generated dune file: it is refused once it is tracked."""
        paths = ("tests/shadow/dune", "docs/dune", "counterexamples/dune", "projects/%s/source/dune" % UNIT,
                 "proofs/%s/plain_halts/classifier/dune" % UNIT, "proofs/%s/provenance/recipe/dune" % UNIT,
                 "proofs/%s/provenance/LICENSES/dune" % UNIT, "projects/zlib/bin/dune",
                 "projects/zlib/bin/images/dune")
        texts = {"a shadow of the model": "(rocq.theory (name LinuxProcessSemantics))\n",
                 "a shadow of the core": "(coq.theory (name OssFuzzTheorems.Core))\n",
                 "a theory with no name": "(rocq.theory (theories Stdlib))\n",
                 "an include": "(include ../shadow.inc)\n",
                 "a subdir": "(subdir s (rocq.theory (name LinuxProcessSemantics)))\n",
                 "a library": "(library (name zarith))\n",
                 "the tests' name in a line comment": "(rocq.theory ; (name OssFuzzTheorems.Tests)\n"
                                                      " (name LinuxProcessSemantics))\n",
                 # '#|' is not a comment to dune: its atoms around a stanza hide nothing
                 "a theory between '#|' and '|#' atoms": "(rule (alias hide) (action (echo #|)))\n"
                                                         "(rocq.theory (name LinuxProcessSemantics))\n"
                                                         "(rule (alias hide2) (action (echo |#)))\n",
                 # a block string runs to the end of its line, so the stanza after it is live
                 "a theory after a block string": '(rule (alias hide) (action (echo "\\| x\n)))\n'
                                                  "(rocq.theory (name LinuxProcessSemantics))\n"
                                                  '; ")))\n',
                 "the tests' name in a string": '(rocq.theory (synopsis "(name OssFuzzTheorems.Tests)")'
                                                ' (name LinuxProcessSemantics))\n',
                 "two names": "(rocq.theory (name OssFuzzTheorems.Tests) (name LinuxProcessSemantics))\n"}
        for path in paths:
            for what, text in texts.items():
                with self.subTest(path=path, what=what), tree() as t:
                    repo(t)
                    t.write(path, text)
                    git(t, "add", "-f", path)
                    with self.assertRaisesRegex(keys.NoKey, "^%s: a hand-written dune file" % path):
                        all_keys(t, commit(t))

    def test_what_a_hand_written_dune_file_may_hold_changes_no_key(self):
        """The tests' own theory and rules, as tests/ has them: none of it reaches another build."""
        with tree() as t:
            first = repo(t)
            t.write("tests/dune", "(include_subdirs qualified)\n(data_only_dirs negative)\n"
                                  "(rocq.theory\n (name OssFuzzTheorems.Tests)\n (theories OssFuzzTheorems.Core))\n")
            t.write("tests/toy/dune", '(rule (targets x.v) (deps %{project_root}/docs/x.md) (action (copy %{deps} '
                                      '%{targets})))\n(alias (name toy))\n')
            t.write("tests/Model.v", "Definition x := 0.\n")
            self.assertEqual(changed(all_keys(t, first), all_keys(t, commit(t))), [])

    def test_hand_theory_follows_the_namespace(self):
        """tests/dune may declare the tests' theory in the namespace that release.yaml names at the commit it is read
        from, and no other: tests/ is no change's file, so a change's names do not reach it."""
        dune = "(include_subdirs qualified)\n(rocq.theory\n (name %s.Tests)\n (theories %s.Core))\n"
        with tree() as t:
            t.write("tests/dune", dune % (names.NAMESPACE_DEFAULT, names.NAMESPACE_DEFAULT))
            before = repo(t)
            keys.check_hand_dune(t.root, before)
            rename_namespace(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            renamed = commit(t)
            keys.check_hand_dune(t.root, before, renamed)   # tests/dune read at the facts commit, with its names
            with self.assertRaisesRegex(keys.NoKey, "^tests/dune: a hand-written dune file declares the theory "
                                                    "OssFuzzTheorems.Tests, .*; only OSSVerify.Tests may be declared"):
                keys.check_hand_dune(t.root, renamed)
            t.write("tests/dune", dune % (NEW_NAMESPACE, NEW_NAMESPACE))
            keys.check_hand_dune(t.root, commit(t))

    def test_theories_dune_holds_only_the_core_s_theory(self):
        """theories/ is in every build's key; a rule there could build the core from a file outside it."""
        with tree() as t:
            repo(t)
            t.write("theories/dune", "(rocq.theory (name OssFuzzTheorems.Core))\n"
                                     "(rule (targets X.v) (action (copy ../docs/x X.v)))\n")
            with self.assertRaisesRegex(keys.NoKey, "^theories/dune: a hand-written dune file with a rule stanza"):
                all_keys(t, commit(t))

    def test_a_counterexample_and_a_finding_change_their_own_part(self):
        with tree() as t:
            first = repo(t)
            cx = next(os.path.join(dp, f) for dp, _d, fs in os.walk(t.path("counterexamples", CX_UNIT))
                      for f in fs if f.endswith(".yaml"))
            with open(cx, "a") as f:
                f.write("# x\n")
            second = commit(t)
            self.assertEqual(changed(all_keys(t, first), all_keys(t, second)), [(CX_UNIT, "counterexamples")])
            t.write("findings/zlib/unpatched.yaml", t.read("findings/zlib/unpatched.yaml") + "# x\n")
            third = commit(t)
            self.assertEqual(changed(all_keys(t, second), all_keys(t, third)), [(UNIT, "findings")])

    def test_a_harness_yaml_changes_every_part_of_its_project_alone(self):
        """`oft fetch` unpacks a project's archive only when every harness's builds are in it."""
        with tree() as t:
            first = repo(t)
            t.write("projects/zlib/api-driver/harness.yaml", t.read("projects/zlib/api-driver/harness.yaml") + "#\n")
            second = commit(t)
            before = all_keys(t, first)
            self.assertEqual(changed(before, all_keys(t, second)),
                             sorted(up for up in before if up[0].startswith("zlib/")))

    def test_a_project_s_generated_files_change_no_key_and_its_facts_change_its_parts(self):
        """A proof re-renders projects/<p>/README.md; no check reads it or the .opam file."""
        with tree() as t:
            first = repo(t)
            for path in ("projects/zlib/README.md", "projects/zlib/rocq-oss-fuzz-theorems-zlib.opam"):
                t.write(path, (t.read(path) if os.path.exists(t.path(path)) else "") + "\nchanged\n")
            second = commit(t)
            self.assertEqual(changed(all_keys(t, first), all_keys(t, second)), [])
            t.write("projects/zlib/project.yaml", t.read("projects/zlib/project.yaml") + "# x\n")
            before = all_keys(t, second)
            self.assertEqual(changed(before, all_keys(t, commit(t))),
                             sorted(up for up in before if up[0].startswith("zlib/")))

    def test_theories_and_the_toolchain_change_every_build_and_nothing_else(self):
        for path, text in (("theories/Extra.v", "Definition x := 0.\n"),
                           ("toolchain/allowed-axioms.txt", "Corelib.Init.Something.prim\n")):
            with self.subTest(path=path), tree() as t:
                first = repo(t)
                t.write(path, text)
                second = commit(t)
                before = all_keys(t, first)
                self.assertEqual(changed(before, all_keys(t, second)),
                                 sorted(up for up in before if up[1] == "build"))

    def test_each_image_changes_the_parts_that_run_in_it(self):
        for image, parts in (("runner", ("counterexamples", "findings")), ("checker", ("build",))):
            with self.subTest(image=image), tree() as t:
                first = repo(t)
                r = t.yaml("release.yaml")
                r["images"][image] = r["images"][image].split("@")[0] + "@sha256:" + "4" * 64
                t.put_yaml("release.yaml", r)
                second = commit(t)
                before = all_keys(t, first)
                self.assertEqual(changed(before, all_keys(t, second)), sorted(up for up in before if up[1] in parts))

    def test_rocqchk_changes_every_build_and_nothing_else(self):
        with tree() as t:
            head = repo(t)
            wanted = keys.wanted(facts.load(t.root))
            plain = {up: k for up, (k, _c) in keys.keys(t.root, wanted, head, head, head).items()}
            checked = {up: k for up, (k, _c) in keys.keys(t.root, wanted, head, head, head, rocqchk=True).items()}
            self.assertEqual(changed(plain, checked), sorted(up for up in plain if up[1] == "build"))

    def test_an_attribute_that_changes_the_bytes_of_one_units_files_changes_that_unit_alone(self):
        """release/libreac's case: a .gitattributes line that gives one harness's files another attribute leaves
        every blob as it was."""
        with tree() as t:
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem x : True. Proof. exact I. Qed.\n")
            first = repo(t)
            t.write(".gitattributes", "* text=auto eol=lf\nproofs/%s/** -text\n" % UNIT)
            second = commit(t)
            self.assertEqual(changed(all_keys(t, first), all_keys(t, second)), [(UNIT, "build")])


class View(unittest.TestCase):
    """check-units.sh checks each part in a view of the paths that unitpaths.view gives: a change to a file of the view
    changes the part's key, and a change to any other file of the tree does not, so the view holds what the key holds,
    and one file more: the barrier dune of a per-project proofs or counterexamples folder, which the folder's own
    component leaves out (lint holds it to its rendering by the checker, whose id is in every key) and the unit's
    build key holds as a file of its build path (keys._dune_path), since a build reads it."""

    def test_a_file_changes_the_key_of_each_part_whose_view_holds_it_and_of_no_other(self):
        with tree() as t:
            t.write("toolchain/allowed-axioms.txt", "Corelib.Init.Something.prim\n")
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "(* stand-in *)\n")
            t.write("proofs/lib/Common.v", "Definition zero := 0.\n")
            first = repo(t)
            before = all_keys(t, first)
            views = {up: unitpaths.view(t.root, *up) for up in before}
            self.assertLessEqual({(UNIT, "build"), (UNIT, "findings"), (CX_UNIT, "counterexamples")}, set(views))
            files = [l for l in git(t, "ls-files").splitlines()
                     if not l.startswith("tools/") and l not in (".gitattributes", "release.yaml", "dune-project")]
            # one file of each directory and one under each path of each view, so that every path of every view,
            # and many outside them, are tried
            under = {p: sorted(f for f in files if f == p or f.startswith(p + "/")) for v in views.values() for p in v}
            sample = sorted(set({os.path.dirname(f): f for f in sorted(files, reverse=True)}.values())
                            | {fs[0] for fs in under.values() if fs})
            self.assertGreater(len(sample), 20)
            for f in sample:
                with self.subTest(file=f):
                    with open(t.path(f), "ab") as fh:
                        fh.write(b"\n")
                    after = all_keys(t, commit(t))
                    holds = sorted(up for up, v in views.items() if any(f == p or f.startswith(p + "/") for p in v))
                    self.assertEqual(changed(before, after), holds)
                    before = after

    def test_the_view_of_a_part(self):
        """The old layout: the statement folder by its entries but HARNESS_DROP, as the key holds it, and the unpatched
        binaries where `oft fetch --findings` puts them (layout.unpatched_bin_dir)."""
        with tree() as t:
            first = repo(t)
            t.write("toolchain/allowed-axioms.txt", "Corelib.Init.Something.prim\n")
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "(* stand-in *)\n")
            t.write("projects/zlib/bin/checksum_fuzzer/checksum_fuzzer.plain", "stand-in")
            t.write("projects/zlib/bin/api-driver/api-driver.plain", "stand-in")
            t.write("projects/zlib/unpatched-bin/checksum_fuzzer/checksum_fuzzer.plain", "stand-in")
            self.assertTrue(first)
            harnesses = ["projects/zlib/%s/harness.yaml" % h for h in ("api-driver",)]
            statement = ["projects/%s/%s" % (UNIT, e) for e in sorted(os.listdir(t.path("projects", UNIT)))
                         if e not in unitpaths.HARNESS_DROP]
            self.assertIn("projects/%s/harness.yaml" % UNIT, statement)
            self.assertTrue(os.path.exists(t.path("projects", UNIT, "README.md")))
            common = statement + ["projects/zlib/project.yaml"] + harnesses
            self.assertEqual(unitpaths.view(t.root, UNIT, "build"), sorted(common + [
                "projects/zlib/bin/checksum_fuzzer", "proofs/zlib/checksum_fuzzer", "theories",
                "toolchain/allowed-axioms.txt"]))
            self.assertEqual(unitpaths.view(t.root, UNIT, "findings"), sorted(common + [
                "findings/zlib/checksum_fuzzer", "findings/zlib/unpatched.yaml",
                "projects/zlib/unpatched-bin/checksum_fuzzer"]))
            os.symlink(t.path("proofs/zlib"), t.path("proofs/link"))
            with self.assertRaisesRegex(ValueError, "symbolic link"):
                unitpaths.view(t.root, "link/checksum_fuzzer", "build")

    def test_a_unit_view_reads_the_per_project_layout(self):
        """Task 3 of the join: own and view take each path from layout.py.  In a ported tree the view of each part
        holds the unit's own folder of that part under projects/<p>/<h>/, no path of the old layout, and none of the
        unit's other parts' folders."""
        self.assertEqual(unitpaths.own(UNIT, "build", layout.NEW)["proofs"], "projects/zlib/checksum_fuzzer/proofs")
        self.assertEqual(unitpaths.own(UNIT, "findings", layout.NEW)["unpatched"], "projects/zlib/unpatched.yaml")
        self.assertEqual(unitpaths.own(UNIT, "findings", layout.NEW)["findings"],
                         "projects/zlib/checksum_fuzzer/findings")
        self.assertEqual(unitpaths.own(CX_UNIT, "counterexamples", layout.NEW)["counterexamples"],
                         "projects/%s/counterexamples" % CX_UNIT)
        self.assertEqual(unitpaths.binaries(UNIT, "findings"), "projects/zlib/unpatched-bin/checksum_fuzzer")
        with tree() as t:
            old_layout_repo(t)
            port_layout(t)
            self.assertEqual(layout.of_tree(t.root), layout.NEW)
            want = {(UNIT, "build"): "projects/%s/proofs" % UNIT, (UNIT, "findings"): "projects/%s/findings" % UNIT,
                    (CX_UNIT, "counterexamples"): "projects/%s/counterexamples" % CX_UNIT}
            for (unit, part), folder in want.items():
                with self.subTest(unit=unit, part=part):
                    got = unitpaths.view(t.root, unit, part)
                    self.assertIn(folder, got)
                    self.assertEqual([r for r in got if r.split("/")[0] in layout.OLD_TOPS], [])
                    others = {"projects/%s/%s" % (unit, n) for n in layout.CHANGE_NAMES} - {folder}
                    self.assertEqual([r for r in got if any(r == o or r.startswith(o + "/") for o in others)], [])
                    self.assertNotIn("projects/%s/README.md" % unit, got)
            self.assertIn("projects/zlib/unpatched.yaml", unitpaths.view(t.root, UNIT, "findings"))

    def test_a_unit_view_reads_the_old_layout_of_an_old_tree(self):
        self.assertEqual(unitpaths.own(UNIT, "build", layout.OLD)["proofs"], "proofs/zlib/checksum_fuzzer")
        self.assertEqual(unitpaths.own(UNIT, "findings", layout.OLD)["unpatched"], "findings/zlib/unpatched.yaml")
        with tree() as t:
            old_layout_repo(t)
            self.assertEqual(layout.of_tree(t.root), layout.OLD)
            got = unitpaths.view(t.root, UNIT, "build")
            self.assertIn("proofs/zlib/checksum_fuzzer", got)
            self.assertNotIn("projects/zlib/checksum_fuzzer/proofs", got)

    def test_a_unit_in_both_layouts_has_no_view(self):
        """As it has no key (Layout.test_a_unit_in_both_layouts_has_no_key)."""
        with tree() as t:
            old_layout_repo(t)
            shutil.copytree(t.path("proofs", UNIT), t.path("projects", UNIT, "proofs"))
            with self.assertRaisesRegex(ValueError, "in both layouts"):
                unitpaths.view(t.root, UNIT, "build")

    def test_keys_and_views_are_equal_across_port_layout(self):
        """L1's invariant run through unitpaths: each part reads the same thing before and after `oft port-layout`
        and `oft generate` -- every component of its key but dune-path, which the barrier dune files the move writes
        in the new proofs and counterexamples folders change for a build (the lead's ruling of 2026-10-30:
        test_port_layout_changes_the_build_key_of_each_unit_that_gains_a_barrier) -- and its view holds the same
        files, each at the place layout.moved gives it, the moved tree's barriers, which its view does hold, taken
        out of the comparison."""
        def files(root, rels):
            out = set()
            for rel in rels:
                path = os.path.join(root, rel)
                if os.path.isdir(path):
                    out |= {os.path.relpath(os.path.join(dp, f), root) for dp, _d, fs in os.walk(path) for f in fs}
                elif os.path.exists(path):
                    out.add(rel)
            return out
        with tree() as t:
            a = old_layout_repo(t)
            want = keys.wanted(facts.load(t.root))
            before = {up: files(t.root, unitpaths.view(t.root, *up)) for up in want}
            comp_a = {up: c for up, (_k, c) in keys.keys(t.root, want, a, a, a).items()}
            b = port_layout(t)
            after = {up: files(t.root, unitpaths.view(t.root, *up)) for up in want}
            comp_b = {up: c for up, (_k, c) in keys.keys(t.root, want, b, b, a).items()}
            barriers = {os.path.join(d, "dune") for u, _p in want for d in layout.barrier_dirs(*u.split("/"))}

            def but_dune_path(comps):
                return {up: {n: v for n, v in c.items() if n != "dune-path"} for up, c in comps.items()}
            self.assertEqual(but_dune_path(comp_a), but_dune_path(comp_b))
            for up in want:
                with self.subTest(unit=up[0], part=up[1]):
                    self.assertEqual({layout.moved(f) or f for f in before[up]}, after[up] - barriers)

    def test_the_view_s_dune_project_holds_what_the_key_does(self):
        """The forms but the package stanzas, and the stanzas of the core, the meta package and the project's own."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            repo(t)
            out = os.path.join(d, "dune-project")
            done = subprocess.run([sys.executable, "-m", "oft.unitpaths", "--root", t.root, "--part", "build",
                                   "--dune-project-to", out, UNIT], capture_output=True, text=True,
                                  env=dict(os.environ, PYTHONPATH=TOOLS, PYTHONDONTWRITEBYTECODE="1"))
            self.assertEqual(done.returncode, 0, done.stderr)
            self.assertEqual(done.stdout.splitlines(), unitpaths.view(t.root, UNIT, "build"))
            with open(out) as f:
                text = f.read()
            parsed = unitpaths.forms(t.read("dune-project"))
            packages = re.findall(r"\(package\s+\(name\s+([^\s()]+)\)", text)
            self.assertEqual(packages, [n for n in unitpaths.dune_packages("zlib", names.OPAM_STEM_DEFAULT)
                                        if "(name %s)" % n in t.read("dune-project")])
            self.assertIn("rocq-oss-fuzz-theorems-zlib", packages)
            self.assertEqual(unitpaths.forms(text), [f for f in parsed if not unitpaths.PACKAGE.match(f)
                                                     or unitpaths.PACKAGE.match(f).group(1) in packages])
            self.assertTrue(text.startswith("(lang dune "), text[:40])

    def test_the_view_s_dune_project_names_the_tree_s_packages(self):
        """In a tree whose release.yaml names another opam stem, the view's dune-project keeps that stem's stanzas of
        the core, the meta package and the project's own, as the key does (keys.dune_project)."""
        with tree(render=False) as t, tempfile.TemporaryDirectory() as d:
            rename_namespace(t)
            self.assertEqual(t.generate(), 0, t.last_output)
            repo(t)
            out = os.path.join(d, "dune-project")
            done = subprocess.run([sys.executable, "-m", "oft.unitpaths", "--root", t.root, "--part", "build",
                                   "--dune-project-to", out, UNIT], capture_output=True, text=True,
                                  env=dict(os.environ, PYTHONPATH=TOOLS, PYTHONDONTWRITEBYTECODE="1"))
            self.assertEqual(done.returncode, 0, done.stderr)
            with open(out) as f:
                packages = re.findall(r"\(package\s+\(name\s+([^\s()]+)\)", f.read())
            self.assertEqual(sorted(packages), sorted(unitpaths.dune_packages("zlib", NEW_OPAM_STEM)))
            self.assertIn("rocq-oss-verify-zlib", packages)



class Checker(unittest.TestCase):
    def opened(self, t, module, *args):
        """`python3 -m <module> --root <t> <args>`, run as check-units.sh runs it: (the files of tools/ it opens,
        each relative to tools/, the files of t it opens, each relative to t, what it prints).  A module Python loads
        from its cached bytecode (written by any earlier run without -B, in __pycache__ or under PYTHONPYCACHEPREFIX)
        counts as its source file, so the audit sees it whether or not a cache exists.  A .pyc that names no source
        (source_from_cache refuses it) stays as it is: an audit hook that raised would end the run."""
        hook = ("import sys, os, runpy, importlib.util\n"
                "seen = set()\n"
                "def hook(ev, args):\n"
                "    if ev == 'open' and isinstance(args[0], str):\n"
                "        p = args[0]\n"
                "        if p.endswith('.pyc'):\n"
                "            try:\n"
                "                p = importlib.util.source_from_cache(p)\n"
                "            except ValueError:\n"
                "                pass\n"
                "        seen.add(os.path.abspath(p))\n"
                "sys.addaudithook(hook)\n"
                "sys.argv = [sys.argv[1]] + sys.argv[2:]\n"
                "try:\n"
                "    runpy.run_module(sys.argv[0], run_name='__main__')\n"
                "except SystemExit:\n"
                "    pass\n"
                "with open(os.environ['AUDIT_OPENED'], 'w') as f:\n"
                "    f.write('\\n'.join(sorted(seen)))\n")
        with tempfile.NamedTemporaryFile("r") as listed:
            pythonpath = TOOLS + os.pathsep + os.environ.get("PYTHONPATH", "")
            done = subprocess.run([sys.executable, "-c", hook, module, "--root", t.root, *args], capture_output=True,
                                  text=True, env=dict(os.environ, PYTHONPATH=pythonpath, AUDIT_OPENED=listed.name,
                                                      PYTHONDONTWRITEBYTECODE="1"))
            paths = listed.read().splitlines()
        tools = TOOLS + os.sep
        root = os.path.abspath(t.root) + os.sep
        return ({p[len(tools):] for p in paths if p.startswith(tools) and "__pycache__" not in p},
                {p[len(root):] for p in paths if p.startswith(root)}, done.stdout + done.stderr)

    @unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
    def test_a_check_and_its_fetch_open_no_file_outside_the_checker(self):
        """`python3 -m oft.check` and `python3 -m oft.fetch`, as check-units.sh runs them, fetch, unpack and check a
        tree without opening any file of tools/ that keys leaves out of every key (a file keys.not_the_checker names),
        and without opening a project's or a fuzz target's README.md, which no key holds."""
        with tree() as t, tempfile.TemporaryDirectory() as assets:
            add_findings(t)
            make_release(t, assets)
            # a proof whose fingerprint is current and an allowlist, so that the check enters the proof's step
            t.write("toolchain/allowed-axioms.txt", "Corelib.Init.Something.prim\n")
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "(* stand-in *)\n")
            t.write("proofs/%s/lib/L.v" % UNIT, "(* stand-in *)\n")
            fingerprint = next(st for h in facts.load(t.root).harnesses() for st in h.statements.values()
                               if st.id == "%s/plain_halts" % UNIT).fingerprint
            t.put_yaml("proofs/%s/plain_halts/proof.yaml" % UNIT, {
                "schema": "oss-fuzz-theorems/proof/1", "proves": "%s/plain_halts" % UNIT, "fingerprint": fingerprint})
            runs = {"fetch --list": self.opened(t, "oft.fetch", "--list", "zlib"),
                    "fetch --findings --list": self.opened(t, "oft.fetch", "--findings", "--list", "zlib"),
                    "fetch --source": self.opened(t, "oft.fetch", "--source", assets, "zlib"),
                    # a step may fail for want of dune, rocq, qemu or a binary, after the check has entered it; the
                    # counterexample's unit has no proof, so it is checked by itself (naming proofs refuses it)
                    "check": self.opened(t, "oft.check", "--parts", "statements,proofs,counterexamples,findings",
                                         UNIT),
                    "check counterexamples": self.opened(t, "oft.check", "--parts", "counterexamples", CX_UNIT)}
            self.assertTrue(os.listdir(t.path("projects", "zlib", "bin")), "fetch --source unpacked nothing")
            said = runs["check"][2] + runs["check counterexamples"][2]
            for step in ("statements", "proofs/%s/plain_halts" % UNIT, "counterexamples/%s/" % CX_UNIT,
                         "findings/%s/" % UNIT):
                self.assertIn(step, said, "the check never reached this step")
            self.assertIn("oft/check.py", runs["check"][0])
            for name, (opened, read, _said) in runs.items():
                with self.subTest(run=name):
                    self.assertIn("oft/facts.py", opened)
                    self.assertEqual(sorted(p for p in opened if keys.not_the_checker("tools/" + p)), [])
                    self.assertIn("projects/zlib/project.yaml", read)
                    self.assertFalse([f for f in read if f.endswith("/README.md") and f.startswith("projects/")])
            # the views check-units.sh makes, which load none of the facts: the statement folder by its entries, its
            # README.md left out (unitpaths.HARNESS_DROP)
            for part, extra in (("build", ("--dune-project-to", os.path.join(assets, "dune-project"))),
                                ("findings", ())):
                with self.subTest(run="unitpaths " + part):
                    opened, _read, said = self.opened(t, "oft.unitpaths", "--part", part, *extra, UNIT)
                    self.assertIn("projects/%s/harness.yaml\n" % UNIT, said)
                    self.assertNotIn("projects/%s/README.md\n" % UNIT, said)
                    self.assertIn("oft/unitpaths.py", opened)
                    self.assertEqual(sorted(p for p in opened if keys.not_the_checker("tools/" + p)), [])

    def test_the_migration_pin_and_the_ci_helpers_are_not_the_checker(self):
        """The pin is read only by pr.yml's plan step and release-check's, from the base; ci/pr-steps.sh and
        ci/pin-digests.sh are run by hand on a clone; tools/publish/ is the publishing workflow's, which no check opens
        (plan D8): a change to any of them leaves keys.checker as it was, so setting or emptying the pin, these
        scripts and the publishing tools re-key nothing.  A change to a file of the checker still moves it."""
        for name in ("migration-pin.yaml", "ci/pr-steps.sh", "ci/pin-digests.sh"):
            self.assertTrue(keys.not_the_checker("tools/oft/" + name), name)
        self.assertTrue(keys.not_the_checker("tools/publish/release.py"))
        with tree() as t:
            first = repo(t)
            t.write("tools/oft/migration-pin.yaml", deferred_pin("e" * 64))
            t.write("tools/oft/ci/pin-digests.sh", "#!/bin/bash\n")
            t.write("tools/oft/ci/pr-steps.sh", "#!/bin/bash\n")
            t.write("tools/publish/publish.py", "print('publish')\n")
            second = commit(t)
            self.assertEqual(keys.checker(t.root, first), keys.checker(t.root, second))
            t.write("tools/oft/check.py", "check, with a fix\n")
            third = commit(t)
            self.assertNotEqual(keys.checker(t.root, first), keys.checker(t.root, third))

    def test_nsrename_is_not_the_checker(self):
        """tools/oft/nsrename.py renames a tree's Rocq namespace (`oft rename-namespace`); no check opens it, so a fix
        to it leaves keys.checker as it was and re-checks no fuzz target (OSSV-162 plan D2).  A change to a file of
        the checker still moves it."""
        self.assertTrue(keys.not_the_checker("tools/oft/nsrename.py"))
        self.assertFalse(keys.not_the_checker("tools/oft/nsrename.pyc"))
        with tree() as t:
            t.write("tools/oft/nsrename.py", "rename\n")
            first = repo(t)
            t.write("tools/oft/nsrename.py", "rename, with a fix\n")
            second = commit(t)
            self.assertEqual(keys.checker(t.root, first), keys.checker(t.root, second))
            t.write("tools/oft/check.py", "check, with a fix\n")
            third = commit(t)
            self.assertNotEqual(keys.checker(t.root, first), keys.checker(t.root, third))


class Layout(unittest.TestCase):
    """A key holds what a check reads, not where it lies, so that the layout move of every proof, counterexample and
    finding into the per-project layout leaves every key as it was, but for the barrier dune files the move writes
    into a unit's build path (the lead's ruling of 2026-10-30)."""

    def test_port_layout_changes_the_build_key_of_each_unit_that_gains_a_barrier(self):
        """The L2 invariant, as the lead's ruling of 2026-10-30 leaves it: `oft port-layout` and `oft generate` move
        every file of the fixture (a proof library, a fuzz target with only a build record, a counterexample and a
        finding), render the harness pages again and write a barrier dune file in each per-project proofs and
        counterexamples folder, both of which a build's dune reads through the statement folder.  Every
        counterexamples and findings key is as it was.  The build key of each unit that gains a barrier changes,
        and in its dune-path component alone: a pass recorded before the move is not a pass of the moved tree,
        which dune reads those barriers for."""
        with tree() as t:
            a = old_layout_repo(t)
            want = keys.wanted(facts.load(t.root))
            self.assertLessEqual({(UNIT, "build"), ("zlib/api-driver", "build"), (CX_UNIT, "counterexamples"),
                                  (UNIT, "findings")}, set(want))
            b = port_layout(t)
            self.assertEqual(keys.wanted(facts.load(t.root)), want)
            moved = git(t, "diff", "--name-only", a, b).splitlines()
            for rel in ("projects/%s/proofs/dune" % UNIT, "projects/zlib/api-driver/proofs/dune",
                        "projects/%s/counterexamples/dune" % CX_UNIT, "projects/%s/README.md" % UNIT,
                        "projects/%s/proofs/lib/A.v" % UNIT, "projects/zlib/unpatched.yaml",
                        "projects/zlib/patches/0001-stand-in.patch"):
                self.assertIn(rel, moved)
            before, after = keys.keys(t.root, want, a, a, a), keys.keys(t.root, want, b, b, a)
            gained = sorted(up for up in want if up[1] == "build"
                            and any(os.path.exists(t.path("projects/%s/%s/dune" % (up[0], n)))
                                    for n in layout.CHANGE_NAMES))
            self.assertLessEqual({(UNIT, "build"), ("zlib/api-driver", "build"), (CX_UNIT, "build")}, set(gained))
            self.assertEqual(sorted(up for up in want if before[up][0] != after[up][0]), gained)
            self.assertEqual({up: before[up][0] for up in want if up[1] != "build"},
                             {up: after[up][0] for up in want if up[1] != "build"})
            for up in gained:
                self.assertEqual({n for n, v in before[up][1].items() if after[up][1][n] != v}, {"dune-path"}, up)
            # each moved folder is in its part's key: the keys are not equal because both sides read nothing
            for up, name in (((UNIT, "build"), "proofs"), (("zlib/api-driver", "build"), "proofs"),
                             ((CX_UNIT, "counterexamples"), "counterexamples"), ((UNIT, "findings"), "findings"),
                             ((UNIT, "findings"), "unpatched")):
                self.assertNotEqual(after[up][1][name], "-", (up, name))

    def test_a_dune_file_of_a_new_layout_build_path_changes_the_builds_under_it(self):
        """In the per-project layout a unit's build path is the repository root, projects/, projects/<p>/, its
        statement folder, and the three folders the statement folder's (include_subdirs qualified) takes: proofs/,
        counterexamples/ and findings/.  `oft generate` writes a barrier dune file in the first two, which shuts
        them out of the statement theory (generate.render_all); the findings folder has none, so a dune file there
        would be taken into that theory.  A dune file in any of the three changes the build keys under it, both
        barriers included; the statement folder's own dune file is in every part of that unit (the folder is), and
        a dune file inside the counterexamples or findings folder is in that folder's id too, unless it is the
        barrier, which the id drops.  No counterexamples or findings key holds a dune file of a path."""
        with tree() as t:
            old_layout_repo(t)
            first = port_layout(t)
            before = all_keys(t, first)
            cases = (("projects/dune", parts_of(before, ("build",))),
                     ("projects/dune-workspace", parts_of(before, ("build",))),
                     ("projects/zlib/dune", parts_of(before, ("build",), "zlib/")),
                     ("projects/zlib/dune-file", parts_of(before, ("build",), "zlib/")),
                     ("projects/%s/dune" % UNIT, parts_of(before, keys.PARTS, UNIT)),
                     ("projects/%s/proofs/dune" % UNIT, [(UNIT, "build")]),
                     ("projects/%s/proofs/dune-workspace" % UNIT, [(UNIT, "build")]),
                     ("projects/%s/counterexamples/dune" % CX_UNIT, [(CX_UNIT, "build")]),
                     ("projects/%s/counterexamples/dune-file" % CX_UNIT,
                      parts_of(before, ("build", "counterexamples"), CX_UNIT)),
                     ("projects/%s/findings/dune" % UNIT, parts_of(before, ("build", "findings"), UNIT)),
                     ("projects/%s/findings/dune-workspace" % UNIT,
                      parts_of(before, ("build", "findings"), UNIT)))
            for rel, want in cases:
                with self.subTest(rel=rel):
                    dune_case(self, t, before, rel, want)

    def test_a_statement_folder_without_a_barrier_has_another_build_key(self):
        """`oft generate` writes the barrier of a per-project proofs and counterexamples folder, and the folder's id
        leaves it out, so that the layout move carries that id: the unit's build key holds each barrier as a file of
        its build path instead, since the statement folder's id drops those folders (layout.CHANGE_NAMES) and the
        statement theory would take them.  A tree whose folder has no barrier has another build key, that unit's
        alone, and the folder's own component is the same on both sides."""
        for unit, part, folder in ((UNIT, "build", "proofs"), (CX_UNIT, "counterexamples", "counterexamples")):
            with self.subTest(folder=folder), tree() as t:
                old_layout_repo(t)
                with_barrier = port_layout(t)
                rel = "projects/%s/%s/dune" % (unit, folder)
                text = t.read(rel)
                os.remove(t.path(rel))
                without = commit(t)
                self.assertEqual(changed(all_keys(t, with_barrier), all_keys(t, without)), [(unit, "build")])
                comps = (all_comps(t, with_barrier)[(unit, part)], all_comps(t, without)[(unit, part)])
                self.assertEqual(comps[0][folder], comps[1][folder])
                build = (all_comps(t, with_barrier)[(unit, "build")], all_comps(t, without)[(unit, "build")])
                self.assertNotEqual(build[0]["dune-path"], build[1]["dune-path"])
                t.write(rel, text)
                self.assertEqual(changed(all_keys(t, with_barrier), all_keys(t, commit(t))), [])

    def test_the_build_path_reads_a_proofs_folder_s_dune_from_the_change_and_the_rest_from_the_facts(self):
        """A pull request that is not a release is checked on the base's statements with its own proofs (D6).  A
        dune file of a proofs folder is the change's, as check_hand_dune reads it; one above the folder is the
        base's, so the change's copy of it is in no key of that run."""
        with tree() as t:
            old_layout_repo(t)
            base = port_layout(t)
            want = [(UNIT, "build")]
            t.write("projects/%s/proofs/dune-workspace" % UNIT, "(dirs :standard)\n")
            t.write("projects/zlib/dune", "(dirs :standard)\n")
            git(t, "add", "-f", "projects/%s/proofs/dune-workspace" % UNIT, "projects/zlib/dune")
            head = commit(t)
            of = {name: keys.keys(t.root, want, f, c, base)[want[0]][1]["dune-path"]
                  for name, (f, c) in {"base": (base, base), "mixed": (base, head), "head": (head, head)}.items()}
            self.assertNotEqual(of["mixed"], of["base"])   # the proofs folder's dune-workspace is the change's
            self.assertNotEqual(of["mixed"], of["head"])   # projects/zlib/dune is the base's

    def test_a_proof_change_changes_only_its_units_build_key(self):
        """In the per-project layout a proof lies in its statement folder, which every part of its unit reads: it
        still changes the build of its unit alone."""
        with tree() as t:
            old_layout_repo(t)
            first = port_layout(t)
            t.write("projects/%s/proofs/plain_halts/Proof.v" % UNIT, "Theorem x : True. Proof. exact I. Qed.\n")
            self.assertEqual(changed(all_keys(t, first), all_keys(t, commit(t))), [(UNIT, "build")])

    def test_a_harness_readme_changes_no_key(self):
        """No check reads a fuzz target's README.md (Checker says so), and oft generate renders it again when its
        proofs move or change: it is in no key, in either layout."""
        for ported in (False, True):
            with self.subTest(ported=ported), tree() as t:
                first = old_layout_repo(t)
                if ported:
                    first = port_layout(t)
                rel = "projects/%s/README.md" % UNIT
                t.write(rel, t.read(rel) + "\nchanged\n")
                self.assertEqual(changed(all_keys(t, first), all_keys(t, commit(t))), [])

    def test_statements_come_from_facts_and_proofs_from_change_in_the_new_layout(self):
        """A change that is not a release is checked on the base's statements and its own proofs (D6), also when
        both lie in one statement folder."""
        with tree() as t:
            old_layout_repo(t)
            f = port_layout(t)
            want = [(UNIT, "build")]
            t.write("projects/%s/Statements.v" % UNIT, t.read("projects/%s/Statements.v" % UNIT) + "(* changed *)\n")
            t.write("projects/%s/proofs/plain_halts/Proof.v" % UNIT, "Theorem x : True. Proof. exact I. Qed.\n")
            c = commit(t)
            base, mixed, own = (keys.keys(t.root, want, x, y, f)[want[0]][1] for x, y in ((f, f), (f, c), (c, c)))
            self.assertEqual(mixed["harness"], base["harness"])
            self.assertNotEqual(own["harness"], base["harness"])
            self.assertNotEqual(mixed["proofs"], base["proofs"])
            self.assertEqual(mixed["proofs"], own["proofs"])

    def test_a_unit_in_both_layouts_has_no_key(self):
        """facts.load refuses such a unit and loads neither copy; a key would read only one of them."""
        cases = {"proofs": ("proofs/%s/plain_halts" % UNIT, "projects/%s/proofs/plain_halts" % UNIT, (UNIT, "build")),
                 "counterexamples": ("counterexamples/%s/plain_halts" % CX_UNIT,
                                     "projects/%s/counterexamples/plain_halts" % CX_UNIT, (CX_UNIT, "counterexamples")),
                 "findings": ("findings/%s/stand-in-abort" % UNIT, "projects/%s/findings/stand-in-abort" % UNIT,
                              (UNIT, "findings")),
                 "unpatched": ("findings/zlib/unpatched.yaml", "projects/zlib/unpatched.yaml", (UNIT, "findings"))}
        for name, (old, new, up) in cases.items():
            with self.subTest(copy=name), tree() as t:
                old_layout_repo(t)
                (shutil.copytree if os.path.isdir(t.path(old)) else shutil.copy)(t.path(old), t.path(new))
                c = commit(t)
                with self.assertRaisesRegex(keys.NoKey, "^%s: in both layouts$" % up[0]):
                    keys.keys(t.root, [up], c, c, c)

    def test_a_hand_written_dune_file_in_a_changes_new_layout_proofs_gives_no_key(self):
        """A dune file under projects/<p>/<h>/proofs/ is the change's, as one under proofs/<p>/<h>/ is: the plan
        reads it from the change, not from the base."""
        with tree() as t:
            old_layout_repo(t)
            base = port_layout(t)
            path = "projects/%s/proofs/plain_halts/classifier/dune" % UNIT
            t.write(path, "(rocq.theory (name LinuxProcessSemantics))\n")
            git(t, "add", "-f", path)
            head = commit(t)
            with self.assertRaisesRegex(keys.NoKey, "^%s: a hand-written dune file" % path):
                keys.keys(t.root, [(UNIT, "build")], base, head, base)

    def test_a_projects_first_patch_changes_no_key(self):
        """No check reads a project's patches (disclosure and release-tree do), in either layout; projects/<p>/patches/
        is no fuzz target's folder, so it adds no harness.yaml to the project's id."""
        for ported in (False, True):
            with self.subTest(ported=ported), tree() as t:
                first = old_layout_repo(t)
                if ported:
                    first = port_layout(t)
                t.write(layout.patches_dir("json", layout.NEW if ported else layout.OLD) + "/0001-x.patch", "x\n")
                self.assertEqual(changed(all_keys(t, first), all_keys(t, commit(t))), [])


class Plan(unittest.TestCase):
    def plan(self, t, **kw):
        buf = io.StringIO()
        plan.plan(t.root, out=buf, **kw)
        return json.loads(buf.getvalue())

    def checked(self, p):
        return sorted((r["unit"], r["part"]) for r in p["parts"] if r["check"])

    def test_a_change_is_checked_on_what_it_changes(self):
        with tree() as t:
            base = repo(t)
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem x : True. Proof. exact I. Qed.\n")
            t.write("tools/oft/check.py", "check, changed\n")
            head = commit(t)
            p = self.plan(t, change=head, base=base, kind="maintainer")
            self.assertEqual(self.checked(p), [(UNIT, "build")])
            row = next(r for r in p["parts"] if r["check"])
            self.assertEqual(row["why"], "changed: proofs")
            self.assertEqual(p["units"], [UNIT])
            # a job's whole shape: the fields the workflows read (pr.yml, release-check.yml and weekly.yml read index,
            # check_units, proof_units, projects, counterexamples, findings and cpus), the job's units, and no key, which
            # the parts carry.  The Proof.v above has no proof.yaml, so facts sees no proof and proof_units is empty.
            self.assertEqual(p["jobs"], [{"index": 0, "units": UNIT, "check_units": UNIT, "proof_units": "",
                                          "projects": "zlib", "counterexamples": "", "findings": "", "cpus": 0}])

    def test_a_change_that_adds_a_shadowing_dune_file_fails_its_own_plan(self):
        """A change that is not a release is checked on the base's tests/, but its own dune files reach main."""
        for kind in ("maintainer", "contributor"):
            with self.subTest(kind=kind), tree() as t:
                base = repo(t)
                t.write("tests/x/dune", "(env (_ (flags (:standard -type-in-type))))\n")
                head = commit(t)
                with self.assertRaisesRegex(keys.NoKey, "^tests/x/dune: a hand-written dune file with a env stanza"):
                    self.plan(t, change=head, base=base, kind=kind)

    def test_a_change_that_is_not_a_release_is_checked_on_the_bases_statements(self):
        with tree() as t:
            base = repo(t)
            t.write("projects/zlib/project.yaml", t.read("projects/zlib/project.yaml") + "# x\n")
            head = commit(t)
            self.assertEqual(self.checked(self.plan(t, change=head, base=base, kind="contributor")), [])
            self.assertEqual({u for u, _ in self.checked(self.plan(t, change=head, base=base, kind="release"))},
                             {u for u, _ in keys.wanted(facts.load(t.root)) if u.startswith("zlib/")})

    def test_a_recorded_pass_is_not_checked_again(self):
        with tree() as t:
            base = repo(t)
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem x : True. Proof. exact I. Qed.\n")
            head = commit(t)
            key = next(r["key"] for r in self.plan(t, change=head, base=base)["parts"] if r["check"])
            git(t, "checkout", "-q", "--orphan", keys.STORE_BRANCH)
            git(t, "rm", "-rq", "--cached", ".")
            t.write(keys.record_path(UNIT, "build", key), "{}\n")
            git(t, "add", keys.record_path(UNIT, "build", key))
            git(t, "commit", "-q", "-m", "record")
            store = git(t, "rev-parse", "HEAD")
            git(t, "checkout", "-q", "-f", head)
            p = self.plan(t, change=head, base=base, store=store)
            self.assertEqual(self.checked(p), [])
            self.assertIn("recorded pass", [r["why"] for r in p["parts"] if r["unit"] == UNIT])

    def test_a_finding_on_a_harness_that_withholds_every_build_is_a_job_that_fetches_and_builds_nothing(self):
        """pr.yml runs a check job for it and required wants it to pass; check-units.sh fetches only its unpatched
        binaries."""
        with tree() as t:
            repo(t)
            withhold_checksum_fuzzer(t)
            p = self.plan(t, change=commit(t))
            self.assertNotIn((UNIT, "build"), self.checked(p))
            job = next(j for j in p["jobs"] if UNIT in j["units"].split())
            self.assertEqual((job["check_units"], job["projects"], job["counterexamples"], job["findings"]),
                             ("", "", "", UNIT))

    def test_with_no_base_every_part_without_a_recorded_pass_is_checked(self):
        with tree() as t:
            head = repo(t)
            p = self.plan(t, change=head)
            self.assertTrue(p["all"])
            self.assertEqual(self.checked(p), keys.wanted(facts.load(t.root)))
            self.assertEqual({r["why"] for r in p["parts"]}, {"no recorded pass"})

    def test_a_harness_whose_every_statement_is_withdrawn_has_no_build_to_check(self):
        """Its builds are published, but its Statements.v defines no statement, so no check job builds it."""
        with tree() as t:
            repo(t)
            withdraw_every_statement(t, "checksum_fuzzer")
            p = self.plan(t, change=commit(t))
            self.assertNotIn((UNIT, "build"), keys.wanted(facts.load(t.root)))
            self.assertNotIn(UNIT, p["check_units"])
            self.assertIn(("zlib/api-driver", "build"), self.checked(p))

    def test_a_harness_with_published_builds_and_no_statement_to_check_is_an_error_of_the_facts(self):
        """wanted leaves a harness with no statement Statements.v carries out of every check, so the facts may not
        reach that state by mistake: an empty or missing statements map, or every statement withheld while a build is
        published.  Withdrawing every one, each with its reason, is the one way there, and it is no error."""
        rel = "projects/zlib/checksum_fuzzer/harness.yaml"

        def errors(t):
            tree_ = facts.load(t.root)
            rules.check(tree_)
            return [e for e in tree_.errors if e.startswith(rel)]

        def withhold(y):
            for st in y["statements"].values():
                for k in ("basis", "reason", "witness", "withheld", "gap"):
                    st.pop(k, None)
                st.update(status="withheld", withheld="not-yet-published")

        for name, change, want in (("empty", lambda y: y.update(statements={}), "expected a non-empty mapping"),
                                   ("missing", lambda y: y.pop("statements"), "missing key 'statements'"),
                                   ("withheld", withhold, "publishes a build, but every statement is withheld")):
            with self.subTest(statements=name), tree() as t:
                y = t.yaml(rel)
                change(y)
                t.put_yaml(rel, y)
                self.assertTrue(any(want in e for e in errors(t)), errors(t))
        with tree() as t:
            withdraw_every_statement(t, "checksum_fuzzer")
            self.assertEqual(errors(t), [])

    def test_each_job_lists_its_units_with_a_proof(self):
        """check-units.sh checks proof_units with their proofs and the other check_units on their statements."""
        with tree() as t:
            repo(t)
            st = next(x for x in facts.load(t.root).statements() if x.id == UNIT + "/plain_halts")
            t.put_yaml("proofs/%s/plain_halts/proof.yaml" % UNIT, {
                "schema": "oss-fuzz-theorems/proof/1", "proves": st.id, "fingerprint": st.fingerprint})
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem plain_halts_holds : True. Qed.\n")
            p = self.plan(t, change=commit(t), max_jobs=1)
            self.assertEqual(len(p["jobs"]), 1)
            self.assertIn("zlib/api-driver", p["jobs"][0]["check_units"].split())
            self.assertEqual(p["jobs"][0]["proof_units"], UNIT)
            self.assertEqual(p["jobs"][0]["cpus"], pack.job_cpus(p["jobs"][0]["proof_units"].split(), pack.load()))

    def test_a_job_holding_paintcmap_gets_the_8_cpus_the_table_gives_it(self):
        """leptonica/paintcmap_fuzzer ran out of memory at 16 CPUs (proof-times.tsv gives it 8): a plan job holding
        it carries cpus 8, which check-units.sh gives the checker container, and it is dealt a job of its own among
        the proved units.  The fixture has no leptonica, so its proved zlib unit stands in, with the tracked row."""
        lep = "leptonica/paintcmap_fuzzer"
        real = pack.load()
        self.assertEqual(real[lep][2], 8)
        self.assertEqual(pack.job_cpus([lep, "zlib/api-driver"], real), 8)
        with tree() as t:
            repo(t)
            st = next(x for x in facts.load(t.root).statements() if x.id == UNIT + "/plain_halts")
            t.put_yaml("proofs/%s/plain_halts/proof.yaml" % UNIT, {
                "schema": "oss-fuzz-theorems/proof/1", "proves": st.id, "fingerprint": st.fingerprint})
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem plain_halts_holds : True. Qed.\n")
            head = commit(t)
            table = dict(real)
            table[UNIT] = table.pop(lep)
            with mock.patch.object(plan.pack, "load", return_value=table):
                for max_jobs in (1, 20):
                    with self.subTest(max_jobs=max_jobs):
                        p = self.plan(t, change=head, max_jobs=max_jobs)
                        job = next(j for j in p["jobs"] if UNIT in j["units"].split())
                        self.assertEqual(job["cpus"], 8)
                        if max_jobs > 1:
                            self.assertEqual(job["proof_units"], UNIT)
                            self.assertEqual({j["cpus"] for j in p["jobs"] if j is not job}, {0})

    def test_a_limited_unit_without_a_proof_leaves_its_job_at_every_cpu(self):
        """A unit the table limits but whose proofs the job does not check (its statements, counterexamples or
        findings alone) never needs fewer CPUs: a job whose only proof is an unlimited unit gets 0, every CPU, though
        it also holds the limited one.  (A review found two such jobs in main's full plan, at 8 and 11.)"""
        lep = "leptonica/paintcmap_fuzzer"
        with tree() as t:
            repo(t)
            st = next(x for x in facts.load(t.root).statements() if x.id == UNIT + "/plain_halts")
            t.put_yaml("proofs/%s/plain_halts/proof.yaml" % UNIT, {
                "schema": "oss-fuzz-theorems/proof/1", "proves": st.id, "fingerprint": st.fingerprint})
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem plain_halts_holds : True. Qed.\n")
            head = commit(t)
            table = dict(pack.load())
            # zlib/api-driver, checked on its statements only, takes paintcmap's limit
            table["zlib/api-driver"] = table.pop(lep)
            with mock.patch.object(plan.pack, "load", return_value=table):
                p = self.plan(t, change=head, max_jobs=1)
            [job] = p["jobs"]
            self.assertIn("zlib/api-driver", job["check_units"].split())
            self.assertEqual(job["proof_units"], UNIT)
            self.assertEqual(job["cpus"], 0)

    def test_explain_marks_what_differs_from_the_base(self):
        with tree() as t:
            base = repo(t)
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem x : True. Proof. exact I. Qed.\n")
            head = commit(t)
            buf = io.StringIO()
            self.assertEqual(plan.explain(t.root, UNIT, change=head, base=base, out=buf), 0)
            lines = buf.getvalue().splitlines()
            self.assertIn("%s build" % UNIT, [" ".join(l.split()[:2]) for l in lines if not l.startswith(" ")])
            self.assertEqual([l.split()[1] for l in lines if l.startswith("  *")], ["proofs"])

    def workflow(self, t, d):
        """A bare remote of t's repository with a clone of it, as a workflow's plan job has them: (remote, clone)."""
        remote, clone = os.path.join(d, "remote.git"), os.path.join(d, "head")
        subprocess.run(GIT + ["clone", "-q", "--bare", t.root, remote], env=GIT_ENV, check=True)
        subprocess.run(GIT + ["clone", "-q", remote, clone], env=GIT_ENV, check=True)
        os.mkdir(os.path.join(d, "bin"))
        with open(os.path.join(d, "bin", "python"), "w") as f:
            f.write('#!/bin/sh\nexec "%s" "$@"\n' % sys.executable)
        os.chmod(os.path.join(d, "bin", "python"), 0o755)
        return remote, clone

    def run_step(self, d, workflow, cwd, **env):
        """The step with id plan of the workflow, run as GitHub runs it in cwd: (its plan.json, or None when it wrote
        none, its outputs); its output and job summary in self.said.  The test is skipped where the workflow is not,
        as in the runner image, whose build runs these tests with tools/oft alone (toolchain/runner.Dockerfile)."""
        path = os.path.join(REPO, ".github", "workflows", workflow)
        if not os.path.exists(path):
            self.skipTest("no .github/workflows/%s beside tools/oft" % workflow)
        step = next(s for s in yamlio.load_file(path)["jobs"]["plan"]["steps"] if s.get("id") == "plan")
        tmp = tempfile.mkdtemp(dir=d)
        with open(os.path.join(tmp, "plan.sh"), "w") as f:
            f.write(step["run"])
        env = dict(GIT_ENV, PATH=os.path.join(d, "bin") + os.pathsep + os.environ["PATH"], RUNNER_TEMP=tmp,
                   GITHUB_OUTPUT=os.path.join(tmp, "output"), GITHUB_STEP_SUMMARY=os.path.join(tmp, "summary"), **env)
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", os.path.join(tmp, "plan.sh")],
                           cwd=cwd, env=env, capture_output=True, text=True)
        self.said = r.stdout + r.stderr
        self.assertEqual(r.returncode, 0, self.said)
        if os.path.exists(os.path.join(tmp, "summary")):
            with open(os.path.join(tmp, "summary")) as f:
                self.said += f.read()
        plan_json = os.path.join(tmp, "plan.json")
        with open(os.path.join(tmp, "output")) as o:
            output = o.read()
        if not os.path.exists(plan_json):
            return None, output
        with open(plan_json) as f:
            return json.load(f), output

    def record(self, t, remote, back, entries):
        """Push a check-results commit holding a pass of each (unit, part, key) of entries, then check out back."""
        git(t, "checkout", "-q", "--orphan", keys.STORE_BRANCH)
        git(t, "rm", "-rq", "--cached", ".")
        for unit, part, key in entries:
            t.write(keys.record_path(unit, part, key), "{}\n")
            git(t, "add", keys.record_path(unit, part, key))
        git(t, "commit", "-q", "-m", "record")
        git(t, "push", "-q", "-f", remote, "%s:refs/heads/%s" % (keys.STORE_BRANCH, keys.STORE_BRANCH))
        git(t, "checkout", "-q", "-f", back)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_pr_plan_step_checks_a_changed_proof_whatever_check_results_holds(self):
        """pr.yml's plan step over a remote with the base and the change, the base's tools in base/.  Nothing protects
        a branch check-results yet, so a pass pushed there must not skip the proof."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = repo(t)
            t.write("proofs/%s/plain_halts/Proof.v" % UNIT, "Theorem x : True. Proof. exact I. Qed.\n")
            head = commit(t)
            remote, _clone = self.workflow(t, d)
            os.makedirs(os.path.join(d, "base"))
            os.symlink(TOOLS, os.path.join(d, "base", "tools"))
            got, output = self.run_step(d, "pr.yml", d, KIND="maintainer", BASE=base, ROUTED="true")
            self.assertEqual((got["units"], "units=1\n" in output), ([UNIT], True), output)
            key = next(r["key"] for r in got["parts"] if r["check"])
            self.record(t, remote, head, [(UNIT, "build", key)])
            got, output = self.run_step(d, "pr.yml", d, KIND="maintainer", BASE=base, ROUTED="true")
            self.assertEqual((got["units"], "units=1\n" in output), ([UNIT], True), output)

    def pr_job(self, t, d, event, event_base, job="plan", **base_env):
        """pr.yml's plan or lint job as GitHub runs it for a push to main or a merge queue group (KIND release) whose
        head is t's last commit and whose EVENT_BASE is event_base: its base step in a clone one commit deep, whose
        origin holds t's history, with base_env in its environment (the lint job's: the plan job's answers); then,
        for the plan job, its plan and reach steps, with this tools/ in place of the base worktree's (the fixture's
        tools/ are stand-ins).  (the base step's exit, the output of the steps, the outputs they wrote, plan.json for
        the plan job or the changed paths for the lint job; None when the base step failed)."""
        path = os.path.join(REPO, ".github", "workflows", "pr.yml")
        if not os.path.exists(path):
            self.skipTest("no .github/workflows/pr.yml beside tools/oft")
        workflow = yamlio.load_file(path)
        steps = {s.get("id"): s for s in workflow["jobs"][job]["steps"]}
        remote = os.path.join(d, "remote.git")
        subprocess.run(GIT + ["clone", "-q", "--bare", t.root, remote], env=GIT_ENV, check=True)
        subprocess.run(GIT + ["clone", "-q", "--depth=1", "file://" + remote, os.path.join(d, "head")], env=GIT_ENV,
                       check=True)
        os.mkdir(os.path.join(d, "bin"))
        with open(os.path.join(d, "bin", "python"), "w") as f:
            f.write('#!/bin/sh\nexec "%s" "$@"\n' % sys.executable)
        os.chmod(os.path.join(d, "bin", "python"), 0o755)
        tmp = os.path.join(d, "runner-temp")
        os.mkdir(tmp)
        out = os.path.join(tmp, "output")
        env = dict(GIT_ENV, PATH=os.path.join(d, "bin") + os.pathsep + os.environ["PATH"], RUNNER_TEMP=tmp,
                   GITHUB_OUTPUT=out, GITHUB_STEP_SUMMARY=os.path.join(tmp, "summary"), GITHUB_WORKSPACE=d,
                   GITHUB_EVENT_NAME=event, EVENT_BASE=event_base, KIND="release", PYTHONDONTWRITEBYTECODE="1")

        def run(step, **more):
            with open(os.path.join(tmp, step + ".sh"), "w") as f:
                f.write(steps[step]["run"])
            return subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", os.path.join(tmp, step + ".sh")],
                                  cwd=d, env=dict(env, **more), capture_output=True, text=True)

        def outputs():
            with open(out) as f:
                return dict(line.rstrip("\n").split("=", 1) for line in f if "=" in line)

        r = run("base", **base_env)
        said = r.stdout + r.stderr
        if r.returncode != 0:
            return r.returncode, said, {}, None
        got = outputs()
        if job == "lint":
            with open(os.path.join(tmp, "changed.txt")) as f:
                return 0, said, got, f.read().splitlines()
        shutil.rmtree(os.path.join(d, "base", "tools"))
        os.symlink(TOOLS, os.path.join(d, "base", "tools"))
        for step in ("plan", "reach"):
            r = run(step, BASE=got["base"], ROUTED=got["routed"])
            said += r.stdout + r.stderr
            self.assertEqual(r.returncode, 0, said)
        with open(os.path.join(tmp, "plan.json")) as f:
            return 0, said, outputs(), json.load(f)

    def pr_plan_job(self, t, d, event, event_base):
        return self.pr_job(t, d, event, event_base, "plan")

    def every_unit(self, t):
        return sorted({unit for unit, _part in keys.wanted(facts.load(t.root))})

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_a_push_of_changelog_md_alone_plans_nothing_and_no_repository_lint(self):
        """A push to main is routed by its own diff from main before the push: CHANGELOG.md is read by no check, no
        test and no control, so the run plans no harness, and neither the tools' tests, their whole-tree lint nor the
        controls run."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.released(t)
            t.write("CHANGELOG.md", "## 2026.11.0\n\nnothing\n")
            commit(t)
            rc, output, got, plan_json = self.pr_plan_job(t, d, "push", base)
            self.assertEqual(rc, 0, output)
            self.assertEqual((plan_json["units"], plan_json["jobs"]), ([], []), output)
            self.assertEqual({k: got.get(k) for k in ("base", "routed", "units", "repository_lint", "tests", "controls")},
                             {"base": base, "routed": "true", "units": "0", "repository_lint": "false",
                              "tests": "false", "controls": "false"}, output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_a_merge_queue_group_that_changes_one_unit_plans_that_unit(self):
        """A merge queue group is routed by its diff from the queue's base: one changed proof plans its own unit's
        build, and nothing else runs."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.released(t)
            t.write("proofs/%s/plain_halts/Proof.v" % CX_UNIT, "(* another stand-in *)\n")
            commit(t)
            rc, output, got, plan_json = self.pr_plan_job(t, d, "merge_group", base)
            self.assertEqual(rc, 0, output)
            self.assertEqual(plan_json["units"], [CX_UNIT], output)
            self.assertEqual([(r["unit"], r["part"]) for r in plan_json["parts"] if r["check"]], [(CX_UNIT, "build")])
            self.assertEqual({k: got.get(k) for k in ("routed", "units", "repository_lint", "tests", "controls")},
                             {"routed": "true", "units": "1", "repository_lint": "false", "tests": "false",
                              "controls": "false"}, output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_a_push_with_no_base_to_compare_with_plans_every_part(self):
        """A push that made the branch (before: all zeros) has no base to diff against, and a push whose base cannot
        be fetched (a force push that dropped it) has none to read: each is a change of every path, judged by its own
        tools, and runs in full: every part planned, the tools' tests with their whole-tree lint, and the controls."""
        for name, before in (("made the branch", "0" * 40), ("a base the remote does not have", "1" * 40)):
            with self.subTest(case=name), tree() as t, tempfile.TemporaryDirectory() as d:
                self.released(t)
                t.write("CHANGELOG.md", "## 2026.11.0\n\nnothing\n")
                head = commit(t)
                rc, output, got, plan_json = self.pr_plan_job(t, d, "push", before)
                self.assertEqual(rc, 0, output)
                self.assertEqual(plan_json["units"], self.every_unit(t), output)
                self.assertEqual(sorted((r["unit"], r["part"]) for r in plan_json["parts"] if r["check"]),
                                 sorted(keys.wanted(facts.load(t.root))), output)
                self.assertEqual({k: got.get(k) for k in ("base", "routed", "repository_lint", "tests", "controls")},
                                 {"base": head, "routed": "false", "repository_lint": "true", "tests": "true",
                                  "controls": "true"}, output)
                self.assertIn("every part is planned", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_a_merge_queue_group_whose_base_cannot_be_fetched_fails(self):
        """A merge queue group is judged by its base's tools: without that base it fails rather than judge the group
        by the tools the group brings."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            self.released(t)
            t.write("CHANGELOG.md", "## 2026.11.0\n\nnothing\n")
            commit(t)
            rc, output, _got, plan_json = self.pr_plan_job(t, d, "merge_group", "1" * 40)
            self.assertNotEqual(rc, 0, output)
            self.assertIsNone(plan_json)
            self.assertIn("cannot be fetched", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_a_push_that_changes_the_workflows_runs_lint_tests_and_controls_but_no_second_whole_tree_lint(self):
        """A change under .github/ runs as the change has it, so the tools' tests and the controls run in full; it
        leaves the tools the base's, so the tests' whole-tree lint would repeat the lint job's and does not run; no
        content key holds a workflow, so it plans no harness."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            t.write(".github/workflows/pr.yml", "# a workflow\n")
            base = self.released(t)
            t.write(".github/workflows/pr.yml", "# a workflow, changed\n")
            commit(t)
            rc, output, got, plan_json = self.pr_plan_job(t, d, "push", base)
            self.assertEqual(rc, 0, output)
            self.assertEqual(plan_json["units"], [], output)
            self.assertEqual({k: got.get(k) for k in ("routed", "units", "repository_lint", "tests", "controls")},
                             {"routed": "true", "units": "0", "repository_lint": "false", "tests": "true",
                              "controls": "true"}, output)

    # The files the farm suites of pr.yml's reach step read (the farm runner's tests and the N6 driver's), a tool under
    # dev/stream/ neither reads, and a stand-in for the head's checker, which the reach step runs for the hunk rows of a
    # change under dev/stream/: this one writes none.
    FARM_TREE = {"dev/stream/bin/ossv-job": "# the route\n", "dev/stream/bin/ossv-job-farm": "# the runner\n",
                 "dev/stream/bin/test_ossv_job_farm.py": "# its tests\n", "dev/stream/conftest.py": "# conftest\n",
                 "dev/stream/pyproject.toml": "# project\n", "dev/stream/uv.lock": "# lock\n",
                 "dev/stream/bin/ossv-n6-farm": "# the N6 driver\n", "dev/stream/bin/ossv-n6-pod": "# its pod\n",
                 "dev/stream/bin/ossv-n6-shards": "# its shards\n", "dev/stream/bin/test_ossv_n6.py": "# its tests\n",
                 "dev/stream/bin/ossv-say": "# a tool no farm suite runs\n",
                 "dev/stream/bin/ossv-tools-check": "import sys\n"}
    FARM_WORKFLOW = ("# the workflow\njobs:\n  farm_tests:\n    runs-on: ubuntu-24.04\n"
                     "  stream_tools:\n    runs-on: ubuntu-24.04\n")
    JOB_FARM = {"test_ossv_job_farm.py": 6}
    N6 = {"test_ossv_n6.py": 1}
    BOTH = dict(JOB_FARM, **N6)

    def farm_answer(self, event, change, tree_files=None, workflow=None):
        """The reach step's answers for a push or merge queue group that writes `change` (path: text) over a released
        tree holding FARM_TREE (or `tree_files`) and `workflow` (FARM_WORKFLOW) as its pr.yml: farm_tests, the legs as
        {file: count} (each file's legs checked to be indices 0 to count - 1 of that count), stream_tools, and the
        output."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            for rel, text in dict(self.FARM_TREE if tree_files is None else tree_files,
                                  **{".github/workflows/pr.yml": workflow or self.FARM_WORKFLOW}).items():
                t.write(rel, text)
            base = self.released(t)
            for rel, text in change.items():
                t.write(rel, text)
            commit(t)
            rc, output, got, _plan_json = self.pr_plan_job(t, d, event, base)
            self.assertEqual(rc, 0, output)
            legs = {}
            for leg in json.loads(got["farm_legs"]):
                legs.setdefault(leg["file"], []).append((leg["index"], leg["count"]))
            for file, got_legs in legs.items():
                self.assertEqual(got_legs, [(i, len(got_legs)) for i in range(len(got_legs))], output)
            self.assertEqual(got["farm_tests"], "true" if legs else "false", output)
            return got["farm_tests"], {file: len(v) for file, v in legs.items()}, got.get("stream_tools"), output

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_each_farm_suite_runs_when_a_file_it_reads_changes_and_only_then(self):
        """Each file a farm suite reads runs that suite's legs, on a push and on a merge queue group alike: the N6
        driver's own files the N6 suite, the farm runner's tests the farm runner's, and the route, the runner and
        pytest's files both -- bin/ossv-job is the submitter both drivers run, and the N6 driver reaches it as its
        own sibling.  Another tool under dev/stream/ runs the stream tools' check and no suite."""
        cases = {"dev/stream/bin/ossv-job": self.BOTH, "dev/stream/bin/test_ossv_job_farm.py": self.JOB_FARM,
                 "dev/stream/bin/ossv-job-farm": self.BOTH, "dev/stream/conftest.py": self.BOTH,
                 "dev/stream/pyproject.toml": self.BOTH, "dev/stream/uv.lock": self.BOTH,
                 "dev/stream/bin/ossv-n6-farm": self.N6, "dev/stream/bin/ossv-n6-pod": self.N6,
                 "dev/stream/bin/ossv-n6-shards": self.N6, "dev/stream/bin/test_ossv_n6.py": self.N6}
        for rel, want in cases.items():
            with self.subTest(path=rel):
                farm, legs, stream, output = self.farm_answer("push", {rel: "# changed\n"})
                self.assertEqual((farm, legs, stream), ("true", want, "true"), output)
                for file in want:
                    self.assertIn("the tests of bin/%s run in %d leg(s) (a file they read changed)"
                                  % (file, want[file]), output)
        farm, legs, stream, output = self.farm_answer("merge_group", {"dev/stream/bin/ossv-n6-pod": "# changed\n"})
        self.assertEqual((farm, legs, stream), ("true", self.N6, "true"), output)
        self.assertIn("nothing the tests of bin/test_ossv_job_farm.py read changed: they do not run", output)
        farm, legs, stream, output = self.farm_answer("push", {"dev/stream/bin/ossv-say": "# changed\n"})
        self.assertEqual((farm, legs, stream), ("false", {}, "true"), output)
        self.assertIn("nothing the tests of bin/test_ossv_n6.py read changed: they do not run", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_a_change_to_pr_yml_runs_every_farm_suite_only_when_it_changes_their_job_or_table(self):
        """pr.yml's farm_tests job, parsed, and the reach step's farm suites table, at the head against the base's: a
        change to either runs every suite, and a change to another job or to a comment does not.  A job the base did
        not have is a change.  A suite whose file the tree does not hold (the public repository holds no dev/stream/)
        runs nothing."""
        farm_changed = self.FARM_WORKFLOW.replace("  farm_tests:\n    runs-on: ubuntu-24.04\n",
                                                  "  farm_tests:\n    runs-on: ubuntu-22.04\n")
        stream_changed = self.FARM_WORKFLOW.replace("  stream_tools:\n    runs-on: ubuntu-24.04\n",
                                                    "  stream_tools:\n    runs-on: ubuntu-22.04\n")
        without_farm = "# the workflow\njobs:\n  stream_tools:\n    runs-on: ubuntu-24.04\n"
        table = "        run: |\n          # farm suites\n          farm_suites=(\n%s          )\n" \
                "          # end of farm suites\n"
        with_table = self.FARM_WORKFLOW + "  plan:\n    steps:\n      - id: reach\n" + table % "            'a 1 b'\n"
        table_changed = with_table.replace("'a 1 b'", "'a 2 b'")
        cases = (("the farm_tests job", self.FARM_WORKFLOW, farm_changed, "true"),
                 ("a farm_tests job the base did not have", without_farm, self.FARM_WORKFLOW, "true"),
                 ("the farm suites table", with_table, table_changed, "true"),
                 ("another job", self.FARM_WORKFLOW, stream_changed, "false"),
                 ("a comment", self.FARM_WORKFLOW,
                  self.FARM_WORKFLOW.replace("# the workflow", "# the workflow, again"), "false"))
        for name, before, after, want in cases:
            with self.subTest(change=name):
                self.assertNotEqual(before, after)
                farm, legs, stream, output = self.farm_answer("merge_group", {".github/workflows/pr.yml": after},
                                                              workflow=before)
                self.assertEqual((farm, legs, stream), (want, self.BOTH if want == "true" else {}, "false"), output)
                if want == "true":
                    self.assertIn("the tests of bin/test_ossv_n6.py run in 1 leg(s) (the farm_tests job or its table "
                                  "changed)", output)
        farm, legs, stream, output = self.farm_answer("push", {".github/workflows/pr.yml": farm_changed},
                                                      tree_files={})
        self.assertEqual((farm, legs, stream), ("false", {}, "false"), output)
        only_farm = {k: v for k, v in self.FARM_TREE.items() if "n6" not in k}
        farm, legs, stream, output = self.farm_answer("push", {".github/workflows/pr.yml": farm_changed},
                                                      tree_files=only_farm)
        self.assertEqual((farm, legs, stream), ("true", self.JOB_FARM, "false"), output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_lint_job_takes_the_plan_job_s_base_and_lists_the_same_paths(self):
        """The plan job decides the base and whether the change is routed, once; the lint job's base step takes both
        from its outputs (it routes nothing itself) and lists the paths with the plan's listing text, so it lints the
        change the plan planned: a merge queue group by its diff, a push with no base to compare with as a change of
        every path judged against itself.  An answer it cannot read, or a routed base it cannot fetch, fails lint."""
        path = os.path.join(REPO, ".github", "workflows", "pr.yml")
        if not os.path.exists(path):
            self.skipTest("no .github/workflows/pr.yml beside tools/oft")
        jobs = yamlio.load_file(path)["jobs"]

        def base_step(job):
            return next(s for s in jobs[job]["steps"] if s.get("id") == "base")

        def listing(job):
            found = re.findall(r"# routing\n(.*?)# end of routing\n", base_step(job)["run"], re.S)
            self.assertEqual(len(found), 1, job)
            return found[0]
        self.assertEqual(listing("lint"), listing("plan"))
        self.assertEqual(base_step("lint")["env"], {"PLAN_BASE": "${{ needs.plan.outputs.base }}",
                                                   "PLAN_ROUTED": "${{ needs.plan.outputs.routed }}"})
        self.assertEqual(jobs["plan"]["outputs"]["routed"], "${{ steps.base.outputs.routed }}")
        self.assertIn("plan", jobs["lint"]["needs"])
        # lint routes nothing of its own: no event base, no merge commit's parents, no API
        for word in ("EVENT_BASE", "cat-file -p HEAD", "gh api", "GITHUB_EVENT_NAME"):
            self.assertNotIn(word, base_step("lint")["run"], word)
        for name, event, before in (("a merge queue group", "merge_group", None),
                                    ("before all zeros", "push", "0" * 40),
                                    ("a base the remote does not have", "push", "1" * 40)):
            with self.subTest(case=name), tree() as t:
                base = self.released(t)
                t.write("proofs/%s/plain_halts/Proof.v" % CX_UNIT, "(* another stand-in *)\n")
                commit(t)
                with tempfile.TemporaryDirectory() as d:
                    rc, output, planned, _plan = self.pr_job(t, d, event, before or base, job="plan")
                    self.assertEqual(rc, 0, output)
                    with open(os.path.join(d, "runner-temp", "changed.txt")) as f:
                        plan_changed = f.read().splitlines()
                with tempfile.TemporaryDirectory() as d:
                    rc, output, got, changed = self.pr_job(t, d, event, "", job="lint", PLAN_BASE=planned["base"],
                                                           PLAN_ROUTED=planned["routed"])
                    self.assertEqual(rc, 0, output)
                    self.assertEqual((got["base"], got["routed"]), (planned["base"], planned["routed"]), output)
                    self.assertEqual(changed, plan_changed)
        with tree() as t:
            base = self.released(t)
            t.write("proofs/%s/plain_halts/Proof.v" % CX_UNIT, "(* another stand-in *)\n")
            head = commit(t)
            for name, plan_base, routed, said in (("no base", "", "true", "the plan named no base"),
                                                  ("routed left unset", base, "", "neither true nor false"),
                                                  ("routed of another word", base, "yes", "neither true nor false"),
                                                  ("not routed, yet a base", base, "false", "the plan routed nothing"),
                                                  ("a base the remote does not have", "1" * 40, "true",
                                                   "cannot be fetched")):
                with self.subTest(case=name), tempfile.TemporaryDirectory() as d:
                    rc, output, _got, changed = self.pr_job(t, d, "merge_group", "", job="lint", PLAN_BASE=plan_base,
                                                            PLAN_ROUTED=routed)
                    self.assertNotEqual(rc, 0, output)
                    self.assertIn(said, output)
            with tempfile.TemporaryDirectory() as d:
                rc, output, got, changed = self.pr_job(t, d, "push", "", job="lint", PLAN_BASE=head,
                                                       PLAN_ROUTED="false")
                self.assertEqual((rc, got.get("routed")), (0, "false"), output)

    def release_check(self, t, d, python=None, **env):
        """release-check.yml's plan step, run in a clone of t's last commit with this tools/: (its plan, outputs).
        env carries what the workflow puts in the job's environment: EVENT_BASE, the commit the push is judged
        against, and GITHUB_EVENT_NAME, which is a push when EVENT_BASE is given and a dispatch (every part
        planned) otherwise, unless env names it.  python, if given, is the text of the `python` the step runs (in
        place of workflow()'s, which runs this one)."""
        _remote, clone = self.workflow(t, d)
        if python is not None:
            with open(os.path.join(d, "bin", "python"), "w") as f:
                f.write(python)
        shutil.rmtree(os.path.join(clone, "tools"))
        os.symlink(TOOLS, os.path.join(clone, "tools"))
        env.setdefault("GITHUB_EVENT_NAME", "push" if "EVENT_BASE" in env else "workflow_dispatch")
        return self.run_step(d, "release-check.yml", clone, **env)

    def assertDeferred(self, got, output):
        """A push that changes shared tooling: no plan.json, no part, and the deferral."""
        self.assertIsNone(got, output)
        self.assertEqual(sorted(output.splitlines()), ["deferred=true", "full=false", "plan=[]", "units=0"])

    def released(self, t):
        """A release tree's first commit: a committed proof of CX_UNIT and the fixture's finding on UNIT, so that
        both harnesses have a part to check."""
        proved = "%s/plain_halts" % CX_UNIT
        st = next(st for h in facts.load(t.root).harnesses() for st in h.statements.values() if st.id == proved)
        t.write("proofs/%s/Proof.v" % proved, "(* stand-in *)\n")
        t.put_yaml("proofs/%s/proof.yaml" % proved, {
            "schema": "oss-fuzz-theorems/proof/1", "proves": proved, "fingerprint": st.fingerprint})
        return repo(t)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_checks_every_part_of_each_harness_with_a_proof_or_a_finding(self):
        """A harness with a committed finding is planned, also when it withholds every build and has no proof, and
        only the harnesses with published builds are built; no other harness is planned."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            proved = "%s/plain_halts" % CX_UNIT
            st = next(st for h in facts.load(t.root).harnesses() for st in h.statements.values() if st.id == proved)
            t.write("proofs/%s/Proof.v" % proved, "(* stand-in *)\n")
            t.put_yaml("proofs/%s/proof.yaml" % proved, {
                "schema": "oss-fuzz-theorems/proof/1", "proves": proved, "fingerprint": st.fingerprint})
            withhold_checksum_fuzzer(t)
            repo(t)
            got, output = self.release_check(t, d)
            self.assertEqual(got["units"], [CX_UNIT, UNIT])
            self.assertEqual(got["check_units"], [CX_UNIT])
            self.assertEqual(" ".join(j["findings"] for j in got["jobs"]).split(), [UNIT])
            self.assertEqual(sorted((r["unit"], r["part"]) for r in got["parts"] if r["check"]),
                             [up for up in keys.wanted(facts.load(t.root)) if up[0] in (CX_UNIT, UNIT)])
            self.assertIn("units=2\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_plans_findings_in_a_tree_with_no_proofs(self):
        """The cross-model review's case: a tree with a finding and no proofs/ directory plans that finding."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            repo(t)
            self.assertFalse(os.path.exists(t.path("proofs")))
            got, output = self.release_check(t, d)
            self.assertEqual(got["units"], [UNIT])
            self.assertEqual(" ".join(j["findings"] for j in got["jobs"]).split(), [UNIT])
            self.assertIn("units=1\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_plans_nothing_for_a_changelog_or_docs_only_commit(self):
        """A commit that changes only CHANGELOG.md or docs/ changes no key, so it plans no proof job."""
        for path, text in (("CHANGELOG.md", "## 2026.11.0\n\nnothing\n"), ("docs/why.md", "why\n")):
            with self.subTest(path=path), tree() as t, tempfile.TemporaryDirectory() as d:
                base = self.released(t)
                t.write(path, text)
                commit(t)
                got, output = self.release_check(t, d, EVENT_BASE=base)
                self.assertEqual((got["units"], got["jobs"]), ([], []), output)
                self.assertIn("units=0\n", output)
                self.assertIn("full=false\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_checks_the_one_unit_whose_proof_changed(self):
        """A commit that changes one unit's proofs re-checks that unit's build, and nothing else."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.released(t)
            t.write("proofs/%s/plain_halts/Proof.v" % CX_UNIT, "(* another stand-in *)\n")
            commit(t)
            got, output = self.release_check(t, d, EVENT_BASE=base)
            self.assertEqual(got["units"], [CX_UNIT], output)
            self.assertEqual([(r["unit"], r["part"]) for r in got["parts"] if r["check"]], [(CX_UNIT, "build")])
            self.assertIn("units=1\n", output)
            self.assertIn("full=false\n", output)
            self.assertIn("deferred=false\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_leaves_a_change_through_shared_files_to_the_release_gate(self):
        """theories/ is in every build key, yet no harness's own file: a push that changes it alone checks nothing
        here and lists both harnesses as deferred; with a proof of one harness beside it, only that harness is
        checked here, and the other is deferred.  A dispatch of the same commit checks every part."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.released(t)
            t.write("theories/Extra.v", "Definition x := 0.\n")
            commit(t)
            got, output = self.release_check(t, d, EVENT_BASE=base)
            self.assertEqual((got["units"], got["jobs"]), ([], []), output)
            self.assertIn("units=0\n", output)
            self.assertIn("deferred=true\n", output)
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.released(t)
            t.write("theories/Extra.v", "Definition x := 0.\n")
            t.write("proofs/%s/plain_halts/Proof.v" % CX_UNIT, "(* another stand-in *)\n")
            commit(t)
            got, output = self.release_check(t, d, EVENT_BASE=base)
            self.assertEqual(got["units"], [CX_UNIT], output)
            self.assertIn("units=1\n", output)
            self.assertIn("deferred=true\n", output)
            with tempfile.TemporaryDirectory() as d2:
                got, output = self.release_check(t, d2, GITHUB_EVENT_NAME="workflow_dispatch")
            self.assertEqual(got["units"], [CX_UNIT, UNIT], output)
            self.assertIn("full=true\n", output)
            self.assertIn("deferred=false\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_plans_nothing_for_a_release_version_and_date(self):
        """release.yaml's version and date name no input of a check: the release commit itself plans no proof job."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.released(t)
            release = t.yaml("release.yaml")
            release["release"], release["date"] = "2026.12.0", "2026-12-07"
            t.put_yaml("release.yaml", release)
            commit(t)
            got, output = self.release_check(t, d, EVENT_BASE=base)
            self.assertEqual((got["units"], got["jobs"]), ([], []), output)
            self.assertIn("units=0\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_defers_a_new_checker_pin(self):
        """The checker image is in every build key, and in no harness's own file: a new pin checks nothing here, and
        both builds are left to the publishing gate."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.released(t)
            release = t.yaml("release.yaml")
            release["images"]["checker"] = "ghcr.io/theorem-labs/oss-fuzz-theorems-checker@sha256:" + "4" * 64
            t.put_yaml("release.yaml", release)
            commit(t)
            got, output = self.release_check(t, d, EVENT_BASE=base)
            self.assertEqual((got["units"], got["jobs"]), ([], []), output)
            self.assertIn("units=0\n", output)
            self.assertIn("full=false\n", output)
            self.assertIn("deferred=true\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_runs_no_check_for_a_push_that_changes_shared_tooling(self):
        """No key can tell a change to the tools the check job runs (one tools/ id on both sides of a comparison), so
        a dispatch plans every part outright; a push that changes them, toolchain/ or keys.py, or that has no base to
        compare with, runs no check job here and defers to the publishing gate: tooling alone checks nothing."""
        for path, text in (("tools/oft/check.py", "check, with a fix\n"),
                           ("toolchain/runner.Dockerfile", "FROM scratch\n"),
                           ("tools/oft/keys.py", "keys, with a narrower checker\n")):
            with self.subTest(path=path), tree() as t, tempfile.TemporaryDirectory() as d:
                base = self.released(t)
                t.write(path, text)
                commit(t)
                self.assertDeferred(*self.release_check(t, d, EVENT_BASE=base))
        with tree() as t, tempfile.TemporaryDirectory() as d:
            self.released(t)
            self.assertDeferred(*self.release_check(t, d, EVENT_BASE="0" * 40))
        with tree() as t, tempfile.TemporaryDirectory() as d:
            self.released(t)
            t.write("tools/oft/check.py", "check, with a fix\n")
            commit(t)
            got, output = self.release_check(t, d)
            self.assertEqual(got["units"], [CX_UNIT, UNIT], output)
            self.assertEqual(sorted((r["unit"], r["part"]) for r in got["parts"] if r["check"]),
                             [up for up in keys.wanted(facts.load(t.root)) if up[0] in (CX_UNIT, UNIT)])
            self.assertIn("units=2\n", output)
            self.assertIn("full=true\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_checks_its_own_harness_in_full_beside_shared_tooling(self):
        """A push that changes the checker (or toolchain/) and one harness's proof checks that harness here, every
        part of it with this commit's checker, and defers every other harness: a proof change does not ride in
        unchecked behind a tool change."""
        for path, text in (("tools/oft/check.py", "check, with a fix\n"),
                           ("toolchain/runner.Dockerfile", "FROM scratch\n")):
            with self.subTest(path=path), tree() as t, tempfile.TemporaryDirectory() as d:
                base = self.released(t)
                t.write(path, text)
                t.write("proofs/%s/plain_halts/Proof.v" % CX_UNIT, "(* another stand-in *)\n")
                commit(t)
                got, output = self.release_check(t, d, EVENT_BASE=base)
                self.assertEqual(got["units"], [CX_UNIT], output)
                self.assertEqual(sorted((r["unit"], r["part"]) for r in got["parts"] if r["check"]),
                                 [up for up in keys.wanted(facts.load(t.root)) if up[0] == CX_UNIT])
                self.assertIn("units=1\n", output)
                self.assertIn("full=false\n", output)
                self.assertIn("deferred=true\n", output)

    def pinned_push(self, t, extra=None, check="deferred"):
        """A base that pins, for a deferred check, the tree of the push after it, and that push: it changes the
        checker and a proof (so it would plan a part here), and, with extra, also writes that file, which the pinned
        tree does not hold.  The base."""
        first = self.released(t)

        def change():
            t.write("tools/oft/check.py", "check, with a fix\n")
            t.write("proofs/%s/plain_halts/Proof.v" % CX_UNIT, "(* another stand-in *)\n")
        change()
        pinned = tree_digest(t, commit(t))
        git(t, "reset", "-q", "--hard", first)
        t.write("tools/oft/migration-pin.yaml", deferred_pin(pinned, check))
        base = commit(t)
        change()
        if extra:
            t.write(extra, "one more file\n")
        head = commit(t)
        self.assertEqual(tree_digest(t, head) == pinned, extra is None)
        return base

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_release_check_defers_the_pinned_tree_push(self):
        """The push of the join's merge commit (plan D12): main before it pins `check: deferred` and this very tree,
        so the step plans nothing, defers, and names the check of record, whatever the push changes."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.pinned_push(t)
            got, output = self.release_check(t, d, EVENT_BASE=base)
            self.assertIsNone(got, output)
            self.assertEqual(sorted(output.splitlines()),
                             ["check_of_record=a VM run of every part at the merge commit", "deferred=true",
                              "full=false", "plan=[]", "units=0"])
            self.assertIn("### no part checked here: the tree the base pins for a deferred check (release/join)",
                          self.said)
            self.assertIn("The check of record: a VM run of every part at the merge commit", self.said)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_release_check_does_not_defer_another_tree(self):
        """The same pin, a pushed tree with one more file: planned as today (#389), its own harness in full beside the
        checker change; a pin whose check is empty, and a dispatch, are planned as today too."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.pinned_push(t, extra="docs/more.md")
            got, output = self.release_check(t, d, EVENT_BASE=base)
            self.assertEqual(got["units"], [CX_UNIT], output)
            self.assertNotIn("the tree the base pins", self.said)
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.pinned_push(t, check="")
            got, output = self.release_check(t, d, EVENT_BASE=base)
            self.assertEqual(got["units"], [CX_UNIT], output)
        with tree() as t, tempfile.TemporaryDirectory() as d:
            self.pinned_push(t)
            got, output = self.release_check(t, d)
            self.assertIn("full=true\n", output)
            self.assertEqual(got["units"], [CX_UNIT, UNIT], output)

    def failed_release_check(self, t, d, base, git_show_fails=False):
        """release-check.yml's plan step for the push after base, which must fail: its output.  With git_show_fails,
        the step's git cannot read the base's pin blob (and runs as git otherwise)."""
        _remote, clone = self.workflow(t, d)
        shutil.rmtree(os.path.join(clone, "tools"))
        os.symlink(TOOLS, os.path.join(clone, "tools"))
        if git_show_fails:
            with open(os.path.join(d, "bin", "git"), "w") as f:
                f.write('#!/bin/sh\ncase "$1 $2" in "show %s:tools/oft/migration-pin.yaml")\n'
                        '  echo "fatal: unable to read the blob" >&2; exit 128 ;; esac\nexec %s "$@"\n'
                        % (base, shlex.quote(shutil.which("git"))))
            os.chmod(os.path.join(d, "bin", "git"), 0o755)
        with self.assertRaises(AssertionError) as raised:
            self.run_step(d, "release-check.yml", clone, EVENT_BASE=base, GITHUB_EVENT_NAME="push")
        return str(raised.exception)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_release_check_fails_a_deferred_pin_of_another_word(self):
        """A pin's `check` is read exactly: another word, or `deferred` with a blank, fails the step."""
        for check in ("later", "deferred ", " deferred"):
            with self.subTest(check=check), tree() as t, tempfile.TemporaryDirectory() as d:
                base = self.pinned_push(t, check=check)
                self.assertIn("neither deferred nor empty", self.failed_release_check(t, d, base))

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_release_check_fails_when_the_base_s_pin_cannot_be_read(self):
        """The base's tree lists the pin and git cannot read its blob: the step fails, rather than plan the push as if
        nothing were pinned (for the join's push, every part of every unit on hosted runners)."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.pinned_push(t)
            self.assertIn("the base's migration pin cannot be read",
                          self.failed_release_check(t, d, base, git_show_fails=True))

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_plans_by_key_for_a_change_to_tools_no_check_opens(self):
        """A change under tools/ to files keys.NOT_THE_CHECKER names (the lint, the planner, the tests) leaves
        keys.checker as it was, so the step plans by key, and a commit that changes nothing else plans no proof:
        every such commit used to re-check every part."""
        for paths in (("tools/oft/lint.py",), ("tools/oft/plan.py", "tools/oft/tests/test_x.py")):
            with self.subTest(paths=paths), tree() as t, tempfile.TemporaryDirectory() as d:
                base = self.released(t)
                for p in paths:
                    t.write(p, "# changed\n")
                commit(t)
                got, output = self.release_check(t, d, EVENT_BASE=base)
                self.assertEqual((got["units"], got["jobs"]), ([], []), output)
                self.assertIn("units=0\n", output)
                self.assertIn("full=false\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_defers_when_the_checker_id_cannot_be_computed(self):
        """A base with no tools/oft/ has no checker id (keys.NoKey): a push fails closed to no hosted check, and the
        publishing gate's run."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            first = self.released(t)
            shutil.rmtree(t.path("tools", "oft"))
            base = commit(t)
            git(t, "checkout", first, "--", "tools")
            commit(t)
            self.assertDeferred(*self.release_check(t, d, EVENT_BASE=base))

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_defers_when_neither_checker_id_can_be_computed(self):
        """Both ids failing must not read as two equal ids (an empty string each): a `python` that fails whenever it
        is asked for keys.checker, and runs this one otherwise, defers the push."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.released(t)
            t.write("tools/oft/lint.py", "# changed\n")
            commit(t)
            shim = ('#!/bin/sh\ncase "$*" in *keys.checker*) echo "no checker id" >&2; exit 1 ;; esac\n'
                    'exec %s "$@"\n' % shlex.quote(sys.executable))
            self.assertDeferred(*self.release_check(t, d, python=shim, EVENT_BASE=base))

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_plans_no_proof_for_a_workflow_only_commit(self):
        """A commit under .github/workflows/, alone or with a CHANGELOG note (the shape of the commit that carries
        this router to the public repository), plans no proof: pr.yml's run of the same push runs the tools' own
        tests, which read these workflow files, and the controls in full for any change under .github/."""
        for paths in ((".github/workflows/release-check.yml",),
                      (".github/workflows/release-check.yml", "CHANGELOG.md")):
            with self.subTest(paths=paths), tree() as t, tempfile.TemporaryDirectory() as d:
                for p in paths:
                    t.write(p, "# a note\n")
                base = self.released(t)
                for p in paths:
                    t.write(p, "# a note, changed\n")
                commit(t)
                got, output = self.release_check(t, d, EVENT_BASE=base)
                self.assertEqual((got["units"], got["jobs"]), ([], []), output)
                self.assertIn("units=0\n", output)
                self.assertIn("full=false\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_plans_nothing_for_a_push_the_merge_queue_checked_with_these_tools(self):
        """A push whose every commit passed pr.yml's merge queue run on its own parent (the queue step's answer), and
        whose tools are the ones each of those runs planned with, was planned and checked there with the same keys:
        the plan names no part and names those runs (one commit, and a batch of two).  A push that takes the full plan
        (a change to the checker, or to keys.py, which defines it) is checked here in full whatever the queue found.
        A change to tools/ outside the checker is planned here by key with this commit's tools, since the queue
        planned with the parent's planner; so is a push whose tools/ changed in one commit and back in the next."""
        proof = "proofs/%s/plain_halts/Proof.v" % CX_UNIT
        for checked, runs, commits in (("true", "11", 1), ("true", "11 12", 2), ("false", "", 1), ("", "", 1)):
            with self.subTest(checked=checked, commits=commits), tree() as t, tempfile.TemporaryDirectory() as d:
                base = self.released(t)
                for n in range(commits):
                    t.write(proof, "(* another stand-in, %d *)\n" % n)
                    commit(t)
                got, output = self.release_check(t, d, EVENT_BASE=base, QUEUE_CHECKED=checked, QUEUE_RUNS=runs)
                if checked == "true":
                    self.assertIsNone(got, output)
                    self.assertEqual(sorted(output.splitlines()),
                                     ["deferred=false", "full=false", "plan=[]", "queue_runs=" + runs, "units=0"])
                else:
                    # the queue step did not answer true: the push is planned by its own change
                    self.assertEqual(got["units"], [CX_UNIT], output)
                    self.assertNotIn("queue_runs=", output)
        for name, path, text in (("the checker", "tools/oft/check.py", "check, with a fix\n"),
                                 ("keys.py", "tools/oft/keys.py", "keys, with a narrower checker\n")):
            with self.subTest(change=name), tree() as t, tempfile.TemporaryDirectory() as d:
                base = self.released(t)
                t.write(path, text)
                commit(t)
                self.assertDeferred(*self.release_check(t, d, EVENT_BASE=base, QUEUE_CHECKED="true",
                                                        QUEUE_RUNS="11"))
        # a change to files of tools/ that neither a check nor a plan opens keeps the queue's credit: the lint, and
        # lint-exceptions.yaml, whose licence-pending rows #679 dropped (run 41545320386 re-checked 28 harnesses)
        for path in ("tools/oft/lint-exceptions.yaml", "tools/oft/lint.py", "tools/oft/tests/test_x.py"):
            with self.subTest(keeps=path), tree() as t, tempfile.TemporaryDirectory() as d:
                base = self.released(t)
                t.write(path, "# changed, and read by no check and no plan\n")
                t.write(proof, "(* another stand-in *)\n")
                commit(t)
                got, output = self.release_check(t, d, EVENT_BASE=base, QUEUE_CHECKED="true", QUEUE_RUNS="11")
                self.assertIsNone(got, output)
                self.assertEqual(sorted(output.splitlines()),
                                 ["deferred=false", "full=false", "plan=[]", "queue_runs=11", "units=0"])
        # the planner (plan.PLANNER: __main__.py's cmd_plan, plan.py, pack.py) is no part of the checker, but a plan
        # runs it: a change to it is planned here by key.  The list lives in plan.py, outside the checker, so that
        # setting it re-keys no unit; plan.py is in it, so changing the list loses the credit too.
        self.assertEqual(plan.PLANNER, ("tools/oft/__main__.py", "tools/oft/plan.py", "tools/oft/pack.py"))
        self.assertFalse(hasattr(keys, "PLANNER"))
        for path in plan.PLANNER:
            self.assertTrue(keys.not_the_checker(path), path)
            with self.subTest(planner=path), tree() as t, tempfile.TemporaryDirectory() as d:
                base = self.released(t)
                t.write(path, "# a planner, with a new rule\n")
                commit(t)
                got, output = self.release_check(t, d, EVENT_BASE=base, QUEUE_CHECKED="true", QUEUE_RUNS="11")
                self.assertIsNotNone(got, output)
                self.assertIn("full=false\n", output)
                self.assertNotIn("queue_runs=", output)
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = self.released(t)
            had = os.path.exists(t.path("tools/oft/plan.py"))
            planner = open(t.path("tools/oft/plan.py")).read() if had else None
            t.write("tools/oft/plan.py", "# a planner, with a new rule\n")
            commit(t)
            if had:
                t.write("tools/oft/plan.py", planner)
            else:
                os.remove(t.path("tools/oft/plan.py"))
            t.write(proof, "(* another stand-in *)\n")
            commit(t)
            got, output = self.release_check(t, d, EVENT_BASE=base, QUEUE_CHECKED="true", QUEUE_RUNS="11 12")
            self.assertEqual(got["units"], [CX_UNIT], output)
            self.assertNotIn("queue_runs=", output)

    def test_the_release_check_verdict_reads_no_answer_it_cannot_read(self):
        """release-check's one required check, run as GitHub runs it: it passes a plan that named parts only when the
        check passed, a plan of nothing only when no check ran, merge queue runs only with nothing planned, and a
        deferral only with no full plan and no merge queue runs; an empty or other answer of the plan fails it."""
        path = os.path.join(REPO, ".github", "workflows", "release-check.yml")
        if not os.path.exists(path):
            self.skipTest("no .github/workflows/release-check.yml beside tools/oft")
        wf = yamlio.load_file(path)
        self.assertEqual(wf["jobs"]["plan"]["outputs"]["deferred"], "${{ steps.plan.outputs.deferred }}")
        job = wf["jobs"]["release-check"]
        self.assertEqual(" ".join(job["if"].split()), "always()")
        step = job["steps"][0]
        self.assertEqual(step["env"], {"UNITS": "${{ needs.plan.outputs.units }}",
                                       "FULL": "${{ needs.plan.outputs.full }}",
                                       "DEFERRED": "${{ needs.plan.outputs.deferred }}",
                                       "CHECK_OF_RECORD": "${{ needs.plan.outputs.check_of_record }}",
                                       "QUEUE_RUNS": "${{ needs.plan.outputs.queue_runs }}",
                                       "PLAN_RESULT": "${{ needs.plan.result }}",
                                       "CHECK_RESULT": "${{ needs.check.result }}",
                                       "DRAFTS_LISTED": "${{ needs.plan.outputs.draft_legs != '[]' }}",
                                       "DRAFTS_RESULT": "${{ needs.fetch-drafts.result }}"})

        def verdict(**env):
            # no draft listed, so fetch-drafts was skipped, as the step's own fetch-drafts check requires
            base = dict(UNITS="0", FULL="false", DEFERRED="false", CHECK_OF_RECORD="", QUEUE_RUNS="",
                        PLAN_RESULT="success", CHECK_RESULT="skipped", DRAFTS_LISTED="false", DRAFTS_RESULT="skipped",
                        GITHUB_SERVER_URL="https://github.com", GITHUB_REPOSITORY="example/repository")
            base.update(env)
            r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", step["run"]],
                               env=dict(os.environ, **base), capture_output=True, text=True)
            return r.returncode, r.stdout + r.stderr
        for name, env in (("nothing planned", {}), ("planned and checked", dict(UNITS="3", CHECK_RESULT="success")),
                          ("a full plan checked", dict(UNITS="3", FULL="true", CHECK_RESULT="success")),
                          ("the queue checked it", dict(QUEUE_RUNS="11 12")),
                          ("deferred, nothing planned", dict(DEFERRED="true")),
                          ("deferred, own harnesses checked",
                           dict(DEFERRED="true", UNITS="1", CHECK_RESULT="success")),
                          # the push of the tree main before it pins with a deferred check (plan D12)
                          ("the pinned tree, deferred to its check of record",
                           dict(DEFERRED="true", CHECK_OF_RECORD="a VM run of every part")),
                          # the release line's drafts: listed and fetched
                          ("a draft listed and fetched", dict(UNITS="3", CHECK_RESULT="success", DRAFTS_LISTED="true",
                                                              DRAFTS_RESULT="success"))):
            with self.subTest(case=name):
                rc, out = verdict(**env)
                self.assertEqual(rc, 0, out)
                deferral = "the publishing gate's run on the release commit" in out
                self.assertEqual(deferral, env.get("DEFERRED") == "true" and not env.get("CHECK_OF_RECORD"), out)
                self.assertEqual("the check of record: a VM run of every part" in out, "CHECK_OF_RECORD" in env, out)
        for name, env in (("the plan failed", dict(PLAN_RESULT="failure")), ("no units answer", dict(UNITS="")),
                          ("units not a count", dict(UNITS="x")), ("no full answer", dict(FULL="")),
                          ("no deferred answer", dict(DEFERRED="")), ("a deferred answer of another word",
                                                                      dict(DEFERRED="yes")),
                          ("deferred with a full plan", dict(DEFERRED="true", FULL="true", UNITS="2",
                                                             CHECK_RESULT="success")),
                          ("deferred with merge queue runs", dict(DEFERRED="true", QUEUE_RUNS="11")),
                          ("deferred, a check that failed", dict(DEFERRED="true", UNITS="1", CHECK_RESULT="failure")),
                          ("the pinned tree deferred, yet a part planned",
                           dict(DEFERRED="true", CHECK_OF_RECORD="a VM run", UNITS="1", CHECK_RESULT="success")),
                          ("a full plan of nothing", dict(FULL="true")),
                          ("a check that failed", dict(UNITS="3", CHECK_RESULT="failure")),
                          ("a check that did not run", dict(UNITS="3", CHECK_RESULT="skipped")),
                          ("a check with nothing planned", dict(CHECK_RESULT="success")),
                          ("queue runs with parts planned", dict(QUEUE_RUNS="11", UNITS="2", CHECK_RESULT="success")),
                          ("queue runs with a full plan", dict(QUEUE_RUNS="11", FULL="true", UNITS="2",
                                                               CHECK_RESULT="success")),
                          ("a garbled run list", dict(QUEUE_RUNS="11 x")),
                          ("a draft listed, its fetch failed", dict(DRAFTS_LISTED="true", DRAFTS_RESULT="failure")),
                          ("a draft listed, its fetch did not run", dict(DRAFTS_LISTED="true", DRAFTS_RESULT="skipped")),
                          ("no draft listed, yet fetch-drafts ran", dict(DRAFTS_RESULT="success"))):
            with self.subTest(case=name):
                self.assertEqual(verdict(**env)[0], 1)


def layout_repo(t, new=True):
    """t as repo() makes it, from the fixture with a proof, a proof library, build records, a counterexample and a
    finding (test_layout.old_layout_tree), ported to the per-project layout when new, and rendered; its first
    commit."""
    from oft import port
    from oft.tests.test_layout import old_layout_tree
    old_layout_tree(t)
    if new:
        assert port.port_worktree(t.root, out=io.StringIO()) == 0
    assert t.generate() == 0, t.last_output
    t.write("tools/oft/check.py", "check\n")
    t.write("tools/oft/lint.py", "lint\n")
    t.write(".gitattributes", "* text=auto eol=lf\n")
    git(t, "init", "-q")
    return commit(t)


def files_under(root):
    """{path relative to root: bytes} of every file under root."""
    out = {}
    for dp, _dns, fns in os.walk(root):
        for f in fns:
            with open(os.path.join(dp, f), "rb") as fh:
                out[os.path.relpath(os.path.join(dp, f), root)] = fh.read()
    return out


class LayoutWorkflows(unittest.TestCase):
    """pr.yml's and release-check.yml's steps over a tree in either layout: a change's proofs, counterexamples and
    findings are its folders proofs/, counterexamples/ and findings/ (the old layout) or projects/<p>/<h>/proofs/,
    projects/<p>/<h>/counterexamples/, projects/<p>/<h>/findings/ and projects/<p>/unpatched.yaml (the new)."""

    workflow, run_step, release_check = Plan.workflow, Plan.run_step, Plan.release_check

    def work_step(self, t, d, base):
        """pr.yml's check-job step 'statements from the base; proofs, counterexamples and findings from this change',
        run as GitHub runs it for a maintainer's change in the workspace d: head/ a clone of t's last commit, `base`
        the plan job's base.  (its exit status, its output); d/base is the tree the check reads."""
        path = os.path.join(REPO, ".github", "workflows", "pr.yml")
        if not os.path.exists(path):
            self.skipTest("no .github/workflows/pr.yml beside tools/oft")
        step = next(s for s in yamlio.load_file(path)["jobs"]["check"]["steps"] if s.get("id") == "work")
        self.assertIn("${{ needs.plan.outputs.base }}", step["run"])
        self.workflow(t, d)
        runner = tempfile.mkdtemp(dir=d)
        with open(os.path.join(runner, "work.sh"), "w") as f:
            f.write(step["run"].replace("${{ needs.plan.outputs.base }}", base))
        env = dict(GIT_ENV, GITHUB_WORKSPACE=d, GITHUB_OUTPUT=os.path.join(runner, "output"), KIND="maintainer")
        r = subprocess.run(["bash", "--noprofile", "--norc", "-eo", "pipefail", os.path.join(runner, "work.sh")],
                           cwd=d, env=env, capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr

    def test_a_pull_request_that_changes_only_new_layout_proofs_is_checked_against_the_base_statements(self):
        """D6.  Base: the ported fixture.  Head: Statements.v of zlib/checksum_fuzzer edited and a Proof.v under
        projects/zlib/checksum_fuzzer/proofs/ edited.  The check job's work step leaves the base's Statements.v and
        takes the head's proofs folder; the plan step (KIND maintainer) plans zlib/checksum_fuzzer build with
        'changed: proofs' and no harness change."""
        statements = "projects/%s/Statements.v" % UNIT
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = layout_repo(t)
            was = t.read(statements)
            t.write(statements, was + "(* a statement this change may not make *)\n")
            t.write("projects/%s/proofs/plain_halts/Proof.v" % UNIT, "Theorem x : True. Proof. exact I. Qed.\n")
            commit(t)
            work = os.path.join(d, "work")
            os.mkdir(work)
            rc, out = self.work_step(t, work, base)
            self.assertEqual(rc, 0, out)
            with open(os.path.join(work, "base", statements)) as f:
                self.assertEqual(f.read(), was)
            proofs = os.path.join("projects", UNIT, "proofs")
            self.assertEqual(files_under(os.path.join(work, "base", proofs)),
                             files_under(os.path.join(work, "head", proofs)))
            self.assertIn(b"exact I", files_under(os.path.join(work, "base", proofs))["plain_halts/Proof.v"])
            planned = os.path.join(d, "plan")
            os.mkdir(planned)
            self.workflow(t, planned)
            os.makedirs(os.path.join(planned, "base"))
            os.symlink(TOOLS, os.path.join(planned, "base", "tools"))
            got, output = self.run_step(planned, "pr.yml", planned, KIND="maintainer", BASE=base, ROUTED="true")
            self.assertEqual([(r["unit"], r["part"], r["why"]) for r in got["parts"] if r["check"]],
                             [(UNIT, "build", "changed: proofs")], output)

    def test_the_overlay_deletes_a_proof_the_change_deleted_in_either_layout(self):
        """The change's folder replaces the base's, so a proof the change deleted is not checked from the base's copy:
        the change's last old-layout proof (no proofs/ left at all), a statement folder of the per-project layout, and
        a fuzz target's whole per-project proofs folder.  The statements stay the base's."""
        for name, new, gone in (("old", False, "proofs"),
                                ("new statement", True, "projects/%s/proofs/plain_halts" % UNIT),
                                ("new proofs folder", True, "projects/zlib/api-driver/proofs")):
            with self.subTest(name), tree() as t, tempfile.TemporaryDirectory() as d:
                base = layout_repo(t, new)
                self.assertTrue(os.path.isdir(t.path(gone)))
                shutil.rmtree(t.path(gone))
                commit(t)
                rc, out = self.work_step(t, d, base)
                self.assertEqual(rc, 0, out)
                self.assertFalse(os.path.exists(os.path.join(d, "base", gone)), out)
                self.assertTrue(os.path.isfile(os.path.join(d, "base", "projects", UNIT, "Statements.v")))
                for top in ("proofs", "projects/%s/proofs" % UNIT, "projects/zlib/api-driver/proofs"):
                    self.assertEqual(files_under(os.path.join(d, "base", top)),
                                     files_under(os.path.join(d, "head", top)), top)

    def test_the_overlay_takes_the_change_s_findings_and_unpatched_pins_in_the_new_layout(self):
        """projects/<p>/unpatched.yaml is a file, not a folder: a change that edits it or deletes a fuzz target's
        findings folder has the check read that, not the base's."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            base = layout_repo(t)
            t.write("projects/zlib/unpatched.yaml", t.read("projects/zlib/unpatched.yaml") + "# edited\n")
            shutil.rmtree(t.path("projects/%s/findings" % UNIT))
            commit(t)
            rc, out = self.work_step(t, d, base)
            self.assertEqual(rc, 0, out)
            with open(os.path.join(d, "base", "projects", "zlib", "unpatched.yaml")) as f:
                self.assertTrue(f.read().endswith("# edited\n"))
            self.assertFalse(os.path.exists(os.path.join(d, "base", "projects", UNIT, "findings")))

    def test_the_overlay_refuses_a_symbolic_link_in_or_on_the_way_to_a_new_layout_folder(self):
        """The next step writes the tree's generated files, and a link would carry a write out of the tree; a link at
        projects/<p>/<h> would lead the overlay to copy what it points at.  A link in a proofs folder, a proofs
        folder or an unpatched.yaml that is one, and a fuzz target's folder that is one."""
        links = (("projects/%s/proofs/plain_halts/Link.v" % UNIT, "Proof.v"),
                 ("projects/zlib/api-driver/proofs", "../checksum_fuzzer/proofs"),
                 ("projects/zlib/unpatched.yaml", "README.md"),
                 ("projects/zlib/linked", "checksum_fuzzer"))
        for link, target in links:
            with self.subTest(link), tree() as t, tempfile.TemporaryDirectory() as d:
                base = layout_repo(t)
                if os.path.isdir(t.path(link)):
                    shutil.rmtree(t.path(link))
                elif os.path.exists(t.path(link)):
                    os.remove(t.path(link))
                os.symlink(target, t.path(link))
                commit(t)
                rc, out = self.work_step(t, d, base)
                self.assertEqual(rc, 1, out)
                self.assertIn("::error::symbolic links", out)
                self.assertIn("head/" + link, out)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_the_release_check_plan_step_plans_every_new_layout_harness_with_a_proof_or_a_finding(self):
        """As the old-layout test of this name: a harness with a committed finding is planned, also when it withholds
        every build and has no proof, and only the harnesses with published builds are built."""
        with tree() as t, tempfile.TemporaryDirectory() as d:
            self.new_layout_release(t)
            got, output = self.release_check(t, d)
            self.assertEqual(got["units"], [CX_UNIT, UNIT])
            self.assertEqual(got["check_units"], [CX_UNIT])
            self.assertEqual(" ".join(j["findings"] for j in got["jobs"]).split(), [UNIT])
            self.assertIn("units=2\n", output)

    @unittest.skipUnless(shutil.which("jq"), "jq is not installed")
    def test_a_release_check_dispatch_for_named_harnesses_plans_them_in_the_new_layout(self):
        """workflow_dispatch's units are PROJECT/HARNESS names, compared with each committed proof's and finding's."""
        for units, want in ((CX_UNIT, [CX_UNIT]), (UNIT, [UNIT]), ("%s %s" % (UNIT, CX_UNIT), [CX_UNIT, UNIT])):
            with self.subTest(units), tree() as t, tempfile.TemporaryDirectory() as d:
                self.new_layout_release(t)
                got, output = self.release_check(t, d, UNITS=units, GITHUB_REF="refs/heads/topic")
                self.assertEqual(got["units"], want, output)

    def new_layout_release(self, t):
        """The fixture with a committed proof of CX_UNIT, its finding on UNIT, and every checksum_fuzzer build
        withheld, as the old-layout test has it, ported to the per-project layout: its first commit.  (Not rendered:
        the proof is of a statement with a counterexample, an error of the facts that generate stops on and plan
        does not.)"""
        from oft import port
        from oft.tests.test_release_tree import add_proof
        add_proof(t, "%s/plain_halts" % CX_UNIT)
        withhold_checksum_fuzzer(t)
        add_findings(t)
        self.assertEqual(port.port_worktree(t.root, out=io.StringIO()), 0)
        self.assertFalse([p for p in ("proofs", "counterexamples", "findings") if os.path.exists(t.path(p))])
        t.write("tools/oft/check.py", "check\n")
        t.write(".gitattributes", "* text=auto eol=lf\n")
        git(t, "init", "-q")
        return commit(t)


class VmEvidence(unittest.TestCase):
    """plan.paths_a_check_reads and plan.vm_evidence_keys, which pr.yml's vm_evidence step runs with the base's
    tools: whether a merge queue group's change can move a verdict, and whether every part the plan marks for
    checking carries the key its check of record ran on.  They are in plan.py, which keys.NOT_THE_CHECKER names, so
    a change to them re-checks no fuzz target (test_a_change_to_the_planner_changes_no_key)."""

    HARMLESS = ["projects/zlib/checksum_fuzzer/proofs/sum/Proof.v", "projects/zlib/checksum_fuzzer/proofs/lib/Lib.v",
                "proofs/curl/fuzz_url/url/Proof.v", "CHANGELOG.md", "tools/oft/lint.py",
                "tools/oft/tests/test_lint.py", "tools/oft/README.md", "tools/enroll/upload",
                "tools/publish/release.py",
                # the generated pages a proof re-renders with its statement's new status: no key holds either
                "projects/zlib/checksum_fuzzer/README.md", "projects/zlib/README.md"]

    def test_a_unit_s_own_proofs_and_the_files_no_check_opens_move_no_verdict(self):
        self.assertEqual(plan.paths_a_check_reads(self.HARMLESS), [])

    def test_every_other_path_can_move_a_verdict(self):
        """A statement, the facts' rows, the theories, the toolchain, the workflows, release.yaml, dune-project and
        the checker; and the parts no evidence line records, a counterexample, a finding and an unpatched.yaml."""
        for path in ("projects/zlib/checksum_fuzzer/harness.yaml", "projects/zlib/project.yaml",
                     "projects/zlib/checksum_fuzzer/Statements.v", "theories/Premises.v",
                     "toolchain/allowed-axioms.txt", ".github/workflows/pr.yml", "release.yaml", "dune-project",
                     "tools/oft/check.py", "tools/oft/keys.py", "tools/oft/unitpaths.py",
                     "projects/zlib/unpatched.yaml", "projects/zlib/checksum_fuzzer/findings/f/finding.yaml",
                     "projects/zlib/patches/README.md", "docs/README.md",
                     "findings/zlib/checksum_fuzzer/f/finding.yaml",
                     "projects/zlib/checksum_fuzzer/counterexamples/sum/x.bin",
                     "counterexamples/zlib/checksum_fuzzer/sum/x.bin", "proofs/lib/Shared.v"):
            with self.subTest(path=path):
                self.assertEqual(plan.paths_a_check_reads(self.HARMLESS + [path]), [path])

    def comp(self, unit, **moved):
        out = {"version": keys.VERSION, "unit": unit, "part": "build", "checker": plan.ONLY_CHECKER[1],
               "project": "p0", "image": "i0", "harness": "h0", "proofs": "pf0", "theories": "th0",
               "allowed-axioms": "ax0", "dune-project": "dp0", "rocqchk": "no"}
        out.update(moved)
        return out

    @staticmethod
    def key_of(comp):
        return keys.digest("%s=%s" % kv for kv in comp.items())

    def part(self, comp, check=True, part="build"):
        return {"unit": comp["unit"], "part": part, "key": self.key_of(comp), "check": check,
                "why": "changed: proofs", "components": comp}

    def line(self, comp):
        return "%s %s" % (comp["unit"], self.key_of(comp))

    def test_every_planned_part_with_the_key_its_check_of_record_ran_on(self):
        a, b = self.comp("zlib/checksum_fuzzer"), self.comp("curl/fuzz_url")
        ok, why = plan.vm_evidence_keys([self.part(a), self.part(b), self.part(self.comp("x/y"), check=False)],
                                        [self.line(a), self.line(b)])
        self.assertEqual((ok, why), (True, "2 part(s), each with the key its check of record ran on"))

    def test_a_component_that_moved_is_a_key_that_differs(self):
        """A proof library another pull request changed reaches this unit's check only through its own proofs
        folder (tools/oft/unitpaths.py), and theories/ is a component of its own: either moves the key."""
        for moved in ({"proofs": "pf1"}, {"theories": "th1"}, {"harness": "h1"}, {"image": "i1"}):
            with self.subTest(**moved):
                a = self.comp("zlib/checksum_fuzzer")
                ok, why = plan.vm_evidence_keys([self.part(self.comp("zlib/checksum_fuzzer", **moved))],
                                                [self.line(a)])
                self.assertFalse(ok)
                self.assertIn("zlib/checksum_fuzzer: its key at this group head is", why)

    def test_a_unit_with_no_line_or_two_that_disagree(self):
        a = self.comp("zlib/checksum_fuzzer")
        ok, why = plan.vm_evidence_keys([self.part(a)], [])
        self.assertEqual((ok, why), (False, "zlib/checksum_fuzzer has no key line in its pull request's evidence "
                                            "comment"))
        # two pull requests of one group touching one unit: each recorded its own key
        ok, why = plan.vm_evidence_keys([self.part(a)],
                                        [self.line(a), self.line(self.comp("zlib/checksum_fuzzer", proofs="pf1"))])
        self.assertFalse(ok)
        self.assertIn("two evidence lines of its own", why)

    def test_a_part_that_is_not_a_build_or_no_part_at_all(self):
        a = self.comp("zlib/checksum_fuzzer")
        ok, why = plan.vm_evidence_keys([self.part(a), self.part(a, part="findings")], [self.line(a)])
        self.assertEqual((ok, why), (False, "the plan marks findings to check, which no evidence line records"))
        self.assertEqual(plan.vm_evidence_keys([], []), (False, "the plan marks no part to check"))
        self.assertEqual(plan.vm_evidence_keys([self.part(a, check=False)], [self.line(a)]),
                         (False, "the plan marks no part to check"))

    def test_a_line_that_is_not_one_unit_and_one_key(self):
        for line in ("zlib/checksum_fuzzer", "zlib/checksum_fuzzer " + "z" * 64, "a b c", "unit " + "a" * 63):
            with self.subTest(line=line):
                ok, why = plan.vm_evidence_keys([self.part(self.comp("zlib/checksum_fuzzer"))], [line])
                self.assertFalse(ok)
                self.assertIn("is not one unit and one key", why)

    def test_ruling_16_lets_the_checker_differ_between_exactly_those_two_ids(self):
        """Until the VM corpus run N6 passes: a key recorded under main's checker at 87c4b944683b and this group's
        under its checker at dd31239f2de differ in that component alone, and the group still skips."""
        old, new = plan.ONLY_CHECKER
        a = self.comp("zlib/checksum_fuzzer")
        ok, why = plan.vm_evidence_keys([self.part(a)], [self.line(self.comp(a["unit"], checker=old))])
        self.assertTrue(ok, why)
        self.assertIn("1 by ruling 16's checker pair: zlib/checksum_fuzzer", why)
        for case, here, recorded in (("another recorded checker", a, self.comp(a["unit"], checker="c" * 64)),
                                     ("another checker here", self.comp(a["unit"], checker="d" * 64),
                                      self.comp(a["unit"], checker=old)),
                                     ("the pair and another component", self.comp(a["unit"], theories="th1"),
                                      self.comp(a["unit"], checker=old)),
                                     ("the pair the other way round", self.comp(a["unit"], checker=old),
                                      self.comp(a["unit"], checker=new))):
            with self.subTest(case=case):
                self.assertFalse(plan.vm_evidence_keys([self.part(here)], [self.line(recorded)])[0])

    def train(self, unit="zlib/checksum_fuzzer", **moved):
        """A build part's components as the train's own tools write them for a unit the train does not touch: the
        two ids ruling 20 pins, a dune-path component and keys.VERSION."""
        return self.comp(unit, **dict({"checker": plan.AFTER_THE_TRAIN_CHECKER,
                                       "theories": plan.AFTER_THE_TRAIN_THEORIES,
                                       "dune-path": "dp-path0"}, **moved))

    def test_ruling_20_lets_a_marker_of_the_pre_train_formula_stand(self):
        """Until N6 passes: a check of record that ran before the W2 train recorded the key of the same tree as it
        stood then -- keys.VERSION 2 with no dune-path component, main's checker id and main's theories id.  Every
        other component is this group's own, so the marker is accepted for a unit the train does not touch and for
        nothing else."""
        a = self.train()
        before = keys.key_of(plan._before_the_train(a))   # noqa: SLF001
        self.assertNotEqual(before, self.key_of(a))
        ok, why = plan.vm_evidence_keys([self.part(a)], ["%s %s" % (a["unit"], before)])
        self.assertTrue(ok, why)
        self.assertIn("1 by ruling 20's pre-train tree: zlib/checksum_fuzzer", why)
        # the same marker, and this group's tree is not the one it measured
        for case, moved in (("a proof file", {"proofs": "pf1"}), ("a statement", {"harness": "h1"}),
                           ("the image", {"image": "i1"}), ("the axiom list", {"allowed-axioms": "ax1"}),
                           ("the project's rows", {"project": "p1"}),
                           ("dune-project", {"dune-project": "dp1"})):
            with self.subTest(case=case):
                ok, why = plan.vm_evidence_keys([self.part(self.train(**moved))],
                                                ["%s %s" % (a["unit"], before)])
                self.assertFalse(ok, why)
                self.assertIn("its evidence comment recorded", why)

    def test_ruling_20_reads_back_the_two_ids_it_pins_and_no_others(self):
        """The checker and theories ids are pinned exactly: a third checker, or a theories id that is neither the
        train's nor what the train's maps back to, is a part this ruling does not know."""
        a = self.train()
        before = keys.key_of(plan._before_the_train(a))   # noqa: SLF001
        for case, moved in (("a third checker", {"checker": "d" * 64}),
                           ("main's checker, not the train's", {"checker": plan.ONLY_CHECKER[1]}),
                           ("a third theories id", {"theories": "th9"}),
                           ("main's theories, not the train's", {"theories": plan.BEFORE_THE_TRAIN_THEORIES})):
            with self.subTest(case=case):
                here = self.train(**moved)
                self.assertIsNone(plan._before_the_train(here))   # noqa: SLF001
                self.assertFalse(plan.ruling_20_allows(here, before))
                self.assertFalse(plan.vm_evidence_keys([self.part(here)], ["%s %s" % (a["unit"], before)])[0])

    def test_ruling_20_holds_ruling_16_s_checker_pair_inside_it(self):
        """A check of record that ran before the train and under main's older checker: all the train's differences
        at once and ruling 16's, and no other."""
        old, new = plan.ONLY_CHECKER
        a = self.train()
        before = keys.key_of(dict(plan._before_the_train(a), checker=old))   # noqa: SLF001
        self.assertEqual(plan._before_the_train(a)["checker"], new)   # noqa: SLF001
        ok, why = plan.vm_evidence_keys([self.part(a)], ["%s %s" % (a["unit"], before)])
        self.assertTrue(ok, why)
        self.assertIn("1 by ruling 20's pre-train tree: zlib/checksum_fuzzer", why)
        self.assertFalse(plan.vm_evidence_keys([self.part(self.train(proofs="pf1"))],
                                               ["%s %s" % (a["unit"], before)])[0])

    def test_the_two_ids_ruling_20_pins_are_the_tree_that_wrote_them(self):
        """The pins are the checker and theories ids of the commit that wrote them, not of this head: a later pull
        request may change a file of the checker or theories/, and must not fail here for it.  Such a change ends
        the ruling on its own, since its part's ids are then neither pinned and _before_the_train gives None.

        Skipped where git cannot read this checkout, or where it holds too little history to find that commit: in
        a clone one commit deep (pr.yml's tests job makes one) `git log -S` answers with the only commit it has,
        this head, whose ids are the very thing this test must not compare; so a shallow clone, and a commit whose
        parent the clone lacks, skip rather than measure the wrong tree, as the test of ruling 16's two ids skips
        a commit the clone does not hold."""
        shallow = subprocess.run(GIT + ["-C", REPO, "rev-parse", "--is-shallow-repository"],
                                 env=GIT_ENV, capture_output=True)
        if shallow.returncode or shallow.stdout.decode().strip() != "false":
            self.skipTest("this checkout is shallow, so `git log -S` would answer with its only commit")
        done = subprocess.run(GIT + ["-C", REPO, "log", "-1", "--format=%H",
                                     "-S", 'AFTER_THE_TRAIN_CHECKER = "%s"' % plan.AFTER_THE_TRAIN_CHECKER,
                                     "--", "tools/oft/plan.py"], env=GIT_ENV, capture_output=True)
        wrote = done.stdout.decode().strip()
        if done.returncode or not wrote:
            self.skipTest("this checkout holds no commit that wrote the pins")
        if subprocess.run(GIT + ["-C", REPO, "rev-parse", "--verify", "--quiet", wrote + "^"],
                          env=GIT_ENV, capture_output=True).returncode:
            self.skipTest("the commit that wrote the pins has no parent here: this clone holds too little history")
        said = ("a later checker or theories/ change ends ruling 20 by itself (_before_the_train returns None); "
                "never re-pin these to extend it: a new pair needs the OSS Verify lead's ruling")
        self.assertEqual(keys.checker(REPO, wrote), plan.AFTER_THE_TRAIN_CHECKER, said)
        at = keys.Attributes(REPO, wrote, keys.FACTS_PATHS)
        self.assertEqual(at.id("theories"), plan.AFTER_THE_TRAIN_THEORIES, said)
        self.assertNotEqual(plan.BEFORE_THE_TRAIN_THEORIES, plan.AFTER_THE_TRAIN_THEORIES)

    def test_key_of_is_the_one_formula_every_key_is_computed_by(self):
        """keys.key_of knows one formula, today's, and keys() computes a key with it; an older formula is a caller's
        components, which plan._before_the_train names for ruling 20 alone."""
        a = self.train()
        self.assertEqual(keys.key_of(a), self.key_of(a))
        pre = plan._before_the_train(a)   # noqa: SLF001
        self.assertEqual(pre, {k: {"version": "2", "checker": plan.ONLY_CHECKER[1],
                                   "theories": plan.BEFORE_THE_TRAIN_THEORIES}.get(k, v)
                               for k, v in a.items() if k != "dune-path"})
        self.assertEqual(keys.key_of(pre), self.key_of(pre))
        self.assertNotEqual(keys.key_of(pre), keys.key_of(a))

    def test_the_two_checker_ids_are_the_ones_main_had(self):
        """keys.checker of main at 87c4b944683b, under which the VM checks of record ran, and at dd31239f2de, the
        base this change was written on; the pair goes when N6 passes.  Skipped in a clone that has neither commit
        (the runner image's tools/oft, a shallow checkout)."""
        for commit, want in zip(("87c4b944683b", "dd31239f2de"), plan.ONLY_CHECKER):
            with self.subTest(commit=commit):
                if subprocess.run(["git", "-C", REPO, "rev-parse", "--verify", "--quiet", commit + "^{commit}"],
                                  capture_output=True).returncode != 0:
                    self.skipTest("%s is not in this clone" % commit)
                self.assertEqual(keys.checker(REPO, commit), want)
