"""findings/: the record of a library bug found while proving, the unpatched binaries it runs on, and its rules; and
the patches entries that ship a public finding's patch."""
import io
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

from oft import facts, layout, paths, port, rules, schema
from oft.tests.helpers import (FINDING as DIR, KEY, add_findings, edit, entry_patch, errors, older_shape, port_built,
                               public_patch, tree)


INTERNAL = "theorem-labs/oss-verify-proofs" + "-internal"

YAML = DIR + "/finding.yaml"
UNPATCHED = "findings/zlib/unpatched.yaml"
# the copied port records of zlib/checksum_fuzzer and json/fuzzer-parse_bjdata, once port_built makes them port builds
ZLIB_RECORD = "proofs/zlib/checksum_fuzzer/provenance/port/projects/zlib/"
JSON_RECORD = "proofs/json/fuzzer-parse_bjdata/provenance/port/projects/json/"


class Record(unittest.TestCase):
    def test_a_finding_loads_with_its_unit_slug_and_unpatched_binaries(self):
        with tree(render=False) as t:
            add_findings(t)
            loaded = facts.load(t.root)
            self.assertEqual(loaded.errors, [])
            self.assertEqual(sorted(loaded.findings), [KEY])
            f = loaded.findings[KEY]
            self.assertEqual((f.path, f.unit, f.slug), (DIR, "zlib/checksum_fuzzer", "stand-in-abort"))
            self.assertEqual(f.data["state"], "patched")
            self.assertEqual(loaded.unpatched["zlib"]["asset"]["file"], "zlib-unpatched-bin.tar.zst")
            h = loaded.projects["zlib"].harnesses["checksum_fuzzer"]
            self.assertEqual(h.unpatched_elf_path("asan"),
                             "projects/zlib/unpatched-bin/checksum_fuzzer/checksum_fuzzer.asan")

    def test_a_tree_with_a_finding_lints_clean(self):
        with tree() as t:
            add_findings(t)
            self.assertEqual([str(f) for f in t.lint()], [])

    def test_a_statement_the_harness_lacks(self):
        with tree(render=False) as t:
            add_findings(t)
            edit(t, YAML, lambda y: y["statements"].append("nosuch_agrees"))
            self.assertIn(YAML + ": names statement nosuch_agrees, which zlib/checksum_fuzzer does not have",
                          errors(t))

    def test_a_build_missing_from_input_or_control(self):
        for which in ("input", "control"):
            with self.subTest(which=which), tree(render=False) as t:
                add_findings(t)
                edit(t, YAML, lambda y: y[which].pop("asan"))
                self.assertIn(YAML + ": %s has no run of build asan, which asan_agrees names" % which, errors(t))

    def test_a_patch_file_that_is_absent(self):
        with tree(render=False) as t:
            add_findings(t)
            os.remove(t.path(DIR, "0001-stand-in.patch"))
            self.assertIn(YAML + ": its patch 0001-stand-in.patch is not in " + DIR, errors(t))

    def test_a_patched_finding_names_its_patch_and_a_not_a_defect_one_keeps_its_ledger(self):
        with tree(render=False) as t:
            add_findings(t)
            edit(t, YAML, lambda y: y.pop("patch"))
            self.assertIn(YAML + ": a patched finding names its patch", errors(t))
        with tree(render=False) as t:
            add_findings(t)
            edit(t, YAML, lambda y: y.update(state="not-a-defect"))
            self.assertFalse(any("a not-a-defect finding has no patch" in e for e in errors(t)))

    def test_a_reported_finding_without_upstream(self):
        for state in ("reported", "public"):
            with self.subTest(state=state), tree(render=False) as t:
                add_findings(t)
                edit(t, YAML, lambda y: y.update(state=state))
                self.assertIn(YAML + ": a %s finding names its report (upstream)" % state, errors(t))

    def test_input_or_control_missing(self):
        for f in ("input.bin", "control.bin"):
            with self.subTest(f=f), tree(render=False) as t:
                add_findings(t)
                os.remove(t.path(DIR, f))
                self.assertIn(DIR + ": missing " + f, errors(t))

    def test_a_finding_whose_project_has_no_unpatched_binaries(self):
        with tree(render=False) as t:
            add_findings(t)
            os.remove(t.path(UNPATCHED))
            self.assertIn(YAML + ": findings/zlib/unpatched.yaml is missing: it pins the binaries this finding runs on",
                          errors(t))

    def test_unpatched_binaries_that_lack_a_build_the_finding_runs(self):
        with tree(render=False) as t:
            add_findings(t)
            edit(t, UNPATCHED, lambda y: y["harnesses"]["checksum_fuzzer"].pop("asan-ubsan"))
            self.assertIn(YAML + ": findings/zlib/unpatched.yaml has no asan-ubsan build of checksum_fuzzer",
                          errors(t))

    def test_the_unpatched_archive_and_its_files_are_named_for_their_project_and_builds(self):
        with tree(render=False) as t:
            add_findings(t)

            def rename(y):
                y["asset"]["release"] = "findings-json"
                y["asset"]["file"] = "json-unpatched-bin.tar.zst"
                y["harnesses"]["checksum_fuzzer"]["plain"]["file"] = "checksum_fuzzer.ubsan"
            edit(t, UNPATCHED, rename)
            errs = errors(t)
            self.assertIn(UNPATCHED + ": asset.file must be zlib-unpatched-bin.tar.zst", errs)
            self.assertIn(UNPATCHED + ": asset.release must be findings-zlib, the release that holds zlib's assets "
                          "while a finding holds it back", errs)
            self.assertIn(UNPATCHED + ": harnesses.checksum_fuzzer.plain.file must be checksum_fuzzer.plain", errs)

    def test_two_pinned_assets_with_one_file_name(self):
        with tree(render=False) as t:
            add_findings(t)
            edit(t, "projects/zlib/project.yaml",
                 lambda y: y["assets"]["bin"].update(file="zlib-unpatched-bin.tar.zst"))
            self.assertIn(UNPATCHED + ": pins zlib-unpatched-bin.tar.zst, which projects/zlib/project.yaml pins "
                          "too: CI and `oft fetch --source` keep assets by file name", errors(t))

    def test_a_finding_with_no_recorded_runs_passes_only_while_recording(self):
        with tree(render=False) as t:
            add_findings(t)
            runs = t.yaml(YAML)["input"]
            edit(t, YAML, lambda y: (y.pop("input"), y.pop("control")))
            self.assertIn(YAML + ": no runs recorded: run `oft check zlib/checksum_fuzzer --parts findings --record` "
                          "and commit the input and control it prints", errors(t))
            self.assertEqual(errors(t, record=True), [])
            edit(t, YAML, lambda y: y.update(input=runs))
            self.assertIn(YAML + ": input and control go together: the runs of one input and of its control",
                          errors(t, record=True))

    def test_calls_is_what_the_driver_header_gives(self):
        with tree(render=False) as t:
            add_findings(t)
            edit(t, YAML, lambda y: y.update(calls=4))
            errs = errors(t)
            self.assertIn(YAML + ": calls is 4, but the driver header of input.bin gives 1", errs)
            self.assertIn(YAML + ": calls is 4, but the driver header of control.bin gives 1", errs)
        with tree(render=False) as t:
            add_findings(t)
            # the four-call header: config length 1, config byte 3, no allocation mask
            with open(t.path(DIR, "input.bin"), "rb") as f:
                payload = f.read()[6:]
            t.write(DIR + "/input.bin", b"\x01\x00\x03\x00\x00\x00\x00" + payload, "wb")
            self.assertIn(YAML + ": calls is 1, but the driver header of input.bin gives 4", errors(t))
            t.write(DIR + "/input.bin", b"\x00\x00", "wb")
            self.assertIn(YAML + ": input.bin is shorter than its driver header", errors(t))

    def test_a_finding_of_a_harness_that_is_not_in_the_tree(self):
        with tree(render=False) as t:
            add_findings(t)
            shutil.move(t.path("findings/zlib/checksum_fuzzer"), t.path("findings/zlib/minigzip_fuzzer"))
            self.assertIn("findings/zlib/minigzip_fuzzer/stand-in-abort/finding.yaml: zlib has no harness "
                          "minigzip_fuzzer in this tree", errors(t))

    def test_the_fetched_binaries_are_never_tracked(self):
        self.assertTrue(paths.ignored("projects/zlib/unpatched-bin/checksum_fuzzer/checksum_fuzzer.plain"))
        self.assertFalse(paths.ignored(UNPATCHED))
        with tree(render=False) as t:
            add_findings(t)
            t.write("projects/zlib/unpatched-bin/checksum_fuzzer/checksum_fuzzer.plain", "\x7fELF stand-in")
            # and what `oft fetch --findings` unpacked before the per-project layout, in a checkout that kept it
            t.write("findings/zlib/bin/checksum_fuzzer/checksum_fuzzer.plain", "\x7fELF stand-in")
            loaded = facts.load(t.root)
            self.assertEqual(loaded.errors, [])
            self.assertEqual(sorted(loaded.findings), [KEY])

    def test_only_a_maintainer_or_a_release_changes_a_finding(self):
        changed = [YAML, DIR + "/input.bin", DIR + "/control.bin", DIR + "/0001-stand-in.patch",
                   "findings/zlib/checksum_fuzzer/series", UNPATCHED]
        with tree() as t:
            add_findings(t)
            for kind in ("maintainer", "release"):
                self.assertEqual([str(f) for f in t.lint(changed=changed, pr_kind=kind)], [], kind)
            refused = [f for f in t.lint(changed=changed, pr_kind="contributor") if f.rule == "paths"]
            self.assertEqual(sorted(f.where for f in refused), sorted(changed))

    def test_a_stray_file_in_a_finding_matches_no_path_pattern(self):
        with tree() as t:
            add_findings(t)
            t.write(DIR + "/VERDICT.md", "a verdict\n")
            self.assertIn("paths %s/VERDICT.md: matches no path pattern" % DIR, [str(f) for f in t.lint()])

    def grow(self, t, rel, size):
        """rel, padded with x to size bytes."""
        with open(t.path(rel), "ab") as f:
            f.write(b"x" * (size - os.path.getsize(t.path(rel))))

    def test_an_input_as_long_as_a_full_payload_and_its_header(self):
        """A bug at a harness's last payload byte needs a payload of the harness's whole length: 64 KiB after the
        six-byte header for a harness that reads 64 KiB.  input.bin and control.bin take up to 1 MiB."""
        for rel in (DIR + "/input.bin", DIR + "/control.bin"):
            for size in ((64 << 10) + 6, 1 << 20):
                with self.subTest(rel=rel, size=size), tree() as t:
                    add_findings(t)
                    self.grow(t, rel, size)
                    self.assertEqual(facts.load(t.root).errors, [])
                    self.assertEqual([str(f) for f in t.lint()], [])

    def test_a_finding_file_over_its_cap(self):
        """input.bin and control.bin: 1 MiB; every other file of a finding: 64 KiB.  lint's paths rule reports it, by
        its own cap (facts.CAPS), apart from the loader's schema error for the same file."""
        for rel, cap in ((DIR + "/input.bin", 1 << 20), (DIR + "/control.bin", 1 << 20),
                         (DIR + "/0001-stand-in.patch", 64 << 10), ("findings/zlib/checksum_fuzzer/series", 64 << 10)):
            with self.subTest(rel=rel), tree() as t:
                add_findings(t)
                self.grow(t, rel, cap + 1)
                self.assertIn("paths %s: %d bytes, over the %d-byte cap" % (rel, cap + 1, cap),
                              [str(f) for f in t.lint()])

    def test_the_loader_refuses_an_oversize_finding_file_before_lint(self):
        for rel, cap in ((DIR + "/input.bin", 1 << 20), (DIR + "/control.bin", 1 << 20),
                         (DIR + "/0001-stand-in.patch", 64 << 10), (YAML, 64 << 10), (UNPATCHED, 64 << 10)):
            with self.subTest(rel=rel), tree(render=False) as t:
                add_findings(t)
                self.grow(t, rel, cap + 1)
                self.assertIn("%s: over the %d-byte cap" % (rel, cap), facts.load(t.root).errors)

    def test_the_loader_never_opens_a_symlinked_finding_file(self):
        with tree(render=False) as t:
            add_findings(t)
            path = t.path(DIR, "input.bin")
            os.remove(path)
            os.symlink("/dev/zero", path)
            tools = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
            try:
                r = subprocess.run([sys.executable, "-B", "-c",
                                    "from oft import facts; import sys; print(*facts.load(sys.argv[1]).errors, sep='\\n')",
                                    t.root], env=dict(os.environ, PYTHONPATH=os.path.dirname(tools)), capture_output=True,
                                   text=True, timeout=2)
            except subprocess.TimeoutExpired:
                self.fail("facts.load followed the /dev/zero symlink")
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertIn(DIR + "/input.bin: a symbolic link", r.stdout)

    def test_the_loader_preflights_unpatched_and_patch_files(self):
        for rel in (UNPATCHED, DIR + "/0001-stand-in.patch"):
            with self.subTest(rel=rel), tree(render=False) as t:
                add_findings(t)
                os.remove(t.path(rel))
                os.symlink("/dev/zero", t.path(rel))
                loaded = facts.load(t.root)
                self.assertIn(rel + ": a symbolic link", loaded.errors)

    def test_a_file_that_grows_past_its_cap_is_refused_without_reading_past_it(self):
        """The size checks run on lstat and fstat; a file that grows after them is still read at most one byte past
        its cap, and refused."""
        cap = 32
        real_lstat, real_fstat, real_fdopen = os.lstat, os.fstat, os.fdopen
        requested = []

        def as_if_small(st):
            fields = list(st)
            fields[6] = cap                      # st_size, as stat saw the file before it grew
            return os.stat_result(fields)

        class Recording:
            def __init__(self, f):
                self.f = f

            def __enter__(self):
                return self

            def __exit__(self, *a):
                self.f.close()

            def read(self, n=-1):
                requested.append(n)
                return self.f.read(n)

        with tempfile.TemporaryDirectory(prefix="oft-test-") as d:
            path = os.path.join(d, "grown.patch")
            with open(path, "wb") as f:
                f.write(b"x" * (cap + 1))
            with mock.patch.object(facts.os, "lstat", lambda p: as_if_small(real_lstat(p))), \
                    mock.patch.object(facts.os, "fstat", lambda fd: as_if_small(real_fstat(fd))), \
                    mock.patch.object(facts.os, "fdopen", lambda fd, mode: Recording(real_fdopen(fd, mode))):
                with self.assertRaisesRegex(facts.BoundedFileError, "over the %d-byte cap" % cap):
                    facts.read_bounded(path, cap)
        self.assertEqual(requested, [cap + 1])

    def test_a_finding_yaml_nested_too_deep_is_a_finding_on_that_file(self):
        """A finding.yaml within its cap can nest deep enough to overflow the C stack of PyYAML's libyaml loader
        (32768 sequences, with the pinned wheel) or Python's recursion limit (1000 mappings): lint, in a child process
        so that a crash fails only this test, reports the file instead."""
        tools = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
        path = os.pathsep.join(filter(None, (tools, os.environ.get("PYTHONPATH"))))
        n = 32 << 10
        for text in ("[" * n + "]" * n, "{a: " * 1000 + "1" + "}" * 1000):
            with self.subTest(text=text[:8]), tree() as t:
                add_findings(t)
                t.write(YAML, text)
                r = subprocess.run([sys.executable, "-B", "-m", "oft", "--root", t.root, "lint"], cwd=tools,
                                   env=dict(os.environ, PYTHONPATH=path), capture_output=True, text=True, timeout=120)
                self.assertEqual(r.returncode, 1, r.stderr)
                self.assertIn("schema %s: %s: collections nested more than 64 deep" % (YAML, t.path(YAML)),
                              r.stdout.splitlines())

    def test_a_finding_yaml_with_an_alias_is_a_finding_on_that_file(self):
        """Aliases of aliases expand a finding.yaml within its cap into a document far larger than the file; the
        loader refuses any alias before it builds anything."""
        with tree() as t:
            add_findings(t)
            t.write(YAML, "a: &a [x, x]\nb: *a\n")
            self.assertIn("%s: an alias (*a) at line 2: the facts give every value once" % t.path(YAML),
                          [f.msg for f in t.lint()])

    def test_an_upstream_link_is_one_the_facts_record(self):
        with tree() as t:
            add_findings(t)
            edit(t, YAML, lambda y: y.update(upstream="https://bugs.example.org/show_bug.cgi?id=1"))
            self.assertEqual([str(f) for f in t.lint()], [])

    def test_a_findings_release_tag_and_the_internal_port(self):
        with tree(render=False) as t:
            p = t.yaml("projects/zlib/project.yaml")
        for release, ok in (("findings-zlib", True), ("findings-", False), ("findings-Zlib", False),
                            ("v2026.11.0", True), ("w2026.11.0", False)):
            with self.subTest(release=release):
                p["assets"]["bin"]["release"] = release
                self.assertEqual(schema.validate("project", p) == [], ok)
        p["assets"]["bin"]["release"] = "v2026.11.0"
        for repository, ok in (("theorem-labs/oss-verify", True), (INTERNAL, True),
                               ("theorem-labs/oss-verify-proofs", False),
                               ("theorem-labs/oss-verify" + "-prelaunch", False)):
            with self.subTest(repository=repository):
                p["build"]["oss_verify"] = {"repository": repository, "commit": "d" * 40, "path": "projects/zlib"}
                self.assertEqual(schema.validate("project", p) == [], ok)

    def test_an_enrollment_draft_tag_is_an_asset_release_tag(self):
        """An enrollment commit's own drafts (tools/enroll/drafts.py): enroll-<project>-<12 hex of the port commit>,
        and the same with -src."""
        with tree(render=False) as t:
            p = t.yaml("projects/zlib/project.yaml")
        for release, ok in (("enroll-libreac-0123456789ab", True), ("enroll-libreac-0123456789ab-src", True),
                            ("enroll-reac-pw-0123456789ab-src", True), ("enroll-libreac-0123", False),
                            ("enroll-Libreac-0123456789ab", False), ("enroll-libreac-0123456789AB", False),
                            ("enroll--0123456789ab", False), ("enroll-libreac-0123456789ab-bin", False),
                            ("enroll-libreac-0123456789abc", False)):
            with self.subTest(release=release):
                p["assets"]["bin"]["release"] = release
                self.assertEqual(schema.validate("project", p) == [], ok)

    def test_a_recipe_release_cannot_be_a_findings_release(self):
        """Neither a recipe release.yaml lists (recipes, or the shape before it, its one recipe) nor the one a binary
        archive pins is attached to a findings-<project> release."""
        with tree(render=False) as t:
            release = t.yaml("release.yaml")
            release["recipes"][0]["release"] = "findings-zlib"
            self.assertEqual(schema.validate("release", release), [
                "release.recipes[0].release: 'findings-zlib' is not a valid release-tag"])
            p = t.yaml("projects/zlib/project.yaml")
            p["assets"]["bin"]["recipe"]["release"] = "findings-zlib"
            self.assertEqual(schema.validate("project", p), [
                "project.assets.bin.recipe.release: 'findings-zlib' is not a valid release-tag"])
            older_shape(t)
            release = t.yaml("release.yaml")
            release["recipe"]["release"] = "findings-zlib"
            self.assertEqual(schema.validate("release", release), [
                "release.recipe.release: 'findings-zlib' is not a valid release-tag"])


# The SHA-256 of "ran\n", of "differs\nran\n" and of nothing: what the fixture's runs print.

RAN = "f4472a14b6160e58b35bfeb710d23d240ab59402cc84bc7b5a579c7373849295"
DIFFERS = "c0595f8938f4c1b33f96d71df39e76f1dc58784e820217db6dbc0797eeecde70"
EMPTY = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
NORMAL = {"exit": 0, "stdout_sha256": RAN, "stderr_sha256": EMPTY}
ABORT = {"exit": 134, "signal": "SIGABRT", "stdout_sha256": EMPTY, "stderr_sha256": EMPTY}


def finding_errors(t, record=False):
    """The tree errors that name a finding, its series or the facts a finding constrains."""
    return [e for e in errors(t, record) if e.startswith(("findings/", "projects/zlib/project.yaml",
                                                          "projects/json/project.yaml", "release.yaml"))]


def runs(**builds):
    return {b.replace("_", "-"): dict(r) for b, r in builds.items()}


class Rules(unittest.TestCase):
    def test_the_fixture_finding_meets_every_rule(self):
        with tree(render=False) as t:
            add_findings(t)
            self.assertEqual(errors(t), [])

    def test_an_input_that_does_not_show_its_statements_false(self):
        with tree(render=False) as t:
            add_findings(t)
            edit(t, YAML, lambda y: y.update(input=runs(plain=NORMAL, asan=NORMAL, asan_ubsan=NORMAL)))
            self.assertEqual(finding_errors(t), [YAML + ": the input does not show asan_agrees false",
                                                 YAML + ": the input does not show asan_ubsan_agrees false"])

    def test_an_agreement_is_shown_false_by_any_difference_or_by_a_signal(self):
        differ = [dict(NORMAL, stdout_sha256=DIFFERS), dict(NORMAL, stderr_sha256=DIFFERS), dict(NORMAL, exit=78)]
        for asan in differ:
            with self.subTest(asan=asan), tree(render=False) as t:
                add_findings(t)
                edit(t, YAML, lambda y: y.update(statements=["asan_agrees"], input=runs(plain=NORMAL, asan=asan),
                                                 control=runs(plain=NORMAL, asan=NORMAL)))
                self.assertEqual(finding_errors(t), [])
        # both builds die alike: neither is error-free, so the agreement is false all the same
        with tree(render=False) as t:
            add_findings(t)
            edit(t, YAML, lambda y: y.update(statements=["asan_agrees"], input=runs(plain=ABORT, asan=ABORT),
                                             control=runs(plain=NORMAL, asan=NORMAL)))
            self.assertEqual(finding_errors(t), [])

    def test_a_control_that_does_not_behave_normally(self):
        for asan in (ABORT, dict(NORMAL, stdout_sha256=DIFFERS)):
            with self.subTest(asan=asan), tree(render=False) as t:
                add_findings(t)
                edit(t, YAML, lambda y: y["control"].update(asan=asan))
                self.assertEqual(finding_errors(t), [
                    YAML + ": the control does not behave normally: it shows asan_agrees false"])

    def test_a_halts_statement(self):
        def halts(input_, control):
            return lambda y: y.update(statements=["asan_halts"], input={"asan": input_}, control={"asan": control})
        cases = [
            (ABORT, NORMAL, []),
            (dict(NORMAL, exit=77), dict(NORMAL, exit=2), []),          # asan_halts allows exits 0 and 2
            (dict(NORMAL, exit=2), NORMAL, [YAML + ": the input does not show asan_halts false"]),
            (ABORT, dict(NORMAL, exit=77), [YAML + ": the control does not behave normally: it shows asan_halts false"]),
            (ABORT, ABORT, [YAML + ": the control does not behave normally: it shows asan_halts false"]),
        ]
        for input_, control, want in cases:
            with self.subTest(input=input_, control=control), tree(render=False) as t:
                add_findings(t)
                edit(t, YAML, halts(input_, control))
                self.assertEqual(finding_errors(t), want)

    def test_a_run_of_a_build_no_statement_names(self):
        with tree(render=False) as t:
            add_findings(t)
            edit(t, YAML, lambda y: (y["input"].update(ubsan=NORMAL), y["control"].update(ubsan=NORMAL)))
            self.assertEqual(finding_errors(t), [YAML + ": input runs build ubsan, which none of its statements names",
                                                 YAML + ": control runs build ubsan, which none of its statements "
                                                 "names"])

    def test_a_pruned_finding_shows_no_statement_false(self):
        with tree(render=False) as t:
            add_findings(t)
            t.write("findings/zlib/checksum_fuzzer/series", "")
            edit(t, YAML, lambda y: y.update(state="pruned"))
            self.assertEqual(finding_errors(t), [YAML + ": pruned, but its record shows asan_agrees false",
                                                 YAML + ": pruned, but its record shows asan_ubsan_agrees false"])
            edit(t, YAML, lambda y: y.update(input=runs(plain=NORMAL, asan=NORMAL, asan_ubsan=NORMAL)))
            self.assertEqual(finding_errors(t), [])

    def test_two_patches_of_one_project_with_one_name(self):
        with tree(render=False) as t:
            add_findings(t)
            shutil.copytree(t.path(DIR), t.path(DIR + "-again"))
            self.assertIn(DIR + "-again/finding.yaml: its patch 0001-stand-in.patch has the name of the patch of "
                          + DIR + ": each patch of a project has a name of its own", finding_errors(t))

    def test_the_series_lists_the_patch_of_each_patched_reported_or_public_finding(self):
        series = "findings/zlib/checksum_fuzzer/series"
        with tree(render=False) as t:
            add_findings(t)
            t.write(series, "")
            self.assertEqual(finding_errors(t), [
                YAML + ": a patched finding's patch 0001-stand-in.patch is not listed in " + series])
            t.write(series, "0001-stand-in.patch\n0002-gone.patch\n0001-stand-in.patch\nnot a patch\n")
            self.assertEqual(finding_errors(t), [
                series + ": lists 0002-gone.patch, which is the patch of 0 findings that are patched, reported or "
                "public, not exactly one",
                series + ": lists 0001-stand-in.patch twice",
                series + ": line 4 is not a patch file name"])
        with tree(render=False) as t:
            add_findings(t)
            edit(t, YAML, lambda y: y.update(state="pruned", input=runs(plain=NORMAL, asan=NORMAL, asan_ubsan=NORMAL)))
            self.assertEqual(finding_errors(t), [
                series + ": lists 0001-stand-in.patch, which is the patch of 0 findings that are patched, reported or "
                "public, not exactly one"])

    def test_a_per_project_series_is_named_where_it_is(self):
        series = layout.series_path("zlib", "checksum_fuzzer", layout.NEW)
        yaml = layout.finding_dir("zlib", "checksum_fuzzer", "stand-in-abort", layout.NEW) + "/finding.yaml"
        with tree(render=False) as t:
            add_findings(t)
            self.assertEqual(port.port_worktree(t.root, out=io.StringIO()), 0)
            t.write(series, "0001-stand-in.patch\nnot a patch\n")
            self.assertIn(series + ": line 2 is not a patch file name", errors(t))
            t.write(series, "")
            self.assertIn(yaml + ": a patched finding's patch 0001-stand-in.patch is not listed in " + series, errors(t))

    def test_a_not_a_defect_finding_s_patch_is_not_in_the_series(self):
        """It keeps its patch in the ledger, but the library is right, so the patched build does not carry it."""
        series = "findings/zlib/checksum_fuzzer/series"
        with tree(render=False) as t:
            add_findings(t)
            edit(t, "projects/zlib/checksum_fuzzer/harness.yaml", lambda y: [y["statements"][s].update(
                status="suspected-false", basis="reading", reason="A stand-in reason for these tests.")
                for s in ("asan_agrees", "asan_ubsan_agrees")])
            edit(t, YAML, lambda y: y.update(state="not-a-defect"))
            self.assertEqual(finding_errors(t), [
                series + ": lists 0001-stand-in.patch, which is the patch of 0 findings that are patched, reported or "
                "public, not exactly one"])
            t.write(series, "")
            self.assertEqual(finding_errors(t), [])

    def test_a_not_a_defect_finding_needs_its_statements_recorded_false(self):
        with tree(render=False) as t:
            add_findings(t)
            t.write("findings/zlib/checksum_fuzzer/series", "")
            os.remove(t.path(DIR, "0001-stand-in.patch"))
            edit(t, YAML, lambda y: (y.pop("patch"), y.update(state="not-a-defect")))
            self.assertEqual(finding_errors(t), [YAML + ": not-a-defect, but asan_agrees is not recorded as false",
                                                 YAML + ": not-a-defect, but asan_ubsan_agrees is not recorded as "
                                                 "false"])
            edit(t, "projects/zlib/checksum_fuzzer/harness.yaml", lambda y: y["statements"]["asan_agrees"].update(
                status="suspected-false", basis="reading", reason="A stand-in reason for these tests."))
            self.assertEqual(finding_errors(t), [YAML + ": not-a-defect, but asan_ubsan_agrees is not recorded as "
                                                 "false"])

    def test_only_a_held_project_builds_from_the_internal_port_or_attaches_to_its_findings_release(self):
        zlib, json = "projects/zlib/project.yaml", "projects/json/project.yaml"
        internal = zlib + (": build.oss_verify.repository is %s: only a project a finding holds "
                           "back whole builds from %s" % (INTERNAL, INTERNAL))

        def attach(rel, release):
            return "%s: assets.bin is attached to %s: only a project a finding holds back whole attaches to " \
                   "findings-<project>, its own" % (rel, release)

        def port(y):
            y["build"]["oss_verify"] = {"repository": INTERNAL, "commit": "d" * 40,
                                        "path": "projects/zlib"}
            y["assets"]["port"] = {"release": "v2026.11.0", "file": "zlib-port.tar.zst", "bytes": 1000,
                                   "sha256": "9" * 64}
            y["assets"]["bin"]["release"] = "findings-zlib"
            del y["assets"]["bin"]["recipe"]   # a port-built archive names no recipe
        with tree(render=False) as t:
            add_findings(t)
            edit(t, zlib, port)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertNotIn(INTERNAL, t.read("projects/zlib/README.md"))
            self.assertEqual(finding_errors(t), [], "zlib is held: both are allowed")
            edit(t, json, lambda y: y["assets"]["bin"].update(release="findings-json"))
            self.assertEqual(finding_errors(t), [attach(json, "findings-json")])
            edit(t, json, lambda y: y["assets"]["bin"].update(release="findings-zlib"))
            self.assertEqual(finding_errors(t), [attach(json, "findings-zlib")])
            edit(t, json, lambda y: y["assets"]["bin"].update(release="v2026.11.0"))
            public_patch(t)
            self.assertEqual(finding_errors(t), [internal, attach(zlib, "findings-zlib")])

    ZLIB = "projects/zlib/project.yaml"
    OWN = "enroll-zlib-0123456789ab"

    @staticmethod
    def enroll_error(rel, kind, release):
        return ("%s: assets.%s is attached to %s: an enrollment's own drafts are enroll-<project>-<12 hex>, its own, the "
                "binaries' without -src and the rest with -src" % (rel, kind, release))

    def own_drafts(self, t, **change):
        """zlib's archives on its own drafts, the binaries' on OWN and the rest on OWN-src, but as `change` says."""
        tags = {"bin": self.OWN, "src": self.OWN + "-src", "src_manifest": self.OWN + "-src"}
        tags.update(change)
        edit(t, self.ZLIB, lambda y: [y["assets"][k].update(release=v) for k, v in tags.items()])

    def test_an_asset_on_another_projects_enroll_draft_is_refused(self):
        with tree(render=False) as t:
            self.own_drafts(t)
            self.assertEqual(finding_errors(t), [], "zlib's own drafts")
            for release in ("enroll-json-0123456789ab", "enroll-zlib-ng-0123456789ab"):
                with self.subTest(release=release):
                    self.own_drafts(t, bin=release)
                    self.assertEqual(finding_errors(t), [self.enroll_error(self.ZLIB, "bin", release)])

    def test_bin_on_the_src_draft_is_refused(self):
        with tree(render=False) as t:
            # the source assets' release: the rule every binary archive has says so too
            self.own_drafts(t, bin=self.OWN + "-src")
            self.assertEqual(finding_errors(t), [
                "%s: assets.bin is attached to %s-src, a release of source assets" % (self.ZLIB, self.OWN),
                self.enroll_error(self.ZLIB, "bin", self.OWN + "-src")])
            # and the source assets on the binaries' draft
            self.own_drafts(t, src=self.OWN, src_manifest=self.OWN)
            self.assertEqual(finding_errors(t), [self.enroll_error(self.ZLIB, "src", self.OWN),
                                                 self.enroll_error(self.ZLIB, "src_manifest", self.OWN)])

    def test_two_commits_across_the_assets_are_refused(self):
        # the binaries of one commit and the source assets of another: each asset whose commit is not the first's
        other = "enroll-zlib-ba9876543210"
        with tree(render=False) as t:
            self.own_drafts(t, bin=other)
            self.assertEqual(finding_errors(t), [self.enroll_error(self.ZLIB, "src", self.OWN + "-src"),
                                                 self.enroll_error(self.ZLIB, "src_manifest", self.OWN + "-src")])
            # a version tag beside the drafts is no commit of its own
            self.own_drafts(t, bin="v2026.11.0")
            self.assertEqual(finding_errors(t), [])

    def test_a_finding_with_no_runs_meets_the_rules_of_its_state_while_recording(self):
        with tree(render=False) as t:
            add_findings(t)
            edit(t, YAML, lambda y: (y.pop("input"), y.pop("control")))
            self.assertEqual(finding_errors(t, record=True), [])


class SeriesNames(unittest.TestCase):
    def test_a_series_is_read_as_the_build_reads_it(self):
        """oss-verify's lay-out-sources: blank lines and lines that start with `#` are skipped, other lines stripped.
        A `#` after leading white space starts no comment, so that line is a name."""
        raw = "0001-a.patch\n\n# a comment\n  0002-b.patch  \nnot a patch\n  # indented\n"
        self.assertEqual(rules.series_names(raw), [(1, "0001-a.patch"), (4, "0002-b.patch"), (5, "not a patch"),
                                                   (6, "# indented")])

    def test_an_empty_series_lists_nothing(self):
        self.assertEqual(rules.series_names(""), [])


class PatchEntries(unittest.TestCase):
    """A project's patches entries, and the copied port record of a port build, against its findings (docs/facts.md,
    "Public patches")."""

    def test_a_patch_text_is_a_fact_of_its_project(self):
        self.assertEqual([c for c, _, _ in paths.classify("patches/zlib/0001-stand-in.patch")], ["facts"])
        with tree() as t:
            changed = ["patches/zlib/example-patch.patch"]
            self.assertEqual([str(f) for f in t.lint(changed=changed, pr_kind="release")], [])
            self.assertIn("paths patches/zlib/example-patch.patch: an exported fact: only a release pull request "
                          "changes it", [str(f) for f in t.lint(changed=changed, pr_kind="maintainer")])

    def test_a_patch_entry_file_is_its_project_s_patch_text(self):
        rel = "projects/zlib/project.yaml"
        for file_, message in (("../json/example-patch.patch",
                                "project.patches[0].file: '../json/example-patch.patch' does not match "
                                r"^[A-Za-z0-9][A-Za-z0-9._+-]*\.patch$"),
                               ("missing.patch", "patches[0].file patches/zlib/missing.patch is missing")):
            with self.subTest(file=file_), tree(render=False) as t:
                edit(t, rel, lambda y: y["patches"][0].update(file=file_))
                self.assertIn(rel + ": " + message, errors(t))
        with tree(render=False) as t:
            os.remove(t.path("patches/zlib/example-patch.patch"))
            os.symlink("/dev/zero", t.path("patches/zlib/example-patch.patch"))
            self.assertIn(rel + ": patches[0].file: a symbolic link", errors(t))
        with tree() as t:
            t.write("patches/zlib/stray.patch", "--- a/crc32.c\n")
            self.assertIn("paths patches/zlib/stray.patch: no patches entry of zlib names it",
                          [str(f) for f in t.lint()])

    def test_a_patch_entry_file_is_read_in_the_per_project_layout(self):
        """The entry names a file name, so `oft port-layout` moves the text to projects/<p>/patches/ and leaves
        project.yaml as it was; the rules, lint and the page read it there."""
        rel = "projects/zlib/project.yaml"
        with tree() as t:
            before = t.read(rel)
            self.assertEqual(port.port_worktree(t.root, out=io.StringIO()), 0)
            self.assertEqual(t.read(rel), before)
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertTrue(os.path.isfile(t.path("projects/zlib/patches/example-patch.patch")))
            self.assertEqual([e for e in errors(t) if "patches" in e], [])
            # an empty old folder left behind does not send the entry there (only a file in it would)
            os.makedirs(t.path("patches/zlib"))
            self.assertEqual([e for e in errors(t) if "patches" in e], [])
            os.rmdir(t.path("patches/zlib"))
            os.rmdir(t.path("patches"))
            self.assertIn("[*example-patch*](../../projects/zlib/patches/example-patch.patch)",
                          t.read("projects/zlib/README.md"))
            self.assertEqual([str(f) for f in t.lint() if "patch" in str(f)], [])
            t.write("projects/zlib/patches/stray.patch", "--- a/crc32.c\n")
            self.assertIn("paths projects/zlib/patches/stray.patch: no patches entry of zlib names it",
                          [str(f) for f in t.lint()])
            self.assertEqual([c for c, _, _ in paths.classify("projects/zlib/patches/stray.patch")], ["facts"])
            edit(t, rel, lambda y: y["patches"][0].update(file="missing.patch"))
            self.assertIn(rel + ": patches[0].file projects/zlib/patches/missing.patch is missing", errors(t))

    def test_a_public_patch_file_is_text(self):
        with tree(render=False) as t:
            t.write("patches/zlib/example-patch.patch", b"--- a/zlib.h\0private-data\n", "wb")
            self.assertIn("projects/zlib/project.yaml: patches[0].file contains a NUL byte: a public patch must be text",
                          errors(t))

    def test_a_patch_entry_requires_a_safe_file_name(self):
        with tree(render=False) as t:
            project = t.yaml("projects/zlib/project.yaml")
        for value, message in ((None, "project.patches[0]: missing key 'file'"),
                               ("not-a-patch.txt", "project.patches[0].file: 'not-a-patch.txt' does not match"),
                               ("patches/zlib/example-patch.patch", "project.patches[0].file: "
                                "'patches/zlib/example-patch.patch' does not match"),
                               ("../example-patch.patch", "project.patches[0].file: "
                                "'../example-patch.patch' does not match")):
            with self.subTest(file=value):
                entry = dict(project["patches"][0])
                if value is None:
                    del entry["file"]
                else:
                    entry["file"] = value
                data = dict(project, patches=[entry])
                self.assertTrue(any(message in e for e in schema.validate("project", data)))

    def test_a_patch_without_a_url_renders_its_plain_upstream_state(self):
        with tree() as t:
            page = t.read("projects/zlib/README.md")
            self.assertIn("[*example-patch*](../../patches/zlib/example-patch.patch): A stand-in patch for these "
                          "tests; it describes no change to zlib (not a defect)", page)
            self.assertNotIn("example-patch*](../../patches/zlib/example-patch.patch): A stand-in patch for these "
                             "tests; it describes no change to zlib ([not a defect]", page)

    def test_a_public_finding_has_a_patch_entry_and_no_other_finding_does(self):
        with tree(render=False) as t:
            add_findings(t)
            edit(t, YAML, lambda y: y.update(state="public", upstream="https://bugs.example.org/stand-in-abort"))
            self.assertIn("projects/zlib/project.yaml: public finding stand-in-abort has no patches entry",
                          finding_errors(t))
        with tree(render=False) as t:
            add_findings(t)
            public_patch(t)
            edit(t, YAML, lambda y: y.update(state="reported"))
            self.assertIn("projects/zlib/project.yaml: patches[1] is stand-in-abort, but its finding is reported, "
                          "not public", finding_errors(t))

    def test_a_public_finding_patch_entry_has_its_summary_and_report_url(self):
        for field, value, message in (
                ("summary", "A different summary.",
                 "patches[1].summary differs from public finding stand-in-abort"),
                ("url", "https://bugs.example.org/a-different-report",
                 "patches[1].url differs from public finding stand-in-abort")):
            with self.subTest(field=field), tree(render=False) as t:
                add_findings(t)
                public_patch(t)
                edit(t, "projects/zlib/project.yaml", lambda y: y["patches"][-1].update({field: value}))
                self.assertIn("projects/zlib/project.yaml: " + message, finding_errors(t))

    def test_a_public_finding_patch_entry_has_its_patch_bytes(self):
        with tree(render=False) as t:
            add_findings(t)
            public_patch(t)
            t.write("patches/zlib/0001-stand-in.patch", b"not the finding patch\n", "wb")
            self.assertIn("projects/zlib/project.yaml: patches[1].file differs from public finding stand-in-abort",
                          finding_errors(t))

    def test_a_finding_patch_over_its_cap_is_reported_once(self):
        """A finding's patch is read within the finding cap.  The loader reports one over it, and that error refuses
        the release; the rules do not repeat it."""
        rel = DIR + "/0001-stand-in.patch"
        with tree(render=False) as t:
            add_findings(t)
            with open(t.path(rel), "ab") as f:
                f.write(b"x" * facts.FINDING_FILE_CAP)
            self.assertEqual([e for e in errors(t) if e.startswith(rel)],
                             ["%s: over the %d-byte cap" % (rel, facts.FINDING_FILE_CAP)])

    def test_public_finding_patch_entries_follow_their_series_order(self):
        with tree(render=False) as t:
            add_findings(t)
            public_patch(t)
            second = "findings/zlib/checksum_fuzzer/stand-in-again"
            shutil.copytree(t.path(DIR), t.path(second))
            os.rename(t.path(second, "0001-stand-in.patch"), t.path(second, "0002-stand-in.patch"))
            edit(t, second + "/finding.yaml", lambda y: y.update(patch="0002-stand-in.patch"))
            t.write("findings/zlib/checksum_fuzzer/series", "0002-stand-in.patch\n0001-stand-in.patch\n")
            second_finding = t.yaml(second + "/finding.yaml")
            with open(t.path(second, "0002-stand-in.patch"), "rb") as f:
                entry_patch(t, "zlib", "stand-in-again", "0002-stand-in.patch", f.read(),
                            summary=second_finding["summary"], upstream="reported", url=second_finding["upstream"])
            self.assertIn("projects/zlib/project.yaml: patches entries for checksum_fuzzer are not in the order of "
                          "findings/zlib/checksum_fuzzer/series", finding_errors(t))
            t.write("findings/zlib/checksum_fuzzer/series", "0001-stand-in.patch\n0002-stand-in.patch\n")
            self.assertEqual(finding_errors(t), [])

    def test_a_build_patch_with_no_finding_is_listed_in_patches_and_not_in_the_findings_series(self):
        """A patch the port's series carries that no finding has (make's 0009 and 0010): the facts list it with its
        upstream state, as each public finding's patch, and findings/<p>/<h>/series lists only findings' patches."""
        record = ZLIB_RECORD
        build_only = b"--- a/zutil.c\n+++ b/zutil.c\n@@ -1 +1 @@\n-a stand-in line\n+a build-only line\n"
        with tree(render=False) as t:
            add_findings(t)
            public_patch(t)
            port_built(t, "zlib")
            t.write(record + "build.sh", "make\n")
            self.assertEqual(errors(t), [record + "series: does not list the patch of public finding stand-in-abort, "
                                         "so the published build does not carry it"], "no series lists nothing")
            t.write(record + "series", "0001-stand-in.patch\n")
            self.assertEqual(errors(t), [record + "series: lists 0001-stand-in.patch, which is missing from the "
                                         "port record",
                                         record + "series: does not list the patch of public finding stand-in-abort, "
                                         "so the published build does not carry it"])
            with open(t.path(DIR, "0001-stand-in.patch"), "rb") as f:
                t.write(record + "0001-stand-in.patch", f.read(), "wb")
            t.write(record + "0002-build-only.patch", build_only, "wb")
            t.write(record + "series", "0001-stand-in.patch\n0002-build-only.patch\n")
            self.assertEqual(errors(t), [record + "series: lists 0002-build-only.patch, and no patches entry of zlib "
                                         "has its text"])
            entry_patch(t, "zlib", "build-only", "0002-build-only.patch", build_only,
                        summary="A stand-in build patch for these tests; no finding shows its bug.",
                        upstream="fixed-upstream", url="https://git.example.org/zlib/commit/1")
            self.assertEqual(t.generate(), 0, t.last_output)
            self.assertEqual(errors(t), [])
            t.write(record + "0002-build-only.patch", b"not the patch the port carries\n", "wb")
            self.assertEqual(errors(t), [record + "series: lists 0002-build-only.patch, and no patches entry of zlib "
                                         "has its text"])
            t.write(record + "0002-build-only.patch", build_only, "wb")
            self.assertIn("[*build-only*](../../patches/zlib/0002-build-only.patch): A stand-in build patch for "
                          "these tests; no finding shows its bug ([fixed upstream](https://git.example.org/zlib/commit/1))",
                          t.read("projects/zlib/README.md"))
            self.assertNotIn("0002-build-only.patch", t.read("findings/zlib/checksum_fuzzer/series"))
            t.write("findings/zlib/checksum_fuzzer/series", "0001-stand-in.patch\n0002-build-only.patch\n")
            self.assertEqual(errors(t), ["findings/zlib/checksum_fuzzer/series: lists 0002-build-only.patch, which "
                                         "is the patch of 0 findings that are patched, reported or public, not "
                                         "exactly one"])

    def test_a_shipping_port_series_carries_each_public_finding_s_patch(self):
        """A public finding's patch is listed in the facts because the published build carries it: the copied port
        series of its fuzz target must list it too, so the build record must copy that series."""
        record = ZLIB_RECORD
        with tree(render=False) as t:
            add_findings(t)
            public_patch(t)
            port_built(t, "zlib")
            self.assertFalse(os.path.lexists(t.path(record)))
            self.assertEqual(errors(t), [record + "series: does not list the patch of public finding stand-in-abort, "
                                         "so the published build does not carry it"], "no record lists nothing")
            t.write(record + "build.sh", "make\n")
            t.write(record + "series", "")
            self.assertEqual(errors(t), [record + "series: does not list the patch of public finding stand-in-abort, "
                                         "so the published build does not carry it"])
            with open(t.path(DIR, "0001-stand-in.patch"), "rb") as f:
                t.write(record + "0001-stand-in.patch", f.read(), "wb")
            t.write(record + "series", "0001-stand-in.patch\n")
            self.assertEqual(errors(t), [])

    def test_a_port_record_with_no_build_patches_has_no_series(self):
        """In oss-verify a project's directory has a series only when the project has build patches (6 of its 11
        projects have none), and the record copies that directory, so no series is an empty one.  A patch in the
        record that no series lists is still refused."""
        record = ZLIB_RECORD
        with tree(render=False) as t:
            port_built(t, "zlib")
            t.write(record + "build.sh", "make\n")
            self.assertEqual(errors(t), [])
            t.write(record + "0001-unlisted.patch", b"--- a/x.c\n+++ b/x.c\n@@ -1 +1 @@\n-x\n+y\n", "wb")
            self.assertEqual(errors(t), [record + "0001-unlisted.patch: a patch of the port record that its series "
                                         "does not list"])

    def test_a_pruned_or_not_a_defect_finding_s_patch_may_ship_in_its_build(self):
        """Neither state holds its project back (facts.HOLDING_STATES), so the shipping build may still carry the
        patch: its series lists it, with an entry that shows its text."""
        record = ZLIB_RECORD
        for state in ("pruned", "not-a-defect"):
            with self.subTest(state=state), tree(render=False) as t:
                add_findings(t)
                t.write("findings/zlib/checksum_fuzzer/series", "")
                if state == "pruned":
                    edit(t, YAML, lambda y: y.update(state="pruned",
                                                     input=runs(plain=NORMAL, asan=NORMAL, asan_ubsan=NORMAL)))
                else:
                    edit(t, "projects/zlib/checksum_fuzzer/harness.yaml", lambda y: [y["statements"][s].update(
                        status="suspected-false", basis="reading", reason="A stand-in reason for these tests.")
                        for s in ("asan_agrees", "asan_ubsan_agrees")])
                    edit(t, YAML, lambda y: y.update(state="not-a-defect"))
                port_built(t, "zlib")
                with open(t.path(DIR, "0001-stand-in.patch"), "rb") as f:
                    patch = f.read()
                t.write(record + "0001-stand-in.patch", patch, "wb")
                t.write(record + "series", "0001-stand-in.patch\n")
                entry_patch(t, "zlib", "stand-in-build", "0001-stand-in.patch", patch)
                self.assertEqual(errors(t), [])

    def test_every_patch_of_a_shipping_port_record_is_listed(self):
        """The final review's reproduction: json is kept and port-built, and its port record holds the reported zlib
        finding's patch under a name its empty series does not list.  The rules refuse the unlisted patch; that it
        is a holding finding's patch is the release's search to find (test_hold), in this file as in every other."""
        record = JSON_RECORD
        with tree(render=False) as t:
            add_findings(t)
            edit(t, YAML, lambda y: y.update(state="reported", upstream="https://bugs.example.org/stand-in-abort"))
            port_built(t, "json")
            t.write(record + "build.sh", "make\n")
            t.write(record + "series", "")
            self.assertEqual([e for e in errors(t) if e.startswith("proofs/")], [])
            with open(t.path(DIR, "0001-stand-in.patch"), "rb") as f:
                t.write(record + "0001-unlisted.patch", f.read(), "wb")
            self.assertEqual([e for e in errors(t) if e.startswith("proofs/")], [
                record + "0001-unlisted.patch: a patch of the port record that its series does not list"])

    def test_a_per_project_port_record_is_read_where_it_is(self):
        """The same rules over the record in the per-project layout (review F4), its provenance folder
        projects/<p>/<h>/proofs/provenance/: an unlisted patch is refused, and so is a listed patch no entry has.
        Reading the old place would read nothing there and refuse neither."""
        record = "projects/json/fuzzer-parse_bjdata/proofs/provenance/port/projects/json/"
        with tree(render=False) as t:
            self.assertEqual(port.port_worktree(t.root, out=io.StringIO()), 0)
            port_built(t, "json")
            t.write(record + "build.sh", "make\n")
            t.write(record + "series", "")
            self.assertEqual([e for e in errors(t) if e.startswith("projects/json/")], [])
            t.write(record + "0001-unlisted.patch", b"--- a/x.c\n+++ b/x.c\n@@ -1 +1 @@\n-x\n+y\n", "wb")
            self.assertEqual([e for e in errors(t) if e.startswith("projects/json/fuzzer")], [
                record + "0001-unlisted.patch: a patch of the port record that its series does not list"])
            t.write(record + "series", "0001-unlisted.patch\n")
            self.assertEqual([e for e in errors(t) if e.startswith("projects/json/fuzzer")], [
                record + "series: lists 0001-unlisted.patch, and no patches entry of json has its text"])

    def test_a_build_record_behind_a_symbolic_link_is_refused_and_not_read(self):
        """The deep review's finding 3: os.walk follows a link at its top, and a no-follow open guards only the last
        part of a path, so a link at the build record, or at a directory between it and the copied port directory,
        would have the rules read files outside the checkout.  The link is refused, once, and nothing behind it is
        read."""
        record = "proofs/json/fuzzer-parse_bjdata/provenance"
        for link in (record, record + "/port", JSON_RECORD.rstrip("/")):
            with self.subTest(link=link), tree(render=False) as t, \
                    tempfile.TemporaryDirectory(prefix="oft-outside-") as outside:
                inside = os.path.relpath(JSON_RECORD, link)
                os.makedirs(os.path.join(outside, inside), exist_ok=True)
                with open(os.path.join(outside, inside, "0001-outside.patch"), "wb") as f:
                    f.write(b"--- a/x.c\n+++ b/x.c\n@@ -1 +1 @@\n-x\n+y\n")
                with open(os.path.join(outside, inside, "series"), "wb") as f:
                    f.write(b"0002-missing.patch\n")
                port_built(t, "json")
                os.makedirs(os.path.dirname(t.path(link)), exist_ok=True)
                os.symlink(outside, t.path(link))
                self.assertEqual([e for e in errors(t) if e.startswith("proofs/")],
                                 [link + ": a symbolic link, which the rules do not follow out of the checkout"])

    def test_a_listed_patch_that_is_a_symbolic_link_is_reported_once(self):
        """The final review's test gap: a patch the series lists that cannot be read, a link to a file or to a
        directory, has one error, and the walk does not enter the directory."""
        record = JSON_RECORD
        for target in ("/dev/null", "/etc"):
            with self.subTest(target=target), tree(render=False) as t:
                port_built(t, "json")
                t.write(record + "build.sh", "make\n")
                t.write(record + "series", "0001-build.patch\n")
                os.symlink(target, t.path(record + "0001-build.patch"))
                self.assertEqual([e for e in errors(t) if e.startswith("proofs/")],
                                 [record + "0001-build.patch: a symbolic link"])

    def test_a_nested_patch_with_a_listed_name_is_not_the_one_the_series_lists(self):
        """The build applies the series' patches from the project directory, so a deeper file of a listed name is not
        one of them."""
        record = JSON_RECORD
        build_only = b"--- a/src/json.hpp\n+++ b/src/json.hpp\n@@ -1 +1 @@\n-a json line\n+another json line\n"
        with tree(render=False) as t:
            port_built(t, "json")
            t.write(record + "build.sh", "make\n")
            t.write(record + "0001-build.patch", build_only, "wb")
            t.write(record + "series", "0001-build.patch\n")
            entry_patch(t, "json", "build", "0001-build.patch", build_only)
            self.assertEqual([e for e in errors(t) if e.startswith("proofs/")], [])
            t.write(record + "sub/0001-build.patch", b"--- a/x.c\n+++ b/x.c\n@@ -1 +1 @@\n-x\n+y\n", "wb")
            self.assertEqual([e for e in errors(t) if e.startswith("proofs/")], [
                record + "sub/0001-build.patch: a patch of the port record that its series does not list"])

    def test_a_held_project_need_not_publish_its_port_patches(self):
        """While a finding holds the project, its port record carries patches no facts entry may show yet."""
        record = ZLIB_RECORD
        with tree(render=False) as t:
            add_findings(t)
            port_built(t, "zlib")
            self.assertEqual(facts.hold(facts.load(t.root)).whole, {"zlib"})
            t.write(record + "build.sh", "make\n")
            self.assertEqual(errors(t), [], "no series")
            with open(t.path(DIR, "0001-stand-in.patch"), "rb") as f:
                t.write(record + "0001-stand-in.patch", f.read(), "wb")
            t.write(record + "series", "0001-stand-in.patch\n")
            self.assertEqual(errors(t), [], "an undisclosed patch in the series")

    def test_a_public_patch_over_the_facts_file_cap(self):
        rel = "patches/zlib/example-patch.patch"
        cap = facts.file_cap(rel)
        with tree(render=False) as t:
            t.write(rel, b"x" * (cap + 1), "wb")
            self.assertIn("projects/zlib/project.yaml: patches[0].file: over the %d-byte cap" % cap, errors(t))

    def test_a_build_patch_uses_the_facts_file_cap(self):
        record = ZLIB_RECORD
        large = b"--- a/zutil.c\n+++ b/zutil.c\n" + b"x" * ((64 << 10) + 1)
        with tree(render=False) as t:
            port_built(t, "zlib")
            t.write(record + "build.sh", "make\n")
            t.write(record + "0001-large.patch", large, "wb")
            t.write(record + "series", "0001-large.patch\n")
            entry_patch(t, "zlib", "large-build", "0001-large.patch", large, summary="A large stand-in build patch.")
            self.assertEqual(errors(t), [])

    def test_a_private_project_need_not_publish_its_port_patches(self):
        record = ZLIB_RECORD
        private_patch = b"--- a/zutil.c\n+++ b/zutil.c\n@@ -1 +1 @@\n-a stand-in line\n+a private line\n"
        with tree(render=False) as t:
            port_built(t, "zlib")
            edit(t, "projects/zlib/project.yaml", lambda y: y.update(release="private"))
            t.write(record + "0001-private.patch", private_patch, "wb")
            t.write(record + "series", "0001-private.patch\n")
            self.assertEqual(errors(t), [])


if __name__ == "__main__":
    unittest.main()
