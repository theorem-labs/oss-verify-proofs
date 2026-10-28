"""findings/: the record of a library bug found while proving, the unpatched binaries it runs on, and its rules."""
import os
import shutil
import subprocess
import sys
import unittest

from oft import facts, paths, rules, schema
from oft.tests.helpers import add_findings, older_shape, tree


KEY = "zlib/checksum_fuzzer/stand-in-abort"
DIR = "findings/" + KEY
INTERNAL = "theorem-labs/oss-verify-proofs" + "-internal"

YAML = DIR + "/finding.yaml"
UNPATCHED = "findings/zlib/unpatched.yaml"


def edit(t, rel, change):
    y = t.yaml(rel)
    change(y)
    t.put_yaml(rel, y)


def errors(t, record=False):
    """Every tree error: the loader's and the rules'."""
    loaded = facts.load(t.root, record=record)
    rules.check(loaded)
    return loaded.errors


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
            self.assertEqual(h.unpatched_elf_path("asan"), "findings/zlib/bin/checksum_fuzzer/checksum_fuzzer.asan")

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
        self.assertTrue(paths.ignored("findings/zlib/bin/checksum_fuzzer/checksum_fuzzer.plain"))
        self.assertFalse(paths.ignored(UNPATCHED))
        with tree(render=False) as t:
            add_findings(t)
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
        its own cap (lint.CAPS), apart from the loader's schema error for the same file."""
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
            edit(t, YAML, lambda y: y.update(state="public", upstream="https://bugs.example.org/1"))
            self.assertEqual(finding_errors(t), [internal, attach(zlib, "findings-zlib")])

    def test_a_finding_with_no_runs_meets_the_rules_of_its_state_while_recording(self):
        with tree(render=False) as t:
            add_findings(t)
            edit(t, YAML, lambda y: (y.pop("input"), y.pop("control")))
            self.assertEqual(finding_errors(t, record=True), [])


if __name__ == "__main__":
    unittest.main()
